"""Pattern manager dialog: one tab per pattern down the left side, the pattern
text in the middle, the decompiler's view of a drafted pattern's source code
on the right.  The X on a tab deletes the pattern, clicking one edits it,
Test runs every tab over the binary without changing it, Merge Into...
generalises one tab with another instance of its code, Apply validates every
tab and saves them all at once.

Run by the Outliner plugin inside Binary Ninja's Python; the patterns are
read, validated, drafted, tested and saved by the plugin through its C API,
so the dialog holds no logic of its own.  The side tabs are a themed list
widget driving a stack of editors rather than a QTabWidget with west tabs,
which would draw rotated labels."""

import ctypes
import json
import re

import binaryninja
from binaryninja import execute_on_main_thread_and_wait, log_error, log_info

PLUGIN_PATH = "@@PLUGIN@@"
VIEW_HANDLE = "@@VIEW@@"
FUNCTION = int("@@FUNCTION@@", 0)          # the function the user is looking at (0: none)
DRAFT = json.loads("@@DRAFT@@")            # a pattern drafted from code, or None
LOGGER = "Outliner"

try:
    from PySide6 import QtCore, QtGui, QtWidgets
    HAVE_QT = True
except ImportError:  # headless
    HAVE_QT = False


class Api:
    """The plugin's C API, over the library the core already loaded."""

    def __init__(self, path):
        lib = ctypes.CDLL(path)
        void, text, chars = ctypes.c_void_p, ctypes.c_char_p, ctypes.POINTER(ctypes.c_char)
        for name, args, ret in [
            ("outliner_free_string", [chars], None),
            ("outliner_list_patterns", [void], chars),
            ("outliner_validate_pattern", [void, text], chars),
            ("outliner_save_patterns", [void, text, ctypes.c_bool], chars),
            ("outliner_split_chunks", [text], chars),
            ("outliner_join_chunks", [text], chars),
            ("outliner_chunk_title", [text], chars),
            ("outliner_chunk_key", [text], chars),
            ("outliner_pattern_template", [], chars),
            ("outliner_preview", [void, text, text, text], chars),
            ("outliner_preview_start", [void, text, text, text], ctypes.c_uint64),
            ("outliner_preview_poll", [ctypes.c_uint64], chars),
            ("outliner_preview_cancel", [ctypes.c_uint64], None),
            ("outliner_preview_result", [ctypes.c_uint64], chars),
            ("outliner_generalize", [text, text], chars),
            ("outliner_draft_region", [void, ctypes.c_uint64, ctypes.c_uint64], chars),
            ("outliner_draft_indices", [void, ctypes.c_uint64, ctypes.c_uint32, ctypes.c_uint32], chars),
        ]:
            f = getattr(lib, name)
            f.argtypes, f.restype = args, ret
        self.lib = lib

    def _take(self, p):
        if not p:
            return None
        s = ctypes.cast(p, ctypes.c_char_p).value.decode("utf-8", "replace")
        self.lib.outliner_free_string(p)
        return s

    @staticmethod
    def _view(bv):
        return ctypes.cast(bv.handle, ctypes.c_void_p)

    def list_patterns(self, bv):
        return json.loads(self._take(self.lib.outliner_list_patterns(self._view(bv))) or "[]")

    def validate(self, bv, text):
        """The record a pattern text makes, or a ValueError with the message for the user."""
        answer = json.loads(self._take(self.lib.outliner_validate_pattern(self._view(bv), text.encode())) or "{}")
        if not answer.get("ok"):
            raise ValueError(answer.get("error", "invalid pattern"))
        return answer["record"]

    def save(self, bv, records):
        err = self._take(self.lib.outliner_save_patterns(self._view(bv), json.dumps(records).encode(), True))
        if err:
            raise ValueError(err)

    def split_chunks(self, content):
        return json.loads(self._take(self.lib.outliner_split_chunks(content.encode())) or "[]")

    def join_chunks(self, chunks):
        return self._take(self.lib.outliner_join_chunks(json.dumps(chunks).encode())) or ""

    def chunk_title(self, text):
        return self._take(self.lib.outliner_chunk_title(text.encode())) or ""

    def chunk_key(self, text):
        return self._take(self.lib.outliner_chunk_key(text.encode())) or ""

    def template(self):
        return self._take(self.lib.outliner_pattern_template()) or ""

    @staticmethod
    def _preview_args(texts, focus, only):
        focus = [focus] if focus else []
        only = None if only is None else [only]
        return json.dumps(texts).encode(), json.dumps(focus).encode(), json.dumps(only).encode()

    def preview(self, bv, texts, focus, only=None):
        return json.loads(self._take(self.lib.outliner_preview(self._view(bv), *self._preview_args(texts, focus, only))) or "{}")

    def preview_start(self, bv, texts, focus, only=None):
        return self.lib.outliner_preview_start(self._view(bv), *self._preview_args(texts, focus, only))

    def preview_poll(self, job):
        return json.loads(self._take(self.lib.outliner_preview_poll(job)) or "{}")

    def preview_cancel(self, job):
        self.lib.outliner_preview_cancel(job)

    def preview_result(self, job):
        return json.loads(self._take(self.lib.outliner_preview_result(job)) or "{}")

    def generalize(self, base, other):
        return json.loads(self._take(self.lib.outliner_generalize(base.encode(), other.encode())) or "{}")

    def draft_region(self, bv, start, end):
        return json.loads(self._take(self.lib.outliner_draft_region(self._view(bv), start, end)) or "{}")

    def draft_indices(self, bv, function, first, last):
        return json.loads(self._take(self.lib.outliner_draft_indices(self._view(bv), function, first, last)) or "{}")


def _selected_mlil_range():
    """The MLIL instruction indices the user selected in the current view,
    when that view shows (non-SSA) MLIL: (first, last) inclusive, else None."""
    try:
        from binaryninja.enums import FunctionGraphType
        from binaryninjaui import UIContext
        ctx = UIContext.activeContext()
        view = ctx.getCurrentView() if ctx is not None else None
        if view is None:
            return None
        if view.getILViewType().view_type != FunctionGraphType.MediumLevelILFunctionGraph:
            return None
        a, b = view.getSelectionStartILInstructionIndex(), view.getCurrentILInstructionIndex()
        if a is None or b is None or a >= 0xffffffff or b >= 0xffffffff:
            return None
        return min(a, b), max(a, b)
    except Exception:
        return None


def _resolve_draft(api, bv, request):
    """A draft for the selection the plugin's command was run on: by the
    selected instructions when the view can say, else by the address range."""
    indices = _selected_mlil_range()
    if indices is not None:
        draft = api.draft_indices(bv, request["function"], indices[0], indices[1])
        if draft.get("ok"):
            return draft
    return api.draft_region(bv, request["start"], request["end"])


if HAVE_QT:

    def _enum(owner, group, name):
        scoped = getattr(owner, group, None)
        if scoped is not None and hasattr(scoped, name):
            return getattr(scoped, name)
        return getattr(owner, name)

    class PatternHighlighter(QtGui.QSyntaxHighlighter):
        """Placeholders, keywords, directives, labels, strings and comments."""

        def __init__(self, document):
            super().__init__(document)

            def fmt(color=None, bold=False):
                f = QtGui.QTextCharFormat()
                if color:
                    f.setForeground(QtGui.QColor(color))
                if bold:
                    f.setFontWeight(QtGui.QFont.Weight.Bold)
                return f

            keywords = r"\b(if|then|else|goto|call|intrinsic|return|nop|noret|when)\b"
            self.rules = [
                (re.compile(r"^\s*(signature|result|branch|value|rewrite|rules)\s*:"), fmt("#9b59b6", True)),
                (re.compile(r"^\s*[A-Za-z_][A-Za-z0-9_]*:\s*(?=$|#|//)"), fmt("#2aa198", True)),
                (re.compile(keywords), fmt(None, True)),
                (re.compile(r"\$[A-Za-z_][A-Za-z0-9_]*"), fmt("#4a90d9")),
                (re.compile(r'"[^"]*"'), fmt("#c07830")),
                (re.compile(r"(#|//).*$"), fmt("#8a8a8a")),
            ]

        def highlightBlock(self, text):
            for pattern, style in self.rules:
                for m in pattern.finditer(text):
                    self.setFormat(m.start(), m.end() - m.start(), style)

    class LineNumbers(QtWidgets.QWidget):
        """The margin of a PatternEditor, where it draws its line numbers."""

        def __init__(self, editor):
            super().__init__(editor)
            self.editor = editor

        def sizeHint(self):
            return QtCore.QSize(self.editor.line_number_width(), 0)

        def paintEvent(self, event):
            self.editor.paint_line_numbers(event)

    class PatternEditor(QtWidgets.QPlainTextEdit):
        """A plain text editor with line numbers in its left margin, so the
        lines that errors and test results name can be found."""

        def __init__(self, parent=None):
            super().__init__(parent)
            self._numbers = LineNumbers(self)
            self.blockCountChanged.connect(self._update_width)
            self.updateRequest.connect(self._update_numbers)
            self._update_width()

        def line_number_width(self):
            digits = max(2, len(str(self.blockCount())))
            return 12 + self.fontMetrics().horizontalAdvance("9") * digits

        def _update_width(self, *_):
            self.setViewportMargins(self.line_number_width(), 0, 0, 0)

        def _update_numbers(self, rect, dy):
            if dy:
                self._numbers.scroll(0, dy)
            else:
                self._numbers.update(0, rect.y(), self._numbers.width(), rect.height())
            if rect.contains(self.viewport().rect()):
                self._update_width()

        def changeEvent(self, event):
            super().changeEvent(event)
            if event.type() == _enum(QtCore.QEvent, "Type", "FontChange"):
                self._update_width()

        def resizeEvent(self, event):
            super().resizeEvent(event)
            area = self.contentsRect()
            self._numbers.setGeometry(QtCore.QRect(area.left(), area.top(), self.line_number_width(), area.height()))

        def paint_line_numbers(self, event):
            painter = QtGui.QPainter(self._numbers)
            palette = self.palette()
            painter.fillRect(event.rect(), palette.color(_enum(QtGui.QPalette, "ColorRole", "Window")))
            painter.setPen(palette.color(_enum(QtGui.QPalette, "ColorRole", "PlaceholderText")))
            painter.setFont(self.font())
            right = _enum(QtCore.Qt, "AlignmentFlag", "AlignRight")
            width = self._numbers.width() - 6
            height = self.fontMetrics().height()
            block = self.firstVisibleBlock()
            number = block.blockNumber()
            top = round(self.blockBoundingGeometry(block).translated(self.contentOffset()).top())
            bottom = top + round(self.blockBoundingRect(block).height())
            while block.isValid() and top <= event.rect().bottom():
                if block.isVisible() and bottom >= event.rect().top():
                    painter.drawText(0, top, width, height, right, str(number + 1))
                block = block.next()
                top = bottom
                bottom = top + round(self.blockBoundingRect(block).height())
                number += 1
            painter.end()

    class PatternManagerDialog(QtWidgets.QDialog):
        def __init__(self, api, bv, parent=None):
            super().__init__(parent)
            self.api = api
            self.bv = bv
            self.setWindowTitle("Outliner Patterns")
            self.resize(1180, 700)
            self._pages = []
            self._deleted_ids = set()

            self.tabs = QtWidgets.QListWidget(self)
            self.tabs.setFixedWidth(220)
            self.tabs.setSpacing(1)
            self.tabs.setSelectionMode(_enum(QtWidgets.QAbstractItemView, "SelectionMode", "SingleSelection"))
            self.stack = QtWidgets.QStackedWidget(self)
            self.tabs.currentRowChanged.connect(self._page_changed)

            # The decompiler's view of a drafted pattern's source, shown beside the editor.
            self.side = QtWidgets.QPlainTextEdit(self)
            self.side.setReadOnly(True)
            self.side.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
            self.side.setLineWrapMode(_enum(QtWidgets.QPlainTextEdit, "LineWrapMode", "NoWrap"))
            self.side.setPlaceholderText("The decompiler's view of the code a pattern was drafted from appears here.")
            self.side.hide()

            body = QtWidgets.QHBoxLayout()
            body.setSpacing(6)
            body.addWidget(self.tabs)
            body.addWidget(self.stack, 3)
            body.addWidget(self.side, 2)

            self.status = QtWidgets.QLabel("")
            self.status.setWordWrap(True)
            self.status.setTextInteractionFlags(_enum(QtCore.Qt, "TextInteractionFlag", "TextSelectableByMouse"))

            # Where Test reports.
            self.results = QtWidgets.QPlainTextEdit(self)
            self.results.setReadOnly(True)
            self.results.setFont(QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont))
            self.results.setMaximumHeight(180)
            self.results.hide()

            new_btn = QtWidgets.QPushButton("New Pattern")
            new_btn.clicked.connect(self._new_pattern)
            load_btn = QtWidgets.QPushButton("Load File...")
            load_btn.clicked.connect(self._load_file)
            save_btn = QtWidgets.QPushButton("Save File...")
            save_btn.setToolTip("Write every pattern shown here, edits included, to a .pattern file")
            save_btn.clicked.connect(self._save_file)
            test_btn = QtWidgets.QPushButton("Test")
            test_btn.setToolTip("Match this tab's pattern against the whole binary without changing it, and explain "
                                "what stops it from matching the function you came from")
            test_btn.clicked.connect(self._test)
            merge_btn = QtWidgets.QPushButton("Merge Into...")
            merge_btn.setToolTip("Generalise another tab with this one, a second instance of the same code: "
                                 "constants that differ become placeholders; a different shape stays its own chunk")
            merge_btn.clicked.connect(self._merge)
            apply_btn = QtWidgets.QPushButton("Apply")
            apply_btn.setDefault(True)
            apply_btn.clicked.connect(self._apply)
            close_btn = QtWidgets.QPushButton("Close")
            close_btn.clicked.connect(self.reject)

            buttons = QtWidgets.QHBoxLayout()
            buttons.addWidget(new_btn)
            buttons.addWidget(load_btn)
            buttons.addWidget(save_btn)
            buttons.addWidget(test_btn)
            buttons.addWidget(merge_btn)
            buttons.addStretch(1)
            buttons.addWidget(apply_btn)
            buttons.addWidget(close_btn)

            layout = QtWidgets.QVBoxLayout(self)
            layout.addLayout(body, 1)
            layout.addWidget(self.status)
            layout.addWidget(self.results)
            layout.addLayout(buttons)

            QtGui.QShortcut(QtGui.QKeySequence.StandardKey.Save, self, activated=self._apply)

            for record in api.list_patterns(bv):
                self._add_page(record["full_text"], record)
            draft = DRAFT
            if draft and draft.get("request"):
                draft = _resolve_draft(api, bv, draft)
            if draft and draft.get("ok"):
                index = self._add_page(draft["text"], None, source=draft)
                self.tabs.setCurrentRow(index)
                notes = draft.get("notes") or []
                self.status.setText(f"Drafted from {draft['name']}. Name the function in the signature line, "
                                    f"then Apply." + ("".join("\n- " + n for n in notes)))
            elif draft:
                if self._pages:
                    self.tabs.setCurrentRow(0)
                self._error(f"Could not draft a pattern: {draft.get('error') or 'unknown error'}")
            elif self._pages:
                self.tabs.setCurrentRow(0)
            else:
                self.status.setText("No patterns yet: New Pattern starts one from a template, Load File... reads a "
                                    "pattern file, and Outliner > Create Pattern From Selection... drafts one "
                                    "from code you select in the MLIL view.")

        # -- tabs -------------------------------------------------------------
        def _add_page(self, text, record, source=None):
            editor = PatternEditor()
            font = QtGui.QFontDatabase.systemFont(QtGui.QFontDatabase.SystemFont.FixedFont)
            editor.setFont(font)
            editor.setPlainText(text)
            editor.setLineWrapMode(_enum(QtWidgets.QPlainTextEdit, "LineWrapMode", "NoWrap"))
            editor.setTabStopDistance(4 * editor.fontMetrics().horizontalAdvance(" "))
            highlighter = PatternHighlighter(editor.document())

            # One row in the side list: the name and an X button.
            row = QtWidgets.QWidget()
            row_layout = QtWidgets.QHBoxLayout(row)
            row_layout.setContentsMargins(8, 4, 4, 4)
            label = QtWidgets.QLabel(self.api.chunk_title(text))
            close = QtWidgets.QToolButton()
            close.setText("✕")
            close.setAutoRaise(True)
            close.setToolTip("Delete this pattern")
            close.setCursor(_enum(QtCore.Qt, "CursorShape", "PointingHandCursor"))
            row_layout.addWidget(label, 1)
            row_layout.addWidget(close)

            item = QtWidgets.QListWidgetItem()
            item.setSizeHint(row.sizeHint())
            page = {"record": record, "editor": editor, "saved_text": text if record else None,
                    "label": label, "item": item, "source": source, "highlighter": highlighter}
            self.tabs.addItem(item)
            self.tabs.setItemWidget(item, row)
            self.stack.addWidget(editor)
            self._pages.append(page)
            editor.textChanged.connect(lambda p=page: self._mark(p))
            close.clicked.connect(lambda _=False, p=page: self._close_tab(p))
            return len(self._pages) - 1

        def _index_of(self, page):
            return self._pages.index(page)

        def _current(self):
            row = self.tabs.currentRow()
            return self._pages[row] if 0 <= row < len(self._pages) else None

        def _page_changed(self, row):
            self.stack.setCurrentIndex(row)
            page = self._pages[row] if 0 <= row < len(self._pages) else None
            source = page and page.get("source")
            if not source:
                self.side.hide()
                return
            self.side.setPlainText(self._decompiled(source))
            self.side.show()

        def _decompiled(self, source):
            """The HLIL of the code a draft came from."""
            try:
                func = self.bv.get_function_at(source["function"])
                if func is None or func.hlil is None:
                    return "(no HLIL)"
                start, end = source["start"], source["end"]
                whole = end <= start
                lines = [f"# {func.name}" + ("" if whole else f" {start:#x}-{end:#x}"), ""]
                for instr in func.hlil.instructions:
                    if whole or start <= instr.address < end:
                        lines.append(f"{instr.address:#x}  {instr}")
                return "\n".join(lines)
            except Exception as e:
                return f"(could not render the HLIL: {e!r})"

        def _mark(self, page):
            text = page["editor"].toPlainText()
            modified = text != page["saved_text"]
            page["label"].setText(self.api.chunk_title(text) + (" *" if modified else ""))

        def _close_tab(self, page, ask=True):
            index = self._index_of(page)
            name = self.api.chunk_title(page["editor"].toPlainText())
            if ask:
                answer = QtWidgets.QMessageBox.question(
                    self, "Delete pattern", f"Delete the pattern '{name}'?\n(Takes effect when you press Apply.)")
                if answer != _enum(QtWidgets.QMessageBox, "StandardButton", "Yes"):
                    return
            if page["record"] is not None:
                self._deleted_ids.add(page["record"]["id"])
            self.tabs.takeItem(index)
            self.stack.removeWidget(page["editor"])
            page["editor"].deleteLater()
            self._pages.pop(index)
            if self._pages:
                self.tabs.setCurrentRow(min(index, len(self._pages) - 1))
            if ask:
                self.status.setStyleSheet("")
                self.status.setText(f"Marked '{name}' for deletion; press Apply to save.")

        def _new_pattern(self):
            index = self._add_page(self.api.template(), None)
            self.tabs.setCurrentRow(index)
            self._pages[index]["editor"].setFocus()

        def _load_file(self):
            path, _ = QtWidgets.QFileDialog.getOpenFileName(self, "Load pattern file", "",
                                                            "Pattern files (*.pattern *.txt);;All files (*)")
            if not path:
                return
            try:
                with open(path, "r", encoding="utf-8") as f:
                    content = f.read()
            except OSError as e:
                self._error(f"Could not read {path}: {e}")
                return
            # A pattern already in a tab (saved or not), or earlier in the file, is
            # skipped; comments and spacing do not make a pattern different.
            present = {self.api.chunk_key(page["editor"].toPlainText()) for page in self._pages}
            added = skipped = 0
            for chunk in self.api.split_chunks(content):
                if not chunk.strip():
                    continue
                key = self.api.chunk_key(chunk)
                if key in present:
                    skipped += 1
                    continue
                present.add(key)
                self._add_page(chunk.strip("\n") + "\n", None)
                added += 1
            if added:
                self.tabs.setCurrentRow(len(self._pages) - 1)
            message = f"Loaded {added} pattern(s) from {path}"
            if skipped:
                message += f", skipped {skipped} already present"
            self.status.setStyleSheet("")
            self.status.setText(message + ("; press Apply to save." if added else "."))

        def _save_file(self):
            """Write the patterns as shown (edits included, whether applied or not)
            to a file that Load File... reads back."""
            if not self._pages:
                self._error("There are no patterns to save.")
                return
            path, _ = QtWidgets.QFileDialog.getSaveFileName(self, "Save pattern file", "patterns.pattern",
                                                            "Pattern files (*.pattern);;All files (*)")
            if not path:
                return
            if "." not in path.rsplit("/", 1)[-1]:
                path += ".pattern"
            content = self.api.join_chunks([page["editor"].toPlainText() for page in self._pages])
            try:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(content)
            except OSError as e:
                self._error(f"Could not write {path}: {e}")
                return
            self.status.setStyleSheet("")
            self.status.setText(f"Saved {len(self._pages)} pattern(s) to {path}.")

        # -- testing -----------------------------------------------------------
        def _test(self):
            page = self._current()
            if page is None:
                self._error("There are no patterns to test.")
                return
            # Only the selected tab's pattern is tested and reported; the
            # other tabs take part, since a pattern may match only code
            # another one outlined (an accessor call, say).
            texts = [p["editor"].toPlainText() for p in self._pages]
            job = self.api.preview_start(self.bv, texts, FUNCTION, self._pages.index(page))
            if not job:
                self._error("The test could not be started.")
                return
            # The test runs on worker threads of its own; a modal progress
            # dialog keeps the UI responsive and lets the user stop early.
            progress = QtWidgets.QProgressDialog("Testing the pattern...", "Cancel", 0, 0, self)
            progress.setWindowTitle("Outliner")
            progress.setWindowModality(_enum(QtCore.Qt, "WindowModality", "WindowModal"))
            progress.setMinimumDuration(0)
            progress.setAutoClose(False)
            progress.setAutoReset(False)
            progress.canceled.connect(lambda: self.api.preview_cancel(job))
            timer = QtCore.QTimer(self)
            timer.setInterval(100)

            def tick():
                state = self.api.preview_poll(job)
                total = state.get("total", 0)
                done = state.get("processed", 0)
                if total:
                    progress.setMaximum(total)
                    progress.setValue(done)
                    progress.setLabelText("Stopping..." if state.get("cancelled") else f"Testing the pattern: {done} of {total} functions")
                if state.get("done"):
                    timer.stop()
                    progress.close()
                    progress.deleteLater()
                    self._show_test(self.api.preview_result(job), page)

            timer.timeout.connect(tick)
            timer.start()
            progress.show()

        def _show_test(self, report, page):
            if report.get("message"):
                self.results.hide()
                self._error(report["message"])
                return
            entries = report.get("patterns", [])
            if not entries:
                self._error("The test produced no report.")
                return
            entry = entries[0]
            title = entry.get("title") or "(untitled)"
            if entry.get("error"):
                self.results.hide()
                self._error(f"{title} does not compile: {entry['error']}", page)
                return
            hits = entry.get("hits", [])
            functions = sorted({h["function"] for h in hits})
            lines = [f"{title}: {len(hits)} match(es) in {len(functions)} function(s)"
                     + (f": {', '.join(functions[:8])}" + (" ..." if len(functions) > 8 else "") if hits else "")]
            for h in hits[:12]:
                when = f", round {h['round']}" if h.get("round", 1) > 1 else ""
                lines.append(f"    {h['function']} @ {h['address']:#x} ({h['kind']}{when}, MLIL {h['instr']}): {h['text']}")
            if len(hits) > 12:
                lines.append(f"    ... and {len(hits) - 12} more")
            for k, d in enumerate(entry.get("diagnoses") or []):
                where = f"line {d['line']}" if d.get("line") else "its first statement"
                lines.append(f"    no match in {d['function']}: {d['matched']} statement(s) matched, then {where} "
                             f"failed against MLIL {d['instr']} `{d['code']}`: {d['reason']}")
                if k == 0 and d.get("line"):
                    self._goto_line(page, d["line"])
            left_out = report.get("left_out") or []
            if left_out:
                lines.append(f"Left out because they do not compile: {', '.join(left_out)}")
            self.results.setPlainText("\n".join(lines))
            self.results.show()
            self.status.setStyleSheet("")
            skipped = report.get("skipped", 0)
            note = f" ({skipped} without MLIL yet were skipped)" if skipped else ""
            how = "Stopped after" if report.get("cancelled") else "Tested"
            self.status.setText(f"{how} {report.get('functions', 0)} function(s){note} as the workflow would run this pattern, "
                                "with the other tabs taking part, on the code as it was before outlining; nothing was changed.")

        # -- generalising ------------------------------------------------------
        def _merge(self):
            current = self._current()
            if current is None or len(self._pages) < 2:
                self._error("Merge needs this tab and another one to merge it into.")
                return
            others = [p for p in self._pages if p is not current]
            titles = [self.api.chunk_title(p["editor"].toPlainText()) for p in others]
            choice, ok = QtWidgets.QInputDialog.getItem(
                self, "Merge into", "Generalise this pattern into:", titles, 0, False)
            if not ok:
                return
            target = others[titles.index(choice)]
            answer = self.api.generalize(target["editor"].toPlainText(), current["editor"].toPlainText())
            kind = answer.get("kind")
            if kind == "merged":
                target["editor"].setPlainText(answer["text"])
                notes = answer.get("notes") or []
                if current["record"] is None:
                    self._close_tab(current, ask=False)
                self.tabs.setCurrentRow(self._index_of(target))
                self.status.setStyleSheet("")
                self.status.setText("Merged: one pattern now covers both instances; press Apply to save."
                                    + "".join("\n- " + n for n in notes))
            elif kind == "chunk":
                current["editor"].setPlainText(answer["text"])
                self.status.setStyleSheet("")
                self.status.setText("The instances differ in shape, so this tab stays a chunk of its own "
                                    f"with the other's signature ({'; '.join(answer.get('notes') or [])}). "
                                    "Both are saved on Apply.")
            else:
                self._error(answer.get("error") or "Could not merge the patterns.")

        # -- saving -------------------------------------------------------------
        def _apply(self):
            records = []
            for page in self._pages:
                text = page["editor"].toPlainText()
                try:
                    record = self.api.validate(self.bv, text)
                except ValueError as e:
                    self.tabs.setCurrentRow(self._index_of(page))
                    self._error(str(e), page)
                    return
                if page["record"] is not None:
                    record["id"] = page["record"]["id"]
                records.append((page, record))
            try:
                self.api.save(self.bv, [r for _, r in records])
            except ValueError as e:
                self._error(f"Could not save patterns: {e}")
                return
            saved = {r["id"]: r for r in self.api.list_patterns(self.bv)}
            for page, record in records:
                page["record"] = saved.get(record.get("id"), record)
                page["saved_text"] = page["editor"].toPlainText()
                self._mark(page)
            self._deleted_ids.clear()
            self.status.setStyleSheet("")
            self.status.setText(f"Saved {len(records)} pattern(s); functions are being reanalyzed.")
            log_info(f"saved {len(records)} pattern(s) from the manager", LOGGER)

        def _goto_line(self, page, line):
            editor = page["editor"]
            block = editor.document().findBlockByNumber(max(0, int(line) - 1))
            if block.isValid():
                cursor = QtGui.QTextCursor(block)
                cursor.select(_enum(QtGui.QTextCursor, "SelectionType", "LineUnderCursor"))
                editor.setTextCursor(cursor)
                editor.setFocus()

        def _error(self, message, page=None):
            self.status.setStyleSheet("color: #d04040;")
            self.status.setText(message)
            m = re.search(r"\bline (\d+)", message)
            if m and page is not None:
                self._goto_line(page, int(m.group(1)))

        # -- closing ------------------------------------------------------------
        def _unsaved(self):
            if self._deleted_ids:
                return True
            return any(p["editor"].toPlainText() != p["saved_text"] for p in self._pages)

        def reject(self):
            if self._unsaved():
                answer = QtWidgets.QMessageBox.question(
                    self, "Unsaved changes", "Discard unsaved pattern changes?")
                if answer != _enum(QtWidgets.QMessageBox, "StandardButton", "Yes"):
                    return
            super().reject()


def _view():
    """The view the command was invoked on: the console's `bv` when the
    scripting instance bound it, else the handle the plugin passed."""
    view = globals().get("bv")
    if view is not None:
        return view
    from binaryninja import _binaryninjacore as core
    handle = ctypes.cast(int(VIEW_HANDLE, 0), core.BNBinaryViewHandle)
    return binaryninja.BinaryView(handle=core.BNNewViewReference(handle))


def _open(api, view):
    parent = None
    try:
        from binaryninjaui import UIContext
        ctx = UIContext.activeContext()
        if ctx is not None:
            parent = ctx.mainWindow()
    except Exception:
        parent = None
    PatternManagerDialog(api, view, parent).exec()


def show():
    if not HAVE_QT:
        log_error("Qt is not available; register patterns through the plugin's C API instead", LOGGER)
        return
    try:
        api = Api(PLUGIN_PATH)
        view = _view()
    except Exception as e:
        log_error(f"could not open the pattern manager: {e!r}", LOGGER)
        return
    execute_on_main_thread_and_wait(lambda: _open(api, view))


show()
