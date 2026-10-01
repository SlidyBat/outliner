"""Adding the Outliner skill to Sidekick's Library when Sidekick is installed.

A background thread waits until Sidekick has initialised, then creates a
Library item holding the skill, which Sidekick's chat can use (`/outliner`)
and its agents can import.  The item records a digest of the skill it was
given, so a newer skill replaces it at the next start unless the user has
edited it in Sidekick.
"""

import hashlib
import json
import sys
import threading
import time
from typing import Dict, Tuple

from binaryninja import Settings, log_info, log_warn

from . import api

LOGGER = "Outliner"
ITEM_NAME = "Outliner"
SKILL_ID = "outliner"
SKILL_PATH = "skills/outliner.md"
DESCRIPTION = "Replace inlined functions with calls by writing Outliner MLIL patterns."
ACCESS_TAGS = ["public", "goal.structure", "file.native"]
DIGEST_KEY = "outliner_skill_sha256"
SETTING = "outliner.sidekickSkill"


def _split_header(document: str) -> Tuple[Dict[str, str], str]:
    """The `key: value` lines of a skill's YAML header, and its body."""
    lines = document.splitlines(keepends=True)
    if not lines or lines[0].strip() != "---":
        return {}, document
    for end in range(1, len(lines)):
        if lines[end].strip() == "---":
            header = {}
            for line in lines[1:end]:
                key, sep, value = line.partition(":")
                if sep and not line.startswith((" ", "\t", "-")):
                    header[key.strip()] = value.strip()
            return header, "".join(lines[end + 1 :])
    return {}, document


def sidekick_document(skill: str) -> str:
    """The skill as a Sidekick skill document: Sidekick's header over the
    skill's body."""
    header, body = _split_header(skill)
    description = header.get("description") or DESCRIPTION
    lines = [
        "---",
        "version: 2",
        f"skill_id: {SKILL_ID}",
        f"name: {ITEM_NAME}",
        f"description: {json.dumps(description)}",
        "access_tags:",
        *(f"  - {tag}" for tag in ACCESS_TAGS),
        "bindings:",
        "  - protocol_id: sidekick",
        f"    skill_name: {SKILL_ID}",
        "---",
    ]
    return "\n".join(lines) + "\n" + body.lstrip("\n")


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def install(app) -> str:
    """Add the Outliner skill to the Library of a running Sidekick
    application, or update the one added earlier.  Returns "added",
    "updated", "current" (already up to date) or "kept" (an item of that name
    that Outliner did not write, or that the user has edited)."""
    from sidekick.foundation.resources import LibraryEntryPoint, LibraryEntryPointKind

    library = app.library
    if library is None:
        raise RuntimeError("Sidekick's Library is unavailable")
    document = sidekick_document(api.skill())
    digest = _digest(document)

    if library.item_exists(ITEM_NAME):
        resolved = app.resolve_library_item(ITEM_NAME)
        if resolved is None:
            raise RuntimeError(f"the Library item {ITEM_NAME!r} exists, but its repository is unavailable")
        repo = resolved.repository
        current = repo.read_file(SKILL_PATH, as_text=True) if repo.file_exists(SKILL_PATH) else None
        if current == document:
            return "current"
        written = repo.get_metadata(DIGEST_KEY)
        if current is None or written is None or _digest(current) != written:
            return "kept"
        repo.write_file(SKILL_PATH, document)
        repo.commit(message=f"Outliner {api.version()}", author=ITEM_NAME)
        repo.set_metadata(DIGEST_KEY, digest)
        return "updated"

    entry_point = LibraryEntryPoint(
        id=SKILL_ID,
        kind=LibraryEntryPointKind.SKILL,
        path=SKILL_PATH,
        title=ITEM_NAME,
        description=DESCRIPTION,
        is_default=True,
    )
    repo = app.create_library_item(
        name=ITEM_NAME,
        initial_files={SKILL_PATH: document},
        entry_points=[entry_point],
        default_entry_point_id=entry_point.id,
        description=DESCRIPTION,
        tags=["outliner", "skill"],
        author=ITEM_NAME,
        draft=False,
    )
    if repo is None:
        raise RuntimeError("Sidekick could not create the Library item")
    repo.set_metadata(DIGEST_KEY, digest)
    return "added"


def _application():
    """Sidekick's application class when the Sidekick plugin is loaded."""
    module = sys.modules.get("sidekick.foundation")
    return getattr(module, "SidekickApplication", None) if module is not None else None


def register_sidekick_skill() -> str:
    """Add the Outliner skill to Sidekick's Library now, or update it (see
    `install`).  Sidekick must be loaded and initialised."""
    application = _application()
    if application is None or not application.is_initialized():
        raise api.OutlinerError("Sidekick is not loaded")
    return install(application.get_instance())


def register_setting() -> None:
    Settings().register_setting(
        SETTING,
        json.dumps(
            {
                "title": "Add Skill to Sidekick",
                "type": "boolean",
                "default": True,
                "description": (
                    "When Sidekick is installed, add the Outliner skill to its Library at startup and "
                    "update it when Outliner's changes, unless it was edited in Sidekick. While this is "
                    "on, a deleted skill is added again at the next start."
                ),
                "ignore": ["SettingsProjectScope", "SettingsResourceScope"],
            }
        ),
    )


def register_in_background(timeout: float = 120.0) -> None:
    """Wait on a background thread for Sidekick to initialise, then add the
    skill.  Does nothing when the setting is off or Sidekick is not installed."""
    if not Settings().get_bool(SETTING):
        return

    def worker():
        deadline = time.monotonic() + timeout
        application = None
        while time.monotonic() < deadline:
            application = _application()
            if application is not None and application.is_initialized() and application.get_instance().library is not None:
                break
            time.sleep(0.5)
        else:
            if application is not None:
                log_warn("Sidekick did not finish initializing; the Outliner skill was not added to its Library", LOGGER)
            return
        try:
            status = install(application.get_instance())
        except Exception as e:
            log_warn(f"Could not add the Outliner skill to Sidekick's Library: {e}", LOGGER)
            return
        if status == "added":
            log_info("Added the Outliner skill to Sidekick's Library", LOGGER)
        elif status == "updated":
            log_info("Updated the Outliner skill in Sidekick's Library", LOGGER)

    threading.Thread(target=worker, name="OutlinerSidekickSkill", daemon=True).start()
