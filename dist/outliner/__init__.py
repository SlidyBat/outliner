"""Outliner for Binary Ninja.

Loads the native plugin (`liboutliner` next to this file) and provides its
Python API:

    import outliner
    outliner.list_patterns(bv)

Binary Ninja only loads native plugins placed directly in its plugins folder;
this package lets the plugin live in `plugins/outliner/`, together with the
pattern manager script it writes there.  Should Binary Ninja load the library
itself, the plugin reports itself initialised and is not initialised twice.

When Sidekick is installed, the Outliner skill is added to its Library (see
`sidekick_skill`).
"""

from ._native import OutlinerError
from ._native import load as _load

_loaded = _load()

from .api import *  # noqa: E402,F401,F403
from .api import __all__ as _api_names  # noqa: E402
from .sidekick_skill import register_sidekick_skill  # noqa: E402

__all__ = list(_api_names) + ["register_sidekick_skill"]

if _loaded:
    from . import sidekick_skill as _sidekick_skill

    _sidekick_skill.register_setting()
    _sidekick_skill.register_in_background()
