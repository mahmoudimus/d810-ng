import abc
import contextlib
import importlib
import sys

import ida_hexrays
import ida_kernwin
import idaapi

import d810
import d810._compat as _compat

D810_VERSION = "0.1"


def init_hexrays() -> bool:
    ALL_DECOMPILERS = {
        idaapi.PLFM_386: "hexx64",
        idaapi.PLFM_ARM: "hexarm",
        idaapi.PLFM_PPC: "hexppc",
        idaapi.PLFM_MIPS: "hexmips",
        idaapi.PLFM_RISCV: "hexrv",
    }
    cpu = idaapi.ph.id
    decompiler = ALL_DECOMPILERS.get(cpu, None)
    if not decompiler:
        print("No known decompilers for architecture with ID: %d" % idaapi.ph.id)
        return False
    if idaapi.load_plugin(decompiler) and idaapi.init_hexrays_plugin():
        return True
    else:
        print(f"Couldn't load or initialize decompiler: {decompiler}")
        return False


class _UIHooks(idaapi.UI_Hooks):

    def ready_to_run(self):
        pass


class Plugin(abc.ABC, idaapi.plugin_t):

    @abc.abstractmethod
    def init(self): ...

    @_compat.override
    @abc.abstractmethod
    def run(self, args): ...

    @_compat.override
    @abc.abstractmethod
    def term(self): ...


class LateInitPlugin(Plugin):

    def __init__(self):
        super().__init__()
        self._ui_hooks: _UIHooks = _UIHooks()

    @_compat.override
    def init(self):
        self._ui_hooks.ready_to_run = self.ready_to_run
        if not self._ui_hooks.hook():
            print("LateInitPlugin.__init__ hooking failed!", file=sys.stderr)
            return idaapi.PLUGIN_SKIP
        return idaapi.PLUGIN_OK

    def ready_to_run(self):
        self.late_init()
        self._ui_hooks.unhook()

    @abc.abstractmethod
    def late_init(self): ...


class ReloadablePlugin(LateInitPlugin, idaapi.action_handler_t):
    def __init__(
        self,
        *,
        global_name: str,
        base_package_name: str,
        plugin_class: str,
    ):
        super().__init__()
        self.global_name = global_name
        self.base_package_name = base_package_name
        self.plugin_class = plugin_class
        self.plugin = self._import_plugin_cls()

    def _import_plugin_cls(self):
        self.plugin_module, self.plugin_class_name = self.plugin_class.rsplit(".", 1)
        mod = importlib.import_module(self.plugin_module)
        return getattr(mod, self.plugin_class_name)()

    @_compat.override
    def update(self, ctx: ida_kernwin.action_ctx_base_t) -> int:
        return idaapi.AST_ENABLE_ALWAYS

    @_compat.override
    def activate(self, ctx: ida_kernwin.action_ctx_base_t):
        with self.plugin_setup_reload():
            self.reload()
        return 1

    @_compat.override
    def late_init(self):
        self.add_plugin_to_console()
        self.register_reload_action()

    @_compat.override
    def term(self):
        self.unregister_reload_action()
        if self.plugin is not None and hasattr(self.plugin, "unload"):
            self.plugin.unload()

    def register_reload_action(self):
        idaapi.register_action(
            idaapi.action_desc_t(
                f"{self.global_name}:reload_plugin",
                f"Reload plugin: {self.global_name}",
                self,
            )
        )

    def unregister_reload_action(self):
        idaapi.unregister_action(f"{self.global_name}:reload_plugin")

    def add_plugin_to_console(self):
        # add plugin to the IDA python console scope, for test/dev/cli access
        setattr(sys.modules["__main__"], self.global_name, self)

    @contextlib.contextmanager
    def plugin_setup_reload(self):
        """Hot-reload the plugin core."""
        # Unload existing plugin if loaded
        if self.plugin.is_loaded():
            self.unregister_reload_action()
            self.term()
            self.plugin = self._import_plugin_cls()
            self.plugin.reset()

        yield

        # Re-register action and load plugin
        self.register_reload_action()
        print(f"{self.global_name} reloading...")
        self.add_plugin_to_console()
        self.plugin.load()

    @abc.abstractmethod
    def reload(self): ...


class D810Plugin(ReloadablePlugin):
    #
    # Plugin flags:
    # - PLUGIN_MOD: plugin may modify the database
    # - PLUGIN_PROC: Load/unload plugin when an IDB opens / closes
    # - PLUGIN_HIDE: Hide plugin from the IDA plugin menu  (if this is set, wanted_hotkey is ignored!)
    # - PLUGIN_FIX: Keep plugin alive after IDB is closed
    #
    #

    flags = idaapi.PLUGIN_PROC | idaapi.PLUGIN_MOD
    wanted_name = "D810"
    wanted_hotkey = "Ctrl-Shift-D"
    comment = "Interface to the D810 plugin"
    help = ""

    def __init__(self):
        super().__init__(
            global_name="D810",
            base_package_name="d810",
            plugin_class="d810.manager.D810State",
        )
        self.suppress_reload_errors = False

    @_compat.override
    def init(self):
        if not init_hexrays():
            print(f"{self.wanted_name} need Hex-Rays decompiler. Skipping")
            return idaapi.PLUGIN_SKIP

        kv = ida_kernwin.get_kernel_version().split(".")
        if (int(kv[0]) < 7) or ((int(kv[0]) == 7) and (int(kv[1]) < 5)):
            print(f"{self.wanted_name} need IDA version >= 7.5. Skipping")
            return idaapi.PLUGIN_SKIP
        return super().init()

    @_compat.override
    def late_init(self):
        super().late_init()
        if not ida_hexrays.init_hexrays_plugin():
            print(f"{self.wanted_name} need Hex-Rays decompiler. Unloading...")
            self.term()
        print(f"{self.wanted_name} initialized (version {D810_VERSION})")

    @_compat.override
    def run(self, args):
        self.reload()

    @_compat.override
    def term(self):
        super().term()
        print(f"Terminating {self.wanted_name}...")

    @_compat.override
    def reload(self):
        """Hot-reload the *entire* package.

        The method delegates to a standalone helper, ``_reload_package_with_graph``, that:

        1. Builds a static import graph for every Python source living under
           the plugin directory.
        2. Detects strongly-connected components (true import cycles).
        3. Produces a deterministic topological order of those components.
        4. Reloads modules in that order, guaranteeing that **all in-package
           dependencies are reloaded before the code that relies on them**.

        Modules whose names match prefixes in ``d810.registry`` are skipped.
        The helper prints a concise warning listing only the *core* cycles it
        found; modules merely *blocked* by a cycle are ordered automatically.
        """
        from d810.reloadable import _reload_package_with_graph

        with self.plugin_setup_reload():
            _reload_package_with_graph(
                pkg_path=d810.__path__,
                base_package=self.base_package_name,
                skip_prefixes=(f"{self.base_package_name}.registry",),
                suppress_errors=self.suppress_reload_errors,
            )


def PLUGIN_ENTRY():
    return D810Plugin()
