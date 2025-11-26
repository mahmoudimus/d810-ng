from __future__ import annotations

import contextlib
import cProfile
import dataclasses
import inspect
import pathlib
import pstats
import time
import typing

# Import IDA module for user directory - only used at initialization
import idaapi

from d810.core import (
    CythonMode,
    D810Configuration,
    EventEmitter,
    OptimizationStatistics,
    ProjectConfiguration,
    ProjectManager,
    SingletonMeta,
    clear_logs,
    configure_loggers,
    getLogger,
)

_IDA_USER_DIR: str | None = idaapi.get_user_idadir()

from d810.hexrays.hexrays_hooks import (
    BlockOptimizerManager,
    DecompilationEvent,
    HexraysDecompilationHook,
    InstructionOptimizerManager,
)
from d810.optimizers.caching import MOP_CONSTANT_CACHE, MOP_TO_AST_CACHE
from d810.optimizers.microcode.flow.handler import FlowOptimizationRule
from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule

# Import GUI only when needed (not in headless/test mode)
if idaapi.is_idaq():
    from d810.ui.ida_ui import D810GUI
else:
    D810GUI = None  # type: ignore

try:
    import pyinstrument  # type: ignore
except ImportError:
    pyinstrument = None

D810_LOG_DIR_NAME = "d810_logs"

logger = getLogger("D810")


class CProfileWrapper:
    """
    A simple wrapper around cProfile.Profile that exposes an `.is_running` property.
    """

    def __init__(self):
        self._profiler = cProfile.Profile()
        self._is_running = False

    @property
    def is_running(self):
        return self._is_running

    def enable(self, *args, **kwargs):
        self._profiler.enable(*args, **kwargs)
        self._is_running = True

    def disable(self):
        self._profiler.disable()
        self._is_running = False

    @property
    def profiler(self):
        return self._profiler


@dataclasses.dataclass
class D810Manager:
    log_dir: pathlib.Path
    instruction_optimizer_rules: list = dataclasses.field(default_factory=list)
    instruction_optimizer_config: dict = dataclasses.field(default_factory=dict)
    block_optimizer_rules: list = dataclasses.field(default_factory=list)
    block_optimizer_config: dict = dataclasses.field(default_factory=dict)
    config: dict = dataclasses.field(default_factory=dict)
    event_emitter: EventEmitter = dataclasses.field(default_factory=EventEmitter)
    profiler: typing.Any = dataclasses.field(
        default_factory=lambda: pyinstrument.Profiler() if pyinstrument else None
    )
    cprofiler: CProfileWrapper | None = dataclasses.field(
        default_factory=lambda: CProfileWrapper() if cProfile else None
    )
    stats: OptimizationStatistics = dataclasses.field(
        default_factory=OptimizationStatistics
    )
    instruction_optimizer: InstructionOptimizerManager = dataclasses.field(init=False)
    block_optimizer: BlockOptimizerManager = dataclasses.field(init=False)
    hx_decompiler_hook: HexraysDecompilationHook = dataclasses.field(init=False)
    _started: bool = dataclasses.field(default=False, init=False)
    _profiling_enabled: bool = dataclasses.field(default=False, init=False)
    _start_ts: float = dataclasses.field(default=0.0, init=False)

    @property
    def started(self):
        return self._started

    def configure(self, **kwargs):
        self.config = kwargs

    def start_profiling(self):
        if not self._profiling_enabled:
            return

        if self.cprofiler and not self.cprofiler.is_running:
            self.cprofiler.enable()
        if self.profiler and not self.profiler.is_running:
            self.profiler.start()

    def stop_profiling(self) -> pathlib.Path | None:
        if self.cprofiler and self.cprofiler.is_running:
            self.cprofiler.disable()
            output_path = self.log_dir / "d810_cprofile.prof"
            self.cprofiler.profiler.dump_stats(str(output_path))
            pstats.Stats(str(output_path)).strip_dirs().sort_stats("time").print_stats()
            return output_path
        if self.profiler and self.profiler.is_running:
            self.profiler.stop()
            self.profiler.print()
            # save the report as an HTML file in the log directory for easy access.
            output_path = self.log_dir / "d810_profile.html"
            with open(output_path, "w", encoding="utf-8") as f:
                f.write(self.profiler.output_html())
            return output_path

    def set_profiling_hooks(self, pre_hook=None, post_hook=None) -> None:
        """Set profiling hooks for tracking optimization passes.

        Args:
            pre_hook: Called before each optimization pass
            post_hook: Called after each optimization pass
        """
        # Store hooks for use during optimization passes
        # These can be used by tests or other monitoring code
        self.pre_pass_hook = pre_hook
        self.post_pass_hook = post_hook

    def disable_profiling(self):
        self._profiling_enabled = False
        self.stop_profiling()

    def enable_profiling(self):
        self._profiling_enabled = True
        self.start_profiling()

    def start(self):
        if self._started:
            self.stop()
        logger.debug("Starting manager...")
        t0 = time.perf_counter()

        # Instantiate core manager classes from registry
        t_inst = time.perf_counter()
        self.instruction_optimizer = InstructionOptimizerManager(
            self.stats,
            log_dir=self.log_dir,
        )
        self.instruction_optimizer.configure(**self.instruction_optimizer_config)
        self.block_optimizer = BlockOptimizerManager(
            self.stats,
            log_dir=self.log_dir,
        )
        self.block_optimizer.configure(**self.block_optimizer_config)
        print(f"    ⏱ Manager instantiation: {time.perf_counter() - t_inst:.2f}s")

        t_rules = time.perf_counter()
        for rule in self.instruction_optimizer_rules:
            rule.log_dir = self.log_dir
            self.instruction_optimizer.add_rule(rule)

        for cfg_rule in self.block_optimizer_rules:
            cfg_rule.log_dir = self.log_dir
            self.block_optimizer.add_rule(cfg_rule)
        print(f"    ⏱ Rule registration: {time.perf_counter() - t_rules:.2f}s")

        t_hooks = time.perf_counter()
        self.hx_decompiler_hook = HexraysDecompilationHook(self.event_emitter.emit)
        self._install_hooks()
        print(f"    ⏱ Hook installation: {time.perf_counter() - t_hooks:.2f}s")
        print(f"    ⏱ D810Manager.start() total: {time.perf_counter() - t0:.2f}s")
        self._started = True

    def stop(self):
        if not self._started:
            return
        self._started = False

        self.instruction_optimizer.remove()
        self.block_optimizer.remove()
        self.hx_decompiler_hook.unhook()
        self.event_emitter.clear()
        if self.profiler or self.cprofiler:
            self.stop_profiling()

    def _start_timer(self):
        self._start_ts = time.perf_counter()

    def _stop_timer(self, report: bool = True):
        if report:
            m, s = divmod(time.perf_counter() - self._start_ts, 60)
            logger.info(
                "Decompilation finished in %dm %ds",
                int(m),
                int(s),
            )
        self._start_ts = 0.0

    def _install_hooks(self):
        # must become before listeners are installed
        for _subscriber in (
            self.start_profiling,
            MOP_CONSTANT_CACHE.clear,
            MOP_TO_AST_CACHE.clear,
            self.stats.reset,
            self._start_timer,
        ):
            self.event_emitter.on(DecompilationEvent.STARTED, _subscriber)

        for _subscriber in (
            self.stop_profiling,
            self._report_caches,
            self.stats.report,
            self._stop_timer,
        ):
            self.event_emitter.on(DecompilationEvent.FINISHED, _subscriber)

        self.instruction_optimizer.install()
        self.block_optimizer.install()
        self.hx_decompiler_hook.hook()

    def _report_caches(self):
        logger.info("MOP_CONSTANT_CACHE stats: %s", MOP_CONSTANT_CACHE.stats())
        logger.info("MOP_TO_AST_CACHE stats: %s", MOP_TO_AST_CACHE.stats())

    def configure_instruction_optimizer(self, rules, **kwargs):
        self.instruction_optimizer_rules = [rule for rule in rules]
        self.instruction_optimizer_config = kwargs

    def configure_block_optimizer(self, rules, **kwargs):
        self.block_optimizer_rules = [rule for rule in rules]
        self.block_optimizer_config = kwargs


class D810State(metaclass=SingletonMeta):
    """
    State class representing the runtime state of the D810 plugin.

    This class is responsible for managing the configuration, the project
    manager, the current project, the current instruction and block rules,
    the known instruction and block rules, and the D810 manager.

    It also provides a GUI for the plugin.
    """

    # placeholders for runtime state
    log_dir: pathlib.Path
    manager: D810Manager
    gui: D810GUI
    current_project: ProjectConfiguration

    def __init__(self):
        self.reset()

    def is_loaded(self):
        return self._is_loaded

    def reset(self) -> None:
        self._initialized: bool = False
        self.d810_config: D810Configuration = D810Configuration(
            ida_user_dir=_IDA_USER_DIR
        )
        # manage projects via ProjectManager
        self.project_manager = ProjectManager(self.d810_config)
        self.current_project_index: int = 0
        self.current_ins_rules: typing.List = []
        self.current_blk_rules: typing.List = []
        self.known_ins_rules: typing.List = []
        self.known_blk_rules: typing.List = []
        self._is_loaded: bool = False
        # Perform logger setup based on current config
        self.log_dir = self.d810_config.log_dir / D810_LOG_DIR_NAME
        if self.d810_config.get("erase_logs_on_reload"):
            clear_logs(self.log_dir)
        configure_loggers(self.log_dir)
        # Always rely on the D810Configuration.log_dir property which falls back
        # to a sensible default when the option is missing, instead of reading
        # the raw option that may be None and break pathlib.Path construction.
        self.manager = D810Manager(self.log_dir)
        self._cython_mode = CythonMode(self.d810_config.get("cython_mode", True))
        self._initialized = True

    def add_project(self, config: ProjectConfiguration):
        self.project_manager.add(config)

    def update_project(
        self, old_config: ProjectConfiguration, new_config: ProjectConfiguration
    ):
        self.project_manager.update(old_config.path.name, new_config)

    def del_project(self, config: ProjectConfiguration):
        self.project_manager.delete(config)

    def load_project(self, project_index: int) -> ProjectConfiguration:
        self.current_project_index = project_index
        self.current_project = self.project_manager.get(project_index)
        self.current_ins_rules = []
        self.current_blk_rules = []

        for rule in self.known_ins_rules:
            for rule_conf in self.current_project.ins_rules:
                if not rule_conf.is_activated:
                    continue
                if rule.name == rule_conf.name:
                    rule_conf.config["dump_intermediate_microcode"] = (
                        self.d810_config.get("dump_intermediate_microcode")
                    )
                    rule.configure(rule_conf.config)
                    rule.set_log_dir(self.log_dir)
                    self.current_ins_rules.append(rule)
        logger.debug("Instruction rules configured")
        for blk_rule in self.known_blk_rules:
            for rule_conf in self.current_project.blk_rules:
                if not rule_conf.is_activated:
                    continue
                if blk_rule.name == rule_conf.name:
                    rule_conf.config["dump_intermediate_microcode"] = (
                        self.d810_config.get("dump_intermediate_microcode")
                    )
                    blk_rule.configure(rule_conf.config)
                    blk_rule.set_log_dir(self.log_dir)
                    self.current_blk_rules.append(blk_rule)
        logger.debug("Block rules configured")
        self.manager.configure(**self.current_project.additional_configuration)
        logger.debug(
            "Loaded project %s (%s) from %s",
            self.current_project.path.name,
            self.current_project.description,
            self.current_project.path,
        )
        return self.current_project

    def start_d810(self):
        print("D-810 ready to deobfuscate...")
        self.manager.configure_instruction_optimizer(
            [rule for rule in self.current_ins_rules],
            generate_z3_code=self.d810_config.get("generate_z3_code"),
            dump_intermediate_microcode=self.d810_config.get(
                "dump_intermediate_microcode"
            ),
            **self.current_project.additional_configuration,
        )
        self.manager.configure_block_optimizer(
            [rule for rule in self.current_blk_rules],
            **self.current_project.additional_configuration,
        )
        self.manager.start()
        self.d810_config.set("last_project_index", self.current_project_index)
        self.d810_config.save()

    def stop_d810(self):
        print("Stopping D-810...")
        self.manager.stop()

    def load(self, gui: bool = True):
        self.reset()
        # Determine which project to auto-load. Fall back to first entry (0)
        # when the configuration value is missing or invalid, and clamp the
        # index to the available range to avoid IndexError when projects were
        # renamed or removed.
        raw_index = self.d810_config.get("last_project_index", 0)
        try:
            self.current_project_index = int(raw_index)
        except (TypeError, ValueError):
            logger.warning(
                "Invalid last_project_index %r in configuration; defaulting to 0",
                raw_index,
            )
            self.current_project_index = 0
        self.current_project = self.project_manager.get(self.current_project_index)

        self.current_ins_rules = []
        self.current_blk_rules = []

        # Build lists of available rules, skipping abstract / hidden ones.
        # Traditional rules come from InstructionOptimizationRule.registry.
        # Verifiable rules (from RULE_REGISTRY) are injected directly into
        # PatternOptimizer at construction time in InstructionOptimizerManager,
        # so they don't need to be merged here.
        t_rules = time.perf_counter()

        self.known_ins_rules = [
            rule_cls()
            for rule_cls in InstructionOptimizationRule.registry.values()
            if not inspect.isabstract(rule_cls)
        ]

        print(
            f"  ⏱ Instantiate {len(self.known_ins_rules)} instruction rules: "
            f"{time.perf_counter() - t_rules:.2f}s"
        )

        t_blk = time.perf_counter()
        self.known_blk_rules = [
            rule_cls()
            for rule_cls in FlowOptimizationRule.registry.values()
            if not inspect.isabstract(rule_cls)
        ]
        print(
            f"  ⏱ Instantiate {len(self.known_blk_rules)} block rules: {time.perf_counter() - t_blk:.2f}s"
        )

        # Clamp to available projects, if any
        if projects := len(self.project_manager):
            self.current_project_index = max(
                0, min(self.current_project_index, projects - 1)
            )
            self._is_loaded = self.load_project(self.current_project_index) is not None
        else:
            logger.warning("No project configurations available; plugin is idle.")
            self._is_loaded = False

        if gui and self._is_loaded and D810GUI is not None:
            self.gui = D810GUI(self)
            self.gui.show_windows()

    def unload(self, gui: bool = True):
        self.manager.stop()
        if gui and self._is_loaded:
            self.gui.term()
            del self.gui
        self._is_loaded = False

    @contextlib.contextmanager
    def for_project(self, name: str) -> typing.Generator[int, None, None]:
        _old_project_index = self.current_project_index
        project_index = self.project_manager.index(name)
        if project_index != _old_project_index:
            logger.info("switching to project %s", name)
        self.load_project(project_index)
        yield project_index
        if project_index != _old_project_index:
            logger.info("switching back to project %s", _old_project_index)
            self.load_project(_old_project_index)

    def enable_cython_speedups(self):
        self._cython_mode.enable()

    def disable_cython_speedups(self):
        self._cython_mode.disable()

    def are_cython_speedups_enabled(self):
        return self._cython_mode.is_enabled()

    # Expose statistics to callers (e.g., tests)
    @property
    def stats(self) -> OptimizationStatistics:
        return self.manager.stats
