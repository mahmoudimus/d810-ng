from __future__ import annotations

import dataclasses
from collections import defaultdict
from typing import Dict, List

from d810.conf.loggers import getLogger

logger = getLogger("D810")


@dataclasses.dataclass
class OptimizationStatistics:
    """Centralized statistics for optimizers & rules.

    Tracks usage across instruction optimizers, individual instruction rules,
    and block (CFG) rules. Provides reset/report and query helpers.
    """

    # instruction optimizer usage (e.g., PatternOptimizer, ChainOptimizer...)
    instruction_optimizer_usage: Dict[str, int] = dataclasses.field(
        default_factory=lambda: defaultdict(int)
    )

    # instruction rule usage by name
    instruction_rule_usage: Dict[str, int] = dataclasses.field(
        default_factory=lambda: defaultdict(int)
    )

    # block/CFG rule usage; we store list of patch counts per use
    cfg_rule_usages: Dict[str, List[int]] = dataclasses.field(
        default_factory=lambda: defaultdict(list)
    )

    def reset(self) -> None:
        self.instruction_optimizer_usage.clear()
        self.instruction_rule_usage.clear()
        self.cfg_rule_usages.clear()

    # Recording APIs
    def record_optimizer_match(self, optimizer_name: str) -> None:
        self.instruction_optimizer_usage[optimizer_name] += 1

    def record_instruction_rule_match(self, rule_name: str) -> None:
        self.instruction_rule_usage[rule_name] += 1

    def record_cfg_rule_patches(self, rule_name: str, nb_patches: int) -> None:
        self.cfg_rule_usages[rule_name].append(nb_patches)

    # Query APIs
    def get_optimizer_match_count(self, optimizer_name: str) -> int:
        return int(self.instruction_optimizer_usage.get(optimizer_name, 0))

    def get_instruction_rule_match_count(self, rule_name: str) -> int:
        return int(self.instruction_rule_usage.get(rule_name, 0))

    def get_cfg_rule_patch_counts(self, rule_name: str) -> List[int]:
        return list(self.cfg_rule_usages.get(rule_name, []))

    # Reporting APIs
    def report(self) -> None:
        # Optimizers
        for optimizer_name, nb_match in self.instruction_optimizer_usage.items():
            if nb_match > 0:
                logger.info(
                    "Instruction optimizer '%s' has been used %d times",
                    optimizer_name,
                    nb_match,
                )

        # Instruction rules
        for rule_name, nb_match in self.instruction_rule_usage.items():
            if nb_match > 0:
                logger.info(
                    "Instruction Rule '%s' has been used %d times",
                    rule_name,
                    nb_match,
                )

        # CFG rules
        for rule_name, patch_list in self.cfg_rule_usages.items():
            nb_use = len(patch_list)
            if nb_use > 0:
                logger.info(
                    "BlkRule '%s' has been used %d times for a total of %d patches",
                    rule_name,
                    nb_use,
                    sum(patch_list),
                )
