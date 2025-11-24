"""Test to debug VerifiableRule registration from refactored files."""
import logging
import sys
import unittest
from pathlib import Path

# Set up logging to see what's happening
logging.basicConfig(
    level=logging.DEBUG,
    format='%(levelname)s - %(name)s - %(message)s'
)
logger = logging.getLogger(__name__)


class TestRuleRegistration(unittest.TestCase):
    """Debug why refactored VerifiableRule classes aren't registering."""

    def test_check_refactored_files_exist(self):
        """Verify refactored files exist on disk."""
        pattern_dir = Path("/home/user/d810-ng/src/d810/optimizers/microcode/instructions/pattern_matching")
        refactored_files = list(pattern_dir.glob("*_refactored.py"))

        logger.info(f"Pattern directory: {pattern_dir}")
        logger.info(f"Found {len(refactored_files)} refactored files:")
        for f in sorted(refactored_files):
            logger.info(f"  - {f.name} ({f.stat().st_size} bytes)")

        self.assertGreater(len(refactored_files), 0, "Should find refactored files")
        self.assertEqual(len(refactored_files), 11, "Should have 11 refactored files")

    def test_import_refactored_xor_module(self):
        """Test importing a refactored module directly."""
        logger.info("Attempting to import rewrite_xor_refactored...")

        sys.path.insert(0, "/home/user/d810-ng/src")
        try:
            from d810.optimizers.microcode.instructions.pattern_matching import rewrite_xor_refactored
            logger.info("✓ Successfully imported rewrite_xor_refactored")

            # Check what classes are in the module
            import inspect
            classes = []
            for name, obj in inspect.getmembers(rewrite_xor_refactored, inspect.isclass):
                if obj.__module__ == rewrite_xor_refactored.__name__:
                    classes.append(name)

            logger.info(f"Found {len(classes)} classes defined in module:")
            for cls_name in sorted(classes):
                logger.info(f"  - {cls_name}")

            self.assertGreater(len(classes), 0, "Should have classes in module")

            # Check for specific HackersDelight rules
            hd_rules = [c for c in classes if 'HackersDelightRule' in c]
            logger.info(f"HackersDelight rules: {hd_rules}")
            self.assertGreater(len(hd_rules), 0, "Should have HackersDelight rules")

        except Exception as e:
            logger.error(f"✗ Failed to import: {e}", exc_info=True)
            raise

    def test_verifiable_rule_registration(self):
        """Check if VerifiableRule classes register themselves."""
        logger.info("Testing VerifiableRule registration...")

        sys.path.insert(0, "/home/user/d810-ng/src")

        # First check the base VerifiableRule
        from d810.optimizers.rules import VerifiableRule
        from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule

        logger.info(f"VerifiableRule class: {VerifiableRule}")
        logger.info(f"VerifiableRule bases: {VerifiableRule.__bases__}")
        logger.info(f"VerifiableRule mro: {[c.__name__ for c in VerifiableRule.__mro__]}")

        # Check registry BEFORE importing refactored files
        all_rules_before = InstructionOptimizationRule.all()
        verifiable_before = [
            r for r in all_rules_before
            if isinstance(r, type) and issubclass(r, VerifiableRule)
        ]
        logger.info(f"VerifiableRule subclasses BEFORE import: {len(verifiable_before)}")

        # Now import a refactored file
        from d810.optimizers.microcode.instructions.pattern_matching import rewrite_xor_refactored

        # Check registry AFTER importing
        all_rules_after = InstructionOptimizationRule.all()
        verifiable_after = [
            r for r in all_rules_after
            if isinstance(r, type) and issubclass(r, VerifiableRule)
        ]
        logger.info(f"VerifiableRule subclasses AFTER import: {len(verifiable_after)}")

        # List the newly registered rules
        new_rules = set(verifiable_after) - set(verifiable_before)
        logger.info(f"Newly registered rules ({len(new_rules)}):")
        for rule_cls in sorted(new_rules, key=lambda r: r.__name__):
            logger.info(f"  - {rule_cls.__name__}")

        self.assertGreater(len(new_rules), 0, "Should register rules after import")

    def test_check_reloadable_scanner(self):
        """Test if reloadable scanner discovers refactored files."""
        logger.info("Testing reloadable scanner...")

        sys.path.insert(0, "/home/user/d810-ng/src")

        from d810._vendor.ida_reloader import Reloader
        import d810.optimizers.microcode.instructions.pattern_matching as pattern_pkg

        # Get package path
        pkg_path = Path(pattern_pkg.__file__).parent
        logger.info(f"Pattern matching package path: {pkg_path}")

        # List all .py files
        all_py_files = list(pkg_path.glob("*.py"))
        logger.info(f"All .py files in pattern_matching ({len(all_py_files)}):")
        for f in sorted(all_py_files):
            logger.info(f"  - {f.name}")

        # Filter refactored files
        refactored_files = [f for f in all_py_files if "_refactored" in f.name]
        logger.info(f"Refactored files: {len(refactored_files)}")
        for f in refactored_files:
            logger.info(f"  - {f.name}")

        # Check if scanner would discover them
        import pkgutil
        discovered = []
        for mod_info in pkgutil.iter_modules([str(pkg_path)]):
            discovered.append(mod_info.name)
            if "refactored" in mod_info.name:
                logger.info(f"Scanner discovered: {mod_info.name}")

        logger.info(f"Total modules discovered by pkgutil: {len(discovered)}")
        refactored_discovered = [m for m in discovered if "refactored" in m]
        logger.info(f"Refactored modules discovered: {refactored_discovered}")

        self.assertGreater(len(refactored_discovered), 0, "Scanner should discover refactored modules")

    def test_pattern_optimizer_rule_discovery(self):
        """Check if PatternOptimizer discovers VerifiableRule classes."""
        logger.info("Testing PatternOptimizer rule discovery...")

        sys.path.insert(0, "/home/user/d810-ng/src")

        from d810.optimizers.microcode.instructions.pattern_matching.handler import PatternOptimizer
        from d810.optimizers.microcode.instructions.handler import InstructionOptimizationRule
        from d810.optimizers.rules import VerifiableRule

        # Import refactored file
        from d810.optimizers.microcode.instructions.pattern_matching import rewrite_xor_refactored

        # Check what PatternOptimizer.RULE_CLASSES looks like
        logger.info(f"PatternOptimizer.RULE_CLASSES: {PatternOptimizer.RULE_CLASSES}")

        # Check InstructionOptimizationRule registry
        all_rules = InstructionOptimizationRule.all()
        logger.info(f"Total rules in InstructionOptimizationRule.all(): {len(all_rules)}")

        # Filter by type
        verifiable = [r for r in all_rules if isinstance(r, type) and issubclass(r, VerifiableRule)]
        logger.info(f"VerifiableRule subclasses: {len(verifiable)}")

        xor_verifiable = [r for r in verifiable if 'Xor' in r.__name__]
        logger.info(f"XOR VerifiableRule subclasses ({len(xor_verifiable)}):")
        for rule_cls in sorted(xor_verifiable, key=lambda r: r.__name__):
            logger.info(f"  - {rule_cls.__name__} from {rule_cls.__module__}")

        self.assertGreater(len(xor_verifiable), 0, "Should have XOR VerifiableRule subclasses")


if __name__ == "__main__":
    unittest.main(verbosity=2)
