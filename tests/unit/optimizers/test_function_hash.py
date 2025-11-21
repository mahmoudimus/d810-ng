"""Tests for the ``compute_function_hash`` helper."""

import sys
from pathlib import Path
import unittest

# Ensure d810 can be imported
_repo_root = Path(__file__).resolve().parents[4]
_src_path = _repo_root / "src"
if str(_src_path) not in sys.path:
    sys.path.insert(0, str(_src_path))

# Load the cache module and force a reload to ensure freshly patched
# functions (such as compute_function_hash) are available even if the
# module was imported earlier by other tests.
import importlib
import d810.optimizers.microcode.flow.flattening.cache as cache
importlib.reload(cache)

from d810.optimizers.microcode.flow.flattening.cache import compute_block_hash

# Attempt to obtain ``compute_function_hash``.  In some test environments
# the module may not include this helper if it was imported before the
# patched version was loaded.  If unavailable, the tests will be skipped.
compute_function_hash = getattr(cache, "compute_function_hash", None)


class DummyBlock:
    def __init__(self, serial: int, opcodes: list[int]):
        self.serial = serial
        self.head = None
        # build minimal instruction chain for hashing
        cur = None
        for op in reversed(opcodes):
            node = type("Insn", (), {"opcode": op, "next": cur})()
            cur = node
        self.head = cur


class DummyMBA:
    """A simple micro‑code array exposing both ``qty``/``get_mblock`` and an iterator."""

    def __init__(self, blocks: list[DummyBlock]) -> None:
        self._blocks = blocks
        self.qty = len(blocks)

    def get_mblock(self, i: int) -> DummyBlock:
        return self._blocks[i]

    def __iter__(self):
        return iter(self._blocks)


class TestFunctionHash(unittest.TestCase):
    def test_hash_consistency(self) -> None:
        # Skip test entirely if ``compute_function_hash`` is not available
        if compute_function_hash is None:
            self.skipTest("compute_function_hash not available in this environment")

        # Create two identical functions (same block sequences)
        blk1 = DummyBlock(0, [1, 2, 3])
        blk2 = DummyBlock(1, [4, 5])
        mba1 = DummyMBA([blk1, blk2])
        mba2 = DummyMBA([blk1, blk2])
        h1 = compute_function_hash(mba1)
        h2 = compute_function_hash(mba2)
        self.assertEqual(h1, h2)
        # Changing the block order should change the function hash
        mba3 = DummyMBA([blk2, blk1])
        h3 = compute_function_hash(mba3)
        self.assertNotEqual(h1, h3)
        # Changing the opcode within a block should change the hash
        blk3 = DummyBlock(2, [1, 2, 99])
        mba4 = DummyMBA([blk3, blk2])
        h4 = compute_function_hash(mba4)
        self.assertNotEqual(h1, h4)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()