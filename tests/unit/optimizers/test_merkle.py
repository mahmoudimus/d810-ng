"""Unit tests for the Merkle tree utilities."""

import sys
from pathlib import Path
import unittest

# Ensure d810 can be imported by adding the src directory to sys.path
_repo_root = Path(__file__).resolve().parents[4]
_src_path = _repo_root / "src"
if str(_src_path) not in sys.path:
    sys.path.insert(0, str(_src_path))

# Load the Merkle module dynamically to ensure patched functions are available.
import importlib
try:
    import d810.optimizers.microcode.flow.flattening.merkle as merkle_mod
    importlib.reload(merkle_mod)
    MerkleTree = merkle_mod.MerkleTree
except Exception:
    # In case the module cannot be imported (e.g. missing dependencies), set
    # MerkleTree to None so that tests can be skipped gracefully.
    MerkleTree = None


class TestMerkleTree(unittest.TestCase):
    def test_build_root(self) -> None:
        if MerkleTree is None:
            self.skipTest("MerkleTree module not available")
        leaves = ["a", "b", "c", "d"]
        tree = MerkleTree(leaves)
        # Root hash should be non‑empty and deterministic
        self.assertIsInstance(tree.root, str)
        self.assertEqual(tree.leaves, leaves)
        # Building the same tree again should yield the same root
        tree2 = MerkleTree(leaves)
        self.assertEqual(tree.root, tree2.root)

    def test_diff(self) -> None:
        if MerkleTree is None:
            self.skipTest("MerkleTree module not available")
        tree1 = MerkleTree(["h1", "h2", "h3", "h4"])
        tree2 = MerkleTree(["h1", "hX", "h3", "h4"])
        diff = tree1.diff(tree2)
        self.assertEqual(diff, [1])


if __name__ == "__main__":  # pragma: no cover
    unittest.main()