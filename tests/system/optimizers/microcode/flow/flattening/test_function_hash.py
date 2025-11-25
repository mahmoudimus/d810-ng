"""Tests for the ``compute_function_hash`` helper."""

import pytest

from d810.optimizers.microcode.flow.flattening.cache import compute_function_hash


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
    """A simple micro-code array exposing both ``qty``/``get_mblock`` and an iterator."""

    def __init__(self, blocks: list):
        self._blocks = blocks
        self.qty = len(blocks)

    def get_mblock(self, i: int):
        return self._blocks[i]

    def __iter__(self):
        return iter(self._blocks)


def test_hash_consistency():
    # Create two identical functions (same block sequences)
    blk1 = DummyBlock(0, [1, 2, 3])
    blk2 = DummyBlock(1, [4, 5])
    mba1 = DummyMBA([blk1, blk2])
    mba2 = DummyMBA([blk1, blk2])
    h1 = compute_function_hash(mba1)
    h2 = compute_function_hash(mba2)
    assert h1 == h2
    # Changing the block order should change the function hash
    mba3 = DummyMBA([blk2, blk1])
    h3 = compute_function_hash(mba3)
    assert h1 != h3
    # Changing the opcode within a block should change the hash
    blk3 = DummyBlock(2, [1, 2, 99])
    mba4 = DummyMBA([blk3, blk2])
    h4 = compute_function_hash(mba4)
    assert h1 != h4
