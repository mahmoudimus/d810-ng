"""Tests for micro-code persistence and heuristics.

These tests exercise the helper functions provided in
``d810.optimizers.microcode.flow.flattening.cache`` as well as a small
dispatcher collector stub that mimics the behaviour of the real
``GenericDispatcherCollector``.  Because the full Hex-Rays environment is
not available during unit testing, we avoid importing the actual
collector and instead implement a simplified version that uses the same
algorithms for computing block hashes, consulting a persistent cache,
applying an entry-opcode heuristic and caching the outcome.

The goal of these tests is twofold:

* Verify that ``compute_block_hash`` produces stable and identical hashes
  for blocks with identical instruction streams, regardless of object
  identity, and falls back to the block serial when no instructions are
  present.
* Ensure that ``PersistentMicrocodeCache`` can store and retrieve JSON
  serializable dictionaries and that it can be used by a collector to
  avoid re-exploring the same block across invocations.  The stub
  collector demonstrates the intended usage pattern of computing a
  block hash, consulting the cache, deciding whether to skip
  exploration and updating the cache with either a skip sentinel or
  dispatcher metadata.

These tests do not depend on IDA Pro or Hex-Rays and therefore can run
in isolation with the standard Python interpreter.
"""

import os
import tempfile
from typing import Any, Dict, List, Optional

from d810.optimizers.microcode.flow.flattening.cache import (
    PersistentMicrocodeCache,
    compute_block_hash,
    dump_dispatcher_info,
)


class DummyInsn:
    """A minimal micro-code instruction for hashing.

    Each instruction exposes an ``opcode`` and a reference to the next
    instruction in the block.  Additional attributes are ignored by
    ``compute_block_hash``.
    """

    def __init__(self, opcode: int, next_insn: Optional["DummyInsn"] = None) -> None:
        self.opcode = opcode
        self.next: Optional["DummyInsn"] = next_insn


class DummyBlock:
    """A minimal micro-code block used for testing.

    A block has a ``serial`` identifier and a linked list of instructions
    via the ``head`` attribute.  No other attributes are needed for
    hashing or for the stub collector below.
    """

    def __init__(self, serial: int, opcodes: Optional[List[int]] = None) -> None:
        self.serial = serial
        # Construct a forward linked list of DummyInsns from the opcode list
        self.head: Optional[DummyInsn]
        if not opcodes:
            self.head = None
        else:
            # Build the list in reverse to simplify linking
            next_insn: Optional[DummyInsn] = None
            for opcode in reversed(opcodes):
                cur = DummyInsn(opcode, next_insn)
                next_insn = cur
            self.head = next_insn
        # Provide a dummy mba attribute to satisfy type hints
        self.mba = None  # type: ignore[assignment]


class StubDispatcherInfo:
    """A trivial dispatcher info used by the stub collector.

    This object holds minimal information required for caching.  The
    ``comparison_values`` field is left as an empty list.  The
    ``dispatcher_internal_blocks`` and ``dispatcher_exit_blocks`` lists
    contain references to DummyBlocks via wrapper objects exposing a
    ``blk`` attribute.  The structure mimics what ``dump_dispatcher_info``
    expects.
    """

    def __init__(self, blk: DummyBlock) -> None:
        self.entry_block = type("_Entry", (), {"blk": blk})
        self.dispatcher_internal_blocks: List[Any] = []
        self.dispatcher_exit_blocks: List[Any] = []
        self.comparison_values: List[int] = []

    def explore(self, blk: DummyBlock) -> bool:
        """Pretend that every block is a dispatcher.

        The real ``GenericDispatcherInfo.explore`` performs complex
        emulation to determine whether a block is a dispatcher.  For
        testing purposes we treat every block as a dispatcher so that the
        collector will attempt to cache positive results.
        """
        # Copy the block reference into the entry_block wrapper
        self.entry_block.blk = blk
        # For demonstration, treat the block serial as a comparison value
        self.comparison_values = [blk.serial]
        return True


class StubDispatcherCollector:
    """A simplified dispatcher collector used for testing.

    This collector demonstrates the intended use of the persistent
    micro-code cache and entry-opcode heuristic without depending on the
    Hex-Rays SDK.  It mimics the logic of
    ``GenericDispatcherCollector.visit_minsn`` from the production code:

    * It maintains a list of discovered dispatchers and a set of visited
      block serials to avoid duplicate processing.
    * It optionally skips blocks that do not contain any opcodes from
      ``candidate_opcodes`` when ``skip_non_entry_blocks`` is true.
    * It computes a stable hash for each block via ``compute_block_hash``
      and consults a ``PersistentMicrocodeCache`` for previously stored
      results.  The cache stores either a ``{"skip": True}`` sentinel or
      a serialized dispatcher dictionary.  Cached dispatchers are
      reconstructed lazily by invoking ``StubDispatcherInfo``.
    * When a block is determined to be a dispatcher, its information is
      serialized with ``dump_dispatcher_info`` and stored back into the
      cache.  Non-dispatcher blocks are cached with ``{"skip": True}``.
    """

    # Define the set of opcodes that qualify a block as a candidate
    # dispatcher entry.  In production this comes from CFF_ENTRY_OPCODES.
    candidate_opcodes: set[int] = {1, 2, 3}

    def __init__(
        self,
        microcode_cache: Optional[PersistentMicrocodeCache] = None,
        *,
        skip_non_entry_blocks: bool = True,
    ) -> None:
        self.microcode_cache = microcode_cache
        self.skip_non_entry_blocks = skip_non_entry_blocks
        self.dispatcher_list: List[StubDispatcherInfo] = []
        self.explored: List[int] = []

    def specific_checks(self, disp_info: StubDispatcherInfo) -> bool:
        """Placeholder for dispatcher validity checks.

        Always return True in the stub collector so that every explored
        block passes the checks and is appended to the dispatcher list.
        """
        return True

    def visit_block(self, blk: DummyBlock) -> None:
        """Process a block, possibly discovering a dispatcher.

        This method mirrors the logic of ``visit_minsn`` in the
        production collector.  It uses block hashes, a persistent cache
        and an entry-opcode heuristic to decide whether to explore the
        block and whether to cache the outcome.
        """
        if blk.serial in self.explored:
            return
        self.explored.append(blk.serial)

        block_hash: Optional[str] = None
        cached_data: Optional[Dict[str, Any]] = None
        if self.microcode_cache is not None:
            # Compute the hash and query the cache
            block_hash = compute_block_hash(blk)
            cached_data = self.microcode_cache.get(block_hash)
            if cached_data is not None:
                if cached_data.get("skip"):
                    return
                # Cached dispatcher: reconstruct a stub dispatcher info
                disp = StubDispatcherInfo(blk)
                self.dispatcher_list.append(disp)
                return

        # Entry-opcode heuristic
        if self.skip_non_entry_blocks:
            cur = blk.head
            has_entry = False
            while cur is not None:
                if cur.opcode in self.candidate_opcodes:
                    has_entry = True
                    break
                cur = cur.next
            if not has_entry:
                # Cache skip sentinel
                if self.microcode_cache is not None and block_hash is not None:
                    self.microcode_cache.set(block_hash, {"skip": True})
                return

        # Explore the block (always returns True in stub)
        disp_info = StubDispatcherInfo(blk)
        is_candidate = disp_info.explore(blk)
        if not is_candidate:
            if self.microcode_cache is not None and block_hash is not None:
                self.microcode_cache.set(block_hash, {"skip": True})
            return
        # Apply specific checks (always True here)
        if not self.specific_checks(disp_info):
            if self.microcode_cache is not None and block_hash is not None:
                self.microcode_cache.set(block_hash, {"skip": True})
            return
        # Record dispatcher
        self.dispatcher_list.append(disp_info)
        # Cache the dispatcher info
        if self.microcode_cache is not None and block_hash is not None:
            data = dump_dispatcher_info(disp_info)
            self.microcode_cache.set(block_hash, data)


def test_compute_block_hash_stable():
    """Hashes should be stable and identical for identical instruction streams."""
    blk1 = DummyBlock(serial=1, opcodes=[1, 2, 3, 4])
    blk2 = DummyBlock(serial=2, opcodes=[1, 2, 3, 4])
    blk3 = DummyBlock(serial=3, opcodes=[4, 3, 2, 1])
    digest1 = compute_block_hash(blk1)
    digest2 = compute_block_hash(blk2)
    digest3 = compute_block_hash(blk3)
    # Blocks with identical opcodes should have identical hashes, regardless of serial
    assert digest1 == digest2
    # Reordering opcodes should result in a different hash
    assert digest1 != digest3
    # Blocks with no instructions fall back to hashing the serial
    empty_blk = DummyBlock(serial=42)
    digest_empty = compute_block_hash(empty_blk)
    digest_empty_again = compute_block_hash(empty_blk)
    assert digest_empty == digest_empty_again
    # Changing the serial produces a different hash when no instructions are present
    empty_blk2 = DummyBlock(serial=99)
    assert digest_empty != compute_block_hash(empty_blk2)


def test_persistent_microcode_cache_set_get():
    """The cache should store and retrieve JSON data correctly."""
    # Use a temporary file so that the database is cleaned up after the test
    with tempfile.NamedTemporaryFile(delete=False) as tmp:
        db_path = tmp.name
    try:
        cache = PersistentMicrocodeCache(db_path)
        payload = {"key": "value", "list": [1, 2, 3]}
        h = "deadbeef"
        assert cache.get(h) is None
        cache.set(h, payload)
        retrieved = cache.get(h)
        assert retrieved == payload
        # Overwrite existing entry
        payload2 = {"k": 1}
        cache.set(h, payload2)
        assert cache.get(h) == payload2
        cache.close()
    finally:
        os.unlink(db_path)


def test_stub_dispatcher_collector_with_cache_and_heuristics():
    """The stub collector should use the cache and heuristic to avoid redundant work."""
    # Use an in-memory cache for convenience
    cache = PersistentMicrocodeCache(":memory:")
    collector = StubDispatcherCollector(
        microcode_cache=cache, skip_non_entry_blocks=True
    )
    # Block without candidate opcodes should be skipped and cached as skip
    blk_skip = DummyBlock(serial=10, opcodes=[100, 200, 300])
    collector.visit_block(blk_skip)
    # The cache should contain a skip entry
    h_skip = compute_block_hash(blk_skip)
    assert cache.get(h_skip) == {"skip": True}
    # Visiting again should immediately return without exploring or modifying dispatcher_list
    before_count = len(collector.dispatcher_list)
    collector.visit_block(blk_skip)
    assert len(collector.dispatcher_list) == before_count
    # Block with a candidate opcode should be treated as a dispatcher and cached accordingly
    blk_disp = DummyBlock(
        serial=20, opcodes=[10, 1, 20]
    )  # opcode 1 is in candidate_opcodes
    collector.visit_block(blk_disp)
    h_disp = compute_block_hash(blk_disp)
    cached_disp = cache.get(h_disp)
    # The cached dispatcher info should be a dictionary with expected keys
    assert isinstance(cached_disp, dict)
    assert "entry_block_serial" in cached_disp
    assert cached_disp["entry_block_serial"] == blk_disp.serial
    # The collector should have recorded one dispatcher
    assert len(collector.dispatcher_list) == 1
    # Visiting the same dispatcher again should reuse the cache and not duplicate
    collector.visit_block(blk_disp)
    # Dispatcher list size should remain the same
    assert len(collector.dispatcher_list) == 1
