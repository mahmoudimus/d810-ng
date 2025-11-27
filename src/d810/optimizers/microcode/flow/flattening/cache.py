"""Persistent micro‑code cache utilities.

This module provides simple helpers to compute a stable hash for a micro‑code
basic block and to persist derived data in a SQLite database.  Because the
Hex‑Rays micro‑code is rebuilt every time the decompiler runs, any expensive
analysis must be cached externally if you want to avoid recomputing it on
subsequent runs.  The cache stores data keyed by a block hash; callers are
responsible for deciding what to store (for example dispatcher metadata).

Functions are deliberately generic: they accept any object with ``head``,
``next`` and ``opcode`` attributes for hashing and return a hexadecimal
digest.  If no instructions are present, the block serial number is used
instead.  Persisted rows are JSON serialised.
"""

from __future__ import annotations

import hashlib
import json
import sqlite3
from typing import Any, Dict, List, Optional


class PersistentMicrocodeCache:
    """Simple SQLite‑backed cache keyed by a block hash.

    Each entry is stored under a unique ``block_hash``.  The associated
    ``data`` value can be any JSON‑serialisable dictionary.  Callers must
    ensure that the data they store can be reconstructed later; this module
    does not attempt to serialise complex Python objects automatically.
    """

    def __init__(self, db_path: str) -> None:
        # Connect to the SQLite database.  Use check_same_thread=False to
        # allow usage from multiple threads if concurrency is employed in
        # the future.
        self.conn = sqlite3.connect(db_path, check_same_thread=False)
        # Create the table if it does not already exist.
        self.conn.execute(
            """
            CREATE TABLE IF NOT EXISTS microcode_cache (
                block_hash TEXT PRIMARY KEY,
                data       TEXT
            )
            """
        )
        self.conn.commit()

    def get(self, block_hash: str) -> Optional[Dict[str, Any]]:
        """Retrieve a cached entry by its hash.

        Returns a dictionary if present or ``None`` if the key is not found.
        """
        cur = self.conn.execute(
            "SELECT data FROM microcode_cache WHERE block_hash=?", (block_hash,)
        )
        row = cur.fetchone()
        if not row:
            return None
        # parse JSON back into a Python dict
        return json.loads(row[0])

    def set(self, block_hash: str, data: Dict[str, Any]) -> None:
        """Insert or replace a cached entry.

        The data must be JSON serialisable.  This method commits the
        transaction immediately.
        """
        self.conn.execute(
            "REPLACE INTO microcode_cache (block_hash, data) VALUES (?, ?)",
            (block_hash, json.dumps(data)),
        )
        self.conn.commit()

    def close(self) -> None:
        """Close the underlying SQLite connection."""
        self.conn.close()

    # Support context manager usage
    def __enter__(self) -> "PersistentMicrocodeCache":  # pragma: no cover
        return self

    def __exit__(self, exc_type, exc, tb) -> None:  # pragma: no cover
        self.close()


def compute_block_hash(blk: Any) -> str:
    """Compute a stable hash of a micro‑code basic block.

    The algorithm walks the instruction list starting at ``blk.head`` and
    collects the opcode of each instruction via the ``opcode`` attribute.  A
    SHA‑256 hash of the comma‑separated opcode list is returned.  If no
    instructions are present or ``blk.head`` is missing, the hash falls back
    to the string representation of the block's serial number (if available).

    Parameters
    ----------
    blk: Any
        An object that exposes ``head`` and ``serial`` attributes as well as a
        linked list of instructions where each instruction exposes
        ``opcode`` and ``next`` attributes.

    Returns
    -------
    str
        A 64‑character hexadecimal digest representing the block contents.
    """
    opcodes: List[str] = []
    cur = getattr(blk, "head", None)
    # Walk the instruction linked list and collect opcodes
    while cur is not None:
        try:
            opcodes.append(str(cur.opcode))
        except Exception:
            opcodes.append("None")
        cur = getattr(cur, "next", None)
    # If no instructions were collected, fall back to the block serial.
    if not opcodes and hasattr(blk, "serial"):
        opcodes.append(str(getattr(blk, "serial")))
    # Compute the SHA‑256 digest
    digest = hashlib.sha256(",".join(opcodes).encode("utf-8")).hexdigest()
    return digest


def compute_function_hash(mba: Any) -> str:
    """Compute a stable hash of an entire micro‑code array (function).

    The default implementation walks all basic blocks in the ``mba`` and
    concatenates their individual hashes computed via
    :func:`compute_block_hash`.  The combined string is then hashed
    using SHA‑256.  Callers must provide an ``mba`` object with a ``get_mblock``
    method and a ``qty`` attribute indicating the number of blocks.  If
    the ``mba`` exposes an iterable interface over its blocks, that will
    be used instead.

    Parameters
    ----------
    mba : Any
        A micro‑code array (``mba_t``) or any iterable of blocks.  Each
        block must expose the attributes required by
        :func:`compute_block_hash`.

    Returns
    -------
    str
        A 64‑character hexadecimal digest representing the function.
    """
    block_digests: List[str] = []
    try:
        # If the mba is iterable, iterate directly
        for blk in mba:
            try:
                block_digests.append(compute_block_hash(blk))
            except Exception:
                continue
    except TypeError:
        # Fallback to indexing via get_mblock and qty
        qty = getattr(mba, "qty", None)
        if qty is None:
            return hashlib.sha256("".encode("utf-8")).hexdigest()
        for i in range(int(qty)):
            try:
                blk = mba.get_mblock(i)
                block_digests.append(compute_block_hash(blk))
            except Exception:
                continue
    # Compute the global digest
    digest = hashlib.sha256(",".join(block_digests).encode("utf-8")).hexdigest()
    return digest


def dump_dispatcher_info(disp_info: Any) -> Dict[str, Any]:
    """Serialise a :class:`GenericDispatcherInfo` into a plain dictionary.

    Only basic fields are recorded: the entry block serial, the serial
    identifiers of the internal and exit blocks, and the list of comparison
    values.  More complex fields such as the compared mop or the history are
    deliberately omitted because they cannot be easily reconstructed without
    access to the live micro‑code environment.

    Parameters
    ----------
    disp_info: Any
        An instance of ``GenericDispatcherInfo`` or a compatible object.

    Returns
    -------
    dict
        A serialisable dictionary that can later be consumed by
        :func:`load_dispatcher_info`.
    """
    entry_serial = None
    if getattr(disp_info, "entry_block", None) is not None:
        entry_serial = getattr(disp_info.entry_block, "serial", None)
    internal_serials = [b.serial for b in getattr(disp_info, "dispatcher_internal_blocks", [])]
    exit_serials = [b.serial for b in getattr(disp_info, "dispatcher_exit_blocks", [])]
    comparison_values = list(getattr(disp_info, "comparison_values", []))
    return {
        "entry_block_serial": entry_serial,
        "internal_blocks": internal_serials,
        "exit_blocks": exit_serials,
        "comparison_values": comparison_values,
    }


def load_dispatcher_info(data: Dict[str, Any], mba: Any) -> Any:
    """Reconstruct a :class:`GenericDispatcherInfo` from a cached dictionary.

    This helper can be used to recreate a ``GenericDispatcherInfo`` object
    from cached data.  Because some attributes (such as mop comparisons and
    history) are lost during serialisation, the reconstructed object may not
    be identical to the original but will contain enough information to skip
    re‑emulation of a dispatcher on future runs.

    Parameters
    ----------
    data: dict
        The dictionary previously returned by :func:`dump_dispatcher_info`.
    mba: Any
        The micro‑code array (``mba_t``) from which blocks can be obtained via
        ``get_mblock(serial)``.

    Returns
    -------
    GenericDispatcherInfo
        A new dispatcher info instance populated with the cached values.
    """
    from .generic import GenericDispatcherInfo, GenericDispatcherBlockInfo  # type: ignore

    disp_info = GenericDispatcherInfo(mba)
    entry_serial = data.get("entry_block_serial")
    if entry_serial is not None:
        disp_info.entry_block = GenericDispatcherBlockInfo(mba.get_mblock(entry_serial))
    # Populate internal and exit blocks
    disp_info.dispatcher_internal_blocks = [
        GenericDispatcherBlockInfo(mba.get_mblock(s)) for s in data.get("internal_blocks", [])
    ]
    disp_info.dispatcher_exit_blocks = [
        GenericDispatcherBlockInfo(mba.get_mblock(s), disp_info.entry_block) for s in data.get("exit_blocks", [])
    ]
    disp_info.comparison_values = list(data.get("comparison_values", []))
    return disp_info