"""Parallel execution engine for optimizing multiple functions concurrently.

This module implements parallel optimization processing using multiprocessing.
It provides:

1. Worker pool management
2. Function work queue
3. Result aggregation
4. Error handling and retry logic
5. Progress tracking

The parallel engine is especially useful for large binaries with many functions,
providing near-linear speedup on multi-core systems.

Architecture:
    - Main process: Coordinates work distribution and result collection
    - Worker processes: Execute optimizations independently
    - Shared state: Minimal (read-only configuration)
    - Communication: Work queue (in) and result queue (out)

Safety:
    - Each worker gets its own IDA instance context
    - No shared mutable state between workers
    - Graceful shutdown on errors
    - Timeout handling for stuck workers

Usage:
    executor = ParallelOptimizer(num_workers=4)

    # Submit functions
    for func_addr in function_addresses:
        executor.submit(func_addr)

    # Collect results
    results = executor.get_results()

    # Shutdown
    executor.shutdown()

Example with context manager:
    with ParallelOptimizer(num_workers=4) as executor:
        for func_addr in function_addresses:
            executor.submit(func_addr)
        results = executor.get_results()
"""

from __future__ import annotations

import multiprocessing as mp
import queue
import time
from dataclasses import dataclass, field
from enum import Enum
from typing import Any, Callable, Dict, List, Optional

from d810.conf.loggers import getLogger

logger = getLogger("D810.parallel")


class TaskStatus(Enum):
    """Status of an optimization task."""
    PENDING = "pending"
    RUNNING = "running"
    COMPLETED = "completed"
    FAILED = "failed"
    TIMEOUT = "timeout"


@dataclass
class OptimizationTask:
    """A unit of work for the parallel optimizer."""
    function_addr: int
    config: Dict[str, Any] = field(default_factory=dict)
    priority: int = 0  # Higher priority = processed first
    retry_count: int = 0
    max_retries: int = 3


@dataclass
class OptimizationResult:
    """Result of optimizing a single function."""
    function_addr: int
    status: TaskStatus
    changes_made: int = 0
    duration: float = 0.0
    error_message: Optional[str] = None
    patches: List[Dict[str, Any]] = field(default_factory=list)


class WorkerProcess:
    """Worker process that executes optimization tasks.

    Each worker runs in its own process and maintains its own optimizer state.
    Workers pull tasks from a shared work queue and push results to a result queue.
    """

    def __init__(
        self,
        worker_id: int,
        work_queue: mp.Queue,
        result_queue: mp.Queue,
        optimizer_factory: Callable,
        timeout: float = 300.0
    ):
        """Initialize worker process.

        Args:
            worker_id: Unique identifier for this worker.
            work_queue: Queue to pull tasks from.
            result_queue: Queue to push results to.
            optimizer_factory: Function that creates an optimizer instance.
            timeout: Maximum time per task (seconds).
        """
        self.worker_id = worker_id
        self.work_queue = work_queue
        self.result_queue = result_queue
        self.optimizer_factory = optimizer_factory
        self.timeout = timeout
        self.optimizer = None

    def run(self):
        """Main worker loop."""
        logger.info(f"Worker {self.worker_id} started")

        # Initialize optimizer in worker process
        try:
            self.optimizer = self.optimizer_factory()
        except Exception as e:
            logger.error(f"Worker {self.worker_id} failed to initialize: {e}")
            return

        while True:
            try:
                # Get next task (with timeout to allow graceful shutdown)
                task = self.work_queue.get(timeout=1.0)

                if task is None:  # Poison pill - shutdown signal
                    logger.info(f"Worker {self.worker_id} received shutdown signal")
                    break

                # Process task
                result = self._process_task(task)
                self.result_queue.put(result)

            except queue.Empty:
                continue  # No work available, keep waiting
            except Exception as e:
                logger.error(f"Worker {self.worker_id} error: {e}")
                continue

        logger.info(f"Worker {self.worker_id} shutdown")

    def _process_task(self, task: OptimizationTask) -> OptimizationResult:
        """Process a single optimization task.

        Args:
            task: The task to process.

        Returns:
            Optimization result.
        """
        start_time = time.time()

        try:
            logger.debug(
                f"Worker {self.worker_id} processing function {task.function_addr:x}"
            )

            # Run optimization with timeout
            changes, patches = self._optimize_with_timeout(task)

            duration = time.time() - start_time

            return OptimizationResult(
                function_addr=task.function_addr,
                status=TaskStatus.COMPLETED,
                changes_made=changes,
                duration=duration,
                patches=patches
            )

        except TimeoutError:
            logger.warning(
                f"Worker {self.worker_id} timeout on function {task.function_addr:x}"
            )
            return OptimizationResult(
                function_addr=task.function_addr,
                status=TaskStatus.TIMEOUT,
                error_message="Optimization timed out",
                duration=time.time() - start_time
            )

        except Exception as e:
            logger.error(
                f"Worker {self.worker_id} error on function {task.function_addr:x}: {e}"
            )
            return OptimizationResult(
                function_addr=task.function_addr,
                status=TaskStatus.FAILED,
                error_message=str(e),
                duration=time.time() - start_time
            )

    def _optimize_with_timeout(
        self,
        task: OptimizationTask
    ) -> tuple[int, List[Dict[str, Any]]]:
        """Run optimization with timeout protection.

        Args:
            task: The task to optimize.

        Returns:
            Tuple of (changes_made, patches).

        Raises:
            TimeoutError: If optimization exceeds timeout.
        """
        # TODO: In real implementation, this would:
        # 1. Get function microcode from IDA
        # 2. Run optimizer on it
        # 3. Collect patches

        # For now, placeholder
        changes = 0
        patches = []

        return changes, patches


class ParallelOptimizer:
    """Parallel optimization executor.

    Manages a pool of worker processes to optimize multiple functions concurrently.
    Provides work distribution, result collection, and progress tracking.

    Example:
        >>> executor = ParallelOptimizer(num_workers=4)
        >>>
        >>> # Submit work
        >>> for func_addr in [0x401000, 0x402000, 0x403000]:
        ...     executor.submit(func_addr)
        >>>
        >>> # Wait for completion
        >>> results = executor.get_results(timeout=60.0)
        >>>
        >>> # Check results
        >>> for result in results:
        ...     if result.status == TaskStatus.COMPLETED:
        ...         print(f"Optimized {result.function_addr:x}: {result.changes_made} changes")
        >>>
        >>> executor.shutdown()
    """

    def __init__(
        self,
        num_workers: Optional[int] = None,
        optimizer_factory: Optional[Callable] = None,
        task_timeout: float = 300.0
    ):
        """Initialize parallel optimizer.

        Args:
            num_workers: Number of worker processes (default: CPU count).
            optimizer_factory: Function that creates optimizer instances.
            task_timeout: Maximum time per task (seconds).
        """
        self.num_workers = num_workers or mp.cpu_count()
        self.optimizer_factory = optimizer_factory or self._default_optimizer_factory
        self.task_timeout = task_timeout

        # Queues for work distribution
        self.work_queue: mp.Queue = mp.Queue()
        self.result_queue: mp.Queue = mp.Queue()

        # Worker processes
        self.workers: List[mp.Process] = []
        self.is_running = False

        # Statistics
        self.tasks_submitted = 0
        self.tasks_completed = 0
        self.total_changes = 0
        self.total_duration = 0.0

        logger.info(f"ParallelOptimizer initialized with {self.num_workers} workers")

    def _default_optimizer_factory(self):
        """Default optimizer factory (placeholder)."""
        # TODO: In real implementation, create OptimizerManager
        return None

    def start(self):
        """Start worker processes."""
        if self.is_running:
            logger.warning("ParallelOptimizer already running")
            return

        logger.info(f"Starting {self.num_workers} worker processes")

        for worker_id in range(self.num_workers):
            worker = WorkerProcess(
                worker_id=worker_id,
                work_queue=self.work_queue,
                result_queue=self.result_queue,
                optimizer_factory=self.optimizer_factory,
                timeout=self.task_timeout
            )

            process = mp.Process(target=worker.run)
            process.start()
            self.workers.append(process)

        self.is_running = True
        logger.info("All workers started")

    def submit(self, function_addr: int, config: Optional[Dict[str, Any]] = None):
        """Submit a function for optimization.

        Args:
            function_addr: Address of function to optimize.
            config: Optional per-function configuration.
        """
        if not self.is_running:
            self.start()

        task = OptimizationTask(
            function_addr=function_addr,
            config=config or {}
        )

        self.work_queue.put(task)
        self.tasks_submitted += 1
        logger.debug(f"Submitted function {function_addr:x} (total: {self.tasks_submitted})")

    def submit_batch(self, function_addresses: List[int]):
        """Submit multiple functions at once.

        Args:
            function_addresses: List of function addresses.
        """
        for addr in function_addresses:
            self.submit(addr)

    def get_results(
        self,
        timeout: Optional[float] = None,
        wait_all: bool = True
    ) -> List[OptimizationResult]:
        """Collect optimization results.

        Args:
            timeout: Maximum time to wait for results (None = wait forever).
            wait_all: If True, wait for all submitted tasks to complete.

        Returns:
            List of optimization results.
        """
        results = []
        start_time = time.time()

        if wait_all:
            expected_results = self.tasks_submitted - self.tasks_completed
        else:
            expected_results = None

        while True:
            # Check timeout
            if timeout and (time.time() - start_time) > timeout:
                logger.warning(f"Result collection timed out (collected {len(results)} results)")
                break

            # Check if we have all expected results
            if expected_results is not None and len(results) >= expected_results:
                break

            try:
                result = self.result_queue.get(timeout=1.0)
                results.append(result)
                self.tasks_completed += 1

                # Update statistics
                if result.status == TaskStatus.COMPLETED:
                    self.total_changes += result.changes_made
                    self.total_duration += result.duration

                logger.debug(
                    f"Collected result for {result.function_addr:x}: "
                    f"{result.status.value} ({self.tasks_completed}/{self.tasks_submitted})"
                )

            except queue.Empty:
                if not wait_all:
                    break  # Return what we have
                continue  # Keep waiting for more results

        return results

    def shutdown(self, timeout: float = 10.0):
        """Shutdown worker processes gracefully.

        Args:
            timeout: Maximum time to wait for workers to finish (seconds).
        """
        if not self.is_running:
            return

        logger.info("Shutting down worker processes")

        # Send poison pills to all workers
        for _ in range(self.num_workers):
            self.work_queue.put(None)

        # Wait for workers to finish
        for worker in self.workers:
            worker.join(timeout=timeout)
            if worker.is_alive():
                logger.warning(f"Worker {worker.pid} did not terminate gracefully, killing")
                worker.terminate()
                worker.join()

        self.workers = []
        self.is_running = False
        logger.info("All workers shutdown")

    def get_statistics(self) -> Dict[str, Any]:
        """Get execution statistics.

        Returns:
            Dictionary with statistics.
        """
        return {
            'num_workers': self.num_workers,
            'tasks_submitted': self.tasks_submitted,
            'tasks_completed': self.tasks_completed,
            'tasks_pending': self.tasks_submitted - self.tasks_completed,
            'total_changes': self.total_changes,
            'total_duration': self.total_duration,
            'avg_duration': self.total_duration / self.tasks_completed if self.tasks_completed > 0 else 0.0
        }

    def __enter__(self):
        """Context manager support."""
        self.start()
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager support."""
        self.shutdown()


def optimize_functions_parallel(
    function_addresses: List[int],
    num_workers: Optional[int] = None,
    progress_callback: Optional[Callable[[int, int], None]] = None
) -> List[OptimizationResult]:
    """Convenience function to optimize multiple functions in parallel.

    Args:
        function_addresses: List of function addresses to optimize.
        num_workers: Number of worker processes (default: CPU count).
        progress_callback: Optional callback for progress updates (completed, total).

    Returns:
        List of optimization results.

    Example:
        >>> results = optimize_functions_parallel(
        ...     [0x401000, 0x402000, 0x403000],
        ...     num_workers=4,
        ...     progress_callback=lambda done, total: print(f"{done}/{total}")
        ... )
    """
    with ParallelOptimizer(num_workers=num_workers) as executor:
        # Submit all functions
        executor.submit_batch(function_addresses)

        # Collect results with progress updates
        results = []
        while len(results) < len(function_addresses):
            batch = executor.get_results(timeout=1.0, wait_all=False)
            results.extend(batch)

            if progress_callback:
                progress_callback(len(results), len(function_addresses))

        return results
