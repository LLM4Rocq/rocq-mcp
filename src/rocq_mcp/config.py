"""Environment-derived configuration (single definition site).

Every ``ROCQ_*`` knob the server reads at import time is defined here.
``server.py`` re-binds these names into its own namespace for backward
compatibility — submodules read them as ``_server.<NAME>`` and tests
monkeypatch them there, both of which keep working because server code
reads its *own* module globals.  (Four submodule-local knobs stay where
their consumers and test-patch points live: ``ROCQ_PET_TIMEOUT_GRACE``
and ``ROCQ_MAX_STATES`` in ``interactive.py``,
``ROCQ_ENRICHMENT_TIMEOUT_CAP`` in ``compile_enrichment.py``,
``ROCQ_DEBUG_ENRICHMENT`` in ``envelope.py``.)

Leaf module: imports nothing from the package.
"""

from __future__ import annotations

import os

import psutil

ROCQ_WORKSPACE: str = os.environ.get("ROCQ_WORKSPACE", os.getcwd())
_ROCQ_WORKSPACE_EXPLICIT: bool = "ROCQ_WORKSPACE" in os.environ
ROCQ_COQC_TIMEOUT: int = int(os.environ.get("ROCQ_COQC_TIMEOUT", "60"))
ROCQ_VERIFY_TIMEOUT: int = int(os.environ.get("ROCQ_VERIFY_TIMEOUT", "120"))
ROCQ_PET_TIMEOUT: float = float(os.environ.get("ROCQ_PET_TIMEOUT", "30"))
ROCQ_QUERY_TIMEOUT_CAP: int = int(os.environ.get("ROCQ_QUERY_TIMEOUT_CAP", "300"))
ROCQ_COQC_BINARY: str = os.environ.get("ROCQ_COQC_BINARY", "coqc")
ROCQ_MAX_SOURCE_SIZE: int = int(os.environ.get("ROCQ_MAX_SOURCE_SIZE", "1000000"))


def _default_max_pet_rss_mb() -> int:
    """Default pet RSS cap: 50% of system RAM, hard-capped at 16 GB.

    Tuned to fire well above legitimate ``vm_compute`` ceilings (~2-4 GB)
    but well below the OOM-killer / swap-thrash zone.  On a 32 GB Mac
    this resolves to 16 GB; on a 16 GB host, 8 GB; on a 64 GB+ host the
    16 GB cap kicks in.
    """
    total_mb = psutil.virtual_memory().total // (1024 * 1024)
    return min(int(0.50 * total_mb), 16_384)


ROCQ_MAX_PET_RSS_MB: int = int(
    os.environ.get("ROCQ_MAX_PET_RSS_MB", str(_default_max_pet_rss_mb()))
)
_MEMORY_WATCHDOG_INTERVAL: float = 0.5
_RECENT_ERRORS_MAX: int = 20

# Multi-error walker tunables for ``rocq_compile_file``.  When CAP is 0
# the feature is disabled and no ``errors`` field is added to the
# response.  TIMEOUT is the per-``pet.run`` budget inside the walker.
_COMPILE_MULTI_ERROR_CAP: int = int(
    os.environ.get("ROCQ_COMPILE_MULTI_ERROR_CAP", "20")
)
_COMPILE_MULTI_ERROR_TIMEOUT: float = float(
    os.environ.get("ROCQ_COMPILE_MULTI_ERROR_TIMEOUT", "5.0")
)
