#!/bin/bash
cd /Users/mahmoud/src/idapro/d810-ng
PYTHONPATH=src python -m pytest tests/unit/core/test_structured_logging.py -v --tb=short 2>&1
