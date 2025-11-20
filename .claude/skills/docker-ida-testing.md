---
description: Running IDA Pro integration tests using Docker in sandboxed environments. Handles Docker installation, authentication, and test execution for d810-ng deobfuscation plugin testing.
tags: [docker, testing, ida-pro, integration-tests, sandboxed]
---

# Docker IDA Pro Testing Skill

This skill enables running IDA Pro integration tests in Docker containers within sandboxed/restricted environments where Docker may not be pre-installed.

## Prerequisites

- Root access (or sufficient permissions)
- Internet connectivity
- GitHub token with `read:packages` scope for GHCR access

## Installation Steps

### 1. Install Docker Static Binaries

```bash
# Download Docker static binaries
curl -fsSL https://download.docker.com/linux/static/stable/x86_64/docker-27.4.1.tgz -o /tmp/docker.tgz

# Extract and install
tar xzvf /tmp/docker.tgz -C /tmp
cp /tmp/docker/* /usr/local/bin/

# Verify installation
docker --version
dockerd --version
```

### 2. Install iptables (if needed)

```bash
# Install iptables package
apt-get update
apt-get install -y iptables

# Switch to legacy mode (required in some sandboxed environments)
update-alternatives --set iptables /usr/sbin/iptables-legacy
update-alternatives --set ip6tables /usr/sbin/ip6tables-legacy

# Verify
iptables --version
```

### 3. Start Docker Daemon

```bash
# Start daemon with VFS storage (no overlay2 needed) and networking disabled
# This works in restricted environments without kernel module support
dockerd --storage-driver=vfs --iptables=false --bridge=none &

# Wait for daemon to start
sleep 5

# Verify daemon is running
docker info
docker ps
```

### 4. Install Docker Compose

```bash
# Download docker-compose binary
curl -SL https://github.com/docker/compose/releases/download/v2.31.0/docker-compose-linux-x86_64 \
  -o /usr/local/bin/docker-compose

# Make executable
chmod +x /usr/local/bin/docker-compose

# Verify
docker-compose --version
```

### 5. Authenticate to GitHub Container Registry

```bash
# Login with GitHub token (user must provide valid token with read:packages scope)
echo "YOUR_GITHUB_TOKEN" | docker login ghcr.io -u mahmoudimus --password-stdin
```

Expected output:
```
Login Succeeded
```

### 6. Pull IDA Pro Test Image

```bash
# Pull the image (this is large, ~2-4GB, may take several minutes)
docker pull ghcr.io/mahmoudimus/idapro-linux:idapro-tests

# Or pull specific digest from docker-compose.yml
docker pull ghcr.io/mahmoudimus/idapro-linux:idapro-tests@sha256:6acc4756c48d3eecfbb85904361365e6f138844f784a93827597074d3d451ab2

# Verify image is available
docker images | grep idapro
```

## Running Tests

### Option 1: Using docker-compose (Recommended)

```bash
# Navigate to project root
cd /home/user/d810-ng

# Run local tests (no IDA required)
docker-compose run --rm --entrypoint bash idapro-tests -c "
    pip install -e .[dev]
    python tests/run_tests_local.py
"

# Run integration tests with IDA Pro
docker-compose run --rm --entrypoint bash idapro-tests -c "
    pip install -e .[dev]
    pytest tests/system -v --tb=short
"

# Run specific test
docker-compose run --rm --entrypoint bash idapro-tests -c "
    pip install -e .[dev]
    pytest tests/system/test_rule_tracking.py::TestRuleTracking::test_verify_refactored_modules_loaded -v
"
```

### Option 2: Using docker run directly

```bash
docker run --rm \
  -v $(pwd)/src:/root/.idapro/plugins:ro \
  -v $(pwd):/work \
  -w /work \
  -e PYTHONPATH=/app/ida/python:/work \
  -e PYTHONWARNINGS=ignore \
  ghcr.io/mahmoudimus/idapro-linux:idapro-tests \
  bash -c "
    pip install -e .[dev]
    pytest tests/system -v --tb=short
  "
```

## Troubleshooting

### Docker daemon won't start

**Problem**: `failed to start daemon: Error initializing network controller`

**Solution**: Use VFS storage driver and disable networking:
```bash
dockerd --storage-driver=vfs --iptables=false --bridge=none &
```

### Cannot pull image - "unauthorized" or "denied"

**Problem**: `Error response from daemon: denied`

**Solutions**:
1. Verify token has `read:packages` scope
2. Check token hasn't expired
3. Ensure token owner has access to the package:
   ```bash
   # Test token manually
   curl -H "Authorization: Bearer YOUR_TOKEN" \
     https://ghcr.io/v2/mahmoudimus/idapro-linux/tags/list
   ```

### Image pull fails - "manifest unknown"

**Problem**: `Error response from daemon: manifest unknown`

**Solution**: The specific digest in docker-compose.yml may not exist. Use tag instead:
```bash
docker pull ghcr.io/mahmoudimus/idapro-linux:idapro-tests
```

### Tests fail with import errors

**Problem**: `ModuleNotFoundError` or similar import errors

**Solution**: Ensure package is installed in editable mode:
```bash
docker-compose run --rm idapro-tests bash -c "
    pip install -e .[dev]
    # Then run tests
"
```

### Container exits immediately

**Problem**: Container starts then exits without running tests

**Solution**: Check entrypoint and working directory:
```bash
# Debug by getting a shell
docker-compose run --rm --entrypoint bash idapro-tests

# Inside container, manually run commands
pip install -e .[dev]
pytest tests/system -v
```

### Tests fail with Qt/GUI import errors (CRITICAL)

**Problem**: `ImportError: PySide6 can only be used from the GUI version of IDA` or `NotImplementedError: Can't import PySide6. Are you trying to use Qt without GUI?`

**Root Cause**: Plugin code unconditionally imports GUI components (like `D810GUI` from `d810.ui.ida_ui`) which require Qt. In headless test environments, Qt is not available.

**Solution**: Make GUI imports conditional in plugin code:
```python
# Import GUI only when needed (not in headless/test mode)
try:
    from d810.ui.ida_ui import D810GUI
except (ImportError, NotImplementedError):
    D810GUI = None  # type: ignore

# Later in code, check before instantiation:
if gui and self._is_loaded and D810GUI is not None:
    self.gui = D810GUI(self)
```

**Files affected**:
- `src/d810/manager.py` - Main plugin manager with GUI initialization
- Any other modules that import Qt/GUI components at module level

**Verification**: After applying this fix, run the critical test:
```bash
pytest tests/system/test_rule_tracking.py::TestRuleFiring::test_verify_refactored_modules_loaded -v
```

### VFS storage driver space limitations

**Problem**: Docker image pull fails with "no space left on device" even when disk space is available

**Root Cause**: VFS storage driver in sandboxed environments has limitations with large image extraction (2-4GB images)

**Solution**: Use alternative installation method - direct IDA Pro installation from zip file instead of Docker image. See `ida-direct-install.md` skill for details.

**Symptoms**:
- Image pull reaches 60-80% completion then fails
- Error: `failed to register layer: write /var/lib/docker/vfs/dir/...: no space left on device`
- `df -h` shows available space but extraction still fails

**Workaround attempts** (may not always work):
1. Clear Docker storage: `rm -rf /var/lib/docker/vfs/*`
2. Restart daemon
3. Retry pull

If workarounds fail, use direct IDA installation method.

## Environment Configuration

### docker-compose.yml structure
```yaml
services:
    idapro-tests:
        image: ghcr.io/mahmoudimus/idapro-linux:idapro-tests
        entrypoint: ["python3"]
        working_dir: /work
        environment:
            - PYTHONPATH=/app/ida/python:/work
            - PYTHONWARNINGS=ignore
            - IDAUSR=/root/.idapro
        volumes:
            - ./src/:/root/.idapro/plugins:ro
            - ./:/work
```

### Key environment variables
- `PYTHONPATH`: Must include both IDA Python path and project root
- `IDAUSR`: IDA Pro user directory for plugins
- `PYTHONWARNINGS=ignore`: Suppress warnings from IDA Pro internals

## Testing Specific Features

### Test refactored DSL rules
```bash
docker-compose run --rm idapro-tests bash -c "
    pip install -e .[dev]
    pytest tests/system/test_rule_tracking.py::TestRuleTracking::test_verify_refactored_modules_loaded -v
"
```

### Test with instrumentation
```bash
docker-compose run --rm idapro-tests bash -c "
    pip install -e .[dev]
    pytest tests/system/test_rule_tracking.py -v --log-cli-level=INFO
"
```

### Generate coverage reports
```bash
docker-compose run --rm idapro-tests bash -c "
    pip install -e .[dev]
    pytest tests/system -v --cov=src/d810 --cov-report=html --cov-report=xml
"
# Coverage reports will be in htmlcov/ and coverage.xml
```

## CI/CD Integration

This setup mirrors the GitHub Actions workflow in `.github/workflows/test-ida.yml`:

```yaml
- name: Run integration tests
  run: |
      docker compose run --rm --entrypoint bash idapro-tests -c "
          pip install -e .[dev]
          pytest tests/system -v --tb=short --cov=src/d810 --cov-report=xml
      "
```

## Performance Notes

- **Image size**: ~2-4GB (IDA Pro + dependencies)
- **Pull time**: 3-10 minutes depending on connection
- **VFS storage**: Slower than overlay2 but works in restricted environments
- **Test execution**: Integration tests take 2-5 minutes

## Security Notes

- **GitHub tokens**: Never commit tokens to repository
- **Token storage**: Docker stores credentials unencrypted in `/root/.docker/config.json`
- **Token scope**: Use minimal scope (`read:packages`) for pulling images
- **Token rotation**: Rotate tokens regularly

## Quick Reference

```bash
# Full setup from scratch
apt-get install -y iptables
curl -fsSL https://download.docker.com/linux/static/stable/x86_64/docker-27.4.1.tgz -o /tmp/docker.tgz
tar xzvf /tmp/docker.tgz -C /tmp && cp /tmp/docker/* /usr/local/bin/
update-alternatives --set iptables /usr/sbin/iptables-legacy
dockerd --storage-driver=vfs --iptables=false --bridge=none &
sleep 5
curl -SL https://github.com/docker/compose/releases/download/v2.31.0/docker-compose-linux-x86_64 -o /usr/local/bin/docker-compose
chmod +x /usr/local/bin/docker-compose
echo "$GITHUB_TOKEN" | docker login ghcr.io -u mahmoudimus --password-stdin
docker pull ghcr.io/mahmoudimus/idapro-linux:idapro-tests

# Run tests
cd /home/user/d810-ng
docker-compose run --rm idapro-tests bash -c "pip install -e .[dev] && pytest tests/system -v"
```

## Related Files

- `.github/workflows/test-ida.yml` - CI workflow using this setup
- `docker-compose.yml` - Service definitions
- `tests/system/` - Integration tests requiring IDA Pro
- `tests/run_tests_local.py` - Local tests not requiring IDA Pro

## Notes for Future Sessions

1. **Always check Docker daemon status** before running tests
2. **GitHub token must be valid** - they expire or can be revoked
3. **Image digest in docker-compose.yml** may change - use tag if digest fails
4. **VFS storage driver** is slow but reliable in sandboxed environments
5. **Network disabled mode** bypasses iptables issues in restricted kernels
6. **GUI imports must be conditional** - Plugin code that imports Qt/GUI components will fail in headless environments. See troubleshooting section for fix pattern.
7. **VFS has space limitations** - Large Docker images (2-4GB) may fail to pull with VFS storage even with available disk space. Use direct IDA installation as fallback.
