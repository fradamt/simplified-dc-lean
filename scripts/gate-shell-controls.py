#!/usr/bin/env python3
"""Test shell failure paths with a fake Lake. Real Lean checks run separately."""

import hashlib
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time


REPO = Path(__file__).resolve().parents[1]
with tempfile.TemporaryDirectory(prefix="gate-shell-controls-") as scratch:
    root = Path(scratch)
    scripts = root / "scripts"
    scripts.mkdir()
    (root / ".lake").mkdir()
    for name in ("fgsa-freeze.sh", "check-fgsa-manifest.sh", "check-fg.sh", "gate-common.sh"):
        shutil.copy2(REPO / "scripts" / name, scripts / name)
    bindir = root / "bin"
    bindir.mkdir()
    lake = bindir / "lake"
    lake.write_text("""#!/usr/bin/env python3
import os
from pathlib import Path
import signal
import sys
import time
mode = os.environ['CONTROL_MODE']
Path('calls').open('a').write(' '.join(sys.argv[1:]) + '\\n')
if mode == 'freeze':
    Path(sys.argv[sys.argv.index('--manifest') + 1]).write_bytes(b'entry\\n\\n\\n')
elif mode == 'signal':
    Path('started').touch()
    while True:
        time.sleep(0.05)
elif mode == 'fail' or (mode == 'setup-fail' and '--write' in sys.argv):
    sys.exit(17)
""")
    lake.chmod(0o755)
    env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ["PATH"])

    def run(name, mode, *args, **extra):
        result = subprocess.run(
            ["bash", str(scripts / name), *args], cwd=root,
            env=dict(env, CONTROL_MODE=mode, **extra), capture_output=True, text=True,
        )
        return result

    result = run("fgsa-freeze.sh", "freeze", "--manifest", "current.md",
                 "--frozen", "frozen.md", "--frozen-sha", "frozen.sha256")
    assert result.returncode == 0, result
    assert (root / "current.md").read_bytes() == b"entry\n"
    assert (root / "frozen.md").read_bytes() == b"entry\n"
    assert (root / "frozen.sha256").read_text() == hashlib.sha256(b"entry\n").hexdigest() + "\n"
    print("CONTROL freeze normalizes before copy/hash: PASS")

    for mode, neg, rc in (("pass", "0", 0), ("fail", "0", 17), ("setup-fail", "1", 17)):
        result = run("check-fgsa-manifest.sh", mode, NEG=neg, AUDIT_TIMING="1")
        assert result.returncode == rc, result
        assert not list((root / ".lake").glob("fgsa-manifest*"))
        print(f"CONTROL manifest cleanup {mode} (rc {rc}): PASS")

    child = subprocess.Popen(
        ["bash", str(scripts / "check-fgsa-manifest.sh")], cwd=root,
        env=dict(env, CONTROL_MODE="signal", NEG="0"), start_new_session=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
    )
    try:
        deadline = time.monotonic() + 10
        while not (root / "started").exists():
            assert time.monotonic() < deadline, "signal control did not start"
            time.sleep(0.01)
        os.killpg(child.pid, signal.SIGTERM)
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 143, (child.returncode, output)
        assert not list((root / ".lake").glob("fgsa-manifest*"))
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
            child.wait()
    print("CONTROL manifest cleanup TERM (rc 143): PASS")

    result = run("check-fg.sh", "fail", "--research-only")
    assert result.returncode == 17 and "NEEDS FRESH FG BUILD" in result.stdout, result
    assert "build --no-build" in (root / "calls").read_text()
    result = run("check-fg.sh", "fail")
    assert result.returncode == 17 and "BUILD FAILED" in result.stdout, result
    assert "build --wfail" in (root / "calls").read_text()
    result = run("check-fg.sh", "pass", "--unknown")
    assert result.returncode == 2, result
    print("CONTROL FG modes: stale build, failed build, unknown option: PASS")
