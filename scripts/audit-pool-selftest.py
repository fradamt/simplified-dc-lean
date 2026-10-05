#!/usr/bin/env python3
"""Exercise the production pool without a Lean build or a claims-audit hook."""
from pathlib import Path
import os
import signal
import subprocess
import sys
sys.dont_write_bytecode = True
import tempfile
import time
from unittest.mock import patch

from audit_pool import AuditPool, positive_seconds


def command(body):
    return [sys.executable, '-c', body]


with tempfile.TemporaryDirectory(prefix='audit-pool-control-') as temp:
    pool = AuditPool(Path(temp), 2, timeout=1)
    pool.run_pool([('valid-reject', command('print("CONTROL"); exit(1)'),
                    {'expect': 'CONTROL'}), ('pass', command('print("PASS")'), {})])
    for label, body, expect in (
        ('missed-reject', 'print("CONTROL")', 'CONTROL'),
        ('wrong-reason', 'print("WRONG"); exit(1)', 'CONTROL'),
        ('signal', 'import os, signal; os.kill(os.getpid(), signal.SIGTERM)', 'CONTROL'),
        ('timeout', 'import time; print("CONTROL", flush=True); time.sleep(30)', 'CONTROL'),
        ('failure', 'exit(7)', None),
    ):
        try:
            pool.run_pool([(label, command(body), {'expect': expect}),
                           ('passing-twin', command('print("PASS")'), {})])
        except SystemExit:
            print(f'CONTROL pool {label}: PASS')
        else:
            raise AssertionError(f'pool accepted {label}')
    pidfile = Path(temp) / 'child.pid'
    body = ('import subprocess, sys, time; from pathlib import Path; '
            'p = subprocess.Popen([sys.executable, "-c", '
            '"import signal,time; signal.signal(signal.SIGTERM, signal.SIG_IGN); '
            'time.sleep(30)"]); '
            f'Path({str(pidfile)!r}).write_text(str(p.pid)); time.sleep(30)')
    try:
        pool.run('timeout-child', command(body))
    except SystemExit as exc:
        assert exc.code == 124
    pid = pidfile.read_text()
    deadline = time.monotonic() + 5
    while True:
        try:
            os.kill(int(pid), 0)
        except ProcessLookupError:
            break
        assert time.monotonic() < deadline, f'child still exists: {pid}'
        time.sleep(0.01)
    print('CONTROL timeout terminates descendants: PASS')
    # A gate fail-fast TERM must stop the new process groups too.
    pidfile.unlink()
    driver = ("from audit_pool import AuditPool; from pathlib import Path; "
              f"p = AuditPool(Path({str(Path(temp) / 'signal')!r}), 2, timeout=30); "
              f"p.run('child', {command(body)!r})")
    child = subprocess.Popen(command(driver), cwd=Path(__file__).resolve().parent,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    try:
        deadline = time.monotonic() + 10
        while not pidfile.exists():
            assert child.poll() is None and time.monotonic() < deadline
            time.sleep(0.01)
        os.kill(child.pid, signal.SIGTERM)
        output, _ = child.communicate(timeout=10)
        assert child.returncode == 143, (child.returncode, output)
        pid = int(pidfile.read_text())
        deadline = time.monotonic() + 5
        while True:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                break
            assert time.monotonic() < deadline, f'signal child still exists: {pid}'
            time.sleep(0.01)
    finally:
        if child.poll() is None:
            child.kill()
            child.wait()
    print('CONTROL pool TERM terminates descendants: PASS')
    for value in ('0', '-1', '1.5', 'bad', ''):
        try:
            positive_seconds(value)
        except ValueError:
            pass
        else:
            raise AssertionError(value)
    print('CONTROL timeout inputs: PASS')
    with patch.dict(os.environ, AUDIT_TIMING='1'):
        timed = AuditPool(Path(temp) / 'timed', 1)
        timed.run('timer', command('print("PASS")'))
        assert list(timed.work.glob('*.time'))
        with patch('audit_pool.subprocess.run',
                   return_value=subprocess.CompletedProcess([], 1)):
            try:
                AuditPool(Path(temp) / 'bad-timer', 1)
            except SystemExit as exc:
                assert 'TIMING PREFLIGHT FAILED' in str(exc)
            else:
                raise AssertionError('unsupported timer accepted')
    print('CONTROL timer preflight and output: PASS')

    # Run the real claims entry point. Stop its first Lake call without Lean.
    repo = Path(__file__).resolve().parents[1]
    bindir = Path(temp) / 'bin'
    bindir.mkdir()
    lake = bindir / 'lake'
    lake.write_text('#!' + sys.executable + '\n'
                    'from pathlib import Path\nimport os, time\n'
                    'Path(os.environ["CLAIMS_READY"]).touch()\ntime.sleep(60)\n')
    lake.chmod(0o755)
    for mode, timeout, rc in (('TERM', '30', 143), ('timeout', '1', 124)):
        ready = Path(temp) / (mode + '.ready')
        log = Path(temp) / (mode + '.log')
        env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ['PATH'],
                   CLAIMS_READY=str(ready), AUDIT_TIMEOUT=timeout, SOURCE_ONLY='0', NEG='0')
        with log.open('w') as output:
            child = subprocess.Popen(['bash', 'scripts/check-fgsa-claims.sh'], cwd=repo,
                                     env=env, stdout=output, stderr=subprocess.STDOUT)
        try:
            deadline = time.monotonic() + 30
            while not ready.exists():
                assert child.poll() is None, log.read_text()
                assert time.monotonic() < deadline, log.read_text()
                time.sleep(0.01)
            line = next(line for line in log.read_text().splitlines()
                        if line.startswith('FGSA claims temporary audit logs: '))
            work = Path(line.split(': ', 1)[1])
            assert work.is_dir() and list(work.iterdir()), work
            if mode == 'TERM':
                child.terminate()
            assert child.wait(timeout=10) == rc, log.read_text()
            assert not work.exists(), f'claims fixtures remain after {mode}: {work}'
        finally:
            if child.poll() is None:
                child.terminate()
                child.wait(timeout=10)
        print(f'CONTROL claims directory gone after {mode} (rc {rc}): PASS')

    # Deliver TERM in the allocation/store gap. The stored path must still be removed.
    marker = Path(temp) / 'allocated'
    driver = f'''
import os, signal, tempfile
from pathlib import Path
from unittest.mock import patch
from audit_pool import AuditPool
allocate = tempfile.mkdtemp
def interrupted_allocation(*args, **kwargs):
    assert signal.getsignal(signal.SIGTERM).__self__.__class__ is AuditPool
    path = allocate(*args, **kwargs)
    Path({str(marker)!r}).write_text(path)
    os.kill(os.getpid(), signal.SIGTERM)
    return path
with patch('audit_pool.tempfile.mkdtemp', interrupted_allocation):
    AuditPool({temp!r}, 1, temp_prefix='allocation-control.')
'''
    result = subprocess.run(command(driver), cwd=repo / 'scripts', capture_output=True, text=True)
    assert result.returncode == 143, result
    assert not Path(marker.read_text()).exists()
    print('CONTROL cleanup installed before allocation; pending TERM removes directory: PASS')
