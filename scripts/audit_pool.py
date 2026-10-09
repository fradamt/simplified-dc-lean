"""Bound audit commands and retain each command's exit code and output."""

from concurrent.futures import ThreadPoolExecutor
import atexit
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import sys
import threading
import tempfile


def positive_seconds(value):
    if not re.fullmatch(r'[1-9][0-9]*', value):
        raise ValueError('AUDIT_TIMEOUT must be a positive integer in seconds')
    return int(value)


class AuditPool:
    def __init__(self, work, workers, timeout=None, *, temp_prefix=None, slot_script=None):
        self.work = None
        self.temporary = temp_prefix is not None
        self.active = set()
        self.lock = threading.Lock()
        self.stopping = False
        # Install exit and signal cleanup before any fixture allocation.
        atexit.register(self.cleanup)
        signal.signal(signal.SIGTERM, self.interrupt)
        signal.signal(signal.SIGINT, self.interrupt)
        self.workers = workers
        self.slot_script = slot_script
        self.timeout = positive_seconds(os.environ.get('AUDIT_TIMEOUT', '1800')) \
            if timeout is None else timeout
        self.serial = 0
        self.time_args = []
        if os.environ.get('AUDIT_TIMING', '0') == '1':
            flags = ['-l'] if sys.platform == 'darwin' else ['-v']
            self.time_args = ['/usr/bin/time', *flags]
            # Refuse an unsupported timer before any build or audit starts.
            probe = subprocess.run([*self.time_args, '-o', os.devnull, 'true'],
                                   capture_output=True, timeout=10)
            if probe.returncode:
                raise SystemExit('AUDIT TIMING PREFLIGHT FAILED')

        # Defer a signal until the allocated path is stored for cleanup.
        mask = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGTERM, signal.SIGINT})
        try:
            if self.temporary:
                self.work = Path(tempfile.mkdtemp(prefix=temp_prefix, dir=work))
            else:
                self.work = Path(work)
                self.work.mkdir(parents=True, exist_ok=True)
        finally:
            signal.pthread_sigmask(signal.SIG_SETMASK, mask)

    def cleanup(self):
        if self.temporary and self.work is not None:
            shutil.rmtree(self.work)
            self.work = None

    @staticmethod
    def terminate(proc):
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=2)
        except subprocess.TimeoutExpired:
            pass
        # A child can survive after its group leader exits.
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()

    def interrupt(self, signum, _frame):
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        signal.signal(signal.SIGINT, signal.SIG_IGN)
        with self.lock:
            self.stopping = True
            active = list(self.active)
        for proc in active:
            self.terminate(proc)
        raise SystemExit(128 + signum)

    def reserve_log(self, label):
        self.serial += 1
        return self.work / f'{self.serial:02d}-{label}.log'

    def execute(self, path, args, *, env=None, cwd=None):
        if self.slot_script is not None:
            args = ['bash', '-c', 'source "$1"; shift; gate_with_slot "$@"',
                    'audit-slot', str(self.slot_script), *args]
        if self.time_args:
            args = [*self.time_args, '-o', str(path.with_suffix('.time')), *args]
        with path.open('w') as out:
            # Only worker threads spawn commands. The main thread can safely
            # wait for this lock in a signal handler, with no spawn/register gap.
            with self.lock:
                if self.stopping:
                    return 143
                proc = subprocess.Popen(args, stdout=out, stderr=subprocess.STDOUT,
                                        env=env, cwd=cwd, start_new_session=True)
                self.active.add(proc)
            try:
                code = proc.wait(timeout=self.timeout)
            except subprocess.TimeoutExpired:
                self.terminate(proc)
                out.write(f'\nAUDIT TIMEOUT after {self.timeout}s\n')
                code = 124
            except BaseException:
                self.terminate(proc)
                raise
            finally:
                with self.lock:
                    self.active.discard(proc)
        path.with_suffix('.rc').write_text(str(code) + '\n')
        return code

    @staticmethod
    def result(label, path, code, expect):
        output = path.read_text()
        print(f'{label}: rc {code} ({path.name})', flush=True)
        if expect is None:
            if code:
                print(output)
                raise SystemExit(code)
        elif code <= 0 or code == 124 or code >= 128 or expect not in output:
            print(output)
            raise SystemExit(f'STOP: negative control {label} did not fail with {expect!r}')
        else:
            print(f'rejected, as expected: {label}', flush=True)
        return output

    def run(self, label, args, *, expect=None, env=None, cwd=None):
        path = self.reserve_log(label)
        with ThreadPoolExecutor(max_workers=1) as pool:
            code = pool.submit(self.execute, path, args, env=env, cwd=cwd).result()
        return self.result(label, path, code, expect)

    def run_pool(self, controls):
        jobs = [(label, self.reserve_log(label), args, options)
                for label, args, options in sorted(controls, key=lambda c: c[0])]
        with ThreadPoolExecutor(max_workers=self.workers) as pool:
            futures = [pool.submit(self.execute, path, args,
                                   env=options.get('env'), cwd=options.get('cwd'))
                       for _, path, args, options in jobs]
            outputs = {}
            failure = None
            for (label, path, _, options), future in zip(jobs, futures):
                try:
                    outputs[label] = self.result(label, path, future.result(),
                                                 options.get('expect'))
                except SystemExit as exc:
                    if failure is None:
                        failure = exc
            if failure is not None:
                raise failure
        return outputs
