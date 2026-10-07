"""A Jupyter kernel for Lean 4, backed by the Lean REPL (leanprover-community/repl).

Each cell is one REPL command. A cell runs in the environment left by the cell executed before
it, so a notebook reads like one Lean file split into pieces. Two rules make re-running work:

* A cell that begins with `import` starts a new file: it runs in a fresh environment.
* Re-running a cell runs it again in the environment it first started from, so a corrected
  definition replaces the old one instead of clashing with it. Cells after it then continue
  from the corrected one.

`#eval`, `#check` and other informational messages appear as output, warnings on stderr, and
errors fail the cell. The REPL runs under `lake env` in the project root, so `import Arnold`
and `import Mathlib` resolve to the project's build.
"""

import json
import os
import re
import shutil
import subprocess
import sys
import threading

from ipykernel.kernelapp import IPKernelApp
from ipykernel.kernelbase import Kernel

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("ARNOLD_ROOT", os.path.dirname(os.path.dirname(HERE)))
REPL = os.environ.get(
    "LEAN_REPL", os.path.join(ROOT, "notebook", ".repl", ".lake", "build", "bin", "repl")
)

_IMPORT = re.compile(r"\A(?:\s|--[^\n]*\n|/-(?:.|\n)*?-/)*import\b")


def _lake():
    found = shutil.which("lake")
    if found:
        return found
    elan = os.path.expanduser("~/.elan/bin/lake")
    if os.path.exists(elan):
        return elan
    raise RuntimeError("lake not found: install Lean with elan")


class Repl:
    """One running REPL process."""

    def __init__(self):
        if not os.path.exists(REPL):
            raise RuntimeError(f"Lean REPL not built at {REPL}: run notebook/kernel/install.sh")
        self.proc = subprocess.Popen(
            [_lake(), "env", REPL],
            cwd=ROOT,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1,
        )
        self.stderr = []
        threading.Thread(target=self._drain, daemon=True).start()

    def _drain(self):
        for line in self.proc.stderr:
            self.stderr.append(line)

    def alive(self):
        return self.proc.poll() is None

    def run(self, cmd, env):
        req = {"cmd": cmd} if env is None else {"cmd": cmd, "env": env}
        self.proc.stdin.write(json.dumps(req) + "\n\n")
        self.proc.stdin.flush()
        buf = []
        while True:
            line = self.proc.stdout.readline()
            if line == "":
                raise RuntimeError("the Lean REPL exited:\n" + "".join(self.stderr[-20:]))
            if line.strip() == "" and buf:
                try:
                    return json.loads("".join(buf))
                except json.JSONDecodeError:
                    pass
            buf.append(line)

    def close(self):
        if self.alive():
            self.proc.kill()


class LeanKernel(Kernel):
    implementation = "lean4-repl"
    implementation_version = "1.0"
    language = "lean4"
    language_version = "4"
    language_info = {
        "name": "lean4",
        "mimetype": "text/x-lean4",
        "file_extension": ".lean",
        "pygments_lexer": "lean4",
        "codemirror_mode": "lean4",
    }
    banner = "Lean 4 through the Lean REPL"

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.repl = None
        self.env = None  # environment after the last successful cell
        self.started = {}  # cell id -> environment it first ran in

    def _out(self, name, text):
        if text and not self.get_parent().get("header", {}).get("silent"):
            self.send_response(self.iopub_socket, "stream", {"name": name, "text": text})

    def do_execute(self, code, silent, store_history=True, user_expressions=None,
                   allow_stdin=False, **kwargs):
        if not code.strip():
            return self._ok()
        meta = self.get_parent().get("metadata", {}) or {}
        cell = meta.get("cellId") or code
        fresh = bool(_IMPORT.match(code))
        if fresh:
            start = None
        elif cell in self.started:
            start = self.started[cell]
        else:
            start = self.env
        try:
            if self.repl is None or not self.repl.alive():
                self.repl = Repl()
                self.started.clear()
                if not fresh:
                    start = None
            res = self.repl.run(code, start)
        except Exception as e:  # noqa: BLE001 - report any failure in the cell
            return self._error("Lean REPL", str(e))
        if "message" in res and "env" not in res:
            return self._error("Lean REPL", res["message"])
        if not fresh:
            self.started.setdefault(cell, start)

        errors = []
        for m in res.get("messages", []):
            line = m.get("pos", {}).get("line", 0)
            text = m.get("data", "").rstrip("\n")
            sev = m.get("severity")
            if sev == "info":
                self._out("stdout", text + "\n")
            elif sev == "warning":
                self._out("stderr", f"warning (line {line}): {text}\n")
            else:
                errors.append(f"error (line {line}): {text}")
        for s in res.get("sorries", []):
            line = s.get("pos", {}).get("line", 0)
            self._out("stderr", f"warning (line {line}): declaration uses 'sorry'\n")
        if errors:
            return self._error("Lean error", "\n".join(errors))
        self.env = res.get("env", self.env)
        return self._ok()

    def _ok(self):
        return {"status": "ok", "execution_count": self.execution_count, "payload": [],
                "user_expressions": {}}

    def _error(self, ename, evalue):
        self.send_response(self.iopub_socket, "error",
                           {"ename": ename, "evalue": evalue, "traceback": [evalue]})
        return {"status": "error", "execution_count": self.execution_count, "ename": ename,
                "evalue": evalue, "traceback": [evalue]}

    def do_shutdown(self, restart):
        if self.repl is not None:
            self.repl.close()
        self.repl, self.env = None, None
        self.started.clear()
        return {"status": "ok", "restart": restart}


if __name__ == "__main__":
    IPKernelApp.launch_instance(kernel_class=LeanKernel, argv=sys.argv[1:])
