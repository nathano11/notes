"""Replay each declaration in the mathlib bridge with the project's pinned Lean."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
CORE = ROOT.parent
spec = importlib.util.spec_from_file_location("core_checkpoints", CORE / "checkpoint.py")
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
DECL = re.compile(r"^(?:(?:private|noncomputable|protected|partial|local|scoped)\s+)*"
                  r"(def|theorem|lemma|structure|abbrev|inductive|instance|example|#guard)\b(?:\s+([\w']+))?")
PIN = (ROOT / "lean-toolchain").read_text("utf8").strip().split(":v")[-1]

def run(args, env=None, stdin=None):
    p = subprocess.run(args, cwd=ROOT, env=env, input=stdin, capture_output=True,
                       encoding="utf8", errors="replace")
    if p.returncode:
        raise RuntimeError((p.stdout+p.stderr).strip())
    return p.stdout.strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def dependencies(module, lib_dirs):
    inputs = {}
    seen = set()
    pending = [ROOT / "Reimann277" / (module + ".lean")]
    while pending:
        source = pending.pop()
        if source in seen:
            continue
        seen.add(source)
        for line in core.code_lines(source.read_text("utf-8-sig")):
            match = re.match(r"^(?:public\s+)?import\s+([\w.]+)$", line)
            if not match:
                continue
            name = match[1]
            rel = Path(*name.split(".")).with_suffix(".lean")
            if name.startswith("Reimann277.") or name.startswith("Reimann."):
                dep = (ROOT if name.startswith("Reimann277.") else CORE) / rel
                inputs[name] = digest(dep)
                pending.append(dep)
            else:
                olean = next((lib / rel.with_suffix(".olean") for lib in lib_dirs
                              if (lib / rel.with_suffix(".olean")).is_file()), None)
                if olean is None:
                    raise RuntimeError(f"Missing imported object {name}")
                inputs[name] = digest(olean)
    return inputs

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("module")
    parser.add_argument("--lake", default=shutil.which("lake") or "lake")
    parser.add_argument("--through", help="last declaration name, e.g. PadicInteger.realize")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z]\w*", args.module):
        parser.error("expected one module name")
    source = ROOT / "Reimann277" / (args.module+".lean")
    steps = list(core.breakpoints(source, ROOT / "Reimann277", DECL))
    if args.through:
        keys = [step[0] for step in steps]
        if args.through not in keys:
            parser.error(f"unknown breakpoint {args.through}")
        steps = steps[:keys.index(args.through)+1]
    lake = args.lake
    env = os.environ.copy()
    if Path(lake).is_absolute():
        env["PATH"] = str(Path(lake).parent) + os.pathsep + env["PATH"]
    version = run([lake, "env", "lean", "--version"],env)
    if not re.search(rf"version {re.escape(PIN)}\b",version):
        raise RuntimeError(f"expected Lean {PIN}, got {version}")
    run([lake,"--rehash","build",f"+Reimann277.{args.module}:deps"],env)
    lean_path = run([lake,"env",sys.executable,"-c","import os; print(os.environ['LEAN_PATH'])"],env)
    sysroot = Path(run([lake,"env","lean","--print-prefix"],env))
    env["LEAN_PATH"] = lean_path
    libs = [(ROOT / p).resolve() for p in lean_path.split(os.pathsep) if p] + [sysroot/"lib"/"lean"]
    imports = dependencies(args.module, libs)
    state = ROOT / f"compat-{PIN}-{args.module}.json"
    old = json.loads(state.read_text("utf8")) if state.exists() else {}
    records = old.get("steps", {}) if old.get("compiler") == version and old.get("imports") == imports else {}
    all_keys = {s[0] for s in core.breakpoints(source, ROOT/"Reimann277", DECL)}
    records = {key:row for key,row in records.items() if key in all_keys}
    def save():
        tmp=state.with_suffix(".tmp")
        tmp.write_text(json.dumps({"compiler":version,"mathlib_rev":"fc4f59e577feb1a4956671bc04ac18aaaf8cd842",
                                   "imports":imports,"steps":records},ensure_ascii=False,indent=2)+"\n","utf8")
        os.replace(tmp,state)
    for key,line,prefix in steps:
        sha=hashlib.sha256(prefix.encode()).hexdigest()
        if records.get(key,{}).get("sha256")==sha and records[key].get("status")=="checked":
            continue
        print("Checking",key,flush=True)
        row=records[key]={"sha256":sha,"line":line,"status":"pending"}
        save()
        try:
            result=run([str(sysroot/"bin"/("lean.exe" if os.name=="nt" else "lean")),"--stdin"],env,prefix)
            if "sorryAx" in result or "Lean.ofReduceBool" in result:
                raise RuntimeError(result)
        except RuntimeError as failure:
            row.update(status="failed",diagnostics=str(failure))
            save()
            raise
        row.update(status="checked")
        if result:
            row["checker_output"]=result
        save()
    print("Passed through",steps[-1][0])
if __name__ == "__main__":
    main()
