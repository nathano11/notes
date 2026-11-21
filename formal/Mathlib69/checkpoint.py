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
import time
import tomllib

ROOT = Path(__file__).resolve().parent
CORE = ROOT.parent
spec = importlib.util.spec_from_file_location("core_checkpoints", CORE / "checkpoint.py")
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)
DECL = re.compile(r"^(?:@\[[^\n]*?\]\s*)*(?:(?:private|noncomputable|protected|partial|local|scoped)\s+)*"
                  r"(def|theorem|lemma|structure|abbrev|inductive|instance|example|#guard)\b"
                  r"(?:\s+([\w']+(?:\.[\w']+)*))?")
PIN = (ROOT / "lean-toolchain").read_text("utf8").strip().split(":v")[-1]

def default_lake():
    executable = "lake.exe" if os.name == "nt" else "lake"
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    pinned = elan / "toolchains" / f"leanprover--lean4---v{PIN}" / "bin" / executable
    return str(pinned) if pinned.is_file() else shutil.which("lake") or "lake"

def mathlib_revision():
    with (ROOT / "lakefile.toml").open("rb") as config:
        requirements = tomllib.load(config)["require"]
    return next(dep["rev"] for dep in requirements if dep["name"] == "mathlib")

def run(args, env=None, stdin=None):
    p = subprocess.run(args, cwd=ROOT, env=env, input=stdin, capture_output=True,
                       encoding="utf8", errors="replace")
    if p.returncode:
        raise RuntimeError((p.stdout+p.stderr).strip())
    return p.stdout.strip()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def lean_environment(lake, env):
    # Query the resolved Lean and its import search path in one Lake invocation.
    probe = ("import json, os, shutil, subprocess; lean = shutil.which('lean'); "
             "print(json.dumps([subprocess.check_output([lean, '--version'], text=True).strip(), "
             "subprocess.check_output([lean, '--print-prefix'], text=True).strip(), "
             "os.environ['LEAN_PATH']]))")
    version, sysroot, lean_path = json.loads(run([lake, "env", sys.executable, "-c", probe], env))
    return version, Path(sysroot), lean_path

def dependencies(module, lib_dirs):
    inputs = {}
    seen = set()
    pending = [ROOT / "ReimannNative69" / (module + ".lean")]
    while pending:
        source = pending.pop()
        if source in seen:
            continue
        seen.add(source)
        for line in core.code_lines(source.read_text("utf-8-sig")):
            match = re.fullmatch(r"\s*(?:(?:public|private|meta)\s+)*import\s+"
                                 r"(?:(?:all|meta)\s+)*([\w.]+)", line)
            if not match:
                continue
            name = match[1]
            rel = Path(*name.split(".")).with_suffix(".lean")
            if name.startswith("ReimannNative69.") or name.startswith("Reimann."):
                dep = (ROOT if name.startswith("ReimannNative69.") else CORE) / rel
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
    parser.add_argument("--lake", default=default_lake())
    parser.add_argument("--rehash", action="store_true",
                        help="ask Lake to recompute dependency hashes even when modification times match")
    parser.add_argument("--through", help="last declaration name, e.g. ConcreteQuotient69.generator_vanishes")
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z]\w*", args.module):
        parser.error("expected one module name")
    source = ROOT / "ReimannNative69" / (args.module+".lean")
    steps = list(core.breakpoints(source, ROOT / "ReimannNative69", DECL))
    keys = [step[0] for step in steps]
    if len(keys) != len(set(keys)) or any(key.endswith(".None") for key in keys):
        parser.error("each declaration needs a distinct explicit name for its checkpoint")
    fingerprints = {key: (line, hashlib.sha256(prefix.encode()).hexdigest())
                    for key, line, prefix in steps}
    if args.through:
        if args.through not in keys:
            parser.error(f"unknown breakpoint {args.through}")
        steps = steps[:keys.index(args.through)+1]
    lake = args.lake
    env = os.environ.copy()
    if Path(lake).is_absolute():
        env["PATH"] = str(Path(lake).parent) + os.pathsep + env["PATH"]
    version, sysroot, lean_path = lean_environment(lake, env)
    if not re.search(rf"version {re.escape(PIN)}\b",version):
        raise RuntimeError(f"expected Lean {PIN}, got {version}")
    checks = ["--rehash"] if args.rehash else []
    run([lake,*checks,"build",f"+ReimannNative69.{args.module}:deps"],env)
    env["LEAN_PATH"] = lean_path
    libs = [(ROOT / p).resolve() for p in lean_path.split(os.pathsep) if p] + [sysroot/"lib"/"lean"]
    imports = dependencies(args.module, libs)
    state = ROOT / f"compat-{PIN}-{args.module}.json"
    old = json.loads(state.read_text("utf8")) if state.exists() else {}
    revision = mathlib_revision()
    same_inputs = (old.get("compiler") == version and old.get("mathlib_rev") == revision
                   and old.get("imports") == imports)
    records = old.get("steps", {}) if same_inputs else {}
    records = {key:row for key,row in records.items()
               if fingerprints.get(key) == (row.get("line"), row.get("sha256"))}
    def save():
        tmp=state.with_suffix(f".{os.getpid()}.tmp")
        tmp.write_text(json.dumps({"compiler":version,"mathlib_rev":revision,
                                   "imports":imports,"steps":records},ensure_ascii=False,indent=2)+"\n","utf8")
        # A reader on Windows can temporarily hold the target without delete sharing.
        for attempt in range(10):
            try:
                os.replace(tmp,state)
                return
            except PermissionError:
                if os.name != "nt" or attempt == 9:
                    raise
                time.sleep(0.05 * (attempt+1))
    if old and (not same_inputs or old.get("steps") != records):
        save()
    for key,line,prefix in steps:
        sha=fingerprints[key][1]
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
