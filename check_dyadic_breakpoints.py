"""Run one Lean kernel check per marked theorem. Invoke with --list or --through NAME."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parent
MODULE_DIR = ROOT / "ReimannWindow" / "DyadicChecks"
MODULES = ["CharacterSums", "DyadicBaseMatrix", "DyadicLayerGrowth", "LatticeQuotient", "PellCertificate"]
STATUS = ROOT / "dyadic-breakpoint-status.json"
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def checkpoints():
    for module in MODULES:
        path = MODULE_DIR / (module + ".lean")
        source = path.read_text(encoding="utf-8")
        namespace, = re.findall(r"^namespace ([\w.]+)$", source, re.M)
        marks = list(re.finditer(r"^-- breakpoint (\w+)$", source, re.M))
        declarations = re.findall(r"^theorem (\w+)", source, re.M)
        if not declarations or declarations != [m[1] for m in marks]:
            raise ValueError(f"{path.name}: every theorem needs its own ordered breakpoint")
        for mark in marks:
            name = mark[1]
            full_name = f"{namespace}.{name}"
            prefix = source[:mark.start()] + f"\n#print axioms {full_name}\nend {namespace}\n"
            yield name, full_name, prefix


def save(state):
    with tempfile.NamedTemporaryFile(mode="w", dir=ROOT, delete=False, encoding="utf-8") as f:
        json.dump(state, f, indent=2)
        f.write("\n")
    os.replace(f.name, STATUS)


def fail(state, message):
    state["stopped"] = message
    save(state)
    print(message, file=sys.stderr, flush=True)
    return 1


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("--lean", help="Path to the Lean compiler or elan shim")
    args.add_argument("--comparison-version", help="Check an additional compiler version and record it separately")
    args.add_argument("--list", action="store_true")
    args.add_argument("--fresh", action="store_true", help="Recheck previously accepted prefixes")
    args.add_argument("--through", metavar="NAME", help="Pause after the named breakpoint")
    opts = args.parse_args()
    gates = []
    for gate in checkpoints():
        gates.append(gate)
        if opts.through == gate[0] and not opts.list:
            break
    names = [name for name, _, _ in gates]
    if opts.list:
        print("\n".join(names))
        return 0
    if opts.through:
        if opts.through not in names:
            args.error("unknown breakpoint: " + opts.through)
    pin = (ROOT / "lean-toolchain").read_text().strip()
    version = opts.comparison_version or pin.split(":v", 1)[1]
    if not re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", version):
        args.error("expected a release version such as 4.33.1")
    global STATUS
    if opts.comparison_version:
        STATUS = ROOT / f"dyadic-breakpoint-status-{version}.json"
    state = {"pin": pin, "checked_version": version, "passed": [], "next": gates[0][0]}
    elan_home = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    lean_name = "lean.exe" if os.name == "nt" else "lean"
    installed = elan_home / "toolchains" / f"leanprover--lean4---v{version}" / "bin" / lean_name
    executable = opts.lean or (str(installed) if installed.is_file() else shutil.which("lean"))
    if not executable:
        return fail(state, f"Lean {version} unavailable. Install the requested release with elan.")
    run = dict(cwd=ROOT, capture_output=True, text=True, encoding="utf-8", errors="replace")
    try:
        probe = subprocess.run([executable, "--version"], timeout=30, **run)
    except (OSError, subprocess.TimeoutExpired) as error:
        return fail(state, str(error))
    compiler_message = (probe.stdout + probe.stderr).strip()
    if probe.returncode or not re.search(r"version " + re.escape(version) + r"(?:,|\s|\))", compiler_message):
        return fail(state, f"Requested Lean {version} unavailable. {compiler_message}")
    state["compiler"] = compiler_message
    previous = json.loads(STATUS.read_text(encoding="utf-8")) if STATUS.is_file() else {}
    cached = {}
    if not opts.fresh and previous.get("compiler") == compiler_message:
        cached = {p["theorem"]: p["sha256"] for p in previous.get("passed", [])}
    for index, (name, full_name, source) in enumerate(gates):
        state["next"] = name
        save(state)
        digest = hashlib.sha256(source.encode()).hexdigest()
        if cached.get(full_name) == digest:
            state["passed"].append({"theorem": full_name, "sha256": digest})
            if opts.through == name:
                state["paused_after"] = name
            state["next"] = gates[index + 1][0] if index + 1 < len(gates) else None
            save(state)
            print(f"Previously passed {full_name}", flush=True)
            continue
        print(f"Checking {full_name}", flush=True)
        result = subprocess.run([executable, "--stdin"], input=source, **run)
        output = (result.stdout + result.stderr).strip()
        if result.returncode:
            return fail(state, output or f"Lean exited with status {result.returncode}")
        audit = re.search(r"depends on axioms:\s*\[([^\]]*)\]", output)
        if audit:
            axioms = {item.strip() for item in audit[1].split(",") if item.strip()}
            if axioms - STANDARD_AXIOMS:
                return fail(state, f"{full_name} uses unexpected axioms: {sorted(axioms)}")
        elif "does not depend on any axioms" not in output:
            return fail(state, f"Missing axiom report for {full_name}: {output}")
        state["passed"].append({"theorem": full_name, "sha256": digest})
        state["next"] = gates[index + 1][0] if index + 1 < len(gates) else None
        if opts.through == name:
            state["paused_after"] = name
        save(state)
        print(f"Passed {full_name}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
