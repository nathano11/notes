"""Check the seven independent Std checkpoint modules. Use --list to find a breakpoint."""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MODULES = ROOT / "ReimannWindow"
RECORDS = ROOT / ".checkpoints" / "verified"
VERSION = "4.33.1"
STANDALONE = ("Baseline", "LocalConditions", "Window", "BottomUnit", "FirstLayer", "Prime277", "CircularUnits")
OPTIONS = ["-DwarningAsError=true"]
DECLARATION = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque)\s+"
    r"([\w'.]+)"
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def visible_lines(lines):
    """Mask nested block comments and line comments, retaining source positions."""
    depth = 0
    for line in lines:
        out = []
        pos = 0
        quoted = False
        while pos < len(line):
            pair = line[pos:pos + 2]
            if depth:
                if pair in ("/-", "-/"):
                    depth += 1 if pair == "/-" else -1
                    out.extend("  ")
                    pos += 2
                else:
                    out.append(" ")
                    pos += 1
            elif quoted:
                char = line[pos]
                out.append(char)
                pos += 1
                if char == "\\" and pos < len(line):
                    out.append(line[pos])
                    pos += 1
                elif char == '"':
                    quoted = False
            elif pair == "/-":
                depth = 1
                out.extend("  ")
                pos += 2
            elif pair == "--":
                break
            else:
                char = line[pos]
                quoted = char == '"'
                out.append(char)
                pos += 1
        yield "".join(out).rstrip()
    if depth:
        raise ValueError("Unclosed Lean block comment")


@dataclass
class Step:
    name: str
    path: Path
    line: int
    prefix: str


def module_steps(path):
    """The checkpoint modules use unindented top-level commands and named declarations."""
    source = path.read_text(encoding="utf-8-sig")
    lines = source.splitlines(keepends=True)
    visible = list(visible_lines(lines))
    starts = []
    scopes = []
    for index, line in enumerate(visible):
        if not line or line[0].isspace():
            continue
        decl = DECLARATION.match(line)
        if decl:
            starts.append((index, decl[1], tuple(scopes)))
        elif re.match(r"^example\b", line):
            starts.append((index, f"example_at_{index+1}", tuple(scopes)))
        elif line.startswith("namespace "):
            scopes.append(line.split()[1])
        elif section := re.match(r"^(?:noncomputable\s+)?section(?:\s+(\S+))?$", line):
            scopes.append(section[1] or "")
        elif re.match(r"^end(?:\s|$)", line):
            if not scopes:
                raise ValueError(f"{path.name}:{index+1}: unmatched end")
            scopes.pop()
    if not starts:
        raise ValueError(f"{path.name} contains no named checkpoints")
    for number, (index, name, open_scopes) in enumerate(starts):
        if number + 1 == len(starts):
            prefix = source
        else:
            limit = starts[number + 1][0]
            # Namespace/section boundaries and attributes belong to later commands.
            # Indented lines, deriving clauses, pattern alternatives, and commas
            # may still be part of this declaration.
            for pos in range(index + 1, limit):
                if re.match(r"^(?:end\b|section\b|namespace\b|set_option\b|@\[|open\b|variable\b)", visible[pos]):
                    limit = pos
                    break
            while limit > index + 1 and not visible[limit - 1]:
                limit -= 1
            # A trailing block comment can begin on the final line of code and
            # close at the next declaration. Cut after the last actual token.
            last_line = limit - 1
            endings = "".join(("end " + scope).rstrip() + "\n" for scope in reversed(open_scopes))
            prefix = "".join(lines[:last_line]) + lines[last_line][:len(visible[last_line])] + "\n" + endings
        yield Step(f"{path.stem}.{name}", path, index + 1, prefix)


def all_steps(module=None):
    paths = [MODULES / (name + ".lean") for name in ((module,) if module else STANDALONE)]
    steps = [step for path in paths for step in module_steps(path)]
    names = [step.name for step in steps]
    if len(names) != len(set(names)):
        raise ValueError("Checkpoint names must be unique within each module")
    return steps


def compiler(explicit, requested):
    exe = "lean.exe" if os.name == "nt" else "lean"
    elan_home = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan")
    if explicit:
        candidates = [Path(shutil.which(explicit) or explicit)]
    else:
        candidates = [
            elan_home / "toolchains" / f"leanprover--lean4---v{requested}" / "bin" / exe,
            Path(shutil.which("lean") or elan_home / "bin" / exe),
        ]
    wrong = []
    for candidate in dict.fromkeys(candidates):
        if not candidate.is_file():
            continue
        path = candidate.resolve()
        version = subprocess.run([str(path), "--version"], cwd=ROOT, capture_output=True)
        banner = (version.stdout + version.stderr).decode("utf-8", "replace").strip()
        if version.returncode == 0 and re.search(r"\bversion " + re.escape(requested) + r"(?=[, )]|$)", banner):
            return path, banner
        wrong.append(f"{path}: {banner}")
    raise ValueError(f"Lean {requested} is required. Set --lean PATH or provide that toolchain via PATH or ELAN_HOME."
                     + ("\n" + "\n".join(wrong) if wrong else ""))


def read_record(path):
    try:
        with path.open(encoding="utf-8") as file:
            return json.load(file)
    except (OSError, ValueError):
        return {}


def save_record(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     suffix=".tmp", delete=False) as file:
        tmp = Path(file.name)
        try:
            json.dump(data, file, indent=2, ensure_ascii=False)
            file.write("\n")
            file.flush()
            os.fsync(file.fileno())
        except BaseException:
            file.close()
            tmp.unlink(missing_ok=True)
            raise
    try:
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--list", action="store_true", help="list checkpoints and source lines without running Lean")
    parser.add_argument("--through", metavar="MODULE.DECL", help="stop after this declaration, inclusive")
    parser.add_argument("--module", choices=STANDALONE, help="check just one independent Std module")
    parser.add_argument("--check-version", default=VERSION, metavar="X.Y.Z",
                        help="check with exactly this release; defaults to the project pin")
    parser.add_argument("--lean", metavar="PATH", help="path to the requested Lean compiler")
    parser.add_argument("--fresh", action="store_true", help="recheck matching successful records")
    args = parser.parse_args()
    pin = (ROOT / "lean-toolchain").read_text(encoding="utf-8-sig").strip()
    if pin != f"leanprover/lean4:v{VERSION}":
        raise ValueError(f"Expected Lean {VERSION}, but lean-toolchain contains {pin!r}")
    if not re.fullmatch(r"\d+\.\d+\.\d+", args.check_version):
        raise ValueError("--check-version requires an exact numeric release such as 4.36.0")
    steps = all_steps(args.module)
    if args.through:
        selected = args.through.removeprefix("ReimannWindow.")
        for index, step in enumerate(steps):
            if step.name == selected:
                steps = steps[:index+1]
                break
        else:
            raise ValueError(f"Unknown checkpoint {args.through!r}. Use --list to see the names.")
    if args.list:
        for step in steps:
            print(f"{step.name}\t{step.path.relative_to(ROOT).as_posix()}:{step.line}")
        return 0
    lean, banner = compiler(args.lean, args.check_version)
    context = {
        "toolchain": pin, "check_version": args.check_version, "version": banner, "compiler": str(lean),
        "compiler_sha256": digest(lean.read_bytes()), "options": OPTIONS,
        "runner_sha256": digest(Path(__file__).read_bytes()),
    }
    # These modules use the bundled standard library. Exclude external olean
    # search paths so an unrelated project cannot change what gets verified.
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    print(banner, flush=True)
    for step in steps:
        data = step.prefix.encode("utf-8")
        fingerprint = dict(context, name=step.name, source=step.path.relative_to(ROOT).as_posix(),
                           line=step.line, prefix_sha256=digest(data))
        key = digest(json.dumps(fingerprint, sort_keys=True).encode("utf-8"))
        path = RECORDS / step.path.stem / (key + ".json")
        failure_file = RECORDS.parent / "failures" / step.path.stem / (key + ".json")
        old = read_record(path)
        failure = read_record(failure_file)
        latest_failure = failure.get("failed_utc", "") if isinstance(failure, dict) else ""
        if (not args.fresh and isinstance(old, dict) and old.get("checked") == fingerprint
                and old.get("exit_code") == 0 and old.get("verified_utc", "") > latest_failure):
            print(f"CACHED {step.name}", flush=True)
            continue
        print(f"CHECK  {step.name}  {fingerprint['source']}:{step.line}", flush=True)
        run = subprocess.run([str(lean), *OPTIONS, "--stdin"], cwd=ROOT, input=data, env=env,
                             stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if run.stdout:
            sys.stdout.buffer.write(run.stdout)
            sys.stdout.buffer.flush()
        if run.returncode:
            failed_at = datetime.now(timezone.utc)
            save_record(failure_file, {"checked": fingerprint, "exit_code": run.returncode,
                                       "failed_utc": failed_at.isoformat(),
                                       "diagnostics": run.stdout.decode("utf-8", "replace")})
            print(f"FAILED {step.name} (Lean exit {run.returncode}); diagnostics: {failure_file}", file=sys.stderr)
            return 1
        save_record(path, {"checked": fingerprint, "exit_code": 0,
                           "verified_utc": datetime.now(timezone.utc).isoformat()})
        print(f"PASS   {step.name}", flush=True)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError) as error:
        print(error, file=sys.stderr)
        sys.exit(2)
