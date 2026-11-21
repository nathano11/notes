"""Check consecutive Lean source prefixes and save each successful breakpoint."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
PIN = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip().split(":v")[-1]
STATE = ROOT / "checkpoint-state.json"
ORDER = ["Foundation", "Cubic", "Dyadic", "Transfer", "OddDescent", "CyclotomicNorm", "Bernoulli"]
ORDER.extend(f"CubicCycles.D{d}" for d in (8, 57, 456, 50613, 320549, 404904, 2564392))
ORDER.append("CubicCycles")
ORDER.extend(["SampleSpacing", "WeightClasses", "FixedClassDescent", "WindowCertificate", "LocalCorrection"])
ORDER.extend(["Character2893", "PairedSigns"])
ORDER.append("PairedOrders")
ORDER.extend(["DyadicEulerFactor", "SignedProduct", "SignedMeasure", "SignedMeasure256", "SignedPreparation"])
ORDER.extend(["SignedCoefficients", "SignedProjection", "SignedRoots", "SignedFiniteFactor"])
ORDER.append("SignedRowDescent")
ORDER.append("SignedStickelberger")
ORDER.append("SignedAdicRoots")
ORDER.extend(["SignedCyclicAction", "SignedSeriesMap", "SignedCyclicFactor", "SignedTowerMeasure", "SignedGammaTower", "SignedTowerRows", "SignedArithmeticProjection", "SignedTaylor"])
ORDER.append("SignedCompletedAction")
ORDER.extend(["SignedPascalAction", "SignedCanonicalProjection"])
ORDER.append("SignedTaylorScalar")
ORDER.extend(["SignedAnalyticDegree", "SignedQuadraticLift"])
ORDER.append("SignedAnalyticPreparation")
ORDER.append("SignedSeriesUnit")
ORDER.append("SignedResidueRoots")
ORDER.append("SignedAdicProduct")
ORDER.extend(["SignedBernoulliPairing", "SignedCommonNormalization"])
ORDER.extend(["SignedOrientationWitness", "SignedNormalizationComparison"])
ORDER.append("SignedNormalizationPrecision")
ORDER.extend(["SignedStickelbergerCandidate", "SignedFieldComparison2893"])
ORDER.extend(["ScalarCoinvariants", "WeightDepth", "CyclicCocycle", "CyclicBoundary"])
ORDER.append("BoundaryLifts")
ORDER.append("WeightedConductor")
ORDER.append("CoinvariantSupport")
ORDER.extend(["CircularQuadratic69", "CircularPolynomial69", "CircularPrimitive69"])
ORDER.extend(["CircularKernel69", "CircularFactor69", "CircularFrobenius69", "CircularNorm69", "CircularReduction69",
              "CircularNonpower69", "CircularQuadraticPower69", "CircularPowerDescent69",
              "CircularAmbient69", "CircularBasisData69", "CircularBasis69"])
ORDER.extend(["CircularConvolution69", "CircularGauss69", "CircularEisenstein69", "CircularPrimeDivisor69",
              "CircularAbsolute69", "CircularMonomial69", "CircularRational69", "CircularRationalPeriod69",
              "CircularNormTransport69", "CircularIrreducible69", "CircularLeastRelation69",
              "CircularRelationEval69", "CircularHorner69", "CircularFiniteSum69", "CircularIndependence69",
              "CircularNormalForm69", "CircularRelativeBasis69", "CircularPolynomialField69",
              "CircularMultiplication69", "CircularIntegralNormal69", "CircularFieldReduction69", "CircularIntersection69",
              "CircularRadicals69", "CircularFieldBasis69", "CircularFieldNorm69", "CircularNormAction69",
              "CircularQuadraticNonpower69", "CircularSubstitution69", "CircularRootOrbit69",
              "CircularPowerSubstitution69", "CircularGalois69", "CircularRelativeGalois69",
              "CircularNormIdentification69", "CircularRealUnit69", "CircularCosetData69",
              "CircularCosets69", "CircularSinnott69", "CircularOrder69"])
ORDER.append("CircularConjugateRadicals69")
ORDER.append("CircularQuotientCoordinate69")
ORDER.append("TameExample")
ORDER.append("TameRestriction")
ORDER.extend(["TameLocal", "TameClassField"])
ORDER.append("TameTwist277")
ORDER.append("TameStrictInterface")
ORDER.append("TameCoefficients")
ORDER.append("TameContinuity")
ORDER.append("TameOrientation")
ORDER.append("TameStability")
ORDER.append("TameChecks")
ORDER.append("TameSplitting277")
ORDER.extend(["TameLimit277", "TameRootExhaustion277", "TameBiquadratic277", "TameArithmetic277"])
ORDER.append("TameRationalField277")
ORDER.append("TameEmbeddings277")
ORDER.append("TameOrderCompletion277")
ORDER.append("TameLocalOrders277")
ORDER.append("TameOrderFaithful277")
ORDER.extend(["TameCauchy277", "TamePlaceRestriction277", "TameIntegralSaturation277"])
ORDER.append("TameSignedEmbeddings277")
ORDER.append("TameFractionTarget277")
ORDER.append("TameRationalCauchy277")
ORDER.extend(["TameDecomposition277", "TameLocalDensity277"])
ORDER.append("TameUnramified277")
ORDER.extend(["TameAdicDomain277", "TameFractionCompletion277"])
ORDER.append("TameLimitRoots277")
ORDER.append("TamePrimePowers277")
ORDER.append("TameOrderReduction277")
ORDER.append("TameTraceLattice277")
ORDER.append("TameOrderPrimes277")
ORDER.append("TameFiber277")
ORDER.append("TameGaloisInterface")
ORDER.append("TameAdditivity")
ORDER.extend(["DyadicMoments", "DyadicLocal", "DyadicEven", "DyadicLift", "DyadicLattice",
              "DyadicQuotient", "DyadicBottom", "DyadicLayers", "DyadicOrder"])
ORDER.extend(["DyadicMatrixImage", "DyadicBaseFactors", "DyadicPositiveFactors", "DyadicMatrixHandoff",
              "DyadicStrictRelation", "DyadicStrictKernel", "DyadicStrictDualAdapter"])
ORDER.extend(["DyadicSplitRoot", "DyadicInert", "DyadicPlaceAlgebra", "DyadicFiberPrimes",
              "DyadicFiberDescent", "DyadicIntegralPlaces", "DyadicTraceOrder",
              "DyadicRealLayer", "DyadicCyclotomicImage", "DyadicPlaceProduct"])
ORDER.extend(["DyadicClass69", "DyadicZeroValues", "DyadicStickelberger69",
              "DyadicSeriesProjection", "DyadicHalfPrecision"])
ORDER.append("DyadicBasisComparison")
ORDER.extend(["DyadicFieldTrace69", "DyadicOrderCompletion69", "DyadicDistribution69", "DyadicProgression69",
              "DyadicGammaDistribution69", "DyadicIntegralCriterion69", "DyadicOrderIntegral69",
              "DyadicLocalizedPrimes69", "DyadicPrimeClassification69", "DyadicLocalizedCompletion69",
              "DyadicMahler69", "DyadicOneSided69", "DyadicArithmetic69", "DyadicPlaceAction69",
              "DyadicLocalOperations69", "DyadicCompletedIntegers69", "DyadicGalois69"])
ORDER.extend(["DyadicCyclotomicRamification69", "DyadicRamifiedOrder69", "DyadicUnramifiedBase69",
              "DyadicRestrictionTower69", "DyadicArtinCommutator69", "DyadicArtinImage69",
              "DyadicCyclotomicSpan69", "DyadicDecomposition69"])
ORDER.extend(["DyadicBottomValue69", "DyadicArtinFrobenius69", "DyadicEmbeddedBase69",
              "DyadicLocalRestriction69"])
ORDER.extend(["DyadicPrimeConjugacy69", "DyadicProfiniteLift69"])
ORDER.append("DyadicGenusField69")
ORDER.append("DyadicKernelLift69")
ORDER.append("DyadicFiniteRestriction69")
ORDER.append("DyadicAutomorphism69")
ORDER.append("DyadicPrimeExchange69")
ORDER.append("DyadicAbsolutePlace69")
ORDER.append("DyadicAbelianTower69")
ORDER.append("DyadicArtinPlace69")
ORDER.extend(["DyadicMizusawaCoordinates69", "DyadicArtinResidueNorm69", "DyadicArtinLimit69"])
ORDER.extend(["DyadicControlJet69", "DyadicGenusSwitcher69"])
ORDER.append("DyadicRamifiedClass69")
ORDER.append("DyadicMizusawaHandoff69")
ORDER.append("DyadicCenterCriterion69")
ORDER.append("DyadicArtinSquare69")
ORDER.append("DyadicTwistedControl69")
ORDER.append("DyadicResidueShape")
ORDER.append("DyadicContent")
ORDER.append("DyadicShapeBridge")
DECL = re.compile(r"^(?:(?:private|noncomputable|protected|partial)\s+)*(def|theorem|lemma|structure|abbrev|inductive|example|#guard)\b(?:\s+([\w']+))?")
COMMAND = re.compile(r"^(?:import|namespace|section|end|open|variable|set_option|attribute|#|@\[)")


def code_lines(source):
    """Mask comments and strings for command detection, retaining line positions."""
    depth = 0
    quoted = False
    for line in source.splitlines(keepends=True):
        out = []
        i = 0
        while i < len(line):
            pair = line[i:i + 2]
            c = line[i]
            if depth:
                if pair in {"/-", "-/"}:
                    depth += 1 if pair == "/-" else -1
                    i += 2
                    out.append("  ")
                else:
                    out.append(" ")
                    i += 1
            elif quoted:
                if c == "\\":
                    i += 2
                    out.append("  ")
                else:
                    quoted = c != '"'
                    out.append(" ")
                    i += 1
            elif pair == "--":
                break
            elif pair == "/-":
                depth = 1
                i += 2
                out.append("  ")
            else:
                quoted = c == '"'
                out.append(" " if quoted else c)
                i += 1
        yield "".join(out).rstrip()
    if depth or quoted:
        raise ValueError("unterminated Lean comment or string")


def reject_placeholders(path, masked):
    for i, line in enumerate(masked, 1):
        if re.search(r"\b(sorry|admit|axiom|native_decide)\b", line):
            raise ValueError(f"{path.name}:{i} contains a proof placeholder or unchecked dependency")


def breakpoints(path, source_dir=None, declarations=DECL, commands=COMMAND):
    source = path.read_text(encoding="utf-8-sig")
    lines = source.splitlines(keepends=True)
    masked = list(code_lines(source))
    reject_placeholders(path, masked)
    module = ".".join(path.relative_to(source_dir or ROOT / "Reimann").with_suffix("").parts)
    starts = [i for i, line in enumerate(masked) if declarations.match(line) or commands.match(line)]
    scopes = []
    for j, start in enumerate(starts):
        line = masked[start]
        if line.startswith(("namespace ", "section ", "section\n")) or line == "section":
            scopes.append(line.split(maxsplit=1)[1] if " " in line else "")
        elif line == "end" or line.startswith("end "):
            scopes.pop()
        match = declarations.match(line)
        if not match:
            continue
        limit = starts[j + 1] if j + 1 < len(starts) else len(lines)
        end = next(i + 1 for i in range(limit - 1, start - 1, -1) if masked[i].strip())
        kind, name = match.groups()
        if kind == "#guard":
            name = "guard_" + "_".join(re.findall(r"[\w']+", line[6:]))
        elif kind == "example":
            name = f"example_L{start+1}"
        prefix = "".join(lines[:end]).rstrip() + "\n"
        if kind in {"theorem", "lemma"}:
            prefix += f"#print axioms {name}\n"
        prefix += "".join(f"end {scope}\n" for scope in reversed(scopes))
        yield f"{module}.{name}", start + 1, prefix
    if scopes:
        raise ValueError(f"unclosed scopes in {path.name}")
    yield f"{module}.complete", len(lines), source


def write_state(state):
    temp = STATE.with_suffix(".tmp")
    temp.write_text(json.dumps(state, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    os.replace(temp, STATE)


def find_compiler(requested):
    if requested:
        return requested
    on_path = shutil.which("lean")
    if on_path:
        return on_path
    exe = "lean.exe" if os.name == "nt" else "lean"
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    for candidate in [elan / "toolchains" / f"leanprover--lean4---v{PIN}" / "bin" / exe,
                      elan / "bin" / exe]:
        if candidate.is_file():
            return str(candidate)
    return None


def checked_output(args, env):
    result = subprocess.run(args, cwd=ROOT, env=env, capture_output=True,
                            text=True, encoding="utf-8", errors="replace")
    if result.returncode:
        raise ValueError((result.stdout + result.stderr).strip() or f"{args} failed")
    return result.stdout.strip()


def local_dependencies(compiler, module, env):
    """Ask this compiler for its imports and fingerprint every local source in the closure."""
    source = ROOT / "Reimann" / Path(*module.split(".")).with_suffix(".lean")
    pending = [source]
    sources = {}
    while pending:
        current = pending.pop()
        for line in checked_output([compiler, "--src-deps", str(current)], env).splitlines():
            path = Path(line).resolve()
            if not path.is_relative_to(ROOT):
                continue
            key = path.relative_to(ROOT).as_posix()
            if key in sources:
                continue
            data = path.read_bytes()
            reject_placeholders(path, code_lines(data.decode("utf-8-sig")))
            sources[key] = hashlib.sha256(data).hexdigest()
            pending.append(path)
    return sources


def prefix_command(compiler, module, sources, env):
    if not sources:
        return [compiler, "--stdin"]
    sysroot = Path(checked_output([compiler, "--print-prefix"], env))
    lake = sysroot / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    checked_output([lake, "--rehash", "build", f"+Reimann.{module}:deps"], env)
    if local_dependencies(compiler, module, env) != sources:
        raise ValueError("imported sources changed during the dependency build; rerun")
    return [lake, "env", compiler, "--stdin"]


def main():
    global STATE
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="absolute path to Lean or its elan shim")
    parser.add_argument("--compat-version", help="run a separately recorded compatibility check with this exact Lean version")
    parser.add_argument("--module", choices=ORDER, help="check one module")
    parser.add_argument("--through", help="stop after this breakpoint, e.g. Cubic.norm_remainder")
    parser.add_argument("--list", action="store_true", help="list all breakpoints without checking")
    args = parser.parse_args()
    expected = args.compat_version or PIN
    if args.compat_version:
        if not re.fullmatch(r"\d+\.\d+\.\d+", expected) or not args.lean or not args.module:
            parser.error("--compat-version requires a numeric release, --lean, and --module")
        STATE = ROOT / f"compat-{expected}-{args.module}.json"
    selected = [args.module] if args.module else ORDER
    points = [step for module in selected for step in
              breakpoints(ROOT / "Reimann" / Path(*module.split(".")).with_suffix(".lean"))]
    active_keys = {key for key, _, _ in points}
    if args.through:
        keys = [key for key, _, _ in points]
        if args.through not in keys:
            parser.error(f"unknown breakpoint {args.through}")
        points = points[:keys.index(args.through) + 1]
    if args.list:
        for key, line, _ in points:
            print(f"{key} (line {line})")
        return 0
    state = json.loads(STATE.read_text(encoding="utf-8")) if STATE.exists() else {}
    records = state.setdefault("steps", {})
    for old_key in list(records):
        if old_key.rsplit(".", 1)[0] in selected and old_key not in active_keys:
            del records[old_key]
    state["required_lean"] = expected
    state["release_pin"] = PIN
    for key, line, prefix in points:
        digest = hashlib.sha256(prefix.encode("utf-8")).hexdigest()
        if records.get(key, {}).get("sha256") != digest:
            records[key] = {"sha256": digest, "status": "pending"}
        records[key]["line"] = line
    compiler = find_compiler(args.lean)
    if not compiler:
        state["toolchain_status"] = "Pinned compiler unavailable"
        write_state(state)
        print(f"STOP before {points[0][0]}: Lean {PIN} unavailable. No checks were executed.", file=sys.stderr)
        return 2
    try:
        proc = subprocess.run([compiler, "--version"], cwd=ROOT, capture_output=True,
                              text=True, encoding="utf-8", errors="replace", timeout=25)
    except (OSError, subprocess.TimeoutExpired) as err:
        state["toolchain_status"] = f"Could not start Lean {expected}"
        write_state(state)
        print(f"STOP before {points[0][0]}: {err}", file=sys.stderr)
        return 2
    version = proc.stdout.strip()
    if proc.returncode or not re.search(rf"\b{re.escape(expected)}\b(?![-.]\w)", version):
        state["toolchain_status"] = "Pin unavailable through this executable" if proc.returncode else f"Version mismatch: {version}"
        write_state(state)
        print(f"Expected Lean {expected}. {version} {proc.stderr}", file=sys.stderr)
        return 2
    state["toolchain_status"] = version
    write_state(state)
    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    env.pop("LEAN_SYSROOT", None)
    env["LEAN_SRC_PATH"] = str(ROOT)
    commands = {}
    for key, _, prefix in points:
        rec = records[key]
        module = key.rsplit(".", 1)[0]
        if module not in commands:
            module_records = [saved for step, saved in records.items()
                              if step.rsplit(".", 1)[0] == module]
            try:
                imports = local_dependencies(compiler, module, env)
                for saved in module_records:
                    if saved.get("local_sources", {}) != imports:
                        saved["status"] = "pending"
                        saved["local_sources"] = imports
                        saved.pop("checker_output", None)
                        saved.pop("diagnostics", None)
                write_state(state)
                commands[module] = prefix_command(compiler, module, imports, env)
            except (OSError, ValueError) as err:
                for saved in module_records:
                    saved["status"] = "pending"
                    saved.pop("checker_output", None)
                    saved.pop("diagnostics", None)
                rec.update(status="failed", compiler=version, diagnostics=str(err))
                write_state(state)
                print(f"STOP before {key}: {err}", file=sys.stderr)
                return 1
        if rec.get("status") == "checked" and rec.get("compiler") == version:
            continue
        print(f"Checking {key}", flush=True)
        run = subprocess.run(commands[module], input=prefix, cwd=ROOT, env=env, capture_output=True,
                             text=True, encoding="utf-8", errors="replace")
        details = (run.stdout + run.stderr).strip()
        if run.returncode or "sorryAx" in details or "Lean.ofReduceBool" in details:
            rec.update(status="failed", compiler=version, diagnostics=details)
            write_state(state)
            print(details, file=sys.stderr)
            return 1
        rec.update(status="checked", compiler=version)
        rec.pop("diagnostics", None)
        if details:
            rec["checker_output"] = details
        write_state(state)
    print(f"Passed through {points[-1][0]}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
