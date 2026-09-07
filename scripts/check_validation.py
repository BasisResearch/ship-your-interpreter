#!/usr/bin/env python3
"""Check validation tooling and actual initial-state regressions.

The default gate rejects current-boundary findings. --self-test checks that the
harness detects the pinned findings; it does not validate the current contract.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

try:
    from scripts import build_private
except ModuleNotFoundError:
    import build_private


def verify_backend(repo: Path, backend: Path) -> None:
    """Reject missing or stale modules, including files outside Vsa's imports."""
    order = build_private.topological_order(
        build_private.discover_modules(repo, include_executable=True)
    )
    current = build_private.module_fingerprints(
        repo, order, build_private.input_context(repo)
    )
    prior = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
    stale = [
        module.name
        for module in order
        if prior.get(module.name) != current[module.name]
        or not build_private.output_path(backend, module).is_file()
    ]
    if stale:
        raise build_private.BuildError(f"stale private backend: {', '.join(stale[:10])}")


def build_backend(repo: Path, backend: Path) -> None:
    """Run the serialized builder and retain the existing module-time gate."""
    allow = {
        line.split("#", 1)[0].strip()
        for line in (repo / "scripts/elab-budget-allow.txt").read_text().splitlines()
    }
    hard = float(os.environ.get("HARD_S", "180"))
    warn = float(os.environ.get("WARN_S", "90"))
    if not 0 < warn <= hard:
        raise build_private.BuildError("invalid elaboration time limits")
    durations = {}
    active = None
    started = time.monotonic()
    command = [sys.executable, "scripts/build_private.py", "--output-root",
               str(backend), "--include-executable", "--resume"]
    with subprocess.Popen(command, cwd=repo, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True) as process:
        for line in process.stdout:
            print(line, end="", flush=True)
            match = re.match(r"\[\d+/\d+\] (build|skip) (.+)\n", line)
            if match:
                now = time.monotonic()
                if active is not None:
                    durations[active] = now - started
                active = build_private.module_name(Path(match[2])) if match[1] == "build" else None
                started = now
        status = process.wait()
        if active is not None:
            durations[active] = time.monotonic() - started
    (backend / "validation-build-times.json").write_text(
        json.dumps(durations, indent=2) + "\n"
    )
    if status:
        raise build_private.BuildError(f"private build failed: {status}")
    over = []
    for name, seconds in durations.items():
        if name in allow:
            continue
        if seconds >= warn:
            print(f"elaboration: {name} {seconds:.1f}s (hard {hard:.1f}s)")
        if seconds >= hard:
            over.append(name)
    if over:
        raise build_private.BuildError(f"elaboration budget exceeded: {', '.join(over)}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", required=True, type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--verify-backend-only", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--build-backend", action="store_true")
    args = parser.parse_args(argv)
    repo = Path(__file__).resolve().parents[1]
    try:
        if args.build_backend:
            build_backend(repo, args.backend)
        verify_backend(repo, args.backend)
    except (build_private.BuildError, OSError, ValueError) as error:
        print(f"validation: {error}", file=sys.stderr)
        return 2
    if args.verify_backend_only:
        return 0
    if args.output is None:
        parser.error("--output is required unless --verify-backend-only")
    census = subprocess.run(
        [sys.executable, "scripts/field_census.py", "--backend", str(args.backend),
         "--output", str(args.output.with_name(args.output.name + "-census")),
         "--inventory-only"],
        cwd=repo, check=False,
    )
    if census.returncode:
        print("validation: complete-library field inventory failed", file=sys.stderr)
        return 2
    command = [
        sys.executable, "scripts/boundary_regressions.py",
        "--backend", str(args.backend), "--output", str(args.output),
    ]
    if args.self_test:
        command.append("--self-test")
    result = subprocess.run(command, cwd=repo, check=False)
    # Run artifact mutation tests even when the boundary has a known finding.
    environment = dict(os.environ)
    environment["BOUNDARY_REGRESSION_ARTIFACTS"] = str(args.output.resolve())
    tests = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s", "scripts/tests"],
        cwd=repo, env=environment, check=False,
    )
    if tests.returncode:
        return 2
    if result.returncode:
        return result.returncode
    mode = "harness SELF-TEST" if args.self_test else "boundary regressions"
    print(f"validation: {mode} passed; full contract NOT-CHECKED")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
