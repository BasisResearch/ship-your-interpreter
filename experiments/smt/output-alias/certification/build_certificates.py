#!/usr/bin/env python3
"""Compile trace certificates serially into their own private directory.

Invoke under `lake env` from the repository root. First build or refresh the
required backend from current sources. Scratch fingerprints cover only each
source and Data, not backend imports. The final repository integration gate
remains authoritative even when this builder reuses matching scratch records.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from typing import TypedDict, cast


class PassRecord(TypedDict):
    """A successful compilation under the original scratch manifest schema."""

    fingerprint: str
    seconds: float
    log: str


@dataclass(frozen=True)
class BuildConfig:
    """Explicit paths and selection for one serialized campaign."""

    certificates: Path
    backend: Path
    names: list[str]
    keep_going: bool


def read_manifest(path: Path) -> dict[str, PassRecord]:
    """Read prior PASS records, rejecting malformed manifest contents."""
    if not path.exists():
        return {}
    raw: object = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError("build manifest must be an object")
    for name, record in raw.items():
        if (
            not isinstance(name, str)
            or not isinstance(record, dict)
            or not isinstance(record.get("fingerprint"), str)
            or not isinstance(record.get("log"), str)
            or not isinstance(record.get("seconds"), (float, int))
        ):
            raise ValueError(f"malformed manifest record: {name}")
    return cast(dict[str, PassRecord], raw)


def build(config: BuildConfig) -> int:
    """Compile missing/stale sources and maintain the existing PASS semantics."""
    certs = config.certificates
    manifest_path = certs / "build-manifest.json"
    manifest = read_manifest(manifest_path)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join(
        [str(certs), str(config.backend)]
        + ([env["LEAN_PATH"]] if env.get("LEAN_PATH") else [])
    )
    data_hash = hashlib.sha256((certs / "AliasTraceData.lean").read_bytes()).hexdigest()
    failed: list[str] = []
    built = 0
    reused = 0
    start = time.monotonic()
    for name in config.names:
        source = certs / f"{name}.lean"
        obj = certs / f"{name}.olean"
        log = certs / f"{name}.log"
        fingerprint = hashlib.sha256(
            source.read_bytes() + data_hash.encode()
        ).hexdigest()
        previous = manifest.get(name)
        if (
            previous is not None
            and previous["fingerprint"] == fingerprint
            and obj.is_file()
        ):
            reused += 1
            continue
        started = time.monotonic()
        with log.open("w", encoding="utf-8") as transcript:
            result = subprocess.run(
                ["lean", "-R", str(certs), "-o", str(obj), str(source)],
                env=env,
                stdout=transcript,
                stderr=subprocess.STDOUT,
                check=False,
            )
        elapsed = time.monotonic() - started
        valid = result.returncode == 0 and "sorryAx" not in log.read_text(
            encoding="utf-8"
        )
        print(name, "PASS" if valid else "FAIL", f"{elapsed:.2f}s", flush=True)
        if valid:
            built += 1
            manifest[name] = {
                "fingerprint": fingerprint,
                "seconds": elapsed,
                "log": str(log),
            }
        else:
            failed.append(name)
            manifest.pop(name, None)
        manifest_path.write_text(
            json.dumps(manifest, indent=2) + "\n", encoding="utf-8"
        )
        if not valid and not config.keep_going:
            break
    print(
        json.dumps(
            {
                "built": built,
                "reused": reused,
                "failed": failed,
                "seconds": time.monotonic() - start,
            }
        ),
        flush=True,
    )
    return int(bool(failed))


def main() -> int:
    """Require portable paths and default to Data followed by units001–285."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificates", required=True, type=Path)
    parser.add_argument("--backend", required=True, type=Path)
    parser.add_argument("--keep-going", action="store_true")
    parser.add_argument("names", nargs="*")
    args = parser.parse_args()
    all_names = ["AliasTraceData", *(f"AliasTrace{i:03}" for i in range(1, 286))]
    names = args.names or all_names
    if len(set(names)) != len(names) or any(name not in all_names for name in names):
        parser.error("names must be unique Data/unit module names")
    if not args.backend.is_dir():
        parser.error("--backend must be a current private build directory")
    return build(
        BuildConfig(
            args.certificates.resolve(), args.backend.resolve(), names, args.keep_going
        )
    )


if __name__ == "__main__":
    raise SystemExit(main())
