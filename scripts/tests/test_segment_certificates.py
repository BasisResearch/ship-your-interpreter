"""Typed effect consumers reject artifact mutations before granting frame facts."""

import copy
import csv
import json
import shutil
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from scripts import difftest, houdini_summary
from scripts import segment_certificates as certs


class SegmentCertificateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.base = Path(self.temp.name)
        self.repo, self.campaign = self.base / "repo", self.base / "campaign"
        self.query = "independentRoute"
        self.field = "independentField"
        for root in certs.SOURCE_ROOTS:
            (self.repo / root).mkdir(parents=True, exist_ok=True)
        for name in (
            *certs.SOURCE_FILES,
            "Vsa/Proof.lean",
            "riscv-lean/lean-sail/State.lean",
        ):
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"fixture {name}\n")
            snapshot = self.campaign / "src-tree" / name
            snapshot.parent.mkdir(parents=True, exist_ok=True)
            snapshot.write_bytes(path.read_bytes())
        self.sources = [
            {
                "path": path.relative_to(self.repo).as_posix(),
                "snapshot": "src-tree/" + path.relative_to(self.repo).as_posix(),
                "sha256": certs.sha256(path),
            }
            for path in self.repo.rglob("*")
            if path.is_file()
        ]
        self.write_table(
            "source-provenance.tsv", ("path", "snapshot", "sha256"), self.sources
        )
        query_path = self.campaign / "queries" / f"{self.query}.smt2"
        query_path.parent.mkdir()
        query_path.write_text("(check-sat)\n")
        self.descriptor = {
            "schema": "vsa.segment-certificate.v1",
            "query": self.query,
            "field": self.field,
            "entry": "0x80004088",
            "stop": "0x80004034",
            "stop_policy": "before-pc",
            "effect": {
                "registers": {"kind": "abi", "gprs": list(certs.ABI_GPRS)},
                "writes": [],
                "output_preserved": True,
            },
            "theorem": "Example.checkedRoute",
            "precondition": "Example.Args.pre",
            "postcondition": "Example.Args.post",
            "query_sha256": certs.sha256(query_path),
            "provenance_manifest": "source-provenance.tsv",
            "provenance_sha256": certs.sha256(self.campaign / "source-provenance.tsv"),
        }
        self.record = {
            key: self.descriptor[key]
            for key in (
                "query",
                "field",
                "entry",
                "stop",
                "stop_policy",
                "query_sha256",
                "theorem",
            )
        }
        self.record.update(
            certificate_path=f"certificates/{self.query}.json", certificate_sha256=""
        )
        self.save_descriptor()
        self.capability = {
            "query": self.query,
            "field": self.field,
            "instance": "base",
            "capability": "closed",
        }
        self.span = {
            "field": self.query,
            "residual": self.field,
            "instance": "base",
            "entry": "0x80004088",
            "stop": "0x80004034",
            "ret_exit": "false",
            "complete": "true",
            "summaries": "0",
        }
        self.effect = certs.SegmentCertificate(
            self.query,
            self.field,
            0x80004088,
            0x80004034,
            certs.ABI_GPRS,
            "Example.checkedRoute",
            "Example.Args.pre",
            "Example.Args.post",
        ).effect_row()
        self.write_table(
            "query-capabilities.tsv", tuple(self.capability), [self.capability]
        )
        self.write_table("spans.tsv", tuple(self.span), [self.span])
        self.write_table("query-effects.tsv", certs.EFFECT_COLUMNS, [self.effect])
        self.write_table(
            f"writes/{self.query}.tsv",
            ("guard", "width", "addr"),
            [{"guard": "true", "width": "0", "addr": "#x1000"}],
        )

        self.authority = self.base / "authority"
        self.authority.mkdir()
        shutil.copytree(self.campaign / "src-tree", self.authority / "src-tree")
        shutil.copyfile(
            self.campaign / "source-provenance.tsv",
            self.authority / "source-provenance.tsv",
        )
        self.authority_contract = {
            key: self.descriptor[key]
            for key in (
                "query",
                "field",
                "entry",
                "stop",
                "stop_policy",
                "effect",
                "theorem",
                "precondition",
                "postcondition",
            )
        }
        (self.authority / "segment-authority.json").write_text(
            json.dumps(
                {
                    "schema": "vsa.segment-authority.v1",
                    "provenance_manifest": "source-provenance.tsv",
                    "provenance_sha256": self.descriptor["provenance_sha256"],
                    "contracts": [self.authority_contract],
                }
            )
        )

    def write_table(
        self, name: str, columns: tuple[str, ...], rows: list[dict]
    ) -> None:
        path = self.campaign / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", newline="") as stream:
            writer = csv.DictWriter(
                stream, fieldnames=columns, delimiter="\t", lineterminator="\n"
            )
            writer.writeheader()
            writer.writerows(rows)

    def save_descriptor(self) -> None:
        path = self.campaign / "certificates" / f"{self.query}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(self.descriptor))
        self.record["certificate_sha256"] = certs.sha256(path)
        self.write_table(
            "segment-certificates.tsv", certs.CERTIFICATE_COLUMNS, [self.record]
        )

    def load(self, directory=None, **kwargs) -> dict[str, certs.SegmentCertificate]:
        return certs.load_segment_certificates(
            directory or self.campaign,
            repo_root=self.repo,
            authority_dir=self.authority,
        )

    def assert_consumers_reject(self) -> None:
        with self.assertRaises(certs.CertificateError):
            self.load()
        with patch.object(houdini_summary, "load_segment_certificates", self.load):
            with self.assertRaises(certs.CertificateError):
                houdini_summary.load_query_effects(self.campaign)
        with patch.object(difftest, "load_segment_certificates", self.load):
            effects, findings = difftest.query_effect_manifest(
                self.campaign, {self.query: self.capability}
            )
            self.assertEqual(effects, {})
            self.assertTrue(findings)

    def test_descriptor_grants_frames_without_name_allowlist(self) -> None:
        with patch.object(houdini_summary, "load_segment_certificates", self.load):
            row = houdini_summary.load_query_effects(self.campaign)[self.query]
        self.assertEqual(
            houdini_summary.certified_effect_frames(row),
            {"abi-registers", "memory", "output"},
        )
        with patch.object(difftest, "load_segment_certificates", self.load):
            effects, findings = difftest.query_effect_manifest(
                self.campaign, {self.query: self.capability}
            )
        self.assertFalse(findings)
        self.assertEqual(
            effects[self.query]["_certificate"].preserved_gprs, certs.ABI_GPRS
        )
        row["theorem"] = "Example.changed"
        self.assertEqual(houdini_summary.certified_effect_frames(row), set())

    def test_observations_use_the_validated_register_footprint(self) -> None:
        effect = dict(self.effect, _certificate=self.load()[self.query])
        registers = [[0] * 32, [0] * 32]
        trace = SimpleNamespace(
            regs_at=lambda row: registers[row],
            n=2,
            out_known=[True, True],
            out_before=[0, 0],
            out_after=[0, 0],
            out_byte=[0, 0],
        )
        self.assertFalse(difftest.observed_effect_findings(effect, trace, 0, 1, set()))
        registers[1][5] = 1
        self.assertFalse(difftest.observed_effect_findings(effect, trace, 0, 1, set()))
        for register in certs.ABI_GPRS:
            with self.subTest(register=register):
                registers[1][register] = 1
                findings = difftest.observed_effect_findings(effect, trace, 0, 1, set())
                self.assertEqual(findings[0][0], "EFFECT-REGISTERS")
                registers[1][register] = 0
        self.assertEqual(
            difftest.observed_effect_findings(effect, trace, 0, 1, {16})[0][0],
            "EFFECT-MEMORY",
        )
        trace.out_before[1] = 1
        self.assertEqual(
            difftest.observed_effect_findings(effect, trace, 0, 1, set())[0][0],
            "EFFECT-OUTPUT",
        )

    def test_raw_abi_inventory_does_not_grant_authority(self) -> None:
        self.assertEqual(houdini_summary.certified_effect_frames(self.effect), set())
        self.assertTrue(
            difftest.observed_effect_findings(self.effect, None, None, None, set())
        )
        (self.campaign / "segment-certificates.tsv").unlink()
        with patch.object(difftest, "load_segment_certificates", self.load):
            self.assertTrue(
                difftest.query_effect_manifest(
                    self.campaign, {self.query: self.capability}
                )[1]
            )

    def test_each_certificate_identity_mutation_is_rejected(self) -> None:
        original = copy.deepcopy(self.descriptor)
        for key, value in (
            ("query", "anotherQuery"),
            ("field", "anotherField"),
            ("entry", "0x8000408c"),
            ("stop", "0x80004038"),
            ("stop_policy", "after-pc"),
            ("theorem", "Example.other"),
        ):
            with self.subTest(key=key):
                self.descriptor = dict(original, **{key: value})
                self.save_descriptor()  # Rehash: test identity checks beyond byte integrity.
                self.assert_consumers_reject()
        self.descriptor = original
        self.save_descriptor()

    def test_footprint_mutations_are_rejected(self) -> None:
        original = copy.deepcopy(self.descriptor)
        for key, value in (
            ("registers", {"kind": "abi", "gprs": list(certs.ABI_GPRS[:-1])}),
            ("registers", {"kind": "none", "gprs": []}),
            ("writes", [{"base": 0, "bytes": 8}]),
            ("output_preserved", False),
            ("output_preserved", 1),
        ):
            with self.subTest(key=key, value=value):
                self.descriptor = copy.deepcopy(original)
                self.descriptor["effect"][key] = value
                self.save_descriptor()
                self.assert_consumers_reject()

    def test_span_capability_and_effect_mutations_are_rejected(self) -> None:
        for filename, baseline, key, value in (
            ("spans.tsv", self.span, "stop", "0x80004038"),
            ("spans.tsv", self.span, "ret_exit", "true"),
            ("spans.tsv", self.span, "complete", "false"),
            ("spans.tsv", self.span, "summaries", "1"),
            ("query-capabilities.tsv", self.capability, "field", "wrong"),
            ("query-effects.tsv", self.effect, "theorem", "Example.other"),
            ("query-effects.tsv", self.effect, "provenance", "Lean:Example.other"),
            (
                "query-effects.tsv",
                self.effect,
                "direct_memory_writes",
                "guarded-write-log",
            ),
        ):
            with self.subTest(filename=filename, key=key):
                self.write_table(
                    filename, tuple(baseline), [dict(baseline, **{key: value})]
                )
                self.assert_consumers_reject()
                self.write_table(filename, tuple(baseline), [baseline])

    def test_query_snapshot_current_source_and_manifest_mutations_are_rejected(
        self,
    ) -> None:
        for path in (
            self.campaign / "queries" / f"{self.query}.smt2",
            self.campaign / "src-tree/Vsa/Proof.lean",
            self.repo / "Vsa/Proof.lean",
            self.repo / "riscv-lean/lean-sail/State.lean",
            self.campaign / "source-provenance.tsv",
            self.campaign / "certificates" / f"{self.query}.json",
        ):
            with self.subTest(path=path):
                original = path.read_bytes()
                path.write_bytes(original + b"\n")
                self.assert_consumers_reject()
                path.write_bytes(original)

    def test_coherent_theorem_and_predicate_mutations_are_rejected(self) -> None:
        original = copy.deepcopy(self.descriptor)
        for key in ("theorem", "precondition", "postcondition"):
            with self.subTest(key=key):
                self.descriptor = dict(original, **{key: "Example.mutated"})
                if key == "theorem":
                    self.record[key] = "Example.mutated"
                    self.effect[key] = "Example.mutated"
                    self.effect["provenance"] = "Lean:Example.mutated"
                    self.write_table(
                        "query-effects.tsv", certs.EFFECT_COLUMNS, [self.effect]
                    )
                self.save_descriptor()
                self.assert_consumers_reject()
                self.record["theorem"] = original["theorem"]
                self.effect["theorem"] = original["theorem"]
                self.effect["provenance"] = "Lean:" + original["theorem"]
                self.write_table(
                    "query-effects.tsv", certs.EFFECT_COLUMNS, [self.effect]
                )

    def test_missing_or_campaign_owned_authority_is_rejected(self) -> None:
        with self.assertRaises(certs.CertificateError):
            certs.load_segment_certificates(self.campaign, repo_root=self.repo)
        for authority in (self.campaign, self.campaign / "authority", self.base):
            with (
                self.subTest(authority=authority),
                self.assertRaises(certs.CertificateError),
            ):
                certs.load_segment_certificates(
                    self.campaign, repo_root=self.repo, authority_dir=authority
                )

    def test_new_dependency_source_invalidates_inventory(self) -> None:
        (self.repo / "Vsa/NewDependency.lean").write_text("new dependency")
        self.assert_consumers_reject()

    def test_nonzero_or_malformed_write_rows_are_rejected(self) -> None:
        for width in ("8", "-1", "unknown"):
            with self.subTest(width=width):
                self.write_table(
                    f"writes/{self.query}.tsv",
                    ("guard", "width", "addr"),
                    [{"guard": "true", "width": width, "addr": "#x1000"}],
                )
                self.assert_consumers_reject()

    def test_duplicate_missing_and_path_traversal_records_are_rejected(self) -> None:
        self.write_table(
            "segment-certificates.tsv",
            certs.CERTIFICATE_COLUMNS,
            [self.record, self.record],
        )
        self.assert_consumers_reject()
        self.record["certificate_path"] = "../escape.json"
        self.write_table(
            "segment-certificates.tsv", certs.CERTIFICATE_COLUMNS, [self.record]
        )
        self.assert_consumers_reject()


if __name__ == "__main__":
    unittest.main()
