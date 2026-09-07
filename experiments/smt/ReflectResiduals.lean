import experiments.smt.ReflectSpan
import Vsa.Sim.EnvGetSpec9
import Vsa.Sim.EnvNewSpec
import Vsa.Sim.EnvSetComplete
import Vsa.Sim.StrcmpSpecW4
import Vsa.Sim.ValueEqualSpec4
import Vsa.Sim.rows.NativeBodyAssert
import Vsa.Sim.rows.ExecWhileRouteRows
import Vsa.Sim.SegEffect
import Vsa.Sim.ExecWhileCertificates

#check Vsa.Sim.FrameGuarantee.refl
#check Vsa.Sim.execWhileLoopRouteRow_framed

/-!
# Per-residual span map + encodability check

`residualSpans` maps each single-span `TermResidualsCore` residual to the
concrete `[entry, exit)` code span whose `Steps` it constrains (from the arm
tables: `KindTablePins` for the eval arms, the exec_stmt dispatch for the
statement arms, `seqLoopImage` for the seq loops). Residuals sharing an arm map
to the same span (the per-op sub-dispatch is inside it).

Global, composite, relational-splice, and sequence-constructor residuals have
no entry here.  Their former finite spans could not identify the named Lean
premise, so the capability manifest reports zero machine instances for them.

`#check_residuals` reflects every span with `reflectExactD` and reports blocks /
summaries / term size — confirming each is encodable (gap-free, DAG-sized) with
the exact reflector.
-/

open Vsa.ReflectSpan

namespace Vsa.ReflectResiduals

open Lean (toJson)

/-- Source inventory for certificate provenance. Include the whole proof tree so
new transitive imports cannot silently escape the provenance boundary. -/
private partial def certificateLeanSources (dir : System.FilePath) : IO (List String) := do
  let mut paths := []
  for entry in ← dir.readDir do
    if ← entry.path.isDir then
      if entry.fileName != ".git" && entry.fileName != ".lake" then
        paths := paths ++ (← certificateLeanSources entry.path)
    else if entry.path.extension == some "lean" ||
        entry.fileName == "lakefile.toml" || entry.fileName == "lake-manifest.json" then
      paths := paths ++ [entry.path.toString]
  return paths

/-- Hash exact artifact bytes with the system SHA256 implementation. -/
private def certificateHashes (paths : List String) : IO (List String) := do
  if paths.isEmpty then return []
  let result ← IO.Process.output
    { cmd := "shasum", args := #["-a", "256"] ++ paths.toArray }
  if result.exitCode != 0 then
    throw (IO.userError s!"certificate SHA256 failed: {result.stderr}")
  let lines := (result.stdout.splitOn "\n").filter (· != "")
  if lines.length != paths.length then
    throw (IO.userError "certificate SHA256 returned the wrong number of digests")
  lines.mapM fun line => do
    let digest := String.ofList (line.toList.take 64)
    if digest.length != 64 || !digest.toList.all (fun c =>
        ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')) then
      throw (IO.userError "certificate SHA256 returned a malformed digest")
    return digest

private def certificateHash (path : String) : IO String := do
  let hashes ← certificateHashes [path]
  match hashes with
  | [hash] => return hash
  | _ => throw (IO.userError "certificate SHA256 omitted its digest")

private def emitCertificateProvenance (dir : String) : IO String := do
  let mut proofSources := []
  for root in ["Vsa", "riscv-lean/lean_emulator", "riscv-lean/Lean_RV64D_executable",
      "riscv-lean/lean-sail", ".lake/packages/ELFSage", ".lake/packages/Cli"] do
    proofSources := proofSources ++ (← certificateLeanSources root)
  let paths := (proofSources ++
    ["Vsa.lean", "experiments/smt/ReflectSpan.lean", "experiments/smt/ReflectResiduals.lean",
     "lakefile.toml", "lake-manifest.json", "lean-toolchain", "c/while-riscv-htif.elf"])
    |>.mergeSort (· ≤ ·)
  for path in paths do
    let snapshot : System.FilePath := s!"{dir}/src-tree/{path}"
    if let some parent := snapshot.parent then IO.FS.createDirAll parent
    IO.FS.writeBinFile snapshot (← IO.FS.readBinFile path)
  let hashes ← certificateHashes (paths.map fun path => s!"{dir}/src-tree/{path}")
  let rows := (paths.zip hashes).map fun (path, hash) =>
    s!"{path}\tsrc-tree/{path}\t{hash}"
  let manifest := s!"{dir}/source-provenance.tsv"
  IO.FS.writeFile manifest ("path\tsnapshot\tsha256\n" ++ String.intercalate "\n" rows ++ "\n")
  certificateHash manifest

private def certificateAddrJson : Vsa.Sim.AddrExpr → Lean.Json
  | .literal value => Lean.Json.mkObj [("kind", "literal"), ("value", toJson value)]
  | .variable index => Lean.Json.mkObj [("kind", "variable"), ("index", toJson index)]
  | .add base offset => Lean.Json.mkObj
      [("kind", "add"), ("base", certificateAddrJson base), ("offset", toJson offset)]

private def certificateGuardJson : Vsa.Sim.GuardExpr → Lean.Json
  | .always => Lean.Json.mkObj [("kind", "always")]
  | .eq left right => Lean.Json.mkObj
      [("kind", "eq"), ("left", certificateAddrJson left), ("right", certificateAddrJson right)]
  | .conj left right => Lean.Json.mkObj
      [("kind", "and"), ("left", certificateGuardJson left), ("right", certificateGuardJson right)]

private def certificateEffectJson (effect : Vsa.Sim.RegionEffect) : Lean.Json :=
  let kind := match effect.regs with
    | .all => "all" | .none => "none" | .abi => "abi" | .explicit _ => "explicit"
  let gprs := (List.range 32).filter fun n => match effect.regs with
    | .all => true
    | .none => false
    | .abi => Vsa.Alloc.AbiPreserved (Vsa.Sim.gprReg n)
    | .explicit regs => regs.contains (Vsa.Sim.gprReg n)
  let writes := effect.writes.map fun region => Lean.Json.mkObj
    [("base", certificateAddrJson region.base), ("bytes", toJson region.bytes),
     ("guard", certificateGuardJson region.guard)]
  Lean.Json.mkObj
    [("registers", Lean.Json.mkObj [("kind", toJson kind), ("gprs", toJson gprs)]),
     ("writes", toJson writes), ("output_preserved", toJson effect.outputPreserved)]

/-- Serialize only an exact dependent export. Query names and theorem names never
select the effect; the effect is projected from the checked certificate. -/
private def whileCertificateDescriptor
    (identity : Vsa.Sim.SegmentIdentity)
    (certificate : Vsa.Sim.WhileBodyReturnExport identity) : List (String × Lean.Json) :=
  [("query", toJson identity.query), ("field", toJson identity.residual),
   ("entry", toJson s!"0x{String.ofList (Nat.toDigits 16 identity.entryPC.toNat)}"),
   ("stop", toJson s!"0x{String.ofList (Nat.toDigits 16 identity.exitPC.toNat)}"),
   ("stop_policy", toJson (if identity.stopBefore then "before-pc" else "return")),
   ("effect", certificateEffectJson certificate.effect),
   ("theorem", "Vsa.Sim.whileBodyReturnCertified"),
   ("precondition", "Vsa.Sim.WhileBodyReturnArgs.pre"),
   ("postcondition", "Vsa.Sim.WhileBodyReturnArgs.post")]

private def emitWhileCertificate (dir provenanceHash : String)
    (identity : Vsa.Sim.SegmentIdentity)
    (certificate : Vsa.Sim.WhileBodyReturnExport identity) : IO String := do
  let entry := s!"0x{String.ofList (Nat.toDigits 16 identity.entryPC.toNat)}"
  let stop := s!"0x{String.ofList (Nat.toDigits 16 identity.exitPC.toNat)}"
  let stopPolicy := if identity.stopBefore then "before-pc" else "return"
  let theoremName := "Vsa.Sim.whileBodyReturnCertified"
  let queryHash ← certificateHash s!"{dir}/queries/{identity.query}.smt2"
  let relativePath := s!"certificates/{identity.query}.json"
  let document := Lean.Json.mkObj (whileCertificateDescriptor identity certificate ++
    [("schema", toJson "vsa.segment-certificate.v1"), ("query_sha256", toJson queryHash),
     ("provenance_manifest", toJson "source-provenance.tsv"), ("provenance_sha256", toJson provenanceHash)])
  IO.FS.createDirAll s!"{dir}/certificates"
  IO.FS.writeFile s!"{dir}/{relativePath}" (document.compress ++ "\n")
  let digest ← certificateHash s!"{dir}/{relativePath}"
  return s!"{identity.query}\t{identity.residual}\t{entry}\t{stop}\t{stopPolicy}\t{relativePath}\t{digest}\t{queryHash}\t{theoremName}"

/-- Independent authority receipt. Consumers receive this trusted directory
explicitly; a campaign cannot nominate its own authority. -/
elab "#emit_segment_authority " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    let provenanceHash ← emitCertificateProvenance dir
    let contracts := [Vsa.Sim.WhileBodyReturnResidual.returning,
      Vsa.Sim.WhileBodyReturnResidual.looping].map fun residual =>
        Lean.Json.mkObj (whileCertificateDescriptor residual.identity
          (Vsa.Sim.whileBodyReturnExport residual))
    let receipt := Lean.Json.mkObj
      [("schema", "vsa.segment-authority.v1"), ("contracts", toJson contracts),
       ("provenance_manifest", "source-provenance.tsv"), ("provenance_sha256", toJson provenanceHash)]
    IO.FS.writeFile s!"{dir}/segment-authority.json" (receipt.compress ++ "\n")
    Lean.logInfo m!"#emit_segment_authority → {dir}: {contracts.length} typed contracts"

/-- A machine-post conjunct discharged by a named, kernel-checked Lean theorem
rather than by the SMT projection.  The driver accepts only the exact rows it
knows how to interpret; this manifest is emitted by Lean with the campaign. -/
structure LeanPostCertificate where
  residual : String
  post : String
  theoremName : String

/-- `NativeAssertInternalAbi` quantifies the full `AbiPreservedNoise` frame.
Its precondition and postcondition use the same ghost register map, so the
closed theorem entails each of these four entry-to-exit equalities. -/
def leanPostCertificates : List LeanPostCertificate := [
  { residual := "hCallAssertOk", post := "abi_frame_x1",
    theoremName := "Vsa.Sim.nativeAssertInternalAbi_closed" },
  { residual := "hCallAssertOk", post := "abi_frame_x8",
    theoremName := "Vsa.Sim.nativeAssertInternalAbi_closed" },
  { residual := "hCallAssertOk", post := "abi_frame_x9",
    theoremName := "Vsa.Sim.nativeAssertInternalAbi_closed" },
  { residual := "hCallAssertOk", post := "abi_frame_x18",
    theoremName := "Vsa.Sim.nativeAssertInternalAbi_closed" } ]

-- Keep the manifest's named proof in the elaborated dependency graph.
#check Vsa.Sim.nativeAssertInternalAbi_closed

/-- Kernel-backed identity for a semantic helper theorem.  This manifest says
only that the named theorem elaborated as a dependency of this emitter.  It
does not identify the SMT helper summary with the theorem's Lean relation. -/
structure SemanticHelperCertificate where
  target : Nat
  name : String
  relation : String
  theoremName : String

def semanticHelperCertificates : List SemanticHelperCertificate := [
  { target := 0x800029fc, name := "env_new",
    relation := "empty 32-byte Env with parent link",
    theoremName := "Vsa.Sim.env_new_spec" },
  { target := 0x8000285c, name := "value_equal",
    relation := "Lean Value.equal",
    theoremName := "Vsa.Sim.value_equal_spec_full" },
  { target := 0x80006ea0, name := "strcmp",
    relation := "Lean string lexicographic sign",
    theoremName := "Vsa.Sim.strcmp_full_spec" },
  { target := 0x80002c10, name := "env_get",
    relation := "Lean Store.get? successful Value words",
    theoremName := "Vsa.Sim.env_get_found_uncond''" },
  { target := 0x80002cdc, name := "env_set",
    relation := "Lean Store.set? successful first binding update",
    theoremName := "Vsa.Sim.env_set_from_entry" } ]

-- These checks make every manifest theorem an elaborated kernel dependency.
#check Vsa.Sim.env_new_spec
#check Vsa.Sim.value_equal_spec_full
#check Vsa.Sim.strcmp_full_spec
#check Vsa.Sim.env_get_found_uncond''
#check Vsa.Sim.env_set_from_entry

/-- residual → (entry PC, exit PC). -/
def residualSpans : List (String × Nat × Nat) := [
  -- eval arms
  ("hInt",  0x80003408, 0x800033ec), ("hStr",  0x80003414, 0x800033ec),
  ("hBool", 0x80003420, 0x800033ec), ("hNull", 0x8000342c, 0x800033ec),
  -- The `var` and `assign` arms do NOT tail into the shared epilogue at
  -- 0x800033ec: both end at eval_expr's SECOND epilogue, 0x80003448 (`ld a3,
  -- 240(sp)` … `ret` at 0x80003478) — `var` by falling through the `env_get`
  -- success test at 0x80003444, `assign` by `bnez a0, 0x80003448` after
  -- `env_set`.  The declared stops were 0x80003480 and 0x80003560, which are
  -- the SECOND INSTRUCTION of the next arm and of the logical arm: not
  -- reachable from these arms at all.  Measured, not guessed — `hAssign`'s arm
  -- runs 226 times over the difftest corpus and reaches 0x80003560 zero times
  -- (`scripts/difftest.sh` phase 1), and the query's dispatch pin and exit guard
  -- are contradictory, so every post came back VALID until the vacuity gate
  -- landed and then VACUOUS.
  ("hVar",     0x80003434, 0x80003448), ("hAssign",  0x8000347c, 0x80003448),
  -- Binary residuals run through their operator-specific tail to the shared
  -- epilogue.  The old stop, 0x800037c0, is inside only the `%` arm and made
  -- every binary query describe modulo executions.
  ("hIAdd", 0x800034e8, 0x800033ec), ("hISub", 0x800034e8, 0x800033ec),
  ("hIMul", 0x800034e8, 0x800033ec), ("hIDiv", 0x800034e8, 0x800033ec),
  ("hIMod", 0x800034e8, 0x800033ec), ("hILt",  0x800034e8, 0x800033ec),
  ("hILe",  0x800034e8, 0x800033ec), ("hIGt",  0x800034e8, 0x800033ec),
  ("hIGe",  0x800034e8, 0x800033ec), ("hEq",   0x800034e8, 0x800033ec),
  ("hNe",   0x800034e8, 0x800033ec),
  -- str ops → the EX_BINARY arm (str operand path)
  ("hStrAddL", 0x800034e8, 0x800033ec), ("hStrAddR", 0x800034e8, 0x800033ec),
  ("hStrGe", 0x800034e8, 0x800033ec), ("hStrGt", 0x800034e8, 0x800033ec),
  ("hStrLe", 0x800034e8, 0x800033ec), ("hStrLt", 0x800034e8, 0x800033ec),
  -- div arithmetic → the div sub-arm (`hDivCorr` is global, not this arm)
  ("hDivOv", 0x800034e8, 0x800033ec),
  -- unary / logical
  -- The unary arm ENDS at 0x80003624 with `jal x0, 0x800033ec`, handing off to
  -- the shared epilogue; 0x80003628 (`addi x15,x10,-3`) is the next arm's code
  -- and is never reached from here.  Demanding it as the exit made these two
  -- queries' assumptions contradictory, so every post came back VALID.
  ("hNeg", 0x800035e0, 0x800033ec), ("hNot", 0x800035e0, 0x800033ec),
  -- Same defect as `hNeg`/`hNot` above, in the same shape and never fixed for
  -- these four: the logical arm ENDS at 0x800035dc with `j 0x800033ec`, and
  -- 0x800035e0 is the UNARY arm's first instruction, which no execution of the
  -- logical arm reaches (13 arm runs, 0 arrivals, over the difftest corpus).
  ("hAndTrue", 0x8000355c, 0x800033ec), ("hAndFalse", 0x8000355c, 0x800033ec),
  ("hOrTrue", 0x8000355c, 0x800033ec), ("hOrFalse", 0x8000355c, 0x800033ec),
  -- call / composition.  `hCall` and the call-case residuals are relational
  -- splices, not identifiable finite spans; they therefore have no machine
  -- residual instance below.
  -- `EvalArgs` starts after the callee has returned.  Nil is the argc branch;
  -- cons is the loop body, including recursive argument evaluation.
  ("hArgsNil", 0x800031d8, 0x80003254),
  ("hArgsCons", 0x800031dc, 0x80003254),
  -- Native-call bodies.  These are the actual `Call.print` / `Call.println`
  -- internal runs, not the opaque indirect dispatch in eval_expr.
  ("hCallAssertOk", 0x80002df4, 0x80002ed4),
  ("hCallPrint", 0x80002ed4, 0x80002f7c),
  ("hCallPrintln", 0x80002f7c, 0x80002fc0),
  ("hFn", 0x800033c4, 0x80003408),
  -- statement arms.  Each residual is about ONE `exec_stmt` arm, so its span is
  -- that arm's own `[execArm*, exec_stmt end)` — NOT the shared dispatch header
  -- `[0x80004014, …)`, which ends at the computed goto `jalr x0, 0(a5)` after
  -- seven instructions and reflects a stub (the old spans' "VALID" frame verdicts
  -- were verdicts about that stub).  The arm PCs are the ELF jump table's, and
  -- coincide with the proof's `Vsa.Sim.execArm*` constants.
  ("hSExpr", 0x80004170, 0x800043ec),
  -- Allocation/setup seam only.  The recursive sequence is projected by the
  -- three finite block instances below; extending this stop to the function
  -- return crosses the loop summary and admits unrelated exit selectors.
  ("hSBlock", 0x8000418c, 0x800041a4),
  ("hSIfTrue", 0x800041e8, 0x800043ec), ("hSIfFalse", 0x800041e8, 0x800043ec),
  ("hSIfNone", 0x800041e8, 0x800043ec), ("hSRet", 0x80004120, 0x800043ec),
  ("hSRetNull", 0x80004120, 0x800043ec), ("hSVarInit", 0x800040d8, 0x800043ec),
  ("hSVarNull", 0x800040d8, 0x800043ec),
  ("hSWhileFalse", 0x8000403c, 0x800043ec), ("hSForStart", 0x80004234, 0x800043ec),
  ("hSBrk", 0x80004098, 0x800043ec), ("hSCont", 0x800040b8, 0x800043ec) ]

/-- A unique machine instance of a residual.  `query` is a filesystem-safe
unique key; `field` is the Lean bundle field. -/
structure ResidualInstance where
  query : String
  field : String
  variant : String
  lo : Nat
  hi : Nat
  /-- Do not widen an internal cut that happens to equal a dispatch arm PC. -/
  directEntry : Bool := false
  /-- A typed proof boundary at one machine state.  These instances validate
  the concrete representation transported by a zero-step `Triple`; they do
  not pretend that an adjacent instruction is part of the Lean stage. -/
  zeroStep : Bool := false

private def ordinaryInstances : List ResidualInstance :=
  residualSpans.map fun (field, lo, hi) =>
    { query := field, field := field, variant := "single", lo := lo, hi := hi }

/-- Exact finite boundaries inside the block loop.  Splitting the child return
from its two status routes is necessary: in the unsplit query `0x800041c8` is
itself a graph loop header and would be replaced by an opaque loop summary. -/
private def blockInstances : List ResidualInstance := [
  { query := "hSBlockIter", field := "hSBlock", variant := "first-child-call-setup",
    lo := 0x800041a4, hi := 0x800041c8 },
  { query := "hSBlockNormal", field := "hSBlock", variant := "normal-status-route",
    lo := 0x800041c8, hi := 0x800041cc },
  { query := "hSBlockAbrupt", field := "hSBlock", variant := "abrupt-status-route",
    lo := 0x800041c8, hi := 0x8000409c } ]

/-- Strict machine projections of the four `CallArmStages` fields.  The
`calleeToArgs` field has two actual target PCs: the empty list is parked at its
`blez` decision, while a nonempty list takes the fallthrough into the loop.
The last two fields are genuinely zero-step typed representation bridges at
0x3254 and 0x33ec. -/
private def callInstances : List ResidualInstance := [
  { query := "hCallCallee", field := "hCall", variant := "callee-call-setup",
    lo := 0x800031b0, hi := 0x800031bc },
  -- `EvalErr.callTooMany` is ordered after the recursive callee evaluation
  -- and before every argument evaluation.  Start at the callee return PC and
  -- stop at the concrete `jal runtime_error`; the callee IH is a typed Lean
  -- boundary, not an opaque SMT summary in this slice.
  { query := "hCallTooMany", field := "hCallTooMany",
    variant := "callee-return-to-max-args-error", lo := 0x800031c0,
    hi := 0x80003fdc, directEntry := true },
  { query := "hCallCalleeToArgsNil", field := "hCall",
    variant := "callee-return-to-empty-args", lo := 0x800031c0,
    hi := 0x800031d8, directEntry := true },
  { query := "hCallCalleeToArgsCons", field := "hCall",
    variant := "callee-return-to-nonempty-args", lo := 0x800031c0,
    hi := 0x800031dc, directEntry := true },
  { query := "hCallArgsToCall", field := "hCall",
    variant := "args-result-to-call-entry", lo := 0x80003254,
    hi := 0x80003254, directEntry := true, zeroStep := true },
  { query := "hCallCallToEpilogue", field := "hCall",
    variant := "call-result-to-epilogue", lo := 0x800033ec,
    hi := 0x800033ec, directEntry := true, zeroStep := true } ]

/-- Compositional finite cuts for the three recursive while constructors.
The two call cuts stop immediately before the recursive call.  The following
cut starts at that call's return PC and validates the truthy route.  The final
cuts start at the body-call return PC and split at the machine loop header
before validating the constructor's status dispatch.  Thus these are machine
projections of the boundaries used
by the Lean IHs, not encodings of the IHs themselves. -/
private def whileInstances : List ResidualInstance := [
  { query := "hSWhileBreakCondSetup", field := "hSWhileBreak",
    variant := "condition-call-setup", lo := 0x8000403c, hi := 0x8000404c,
    directEntry := true },
  { query := "hSWhileBreakCondTruthy", field := "hSWhileBreak",
    variant := "condition-return-truthy-route", lo := 0x80004050, hi := 0x80004074 },
  { query := "hSWhileBreakBodySetup", field := "hSWhileBreak",
    variant := "body-call-setup", lo := 0x80004074, hi := 0x80004084 },
  { query := "hSWhileBreakRoute", field := "hSWhileBreak",
    variant := "break-to-normal-route", lo := 0x80004088, hi := 0x8000409c },
  { query := "hSWhileRetCondSetup", field := "hSWhileRet",
    variant := "condition-call-setup", lo := 0x8000403c, hi := 0x8000404c,
    directEntry := true },
  { query := "hSWhileRetCondTruthy", field := "hSWhileRet",
    variant := "condition-return-truthy-route", lo := 0x80004050, hi := 0x80004074 },
  { query := "hSWhileRetBodySetup", field := "hSWhileRet",
    variant := "body-call-setup", lo := 0x80004074, hi := 0x80004084 },
  { query := "hSWhileRetBodyReturn", field := "hSWhileRet",
    variant := "body-return-to-status-dispatch", lo := 0x80004088, hi := 0x80004034 },
  { query := "hSWhileRetRoute", field := "hSWhileRet",
    variant := "return-status-route", lo := 0x80004034, hi := 0x80004150 },
  { query := "hSWhileLoopCondSetup", field := "hSWhileLoop",
    variant := "condition-call-setup", lo := 0x8000403c, hi := 0x8000404c,
    directEntry := true },
  { query := "hSWhileLoopCondTruthy", field := "hSWhileLoop",
    variant := "condition-return-truthy-route", lo := 0x80004050, hi := 0x80004074 },
  { query := "hSWhileLoopBodySetup", field := "hSWhileLoop",
    variant := "body-call-setup", lo := 0x80004074, hi := 0x80004084 },
  { query := "hSWhileLoopBodyReturn", field := "hSWhileLoop",
    variant := "body-return-to-status-dispatch", lo := 0x80004088, hi := 0x80004034 },
  { query := "hSWhileLoopRoute", field := "hSWhileLoop",
    variant := "normal-or-continue-loop-back", lo := 0x80004034, hi := 0x8000403c } ]

def residualInstances : List ResidualInstance :=
  ordinaryInstances ++ blockInstances ++ callInstances ++ whileInstances

/-- Exact field inventory of `TermResidualsCore`.  Retired constructor rows
`hArgsNil` and `hSeqNil`/`hSeqCons*` are suppliers, not record fields. -/
def termCoreResidualFields : List String :=
  (((residualSpans.map fun t => t.1).filter (· != "hArgsNil")) ++
    ["hExecRouteCases", "hCall", "hCallClosure", "hCallPrint", "hCallPrintln",
     "hCallAssertOk", "hSWhileBreak", "hSWhileRet", "hSWhileLoop",
     "hInitNone", "hInitSome", "hFlCondFalse", "hFlBodyBreak", "hFlBodyRet",
     "hFlLoop", "hSeqSteps", "hEpilogueSpill", "hInitStore", "hDivCorr"]).eraseDups

/-- Indexed error projections are not fields of `TermResidualsCore`. -/
def indexedErrorProjectionFields : List String := ["hCallTooMany"]

/-- Aggregate error-family field added by `TermResiduals`. -/
def errorFamilyFields : List String := ["hErrFam"]

/-- Machine boundary checks retained after their former record fields retired. -/
def machineBoundaryProjectionFields : List String := ["hArgsNil"]

/-- Complete proof-obligation inventory used by the coverage manifest. -/
def residualFields : List String :=
  (termCoreResidualFields ++ indexedErrorProjectionFields ++ errorFamilyFields).eraseDups

/-- Term-field projections with a semantic postcondition. -/
def termProjectedFields : List String :=
  [ "hArgsCons", "hInt", "hStr", "hBool", "hNull", "hVar", "hAssign",
    "hNeg", "hNot", "hAndFalse",
    "hOrTrue", "hAndTrue", "hOrFalse", "hIAdd", "hISub", "hIMul",
    "hIDiv", "hIMod", "hILt", "hILe", "hIGt", "hIGe", "hDivOv",
    "hEq", "hNe", "hStrAddL", "hStrAddR", "hStrLt", "hStrLe",
    "hStrGt", "hStrGe", "hFn", "hCall", "hCallPrint", "hCallPrintln",
    "hCallAssertOk",
    "hSExpr", "hSBlock", "hSRet", "hSRetNull", "hSVarInit", "hSVarNull",
    "hSIfNone", "hSWhileFalse", "hSWhileBreak", "hSWhileRet", "hSWhileLoop",
    "hSBrk", "hSCont" ]

def projectedFields : List String :=
  (termProjectedFields ++ indexedErrorProjectionFields ++
    machineBoundaryProjectionFields).eraseDups

def queryCapability (inst : ResidualInstance) : String :=
  if indexedErrorProjectionFields.contains inst.field then "indexed-error-projection"
  else if machineBoundaryProjectionFields.contains inst.field then "machine-boundary"
  else if termProjectedFields.contains inst.field then "partial-projection"
  else "machine-only"

/-- Capability is an inventory classification, never evidence of closure. -/
def residualCapabilityClass (instances : List ResidualInstance) (field : String) : String :=
  if instances.any (fun inst => inst.field == field) then "finite-projection"
  else if field == "hDivCorr" then "non-finite"
  else if ["hExecRouteCases", "hFlCondFalse", "hFlBodyBreak", "hFlBodyRet",
      "hFlLoop", "hSeqSteps", "hErrFam"].contains field then "composite-family"
  else "lean-only"

/-- The proof ELF's complete set of direct `jal runtime_error` instructions.
This is machine coverage metadata, not an encoding of `ErrFamily`. -/
def errorPhysicalSites : List (Nat × String × String) := [
  (0x80002e90, "assert-arity", "constructible"),
  (0x80002ebc, "assert-falsy", "constructible"),
  (0x800034e4, "assignment-unbound", "constructible"),
  (0x80003950, "unknown-binary-operator", "parser-unconstructible"),
  (0x80003b54, "unknown-expression-kind", "parser-unconstructible"),
  (0x80003b9c, "minus-or-neg-non-int", "constructible"),
  (0x80003bc8, "modulo-by-zero", "constructible"),
  (0x80003c10, "modulo-non-int", "constructible"),
  (0x80003c7c, "multiply-non-int", "constructible"),
  (0x80003cc4, "call-depth", "constructible"),
  (0x80003ce8, "closure-break-or-continue", "constructible"),
  (0x80003d14, "division-by-zero", "constructible"),
  (0x80003d5c, "addition-non-int", "constructible"),
  (0x80003da0, "closure-arity", "constructible"),
  (0x80003de8, "not-callable", "constructible"),
  (0x80003e98, "comparison-non-int", "constructible"),
  (0x80003f58, "division-non-int", "constructible"),
  (0x80003fac, "undefined-variable", "constructible"),
  (0x80003fdc, "more-than-32-call-arguments", "constructible") ]

/-- The 44 premises of `errorSim_of_sites`: 43 executable semantic
constructors plus the spec-completeness-only dangling-closure constructor.
`TopAbrupt` is a separate 45th obligation in `BigStepErr`. -/
def errorIndexedPremises : List String := [
  "hVarUndef", "hAssignE", "hAssignUnbound", "hBinaryL", "hBinaryR",
  "hBinaryOp", "hOrL", "hOrR", "hAndL", "hAndR", "hUnaryE", "hNegType",
  "hCallF", "hCallTooMany", "hCallArgs", "hCallC", "hArgsHead", "hArgsTail", "hNotCallable",
  "hBadClosure", "hArity", "hDepth", "hBody", "hEscape", "hAssertFail",
  "hAssertArity", "hExpr", "hVarInit", "hBlock", "hIfCond", "hIfThen",
  "hIfElse", "hWhileCond", "hWhileBody", "hWhileLoop", "hForInit", "hForLoop",
  "hRet", "hFlCond", "hFlBody", "hFlStep", "hFlLoop", "hSeqHead", "hSeqTail" ]

/-- The theorem dimensions the executable campaign does not encode.  This is a
coverage manifest, not an assumption. -/
def residualHoles : List (String × String × String) :=
  (residualFields.map fun field =>
    (field, "full-lean-proposition",
      "quantified Triple, representation predicates, ghost state, and recursive hypotheses are not encoded")) ++
  [ ("hExecRouteCases", "no-finite-residual-instance",
      "the constructor-local dispatch family is assembled from multiple entry-indexed rows, not one finite machine span"),
    ("hInitNone", "no-finite-residual-instance",
      "the context-indexed none initializer is an exact identity supplier and has no residual query"),
    ("hInitSome", "recursive-stitching",
      "the context-indexed initializer consumes an ExecIH and has no finite standalone projection"),
    ("hFlCondFalse", "recursive-stitching",
      "the for-condition exit consumes indexed condition state and has no standalone finite projection"),
    ("hFlBodyBreak", "recursive-stitching",
      "the for-body break route consumes indexed condition and body boundaries"),
    ("hFlBodyRet", "recursive-stitching",
      "the for-body return route consumes indexed condition and body boundaries"),
    ("hFlLoop", "recursive-stitching",
      "the recursive for-loop route consumes condition, body, step, and recursive loop boundaries"),
    ("hSeqSteps", "recursive-stitching",
      "the copy-indexed sequence-step family replaces the retired nil/cons constructor fields"),
    ("hVar", "environment-lookup-relation",
      "the ground env_get projection names the first-match relation and checks all three returned Value words; the independent fuzzer executes the chain lookup, while SMT leaves the semantic function abstract and relies on the named Lean helper theorem rather than encoding the quantified Store.get? proof"),
    ("hVar", "result-value-index",
      "the trace model observes the three temporary result words at the shared-tail boundary but does not decode the indexed Lean Value v or cover the final copy into the caller's sret buffer"),
    ("hAssign", "recursive-eval-ih",
      "the indexed residual names the RHS EvalE derivation and result v; the SMT query has an uninterpreted eval_expr call but no typed EvalIH boundary naming v"),
    ("hAssign", "store-update-relation",
      "the ground env_set projection names the successful first-match relation and checks the three-word update; the independent fuzzer executes it, while SMT leaves the semantic function abstract and does not reconstruct the ghost Store or prove Store.set? = some store''"),
    ("hAssign", "result-value-tail",
      "the projection stops when the successful env_set branch reaches 0x80003448; the final three-word copy into the caller's sret buffer is a separate proved Lean tail and is not in this SMT instance"),
    ("hArgsCons", "recursive-eval-args-ih",
      "the projection treats the child eval_expr return as 24 opaque bytes and does not name either the head EvalIH or the tail mEvalArgs hypothesis consumed by the indexed residual"),
    ("hArgsCons", "argument-vector-index",
      "the query checks the concrete args[i] child call, its 24-byte copy into slot i, and final i = argc, but does not decode ExprArrayRepr es or ArgVecRepr (v :: vs) and therefore proves no semantic list postcondition"),
    ("hArgsCons", "later-iterations",
      "the post follows the first child return visible in the finite span and checks that slot through loop exit; later child returns and slots remain behind the loop summary and are not individually projected"),
    ("hDivCorr", "global-liveness",
      "DivCorrFamily quantifies over every Loaded configuration and an existential correspondence"),
    ("hErrFam", "composite-error-family",
      "ErrFamily combines 44 indexed constructor premises and a separate TopAbrupt obligation; it is not one finite projection"),
    ("hErrFam", "physical-site-coverage",
      "the proof ELF has 19 direct runtime_error call PCs: 17 are source-constructible, while unknown BinOp and unknown Expr fallbacks cannot be produced by the parser"),
    ("hErrFam", "constructor-premise-coverage",
      "focused traces witness 43 of 44 indexed premises; hBadClosure is spec-only because C closure pointers are valid by construction; TopAbrupt is tested separately without a jal"),
    ("hErrFam", "nonfunctional-premise-routing",
      "a propagation constructor has no unique error PC: its child may terminate at any compatible leaf site, so a fixed premise-to-PC table is not a faithful encoding"),
    ("hCall", "recursive-semantic-stitching",
      "the five finite projections expose all four CallArmStages boundaries, but do not identify the recursive EvalIH, mEvalArgs, and mCall runs with the indexed SpecSt transitions"),
    ("hCall", "value-shadow-abstraction",
      "the QF Value shadow checks the concrete ValueRepr tag/payload fields and all 24 readable bytes; string and closure pointers remain opaque identity tokens rather than CString/ClosureRepr ghost-map values"),
    ("hCall", "store-output-ghost-index",
      "the zero-step args-to-call and call-to-epilogue cuts transport the exact memory and output arrays, but do not reconstruct PhiExtends, StoreRepr, OutRepr, or the four semantic shadow states"),
    ("hCall", "final-eval-epilogue",
      "CallArmStages ends at the shared epilogue handoff; the final EvalExit proof remains the separate callArmEpilogueRun composition"),
    ("hCallTooMany", "callee-semantic-boundary",
      "the finite query begins at the callee return PC; the preceding EvalIH that identifies the returned machine state with EvalE st d env f st' fv remains a Lean bridge"),
    ("hCallTooMany", "signed-count-representation",
      "the machine uses lw followed by signed blt, so ExprArrayRepr/AST-region geometry must prove args.length fits nonnegative signed i32; the SMT projection carries that fact explicitly"),
    ("hCallTooMany", "error-tail-composition",
      "the projection stops at the exact jal runtime_error entry; ReachJal-to-ErrHalts and the shared runtime_error/longjmp/exit tail remain the Lean error-family composition"),
    ("hCallClosure", "no-faithful-machine-instance",
      "the former 0x800031b0 to 0x80003360 query was not the Lean 0x80003254 to 0x800033ec closure splice"),
    ("hCallClosure", "closure-store-and-body-index",
      "the SMT model has no decoder for closure table lookup, params.zip argument binding, allocFrame, or the indexed body mExecSeq result/status relation"),
    ("hCallPrint", "native-output-loop-proof",
      "the SMT query carries the exact printed-suffix/control-state relation and proves the caller projection; Lean derives NativePrintInternal by finite induction from reflected common/setup/body/separator/restore/return regions, grounded fputc/value_print leaves, and the named/anonymous closure arms; only individual branch/jal/ret and representation-marshalling seams plus the grounded newlib implementations remain machine premises"),
    ("hCallPrintln", "native-output-loop-proof",
      "the SMT query proves printArgs followed by one newline; Lean derives NativePrintlnInternal from its reflected prologue, component-derived native_print run, grounded newline fputc, proved value_null, and reflected return; only individual jal/ret and representation-marshalling seams plus the grounded newlib implementations remain machine premises"),
    ("hCallAssertOk", "native-body-boundary",
      "the finite projection begins at native_assert entry; the preceding native-target dispatch and the return-to-call epilogue remain typed Lean stages"),
    ("hCallAssertOk", "native-contract-index",
      "the native-body projection pins argc in {1,2}, a valid first Value shadow, and its concrete truthiness, but does not reconstruct vs = [v] or [v,m] or the preceding indirect-target relation"),
    ("hSExpr", "status-only-projection",
      "checks a0 = normal, not the child EvalIH or resulting StoreRepr/OutRepr"),
    ("hSRet", "status-only-projection",
      "checks a0 = return, not the returned ValueRepr or resulting StoreRepr/OutRepr"),
    ("hSRetNull", "status-only-projection",
      "checks a0 = return, not the null result representation or resulting StoreRepr/OutRepr"),
    ("hSVarInit", "status-only-projection",
      "checks a0 = normal, not the initializer EvalIH, env_define effect, or resulting StoreRepr"),
    ("hSVarNull", "status-only-projection",
      "checks a0 = normal, not the null binding, env_define effect, or resulting StoreRepr"),
    ("hSIfNone", "status-and-route-only-projection",
      "checks the false/no-else route and a0 = normal, not the condition EvalIH or resulting StoreRepr/OutRepr"),
    ("hSWhileFalse", "status-and-route-only-projection",
      "checks the false loop exit and a0 = normal, not the condition EvalIH or resulting StoreRepr/OutRepr"),
    ("hSIfTrue", "recursive-status-and-state",
      "the result status and SpecSt are those of the then-branch ExecIH; the SMT loop summary does not expose that typed child exit, so no fixed a0 post is sound"),
    ("hSIfFalse", "recursive-status-and-state",
      "the result status and SpecSt are those of the else-branch ExecIH; has-else is representable, but the false condition and typed child exit are not a semantic post oracle"),
    ("hSBlock", "sequence-status-and-state",
      "the finite projections expose one exact recursive exec_stmt call and its immediate normal/abrupt machine routes, but no SMT relation identifies the child with an indexed mExecSeq status or SpecSt"),
    ("hSBlock", "allocated-frame-index",
      "the env_new seam checks the exact empty 32-byte Env layout and parent link under the named env_new helper contract, but no SMT relation connects those bytes to Store.allocFrame (some env) = (store', inner) or its ghost frame map"),
    ("hSBlock", "later-sequence-iterations",
      "hSBlockIter stops at its first child return; later recursive children are not individually related to ExecSeq constructors"),
    ("hSForStart", "init-and-forloop-boundaries",
      "the result is indexed by separate mExecInit and mForLoop boundaries with arbitrary status; the finite query cannot name either semantic child state"),
    ("hSForStart", "allocated-frame-index",
      "env_new and the subsequent loop are machine-visible, but the SMT model has no Store.allocFrame/outer relation or typed ForLoop result oracle"),
    ("hSWhileBreak", "recursive-stitching",
      "four finite projections validate condition-call setup, the truthy return route, body-call setup, and break-to-normal dispatch; they do not identify the EvalIH or body ExecIH with indexed SpecSt values"),
    ("hSWhileRet", "recursive-stitching",
      "five finite projections validate condition-call setup, the truthy return route, body-call setup, the body-return status edge, and return-status dispatch; they do not identify the EvalIH, body ExecIH, returned Lean Value, or exit widener"),
    ("hSWhileLoop", "recursive-stitching",
      "five finite projections validate condition-call setup, the truthy return route, body-call setup, the body-return status edge, and normal-or-continue back-edge; the recursive while IH and its final status/state remain outside SMT"),
    ("hEpilogueSpill", "no-faithful-machine-instance",
      "the former query covered the eval epilogue, not the interpreter exit restore chain"),
    ("hInitStore", "no-faithful-machine-instance",
      "the interpreter prologue does not establish the Lean initial-store representation premise"),
    ("hEq", "value-equal-contract",
      "the independent oracle checks staged Values and every observed value_equal call against Lean Value.equal, but the SMT formula still treats the call summary opaquely"),
    ("hNe", "value-equal-contract",
      "the independent oracle checks staged Values and every observed value_equal call against Lean Value.equal, but the SMT formula still treats the call summary opaquely"),
    ("hStrAddL", "string-concatenation-contract",
      "the independent oracle checks every concrete result CString against Lean catDisplay concatenation, but the SMT formula itself still checks only boxing of the completed pointer"),
    ("hStrAddR", "string-concatenation-contract",
      "the independent oracle checks every concrete result CString against Lean catDisplay concatenation, but the SMT formula itself still checks only boxing of the completed pointer"),
    ("hStrLt", "strcmp-contract", "the independent oracle checks staged strings and every observed strcmp call against Lean lexicographic order, but the SMT formula still treats the call summary opaquely"),
    ("hStrLe", "strcmp-contract", "the independent oracle checks staged strings and every observed strcmp call against Lean lexicographic order, but the SMT formula still treats the call summary opaquely"),
    ("hStrGt", "strcmp-contract", "the independent oracle checks staged strings and every observed strcmp call against Lean lexicographic order, but the SMT formula still treats the call summary opaquely"),
    ("hStrGe", "strcmp-contract", "the independent oracle checks staged strings and every observed strcmp call against Lean lexicographic order, but the SMT formula still treats the call summary opaquely"),
    ("hFn", "closure-allocation-contract",
      "the SMT post checks the MallocContract success geometry, exact 16-byte closure header, and boxing; Lean's storeRepr_pushClosure/allocClosureContract_of bridge these bytes to Store.allocClosure and ClosureRepr, while only the arm-front staging and post-malloc reload/transport seams remain local machine premises because ghost maps cannot be reconstructed from byte traces") ]

/-- A residual-specific premise.  `point = none` means function entry; a PC
means the unique merged state at that reflected block entry. -/
structure ResidualExtension where
  field : String
  name : String
  point : Option Nat
  predicate : String → String
  /-- Restrict this extension to one machine instance of a residual. -/
  query : Option String := none

private def addrAt (s : String) (reg off : Nat) : String :=
  s!"(bvadd (select (rr {s}) {bvN reg}) {bvN off})"

private def ld4Eq (reg off value : Nat) (s : String) : String :=
  s!"(= (ld4 (mm {s}) {addrAt s reg off}) {bvN value})"

private def ld8Eq (reg off value : Nat) (s : String) : String :=
  s!"(= (ld8 (mm {s}) {addrAt s reg off}) {bvN value})"

private def ld8Ne (reg off value : Nat) (s : String) : String :=
  s!"(not {ld8Eq reg off value s})"

private def regEq (reg value : Nat) (s : String) : String :=
  s!"(= (select (rr {s}) {bvN reg}) {bvN value})"

private def bindingName (b : String) : String :=
  let inner := (b.drop 1).dropRight 1
  (inner.takeWhile (· != ' ')).toString

private def valueTruthy (off : Nat) (s : String) : String :=
  let k := s!"(ld4 (mm {s}) {addrAt s 2 off})"
  let b := s!"(ld4 (mm {s}) {addrAt s 2 (off + 8)})"
  let i := s!"(ld8 (mm {s}) {addrAt s 2 (off + 8)})"
  s!"(or (and (= {k} {bvN 1}) (not (= {b} {bvN 0}))) (and (= {k} {bvN 2}) (not (= {i} {bvN 0}))) (= {k} {bvN 3}) (= {k} {bvN 4}) (= {k} {bvN 5}))"

private def valueTruthyAt (addr : String → String) (s : String) : String :=
  let a := addr s
  let k := s!"(ld4 (mm {s}) {a})"
  let b := s!"(ld4 (mm {s}) (bvadd {a} {bvN 8}))"
  let i := s!"(ld8 (mm {s}) (bvadd {a} {bvN 8}))"
  s!"(or (and (= {k} {bvN 1}) (not (= {b} {bvN 0}))) (and (= {k} {bvN 2}) (not (= {i} {bvN 0}))) (= {k} {bvN 3}) (= {k} {bvN 4}) (= {k} {bvN 5}))"

/-- The `ValueRepr` fact needed by `value_truthy`: a Boolean payload is the
canonical machine word 0 or 1.  Other Value constructors are unrestricted by
this projection. -/
private def valueBoolCanonical (off : Nat) (s : String) : String :=
  let k := s!"(ld4 (mm {s}) {addrAt s 2 off})"
  let b := s!"(ld4 (mm {s}) {addrAt s 2 (off + 8)})"
  s!"(=> (= {k} {bvN 1}) (or (= {b} {bvN 0}) (= {b} {bvN 1})))"

private def valueFalsy (off : Nat) (s : String) : String :=
  let k := s!"(ld4 (mm {s}) {addrAt s 2 off})"
  let b := s!"(ld4 (mm {s}) {addrAt s 2 (off + 8)})"
  let i := s!"(ld8 (mm {s}) {addrAt s 2 (off + 8)})"
  s!"(or (= {k} {bvN 0}) (and (= {k} {bvN 1}) (= {b} {bvN 0})) (and (= {k} {bvN 2}) (= {i} {bvN 0})))"

private def valueKindValid (off : Nat) (s : String) : String :=
  s!"(bvule (ld4 (mm {s}) {addrAt s 2 off}) {bvN 5})"

private def binaryToken (field : String) (token : Nat) : ResidualExtension :=
  { field := field, name := "binop-token", point := none,
    predicate := ld4Eq 12 8 token }

private def binaryKind (field name : String) (off kind : Nat) : ResidualExtension :=
  { field := field, name := name, point := some 0x8000351c,
    predicate := ld4Eq 2 off kind }

private def leafExprFrame (field : String) : ResidualExtension :=
  { field := field, name := "expr-vs-eval-frame", point := none,
    predicate := fun s =>
      let expr := s!"(select (rr {s}) {bvN 12})"
      let sp := s!"(select (rr {s}) {bvN 2})"
      -- `EvalEntry.expr_stack_disjoint`, specialized to the 1088-byte frame
      -- this function is about.  This prevents the prologue spill chain from
      -- overwriting the leaf payload before the arm loads it.
      s!"(or (bvule (bvadd {expr} {bvN 16}) (bvsub {sp} {bvN 1088})) (bvule {sp} {expr}))" }

private def exprKindAt (field name : String) (point kind : Nat) : ResidualExtension :=
  { field := field, name := name, point := some point, predicate := ld4Eq 12 0 kind }

private def savedExprKindAt (field name : String) (point kind : Nat) : ResidualExtension :=
  { field := field, name := name, point := some point, predicate := ld4Eq 8 0 kind }

private def checkpointAt (field name : String) (point : Nat) : ResidualExtension :=
  { field := field, name := name, point := some point, predicate := fun _ => "true" }

private def checkpointAtQuery (query field name : String) (point : Nat) : ResidualExtension :=
  { query := some query, field := field, name := name, point := some point,
    predicate := fun _ => "true" }

/-- One register fact supplied by the proved `execBlockA` arm-entry bridge.
The source register is at `eval_expr` entry (`s0`); the destination is at the
selected call-arm checkpoint. -/
private def callArmBridge (name : String) (dst src : Nat) : ResidualExtension :=
  { query := some "hCallCallee", field := "hCall", name := name,
    point := some 0x800031b0,
    predicate := fun s =>
      s!"(= (select (rr {s}) {bvN dst}) (select (rr s0) {bvN src}))" }

/-- Concrete, quantifier-free portion of `ValueRepr`.  The three complete
machine words are the value shadow.  Null/int need no payload restriction;
booleans are canonical; string and closure pointers are non-null opaque IDs;
native values retain non-null name and function-pointer IDs.  CString contents,
closure maps, and native-address maps remain explicit semantic holes. -/
private def valueShadowValid (mem addr : String) : String :=
  let kind := s!"(ld4 {mem} {addr})"
  let payload := s!"(ld8 {mem} (bvadd {addr} {bvN 8}))"
  let boolPayload := s!"(ld4 {mem} (bvadd {addr} {bvN 8}))"
  let aux := s!"(ld8 {mem} (bvadd {addr} {bvN 16}))"
  s!"(or (= {kind} {bvN 0}) (and (= {kind} {bvN 1}) (bvule {boolPayload} {bvN 1})) (= {kind} {bvN 2}) (and (= {kind} {bvN 3}) (not (= {payload} {bvN 0}))) (and (= {kind} {bvN 4}) (not (= {payload} {bvN 0}))) (and (= {kind} {bvN 5}) (not (= {payload} {bvN 0})) (not (= {aux} {bvN 0}))))"

private def valueShadowAt (query name : String) (point : Option Nat)
    (addr : String → String) : ResidualExtension :=
  { query := some query, field := "hCall", name := name, point := point,
    predicate := fun s => valueShadowValid s!"(mm {s})" (addr s) }

/-- Finite first-order shadow of `ArgVecRepr`; C rejects more than 32 call
arguments.  Every active 24-byte slot must have the concrete part of a
`ValueRepr`. -/
private def argVecShadowValid (s : String) : String :=
  let count := s!"(select (rr {s}) {bvN 15})"
  let sp := s!"(select (rr {s}) {bvN 2})"
  let mem := s!"(mm {s})"
  let slots := (List.range 32).map fun i =>
    let idx := bvN i
    let addr := s!"(bvadd (bvadd {sp} {bvN 240}) (bvmul {idx} {bvN 24}))"
    s!"(=> (bvult {idx} {count}) {valueShadowValid mem addr})"
  s!"(and {String.intercalate " " slots})"

/-- Premises which distinguish residuals sharing a machine arm.  Entry facts
come directly from `ExprRepr`/`StmtRepr`.  The 0x8000351c facts are the two
`ValueRepr`s supplied by the recursive hypotheses at `TwoSubReturn`: left at
`sp+120`, right at `sp+144`, payloads at `+128` and `+152`. -/
def residualExtensions : List ResidualExtension :=
  [ leafExprFrame "hInt", leafExprFrame "hStr", leafExprFrame "hBool",
    leafExprFrame "hNull",
    callArmBridge "execBlockA-x8-expr" 8 12,
    callArmBridge "execBlockA-x9-sret" 9 10,
    callArmBridge "execBlockA-x18-interp" 18 11,
    callArmBridge "execBlockA-x19-env" 19 13,
    { query := some "hCallCallee", field := "hCall",
      name := "callee-stack-window", point := some 0x800031b0,
      predicate := fun s =>
        s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 2}))" },
    checkpointAtQuery "hCallCallee" "hCall" "pre-callee-eval" 0x800031bc,
    { query := some "hCallTooMany", field := "hCallTooMany",
      name := "call-node-kind", point := none, predicate := ld4Eq 8 0 9 },
    { query := some "hCallTooMany", field := "hCallTooMany",
      name := "argc-over-max", point := none,
      predicate := fun s =>
        s!"(bvult {bvN 32} (ld4 (mm {s}) {addrAt s 8 24}))" },
    { query := some "hCallTooMany", field := "hCallTooMany",
      name := "argc-signed-nonnegative", point := none,
      predicate := fun s =>
        s!"(bvult (ld4 (mm {s}) {addrAt s 8 24}) {bvN 0x80000000})" },
    { query := some "hCallTooMany", field := "hCallTooMany",
      name := "callee-return-stack-window", point := none,
      predicate := fun s =>
        s!"(bvule {bvN 0x8001ad10} (bvadd (select (rr {s}) {bvN 2}) {bvN 1016}))" },
    { query := some "hCallTooMany", field := "hCallTooMany",
      name := "callee-value-shadow", point := none,
      predicate := fun s => valueShadowValid s!"(mm {s})" (addrAt s 2 96) },
    { query := some "hCallCalleeToArgsNil", field := "hCall",
      name := "empty-argc", point := none, predicate := ld4Eq 8 24 0 },
    { query := some "hCallCalleeToArgsNil", field := "hCall",
      name := "callee-return-stack-window", point := none,
      predicate := fun s =>
        s!"(bvule {bvN 0x8001ad10} (bvadd (select (rr {s}) {bvN 2}) {bvN 1016}))" },
    valueShadowAt "hCallCalleeToArgsNil" "callee-value-shadow" none
      (fun s => addrAt s 2 96),
    { query := some "hCallCalleeToArgsCons", field := "hCall",
      name := "nonempty-argc", point := none,
      predicate := fun s =>
        s!"(bvult {bvN 0} (ld4 (mm {s}) {addrAt s 8 24}))" },
    { query := some "hCallCalleeToArgsCons", field := "hCall",
      name := "argc-bound", point := none,
      predicate := fun s =>
        s!"(bvule (ld4 (mm {s}) {addrAt s 8 24}) {bvN 32})" },
    { query := some "hCallCalleeToArgsCons", field := "hCall",
      name := "callee-return-stack-window", point := none,
      predicate := fun s =>
        s!"(bvule {bvN 0x8001ad10} (bvadd (select (rr {s}) {bvN 2}) {bvN 1016}))" },
    valueShadowAt "hCallCalleeToArgsCons" "callee-value-shadow" none
      (fun s => addrAt s 2 96),
    { query := some "hCallArgsToCall", field := "hCall",
      name := "argc-bound", point := none,
      predicate := fun s =>
        s!"(bvule (select (rr {s}) {bvN 15}) {bvN 32})" },
    valueShadowAt "hCallArgsToCall" "callee-value-shadow" none
      (fun s => addrAt s 2 96),
    { query := some "hCallArgsToCall", field := "hCall",
      name := "arg-vector-shadow", point := none,
      predicate := argVecShadowValid },
    valueShadowAt "hCallCallToEpilogue" "result-value-shadow" none
      (fun s => s!"(select (rr {s}) {bvN 9})"),
    checkpointAt "hVar" "post-env-get" 0x80003444,
    checkpointAt "hAssign" "post-rhs-eval" 0x8000348c,
    checkpointAt "hAssign" "pre-env-set" 0x800034b0,
    checkpointAt "hAssign" "post-env-set" 0x800034b4,
    { field := "hArgsNil", name := "empty-argc", point := none,
      predicate := regEq 15 0 },
    { field := "hArgsNil", name := "empty-index", point := none,
      predicate := regEq 16 0 },
    { field := "hCallPrint", name := "argc-bound", point := none,
      predicate := fun s => s!"(bvule (select (rr {s}) {bvN 12}) {bvN 32})" },
    { field := "hCallPrintln", name := "argc-bound", point := none,
      predicate := fun s => s!"(bvule (select (rr {s}) {bvN 12}) {bvN 32})" },
    { field := "hCallPrint", name := "sret-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 10}))" },
    { field := "hCallPrintln", name := "sret-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 10}))" },
    { field := "hCallPrint", name := "sret-no-wrap", point := none,
      predicate := fun s => s!"(bvule (select (rr {s}) {bvN 10}) (bvadd (select (rr {s}) {bvN 10}) {bvN 24}))" },
    { field := "hCallPrintln", name := "sret-no-wrap", point := none,
      predicate := fun s => s!"(bvule (select (rr {s}) {bvN 10}) (bvadd (select (rr {s}) {bvN 10}) {bvN 24}))" },
    { field := "hCallPrint", name := "sret-below-4g", point := none,
      predicate := fun s => s!"(bvule (bvadd (select (rr {s}) {bvN 10}) {bvN 24}) {bvN 0x100000000})" },
    { field := "hCallPrintln", name := "sret-below-4g", point := none,
      predicate := fun s => s!"(bvule (bvadd (select (rr {s}) {bvN 10}) {bvN 24}) {bvN 0x100000000})" },
    { field := "hCallPrint", name := "stack-frame-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (bvsub (select (rr {s}) {bvN 2}) {bvN 48}))" },
    { field := "hCallPrintln", name := "stack-frame-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (bvsub (select (rr {s}) {bvN 2}) {bvN 16}))" },
    { field := "hCallAssertOk", name := "assert-argc-one-or-two", point := none,
      predicate := fun s =>
        s!"(or (= (select (rr {s}) {bvN 12}) {bvN 1}) (= (select (rr {s}) {bvN 12}) {bvN 2}))" },
    { field := "hCallAssertOk", name := "assert-first-value", point := none,
      predicate := fun s => valueShadowValid s!"(mm {s})" s!"(select (rr {s}) {bvN 13})" },
    { field := "hCallAssertOk", name := "assert-first-truthy", point := none,
      predicate := valueTruthyAt (fun s => s!"(select (rr {s}) {bvN 13})") },
    { field := "hCallAssertOk", name := "sret-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 10}))" },
    { field := "hCallAssertOk", name := "sret-no-wrap", point := none,
      predicate := fun s => s!"(bvule (select (rr {s}) {bvN 10}) (bvadd (select (rr {s}) {bvN 10}) {bvN 24}))" },
    { field := "hCallAssertOk", name := "sret-below-4g", point := none,
      predicate := fun s => s!"(bvule (bvadd (select (rr {s}) {bvN 10}) {bvN 24}) {bvN 0x100000000})" },
    { field := "hCallAssertOk", name := "stack-frame-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN (0x8001ad10 + 80)} (select (rr {s}) {bvN 2}))" },
    exprKindAt "hInt" "leaf-arm-kind" 0x80003408 0,
    exprKindAt "hStr" "leaf-arm-kind" 0x80003414 1,
    exprKindAt "hBool" "leaf-arm-kind" 0x80003420 2,
    exprKindAt "hNull" "leaf-arm-kind" 0x8000342c 3,
    binaryToken "hIAdd" 11, binaryKind "hIAdd" "left-int" 120 2,
    binaryKind "hIAdd" "right-int" 144 2,
    binaryToken "hISub" 12, binaryKind "hISub" "left-int" 120 2,
    binaryKind "hISub" "right-int" 144 2,
    binaryToken "hIMul" 13, binaryKind "hIMul" "left-int" 120 2,
    binaryKind "hIMul" "right-int" 144 2,
    binaryToken "hIDiv" 14, binaryKind "hIDiv" "left-int" 120 2,
    binaryKind "hIDiv" "right-int" 144 2,
    { field := "hIDiv", name := "nonzero-divisor", point := some 0x8000351c,
      predicate := ld8Ne 2 152 0 },
    { field := "hIDiv", name := "nonoverflow", point := some 0x8000351c,
      predicate := fun s => s!"(not (and {ld8Eq 2 128 0x8000000000000000 s} {ld8Eq 2 152 0xffffffffffffffff s}))" },
    binaryToken "hIMod" 15, binaryKind "hIMod" "left-int" 120 2,
    binaryKind "hIMod" "right-int" 144 2,
    { field := "hIMod", name := "nonzero-divisor", point := some 0x8000351c,
      predicate := ld8Ne 2 152 0 },
    binaryToken "hILt" 20, binaryKind "hILt" "left-int" 120 2,
    binaryKind "hILt" "right-int" 144 2,
    binaryToken "hILe" 21, binaryKind "hILe" "left-int" 120 2,
    binaryKind "hILe" "right-int" 144 2,
    binaryToken "hIGt" 22, binaryKind "hIGt" "left-int" 120 2,
    binaryKind "hIGt" "right-int" 144 2,
    binaryToken "hIGe" 23, binaryKind "hIGe" "left-int" 120 2,
    binaryKind "hIGe" "right-int" 144 2,
    binaryToken "hEq" 19, binaryToken "hNe" 17,
    checkpointAt "hEq" "post-value-equal" 0x80003720,
    checkpointAt "hNe" "post-value-equal" 0x80003770,
    binaryToken "hStrAddL" 11, binaryKind "hStrAddL" "left-str" 120 3,
    { field := "hStrAddL", name := "concat-left-str", point := some 0x80003ac8,
      predicate := ld4Eq 2 120 3 },
    binaryToken "hStrAddR" 11, binaryKind "hStrAddR" "right-str" 144 3,
    { field := "hStrAddR", name := "left-not-str", point := some 0x8000351c,
      predicate := fun s => s!"(not {ld4Eq 2 120 3 s})" },
    { field := "hStrAddR", name := "concat-right-str", point := some 0x80003ac8,
      predicate := ld4Eq 2 144 3 },
    { field := "hStrAddR", name := "concat-left-not-str", point := some 0x80003ac8,
      predicate := fun s => s!"(not {ld4Eq 2 120 3 s})" },
    binaryToken "hStrLt" 20, binaryKind "hStrLt" "left-str" 120 3,
    binaryKind "hStrLt" "right-str" 144 3,
    { field := "hStrLt", name := "post-strcmp-token", point := some 0x800036c0,
      predicate := regEq 12 20 },
    checkpointAt "hStrLt" "post-strcmp" 0x80003b1c,
    binaryToken "hStrLe" 21, binaryKind "hStrLe" "left-str" 120 3,
    binaryKind "hStrLe" "right-str" 144 3,
    { field := "hStrLe", name := "post-strcmp-token", point := some 0x80003af8,
      predicate := regEq 12 21 },
    checkpointAt "hStrLe" "post-strcmp" 0x80003b1c,
    binaryToken "hStrGt" 22, binaryKind "hStrGt" "left-str" 120 3,
    binaryKind "hStrGt" "right-str" 144 3,
    { field := "hStrGt", name := "post-strcmp-token", point := some 0x80003ae4,
      predicate := regEq 12 22 },
    checkpointAt "hStrGt" "post-strcmp" 0x80003b1c,
    binaryToken "hStrGe" 23, binaryKind "hStrGe" "left-str" 120 3,
    binaryKind "hStrGe" "right-str" 144 3,
    { field := "hStrGe", name := "post-strcmp-token", point := some 0x800036bc,
      predicate := regEq 12 23 },
    checkpointAt "hStrGe" "post-strcmp" 0x80003b1c,
    binaryToken "hDivOv" 14, binaryKind "hDivOv" "left-int" 120 2,
    binaryKind "hDivOv" "right-int" 144 2,
    { field := "hDivOv", name := "min-dividend", point := some 0x8000351c,
      predicate := ld8Eq 2 128 0x8000000000000000 },
    { field := "hDivOv", name := "minus-one-divisor", point := some 0x8000351c,
      predicate := ld8Eq 2 152 0xffffffffffffffff },
    { field := "hNeg", name := "unop-token", point := none, predicate := ld4Eq 12 8 12 },
    { field := "hNeg", name := "operand-int", point := some 0x800035ec,
      predicate := ld4Eq 2 144 2 },
    { field := "hNot", name := "unop-token", point := none, predicate := ld4Eq 12 8 16 },
    { field := "hNot", name := "operand-value", point := some 0x800035ec,
      predicate := valueKindValid 144 },
    { field := "hAndTrue", name := "logop-token", point := none, predicate := ld4Eq 12 8 24 },
    { field := "hAndTrue", name := "left-truthy", point := some 0x8000356c,
      predicate := valueTruthy 120 },
    { field := "hAndTrue", name := "right-value", point := some 0x800035b0,
      predicate := valueKindValid 240 },
    { field := "hAndFalse", name := "logop-token", point := none, predicate := ld4Eq 12 8 24 },
    { field := "hAndFalse", name := "left-falsy", point := some 0x8000356c,
      predicate := valueFalsy 120 },
    { field := "hOrTrue", name := "logop-token", point := none, predicate := ld4Eq 12 8 25 },
    { field := "hOrTrue", name := "left-truthy", point := some 0x8000356c,
      predicate := valueTruthy 120 },
    { field := "hOrFalse", name := "logop-token", point := none, predicate := ld4Eq 12 8 25 },
    { field := "hOrFalse", name := "left-falsy", point := some 0x8000356c,
      predicate := valueFalsy 120 },
    { field := "hOrFalse", name := "right-value", point := some 0x80003a10,
      predicate := valueKindValid 144 },
    savedExprKindAt "hFn" "fn-kind" 0x800033d0 10,
    { field := "hFn", name := "malloc-success", point := some 0x800033d0,
      predicate := fun s => s!"(not (= (select (rr {s}) {bvN 10}) {bvN 0}))" },
    { field := "hArgsCons", name := "index-nonnegative", point := none,
      predicate := fun s => s!"(bvsle {bvN 0} (select (rr {s}) {bvN 16}))" },
    { field := "hArgsCons", name := "index-below-argc", point := none,
      predicate := fun s => s!"(bvslt (select (rr {s}) {bvN 16}) (select (rr {s}) {bvN 15}))" },
    { field := "hArgsCons", name := "argc-bound", point := none,
      predicate := fun s => s!"(bvsle (select (rr {s}) {bvN 15}) {bvN 32})" },
    checkpointAt "hArgsCons" "pre-child-eval" 0x80003220,
    checkpointAt "hArgsCons" "post-child-eval" 0x80003224,
    -- Named ground dependency on the proved `execBlockA` entry bridge.  The
    -- generic dispatcher loop summary has no sound global register invariant;
    -- these four facts apply only to its block-arm exit.
    { query := some "hSBlock", field := "hSBlock", name := "execBlockA-x8-stmt",
      point := some 0x8000418c,
      predicate := fun s => s!"(= (select (rr {s}) {bvN 8}) (select (rr s0) {bvN 11}))" },
    { query := some "hSBlock", field := "hSBlock", name := "execBlockA-x9-interp",
      point := some 0x8000418c,
      predicate := fun s => s!"(= (select (rr {s}) {bvN 9}) (select (rr s0) {bvN 10}))" },
    { query := some "hSBlock", field := "hSBlock", name := "execBlockA-x19-env",
      point := some 0x8000418c,
      predicate := fun s => s!"(= (select (rr {s}) {bvN 19}) (select (rr s0) {bvN 12}))" },
    { query := some "hSBlock", field := "hSBlock", name := "execBlockA-x18-ret",
      point := some 0x8000418c,
      predicate := fun s => s!"(= (select (rr {s}) {bvN 18}) (select (rr s0) {bvN 13}))" },
    checkpointAtQuery "hSBlock" "hSBlock" "pre-env-new" 0x80004190,
    checkpointAtQuery "hSBlock" "hSBlock" "post-env-new" 0x80004194,
    checkpointAtQuery "hSBlock" "hSBlock" "post-env-new-setup" 0x800041a0,
    { query := some "hSBlockIter", field := "hSBlock", name := "index-nonnegative",
      point := none,
      predicate := fun s => s!"(bvsle {bvN 0} (select (rr {s}) {bvN 16}))" },
    { query := some "hSBlockIter", field := "hSBlock", name := "index-below-count",
      point := none,
      predicate := fun s =>
        s!"(bvslt (select (rr {s}) {bvN 16}) (ld4s (mm {s}) {addrAt s 8 16}))" },
    checkpointAtQuery "hSBlockIter" "hSBlock" "pre-child-exec" 0x800041c4,
    checkpointAtQuery "hSBlockIter" "hSBlock" "post-child-exec" 0x800041c8,
    { query := some "hSBlockNormal", field := "hSBlock", name := "normal-child-status",
      point := none,
      predicate := fun s => s!"(= (select (rr {s}) {bvN 10}) {bvN 0})" },
    { query := some "hSBlockAbrupt", field := "hSBlock", name := "abrupt-child-status",
      point := none,
      predicate := fun s => s!"(not (= (select (rr {s}) {bvN 10}) {bvN 0}))" },
    { query := some "hSWhileBreakCondTruthy", field := "hSWhileBreak",
      name := "condition-truthy", point := none, predicate := valueTruthy 80 },
    { query := some "hSWhileBreakCondTruthy", field := "hSWhileBreak",
      name := "condition-bool-canonical", point := none,
      predicate := valueBoolCanonical 80 },
    { query := some "hSWhileBreakCondTruthy", field := "hSWhileBreak",
      name := "stack-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 2}))" },
    { query := some "hSWhileBreakRoute", field := "hSWhileBreak",
      name := "body-break-status", point := none, predicate := regEq 10 1 },
    { query := some "hSWhileRetCondTruthy", field := "hSWhileRet",
      name := "condition-truthy", point := none, predicate := valueTruthy 80 },
    { query := some "hSWhileRetCondTruthy", field := "hSWhileRet",
      name := "condition-bool-canonical", point := none,
      predicate := valueBoolCanonical 80 },
    { query := some "hSWhileRetCondTruthy", field := "hSWhileRet",
      name := "stack-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 2}))" },
    { query := some "hSWhileRetBodyReturn", field := "hSWhileRet",
      name := "body-return-status", point := none, predicate := regEq 10 3 },
    { query := some "hSWhileRetRoute", field := "hSWhileRet",
      name := "body-return-status", point := none, predicate := regEq 10 3 },
    { query := some "hSWhileLoopCondTruthy", field := "hSWhileLoop",
      name := "condition-truthy", point := none, predicate := valueTruthy 80 },
    { query := some "hSWhileLoopCondTruthy", field := "hSWhileLoop",
      name := "condition-bool-canonical", point := none,
      predicate := valueBoolCanonical 80 },
    { query := some "hSWhileLoopCondTruthy", field := "hSWhileLoop",
      name := "stack-above-htif", point := none,
      predicate := fun s => s!"(bvule {bvN 0x8001ad10} (select (rr {s}) {bvN 2}))" },
    { query := some "hSWhileLoopBodyReturn", field := "hSWhileLoop",
      name := "body-loop-status", point := none,
      predicate := fun s =>
        s!"(or (= (select (rr {s}) {bvN 10}) {bvN 0}) (= (select (rr {s}) {bvN 10}) {bvN 2}))" },
    { query := some "hSWhileLoopRoute", field := "hSWhileLoop",
      name := "body-loop-status", point := none,
      predicate := fun s =>
        s!"(or (= (select (rr {s}) {bvN 10}) {bvN 0}) (= (select (rr {s}) {bvN 10}) {bvN 2}))" },
    { field := "hSRet", name := "return-expr", point := none, predicate := ld8Ne 11 8 0 },
    { field := "hSRetNull", name := "return-null", point := none, predicate := ld8Eq 11 8 0 },
    { field := "hSVarInit", name := "initializer", point := none, predicate := ld8Ne 11 16 0 },
    { field := "hSVarNull", name := "no-initializer", point := none, predicate := ld8Eq 11 16 0 },
    { field := "hSIfFalse", name := "has-else", point := none, predicate := ld8Ne 11 24 0 },
    { field := "hSIfNone", name := "no-else", point := none, predicate := ld8Eq 11 24 0 },
    -- These two leaf arms have identical output shape and differ only in the
    -- statement constructor.  Carry the discriminator explicitly in the
    -- residual manifest so the independent checker can reject a swapped or
    -- omitted query pin, rather than relying on an anonymous dispatch guard.
    { field := "hSBrk", name := "stmt-kind", point := none, predicate := ld4Eq 11 0 7 },
    { field := "hSCont", name := "stmt-kind", point := none, predicate := ld4Eq 11 0 8 } ]

/-- Residual-level semantic symbols.  String/output lengths remain abstract;
the independent trace checker gives these symbols their executable Lean
meaning without imposing a false finite string bound on SMT. -/
def residualSemanticSmt : String := "
(declare-fun lean_print_args_len
  ((Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
(declare-fun lean_print_args_out
  ((Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64)
   (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64))
  (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun lean_print_args_same
  ((Array (_ BitVec 64) (_ BitVec 8))
   (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64) (_ BitVec 64)) Bool)
(declare-fun lean_malloc16_rel
  ((Array (_ BitVec 64) (_ BitVec 8))
   (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
; Observable part of `Store.allocFrame`: the successful env_new helper returns
; one aligned, non-null 32-byte Env whose scalar fields are initially empty and
; whose final word is the incoming parent.  The ghost Store/frame-map relation
; is deliberately outside this machine projection.
(define-fun lean_env_new_frame
  ((m (Array (_ BitVec 64) (_ BitVec 8)))
   (inner (_ BitVec 64)) (parent (_ BitVec 64))) Bool
  (and (not (= inner #x0000000000000000))
       (= (bvand inner #x0000000000000007) #x0000000000000000)
       (= (ld4 m inner) #x0000000000000000)
       (= (ld4 m (bvadd inner #x0000000000000004)) #x0000000000000000)
       (= (ld8 m (bvadd inner #x0000000000000008)) #x0000000000000000)
       (= (ld8 m (bvadd inner #x0000000000000010)) #x0000000000000000)
       (= (ld8 m (bvadd inner #x0000000000000018)) parent)))"

/-- Splice: the reflected-Steps SMT for a residual's span + a Post-conjunct
validity query.  `postNeg` is the NEGATED post (SAT ⇒ refutable, UNSAT ⇒ valid,
unknown ⇒ needs invariant).  The default is the FRAME conjunct every residual
carries — memory below the stack frame is preserved — but any Post encoded over
`(mm state_exit)` / `(select (rr state_exit) n)` splices the same way. -/
def spliceResidualSmt (lo hi : Nat) (postNeg : String) : IO String := do
  let base ← reflectExactSmt lo hi
  return s!"{base}\n; ---- Pre ∧ ¬Post validity query (Pre trivial here; Post = frame conjunct) ----\n{postNeg}\n(check-sat)\n"

/-- The frame-conjunct negation: some address `A` below the stack frame differs
between entry and exit memory (should be UNSAT — the frame is preserved). -/
def frameNeg : String :=
  "(declare-const A Int)\n(assert (< A (- (select (rr s0) 2) 1000000)))\n(assert (not (= (select (mm state_exit) A) (select (mm s0) A))))"

/-- The GLOBAL summary closure: every `callee_`/`loop_` summary any of the 52
residual spans reaches, transitively.  Each is characterised once by the mined
clause set, then reused by every query that mentions it. -/
def globalSummaries : IO (List String) := do
  let img ← loadElf elfPath
  let mut acc : List String := []
  for inst in residualInstances do
    let (_, _, _, sums) := reflectExactD img inst.hi 200 inst.lo "s0" 0 [] []
    acc := summaryClosure img sums acc
  return acc

end Vsa.ReflectResiduals

open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#splice_all "<dir>"` — write a per-residual validity SMT (reflected Steps +
frame Post) for every residual; a Python driver runs Z3 (unknown ok on loops). -/
elab "#splice_all " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll dir
    for inst in residualInstances do
      let smt ← spliceResidualSmt inst.lo inst.hi frameNeg
      IO.FS.writeFile s!"{dir}/{inst.query}.smt2" smt
    Lean.logInfo m!"#splice_all → {dir} ({residualInstances.length} machine-instance validity queries)"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_campaign "<dir>"` — write the whole lemma-mode campaign:

* `<dir>/obligations/<sym>.smt2` — one per summary in the global closure: the
  one-step body under the `<sym>_ih` induction hypothesis, with `; @@ASSUME@@`
  and `; @@GOAL@@` injection points;
* `<dir>/queries/<field>.smt2` — one per residual: the span's exit-state DAG
  with summaries left uninterpreted, with `; @@ASSUME@@` and `; @@POST@@`;
* `<dir>/summaries.tsv`, `<dir>/query-summaries.tsv` — which summaries exist and
  which each query depends on (the driver only assumes the relevant ones).

The Houdini driver (`scripts/houdini_summary.py`) fills the injection points and
runs Z3.  Nothing here proves anything; run via `lake env lean`. -/
elab "#emit_campaign " pathStx:str : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/writes"
    IO.FS.createDirAll s!"{dir}/queries"
    let img ← loadElf elfPath
    let syms ← globalSummaries
    for sym in syms do
      IO.FS.writeFile s!"{dir}/obligations/{sym}.smt2" (summaryObligationSmt img syms sym)
    let mut rows : List String := []
    for inst in residualInstances do
      let (txt, deps) ← lemmaModeSmt inst.lo inst.hi
      IO.FS.writeFile s!"{dir}/queries/{inst.query}.smt2" txt
      rows := rows ++ [s!"{inst.query}\t{String.intercalate "," deps}"]
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\n" ++ String.intercalate "\n" syms ++ "\n")
    -- per-summary immediate dependencies: the driver only re-checks a summary
    -- when one of the summaries its body applies has lost a clause.
    let depRows := syms.map (fun s => s!"{s}\t{String.intercalate "," (summaryDeps img s)}")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    IO.FS.writeBinFile s!"{dir}/src/NativeBodyAssert.lean"
      (← IO.FS.readBinFile "Vsa/Sim/rows/NativeBodyAssert.lean")
    IO.FS.writeBinFile s!"{dir}/src/EvalCallNative2.lean"
      (← IO.FS.readBinFile "Vsa/Sim/EvalCallNative2.lean")
    IO.FS.writeBinFile s!"{dir}/src/SegEffect.lean"
      (← IO.FS.readBinFile "Vsa/Sim/SegEffect.lean")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv" ("summary\tdeps\n" ++ String.intercalate "\n" depRows ++ "\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" rows ++ "\n")
    Lean.logInfo m!"#emit_campaign → {dir} ({syms.length} summaries, {residualInstances.length} machine-instance queries)"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_machine "<dir>" <lo> <hi>` — the PC-THREADED campaign over the code
region `[lo,hi)`: one shared `mstep`/`mrun` pair and one query per residual.

* `<dir>/machine.smt2` — preamble + summary declarations + `mstep` + `mrun`;
* `<dir>/obligations/mrun.smt2` — the one-step `mrun` obligation under `mrun_ih`;
* `<dir>/queries/<field>.smt2` — `pc s0 = <entry>`, `STOP = <exit>`,
  `state_exit = (mrun s0)`, with `; @@ASSUME@@` / `; @@POST@@`;
* `<dir>/summaries.tsv`, `<dir>/unmodelled.tsv` — the out-of-region callee
  summaries, and every PC whose register effect is over-approximated.

Every residual whose span lies in `[lo,hi)` reflects with NO control-flow
analysis: computed gotos, shared epilogues, multi-exit loops and the
`eval_expr`↔`exec_stmt` recursion are all just PC values. -/
elab "#emit_machine " pathStx:str loStx:num hiStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    let lo := loStx.getNat
    let hi := hiStx.getNat
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/writes"
    IO.FS.createDirAll s!"{dir}/queries"
    IO.FS.createDirAll s!"{dir}/bounded"
    let img ← loadElf elfPath
    let (machine, sums, bad) := machineSmt img lo hi
    let decls := summaryDecls sums
    let unmodelledDecls := "(declare-fun unmodelled_step (MState) MState)"
    let pre := s!"{smtPreamble}\n{decls}\n{unmodelledDecls}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n{machine}"
    IO.FS.writeFile s!"{dir}/machine.smt2" (pre ++ "\n")
    -- the `mrun` induction obligation: `mrun` itself is NOT axiomatised here;
    -- the recursive occurrence is the free `mrun_ih`.
    let preNoRun := s!"{smtPreamble}\n{decls}\n{unmodelledDecls}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const STOP (_ BitVec 64))\n(declare-fun mrun_ih (MState) MState)"
    let stepOnly := (machine.splitOn "\n(declare-const STOP Int)").headD machine
    IO.FS.writeFile s!"{dir}/obligations/mrun.smt2"
      s!"{preNoRun}\n{stepOnly}\n(declare-const S0 MState)\n(define-fun fbody () MState {machineRunBody lo hi "S0"})\n; @@ASSUME@@\n; @@GOAL@@\n"
    let mut rows : List String := []
    for inst in residualInstances do
      if lo ≤ inst.lo && inst.lo < hi then
        IO.FS.writeFile s!"{dir}/queries/{inst.query}.smt2"
          s!"{pre}\n(declare-const s0 MState)\n(assert (= {stPC "s0"} {bvN inst.lo}))\n(assert (= STOP {bvN inst.hi}))\n; @@ASSUME@@\n(define-fun state_exit () MState (mrun s0))\n(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))\n; @@POST@@\n"
        -- BOUNDED companion: `mstep` unrolled `k` times with an explicit
        -- "the span actually finished" conjunct.  A SAT model here is a GENUINE
        -- countermodel (the run reached `STOP` inside `k` steps, so the unrolling
        -- is exact on it); an UNSAT is bounded validity, reported as such.
        IO.FS.writeFile s!"{dir}/bounded/{inst.query}.smt2"
          s!"{pre}\n(declare-const s0 MState)\n(assert (= {stPC "s0"} {bvN inst.lo}))\n(assert (= STOP {bvN inst.hi}))\n; @@ASSUME@@\n; @@EXIT@@\n(assert (= {stPC "state_exit"} {bvN inst.hi}))\n; @@POST@@\n"
      rows := rows ++ [s!"{inst.query}\tmrun"]
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\nmrun\n")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv" ("summary\tdeps\nmrun\tmrun\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" rows ++ "\n")
    IO.FS.writeFile s!"{dir}/unmodelled.tsv"
      ("pc\n" ++ String.intercalate "\n" (bad.map toString) ++ "\n")
    Lean.logInfo m!"#emit_machine [{lo},{hi}) → {dir}: {(hi-lo)/4} instrs, {sums.length} out-of-region callee summaries, {bad.length} unmodelled PCs, {rows.length} queries"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
/-- `#emit_bmc "<dir>" <rounds>` — the BOUNDED-SYMBOLIC-EXECUTION campaign.

Set the task-specific environment variable `VSA_BMC_ONLY` to one query key
(for example `hCallTooMany`) to emit a provenance-complete focused campaign.
This uses the identical reflector, manifests, and summary obligations while
avoiding symbolic execution of every unrelated residual during design loops.

Per residual: the span's REGION is its enclosing function (bounded by the image's
`jal ra` target set), the STOP is the residual's declared exit PC, and the
frontier is merged by PC every round.  Writes

* `<dir>/queries/<field>.smt2` — `state_exit` as the guarded merge of every exit
  arrival, with `; @@ASSUME@@` / `; @@POST@@` for the driver;
* `<dir>/obligations/<sym>.smt2` — one per callee/loop/opaque summary reached;
* `<dir>/spans.tsv` — per residual: region, stop, rounds used, whether the
  frontier EMPTIED (`complete`, so the encoding is exact for this span), term
  size and summary count.  A residual is only ever reported VALID when its span
  is complete; otherwise its verdict is a BOUNDED one. -/
elab "#emit_bmc " pathStx:str roundsStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let dir := pathStx.getString
    let rounds := roundsStx.getNat
    let only ← IO.getEnv "VSA_BMC_ONLY"
    let instances := match only with
      | none => residualInstances
      | some query => residualInstances.filter fun inst => inst.query == query
    if instances.isEmpty then
      throwError m!"#emit_bmc: VSA_BMC_ONLY names no residual query: {only.getD ""}"
    IO.FS.createDirAll s!"{dir}/queries"
    IO.FS.createDirAll s!"{dir}/obligations"
    IO.FS.createDirAll s!"{dir}/writes"
    IO.FS.createDirAll s!"{dir}/halts"
    let img ← loadElf elfPath
    let codeLo := 0x80000000
    let codeHi := 0x80018be0
    let starts := funcStarts img codeLo codeHi
    -- the image's writable static region, named as ground constants so the
    -- memory clauses can exempt it (see `writableRegion`).
    let (gLo, gHi) ← writableRegion elfPath
    let gDecl := s!"(define-fun G_lo () (_ BitVec 64) {bvN gLo})\n(define-fun G_hi () (_ BitVec 64) {bvN gHi})"
    -- the `jal ra` targets that never come back (the exit / _exit / abort
    -- family): a call to one ENDS the path instead of applying a `callee_`
    -- summary, because there is no return for a summary to describe.
    let noret := noReturnTargets img starts
    let mut rows : List String := []
    let mut deps : List String := []
    let mut noExit : List String := []
    let mut stopOutside : List String := []
    let mut allSums : List String := []
    let mut extensionRows : List String := []
    let mut routeRows : List String := []
    let mut effectRows : List String := []
    let mut certificateIdentities : List Vsa.Sim.SegmentIdentity := []
    for inst in instances do
      let nm := inst.query
      let field := inst.field
      let elo := inst.lo
      let ehi := inst.hi
      -- If the span's entry is a jump-table ARM, start at the FUNCTION entry with
      -- the AST kind pinned and let the dispatch derive the arm.  Everything the
      -- prologue establishes — `s1 = sret` (which every arm stores the boxed
      -- result through), the lowered `sp`, the callee-saved spills — is then
      -- DERIVED rather than assumed, exactly as `blockA_k` derives it in the
      -- proof.  Starting at the arm instead leaves those unconstrained, and the
      -- solver duly puts the result store inside the code image.
      let (bmcEntry, kindReg) :=
        if inst.directEntry then
          (elo, none)
        else
          match armDispatch img elo with
          | some (fe, reg, k) => (fe, some (reg, k))
          | none => (elo, none)
      let (rlo, rhi) := funcRange starts codeLo codeHi bmcEntry
      -- Is the span's stop the RETURN, or an internal pc?  The whole-arm
      -- convention puts the stop one instruction after the `ret`; a span that
      -- stops inside the function (hInitStore, at `interp_run`'s loop head)
      -- must not treat a return as an arrival at its exit.
      --
      -- A stop OUTSIDE the span's own region can never be an arrival at all
      -- (`stepBlock` only tests `stops` at PCs it walks through), so the span's
      -- exit is the function's RETURN and nothing else.  Reading `isRet` at
      -- `ehi - 4` there is reading a word in a DIFFERENT function: the twelve
      -- `exec_stmt` arms declare `0x800043ec` (`interp_run`), so their
      -- `retExit` was decided by `interp_init`'s `ret` at `0x800043e8` and came
      -- out true by luck.  Had that word not been a `ret`, all twelve spans
      -- would have had zero exit arrivals -- defect 2 of DIFFTEST-PLAN's table,
      -- one word away.  Decide it structurally instead, and record the
      -- mis-declared stops so they are visible rather than latent.
      let stopInRegion := rlo ≤ ehi && ehi < rhi
      let retExit := if stopInRegion then isRet (wordAt img (ehi - 4)) else true
      if !stopInRegion then
        stopOutside := stopOutside ++
          [s!"{nm}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t0x{String.ofList (Nat.toDigits 16 rlo)}\t0x{String.ofList (Nat.toDigits 16 rhi)}"]
      let (ev, binds, sums, complete, used, writes, dispG, halts, exitG,
          checkpoints) :=
        if inst.zeroStep then
          ("s0", ([] : List String), ([] : List String), true, 0,
            ([] : List (String × String × Nat)),
            ([] : List (Nat × Nat × String)), ([] : List (String × Nat)),
            "true", [(elo, "true", "s0")])
        else
          reflectBmcTopo img rlo rhi bmcEntry [ehi] starts noret retExit rounds "s0"
      -- The kind pin, PLUS which dispatch guard it makes true.  The encoder
      -- already resolved the jump table statically (that is how it knows the
      -- arms), so stating the selected guard here is the same ground fact as the
      -- rodata pins — just at the point of use.  Leaving it to the solver means
      -- re-deriving the dispatch through the prologue's store chain, which it
      -- does not do, so an arm the pin EXCLUDES still looks reachable and the
      -- span has to discharge invariants belonging to it.
      let kindPin :=
        match kindReg with
        | none => ""
        | some (reg, _) =>
          s!"; the arm is selected by the pinned AST kind (`ExprRepr`/`StmtRepr`)\n(assert (= (ld4 (mm s0) {stR "s0" reg}) {bvN (kindIndex img elo)}))\n"
      -- A loop summary can carry the exec dispatcher to one of several leaf
      -- arms.  Its per-exit selector is then the exact residual route fact.
      -- Recover the emitted selector bindings by their target constant so the
      -- brk/cont queries can pin 0x4098 versus 0x40b8 explicitly.
      let loopRoute : Option (String × List String) :=
        match binds.find? (fun b =>
          (b.splitOn "loopexit_").length > 1 && (b.splitOn (bvN elo)).length > 1) with
        | none => none
        | some selectedBind =>
          let after := (selectedBind.splitOn "loopexit_").getD 1 ""
          let ident := (after.takeWhile (·.isDigit)).toString
          let siblings := (binds.filter (fun b =>
            (b.splitOn s!"loopexit_{ident}").length > 1)).map bindingName
          some (bindingName selectedBind,
            siblings.filter (fun g => g != bindingName selectedBind))
      -- The guard selection has to come AFTER the binding chain: it names guard
      -- variables, and SMT-LIB wants them declared first.
      let dispPin :=
        match kindReg with
        | none => ""
        | some _ =>
          -- Pin ONLY the dispatch site whose arms include this residual's arm.
          -- Every other ground dispatch on the path -- eval_expr nests the
          -- operator table at 0x80003558 -- must be left free: asserting that
          -- none of ITS arms is taken, while the exit guard demands a path
          -- through one, makes the assumptions contradictory, and a query with
          -- contradictory assumptions reports VALID on every post.
          match dispG.find? (fun (t : Nat × Nat × String) => t.2.1 == elo) with
          | none =>
            match loopRoute with
            | none => ""
            | some (selected, excluded) =>
              "; exact per-exit route of the enclosing loop summary\n"
                ++ s!"(assert {selected})\n"
                ++ String.intercalate "\n" (excluded.map fun g => s!"(assert (not {g}))")
                ++ "\n"
          | some (site, _, _) =>
            let sel : List String :=
              (dispG.filter (fun (t : Nat × Nat × String) => t.1 == site)).map
                (fun (t : Nat × Nat × String) =>
                  if t.2.1 == elo then s!"(assert {t.2.2})"
                  else s!"(assert (not {t.2.2}))")
            "; and therefore which arm of THIS dispatch is taken (other ground\n"
              ++ "; dispatches on the path are left free)\n"
              ++ String.intercalate "\n" sel ++ "\n"
      -- A machine-readable copy of the exact route pin.  `dispPin` itself is
      -- part of the query; this row lets the independent fuzzer require the
      -- selected guard and every sibling exclusion, including for hSBrk/
      -- hSCont where swapping the two still yields a perfectly feasible run.
      match kindReg with
      | none => pure ()
      | some (reg, k) =>
        match dispG.find? (fun (t : Nat × Nat × String) => t.2.1 == elo) with
        | none =>
          -- Some shared-tail statement arms do not survive as a tagged BMC
          -- successor: the guard is folded into a larger block before the arm
          -- reaches the return frontier.  The exact route premise is still the
          -- statement-kind table selector.  Record and assert that ground fact
          -- explicitly, together with the independently recoverable dispatch
          -- site, so hSBrk and hSCont cannot borrow each other's route.
          let sites := (List.range ((rhi - rlo) / 4)).map (fun n => rlo + 4*n)
          match sites.find? (fun p =>
            match dispatchArms img p with
            | some arms => arms.contains elo
            | none => false) with
          | none => pure ()
          | some site =>
            let (selected, excluded) :=
              match loopRoute with
              | some pair => pair
              | none => (s!"(= (ld4 (mm s0) {stR "s0" reg}) {bvN k})", [])
            routeRows := routeRows ++
              [s!"{nm}\t{field}\t0x{String.ofList (Nat.toDigits 16 site)}\t0x{String.ofList (Nat.toDigits 16 elo)}\t{selected}\t{String.intercalate "," excluded}"]
        | some (site, _, selected) =>
          let excluded :=
            (dispG.filter (fun (t : Nat × Nat × String) =>
              t.1 == site && t.2.1 != elo)).map (fun t => t.2.2)
          routeRows := routeRows ++
            [s!"{nm}\t{field}\t0x{String.ofList (Nat.toDigits 16 site)}\t0x{String.ofList (Nat.toDigits 16 elo)}\t{selected}\t{String.intercalate "," excluded}"]
      let decls2 := bindsToDecls binds
      let mut extPin := ""
      for ext in residualExtensions.filter (fun e =>
          e.field == field && e.query.all (fun query => query == nm)) do
        let (point, guard, state) ←
          match ext.point with
          | none => pure ("entry", "true", "s0")
          | some pc =>
            if pc == ehi then
              -- `reflectBmcTopo` stops before decoding the stop instruction,
              -- so it does not return that PC in `checkpoints`.  The merged
              -- exit term is exactly the state on arrival at that PC.
              pure (s!"0x{String.ofList (Nat.toDigits 16 pc)}", exitG, ev)
            else
              match checkpoints.find? (fun t => t.1 == pc) with
              | some (_, g, s) => pure (s!"0x{String.ofList (Nat.toDigits 16 pc)}", g, s)
              | none => throwError m!"{nm}: residual extension {ext.name} names missing checkpoint 0x{String.ofList (Nat.toDigits 16 pc)}"
        let pred := ext.predicate state
        if guard != "true" then extPin := extPin ++ s!"(assert {guard})\n"
        extPin := extPin ++ s!"(assert {pred})\n"
        extensionRows := extensionRows ++ [s!"{nm}\t{field}\t{ext.name}\t{point}\t{guard}\t{state}\t{pred}"]
      allSums := (allSums ++ sums).eraseDups
      let decls := summaryDecls sums
      -- NO-EXIT: `reflectBmc` returns the entry name unchanged when the span has
      -- no exit arrival at all (every path halts, or the stop PC is unreachable).
      -- Writing the query anyway would ask the post about the ENTRY state and
      -- report VALID.  Record the field and skip it instead.
      if ev == "s0" && !inst.zeroStep then
        noExit := noExit ++ [s!"{nm}\t0x{String.ofList (Nat.toDigits 16 bmcEntry)}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t{halts.length}"]
      else
      IO.FS.writeFile s!"{dir}/queries/{nm}.smt2"
        s!"; query={nm} residual={field} instance={inst.variant} capability={queryCapability inst}\n; This is not a full encoding of the Lean residual proposition.\n{smtPreamble}\n{residualSemanticSmt}\n{decls}\n{gDecl}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const s0 MState)\n{kindPin}{decls2}\n{dispPin}; residual-specific premises from the Lean constructor\n{extPin}; only inputs that REACH the exit PC: without this the `ite` merge\n; falls through to the last arrival for an input no guard covers, and the\n; resulting state is one the machine is never in -- spurious REFUTED.\n(assert {exitG})\n; mined clause set for every summary\n; @@ASSUME@@\n(define-fun state_exit () MState {ev})\n(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) (mm state_exit))\n; @@POST@@\n"
      IO.FS.writeFile s!"{dir}/writes/{nm}.tsv"
        ("guard\twidth\taddr\n" ++ String.intercalate "\n"
          (writes.map (fun (g, a, w) => s!"{g}\t{w}\t{a}")) ++ "\n")
      -- Frame claims come from a typed certificate for the exact query identity.
      -- The direct-memory column separately describes the reflected write log.
      let directWriteRows :=
        (writes.filter fun row => row.2.2 != 0).length
      let directMemory :=
        if directWriteRows == 0 then "none" else "guarded-write-log"
      let routeIdentity : Vsa.Sim.SegmentIdentity :=
        ⟨nm, field, BitVec.ofNat 64 bmcEntry, BitVec.ofNat 64 ehi, !retExit⟩
      let routeCertificate :=
        if complete && ev != "s0" && sums.isEmpty && directWriteRows == 0 then
          Vsa.Sim.lookupWhileBodyReturnExport routeIdentity
        else none
      if routeCertificate.isSome then
        certificateIdentities := certificateIdentities ++ [routeIdentity]
      let registerWrites :=
        if inst.zeroStep then "none"
        else match routeCertificate with
          | some cert => match cert.effect.regs with
            | .all => "none"
            | .abi => "preserves-abi"
            | _ => "unsupported-dynamic"
          | none => "unsupported-dynamic"
      let outputEffect :=
        if inst.zeroStep then "preserved"
        else match routeCertificate with
          | some cert => if cert.effect.outputPreserved then "preserved"
              else "unsupported-dynamic"
          | none => "unsupported-dynamic"
      let effectTheorem :=
        if inst.zeroStep then "Vsa.Sim.FrameGuarantee.refl"
        else if routeCertificate.isSome then
          "Vsa.Sim.whileBodyReturnCertified"
        else "-"
      let effectProvenance :=
        if inst.zeroStep then "Lean:Vsa.Sim.FrameGuarantee.refl"
        else if routeCertificate.isSome then
          "Lean:Vsa.Sim.whileBodyReturnCertified"
        else "Lean-emitted:Vsa.ReflectSpan.reflectBmcTopo"
      effectRows := effectRows ++
        [s!"{nm}\t{field}\t{registerWrites}\t{directMemory}\t{directWriteRows}\t{outputEffect}\t{effectTheorem}\t{effectProvenance}"]
      -- The paths EXCLUDED from the exit merge because they transfer to a
      -- function that never returns.  A verdict on this span is a verdict on
      -- the paths that reach the exit PC; these ones halt instead, and are the
      -- error-site seam's obligation (`Vsa/Sim/ErrorSiteJal.lean`), not a frame
      -- post's.  Named here so the verdict can be qualified rather than bare.
      IO.FS.writeFile s!"{dir}/halts/{nm}.tsv"
        ("guard\tsite\n" ++ String.intercalate "\n"
          (halts.map (fun (g, a) => s!"{g}\t0x{String.ofList (Nat.toDigits 16 a)}")) ++ "\n")
      rows := rows ++ [s!"{nm}\t{field}\t{inst.variant}\t0x{String.ofList (Nat.toDigits 16 rlo)}\t0x{String.ofList (Nat.toDigits 16 rhi)}\t0x{String.ofList (Nat.toDigits 16 bmcEntry)}\t0x{String.ofList (Nat.toDigits 16 ehi)}\t{retExit}\t{used}\t{complete}\t{decls2.length}\t{sums.length}\t{halts.length}"]
      deps := deps ++ [s!"{nm}\t{String.intercalate "," sums}"]
    -- Summary obligations, over the SAME encoder.
    --   `callee_t` — symbolically execute the callee's own function;
    --   `loop_h`   — symbolically execute the loop from its header, stopping at
    --               the loop's exit edges, so the term IS the one-step body
    --               (a re-arrival at `h` becomes `loop_h_ih`, the IH);
    --   `icall_`/`idisp_` — opaque by construction (an indirect call through a
    --               register / an unlisted computed goto): NO obligation exists,
    --               so they are listed in `opaque.tsv` and their clauses can only
    --               ever be assumed, never established.
    -- A summary's own body reaches further summaries, so the obligation set is a
    -- FIXPOINT, not one pass over the residuals' summaries: iterate until nothing
    -- new is discovered, or the campaign silently assumes clauses for symbols it
    -- never generated an obligation for.
    let mut opaqueSyms : List String := []
    let mut symDeps : List String := []
    -- The campaign's scope is the INTERPRETER's own code, and no further.  A
    -- summary whose body lies outside the residual spans' own functions is a
    -- CALLEE CONTRACT — `value_int`, `value_bool`, `strcmp`, `malloc`, … — and
    -- the Lean development does not re-derive those either: they are landed
    -- specs (`TermCallees.valueInt`/`strcmp`/`divdi3`/`envGet`) or named open
    -- premises (`envDefine`/`malloc`/`realloc`).  Mining them would drag in the
    -- whole C runtime; they are ASSUMED, listed in `assumed.tsv`, and every
    -- verdict that rests on one says so.
    let armRegions := (instances.map (fun inst =>
      funcRange starts codeLo codeHi inst.lo)).eraseDups
    let inArm := fun (q : Nat) => armRegions.any (fun (a, b) => a ≤ q && q < b)
    let mut worklist := allSums
    let mut done : List String := []
    let mut assumedSyms : List String := []
    while !worklist.isEmpty do
      let sym := worklist.head!
      worklist := worklist.tail!
      if done.contains sym then continue
      done := sym :: done
      let tgt : Option Nat :=
        if sym.startsWith "callee_" then some (sym.drop 7).toNat!
        else if sym.startsWith "loop_" then some (sym.drop 5).toNat!
        else none
      if let some t := tgt then
        if !(inArm t) then
          assumedSyms := assumedSyms ++ [sym]
          continue
      let mk : Nat → Nat → Nat → List Nat → IO (String × List String) := fun rlo rhi entry stops => do
        let (ev, binds, subs, complete, _, writes, _, _, _, _) := reflectBmcTopo img rlo rhi entry stops starts noret true rounds "S0"
        let declsB := (bindsToDecls binds).replace s!"({sym} " s!"({sym}_ih "
        let decls := summaryDecls ((allSums ++ subs).eraseDups ++ [s!"{sym}_ih"])
        IO.FS.writeFile s!"{dir}/obligations/{sym}.smt2"
          s!"{smtPreamble}\n{residualSemanticSmt}\n{decls}\n{gDecl}\n(declare-const SL_lo (_ BitVec 64))\n(declare-const SL_hi (_ BitVec 64))\n(declare-const A_lo (_ BitVec 64))\n(declare-const A_hi (_ BitVec 64))\n(define-fun INV ((S MState)) Bool (and (bvule #x0000000000010000 SL_lo) (bvult SL_lo SL_hi) (bvult SL_hi #x0000000100000000) (bvule #x0000000000010000 A_lo) (bvult A_lo A_hi) (bvult A_hi #x0000000100000000) (or (bvult A_hi SL_lo) (bvugt A_lo SL_hi)) (bvule (bvadd SL_lo #x0000000000001100) (select (rr S) #x0000000000000002)) (bvule (select (rr S) #x0000000000000002) (bvsub SL_hi #x0000000000001100))))\n(declare-const S0 MState)\n{declsB}\n; complete={complete}\n(define-fun fbody () MState {ev})\n; clause set for every summary; `{sym}` itself is supplied as `{sym}_ih`\n; @@ASSUME@@\n; negated clause under test, over S0 / fbody\n; @@GOAL@@\n"
        IO.FS.writeFile s!"{dir}/writes/{sym}.tsv"
          ("guard\twidth\taddr\n" ++ String.intercalate "\n"
            ((writes.map (fun (g, a, w) => s!"{g}\t{w}\t{a}")).map
              (fun r => r.replace s!"({sym} " s!"({sym}_ih ")) ++ "\n")
        return (s!"{sym}\t{String.intercalate "," ((sym :: subs).eraseDups)}", subs)
      if sym.startsWith "callee_" then
        let t := (sym.drop 7).toNat!
        let (rlo, rhi) := funcRange starts codeLo codeHi t
        let (row, subs) ← mk rlo rhi t []
        symDeps := symDeps ++ [row]; worklist := worklist ++ subs
      else if sym.startsWith "loop_" then
        let h := (sym.drop 5).toNat!
        let (rlo, rhi) := funcRange starts codeLo codeHi h
        let (qs, _) := loopExits img rlo rhi [] h
        let (row, subs) ← mk rlo rhi h qs
        symDeps := symDeps ++ [row]; worklist := worklist ++ subs
      else opaqueSyms := opaqueSyms ++ [sym]
    IO.FS.writeFile s!"{dir}/opaque.tsv" ("summary\n" ++ String.intercalate "\n" opaqueSyms ++ "\n")
    -- Clauses that must NOT be assumed for a given summary, with the structural
    -- reason.  An assumed contract is checked by nobody, so anything the image
    -- itself contradicts has to be taken off the table here rather than left to
    -- be discovered by a countermodel (or not discovered at all).
    let mut drops : List String := []
    for sym in assumedSyms do
      if sym.startsWith "callee_" then
        let t := (sym.drop 7).toNat!
        if retsViaSaved img starts t then
          drops := drops ++ [s!"{sym}\tra_restore\treturns through a saved register / unresolved computed goto, so `ra` is not preserved"]
    IO.FS.writeFile s!"{dir}/clause-drop.tsv"
      ("summary\tclause\treason\n" ++ String.intercalate "\n" drops ++ "\n")
    IO.FS.writeFile s!"{dir}/regions.tsv"
      s!"region\tlo\thi\nwritable_static\t0x{String.ofList (Nat.toDigits 16 gLo)}\t0x{String.ofList (Nat.toDigits 16 gHi)}\n"
    IO.FS.writeFile s!"{dir}/assumed.tsv"
      ("summary\trole\n" ++ String.intercalate "\n"
        (assumedSyms.map (fun a => s!"{a}\tcallee contract outside the interpreter's own code")) ++ "\n"
        ++ "d < maxCallDepth\tentry stack budget: the 7408 headroom pin needs the closure depth guard; ExecEntry has no depth field\n")
    -- PROVENANCE.  A campaign directory is read back by a driver that has no way
    -- to tell which encoder emitted it, and a second session regenerating this
    -- same directory from a different `ReflectResiduals.lean` is not a
    -- hypothetical: it happened, and a `--phase check` run here reported five
    -- fields VACUOUS that the current tree reports UNKNOWN.  Stamp the sources
    -- so the driver can refuse rather than answer about a different program.
    -- The sources are COPIED rather than hashed: a hash has to be recomputed
    -- identically on the reading side, and a reimplementation of `String.hash`
    -- in the driver is one more thing that can silently drift.  Bytes compare.
    IO.FS.createDirAll s!"{dir}/src"
    for nm in ["ReflectSpan.lean", "ReflectResiduals.lean"] do
      IO.FS.writeBinFile s!"{dir}/src/{nm}" (← IO.FS.readBinFile s!"experiments/smt/{nm}")
    IO.FS.writeBinFile s!"{dir}/src/NativeBodyAssert.lean"
      (← IO.FS.readBinFile "Vsa/Sim/rows/NativeBodyAssert.lean")
    IO.FS.writeBinFile s!"{dir}/src/EvalCallNative2.lean"
      (← IO.FS.readBinFile "Vsa/Sim/EvalCallNative2.lean")
    IO.FS.writeBinFile s!"{dir}/src/SegEffect.lean"
      (← IO.FS.readBinFile "Vsa/Sim/SegEffect.lean")
    let elfBytes ← IO.FS.readBinFile elfPath
    IO.FS.writeBinFile s!"{dir}/src/proof.elf" elfBytes
    let certificateProvenance ← emitCertificateProvenance dir
    let mut certificateRows := []
    for identity in certificateIdentities do
      match Vsa.Sim.lookupWhileBodyReturnExport identity with
      | some certificate =>
        certificateRows := certificateRows ++
          [← emitWhileCertificate dir certificateProvenance identity certificate]
      | none => throwError "typed segment certificate identity disappeared during emission"
    IO.FS.writeFile s!"{dir}/segment-certificates.tsv"
      ("query\tfield\tentry\tstop\tstop_policy\tcertificate_path\tcertificate_sha256\tquery_sha256\ttheorem\n" ++
        String.intercalate "\n" certificateRows ++ "\n")
    IO.FS.writeFile s!"{dir}/provenance.txt"
      s!"emitter sources are copied verbatim to {dir}/src/; the driver compares bytes\nelf\t{elfPath}\nelf_bytes\t{elfBytes.size}\n"
    IO.FS.writeFile s!"{dir}/pre.smt2" (entryPinsSmt img ++ "\n")
    IO.FS.writeFile s!"{dir}/summary-deps.tsv"
      ("summary\tdeps\n" ++ String.intercalate "\n" symDeps ++ "\n")
    IO.FS.writeFile s!"{dir}/stop-outside.tsv"
      ("field\tstop\tregion_lo\tregion_hi\n" ++ String.intercalate "\n" stopOutside ++ "\n")
    IO.FS.writeFile s!"{dir}/no-exit.tsv"
      ("field\tentry\tstop\thalts\n" ++ String.intercalate "\n" noExit ++ "\n")
    IO.FS.writeFile s!"{dir}/spans.tsv"
      ("field\tresidual\tinstance\tregion_lo\tregion_hi\tentry\tstop\tret_exit\trounds\tcomplete\tterm_bytes\tsummaries\thalts\n"
        ++ String.intercalate "\n" rows ++ "\n")
    IO.FS.writeFile s!"{dir}/summaries.tsv" ("summary\n" ++ String.intercalate "\n" done.reverse ++ "\n")
    IO.FS.writeFile s!"{dir}/query-summaries.tsv" ("field\tsummaries\n" ++ String.intercalate "\n" deps ++ "\n")
    IO.FS.writeFile s!"{dir}/residual-extensions.tsv"
      ("query\tfield\tname\tpoint\tguard\tstate\tpredicate\n" ++
        String.intercalate "\n" extensionRows ++ "\n")
    IO.FS.writeFile s!"{dir}/residual-routes.tsv"
      ("query\tfield\tsite\tarm\tselected_guard\texcluded_guards\n" ++
        String.intercalate "\n" routeRows ++ "\n")
    IO.FS.writeFile s!"{dir}/exact-callees.tsv"
      ("target\tname\tmode\tlean_basis\tmemory\n" ++
       "0x800027ec\tvalue_null\tinline-exact\tVsa.Sim.value_null_spec\twrite [a0,a0+4) and [a0+8,a0+16) only\n" ++
       "0x800027f8\tvalue_bool\tinline-exact\tVsa.Sim.value_bool_spec_full\twrite [a0,a0+4) and [a0+8,a0+12) only\n" ++
       "0x8000280c\tvalue_int\tinline-exact\tVsa.Sim.value_int_spec\twrite [a0,a0+4) and [a0+8,a0+16) only\n" ++
       "0x8000281c\tvalue_str\tinline-exact\tVsa.Sim.value_str_spec_full\twrite [a0,a0+4) and [a0+8,a0+16) only\n" ++
       "0x8000282c\tvalue_truthy\tinline-exact\tVsa.Sim.value_truthy_spec\tread-only\n")
    IO.FS.writeFile s!"{dir}/functional-callees.tsv"
      ("target\tname\tmode\tresult\tmemory\tclobbers\n" ++
       "0x80004640\t__muldi3\tground-functional-post\tbvmul(a0,a1)\tread-only\ta0,a1,a2,a3\n" ++
       "0x800046a4\t__divdi3\tground-functional-post\tbvsdiv(a0,a1)\tread-only\tra,t0,a0,a1,a2,a3\n" ++
       "0x80004728\t__moddi3\tground-functional-post\tbvsrem(a0,a1)\tread-only\tra,t0,a0,a1,a2,a3\n")
    IO.FS.writeFile s!"{dir}/semantic-helpers.tsv"
      ("target\tname\tmode\trelation\tlean_basis\n" ++ String.intercalate "\n"
        (semanticHelperCertificates.map fun cert =>
          s!"0x{String.ofList (Nat.toDigits 16 cert.target)}\t{cert.name}\tground-semantic-post\t{cert.relation}\t{cert.theoremName}") ++ "\n")
    IO.FS.writeFile s!"{dir}/semantic-helper-certificates.tsv"
      ("target\tname\trelation\ttheorem\n" ++ String.intercalate "\n"
        (semanticHelperCertificates.map fun cert =>
          s!"0x{String.ofList (Nat.toDigits 16 cert.target)}\t{cert.name}\t{cert.relation}\t{cert.theoremName}") ++ "\n")
    IO.FS.writeFile s!"{dir}/lean-certificates.tsv"
      ("residual\tpost\ttheorem\n" ++ String.intercalate "\n"
        (leanPostCertificates.map fun cert =>
          s!"{cert.residual}\t{cert.post}\t{cert.theoremName}") ++ "\n")
    IO.FS.writeFile s!"{dir}/residual-holes.tsv"
      ("field\tdimension\treason\n" ++ String.intercalate "\n"
        (residualHoles.map fun (field, dimension, reason) =>
          s!"{field}\t{dimension}\t{reason}") ++ "\n")
    IO.FS.writeFile s!"{dir}/query-capabilities.tsv"
      ("query\tfield\tinstance\tcapability\n" ++ String.intercalate "\n"
        (instances.map fun inst =>
          s!"{inst.query}\t{inst.field}\t{inst.variant}\t{queryCapability inst}") ++ "\n")
    IO.FS.writeFile s!"{dir}/query-effects.tsv"
      ("query\tfield\tregister_writes\tdirect_memory_writes\tdirect_write_rows\toutput\ttheorem\tprovenance\n" ++
        String.intercalate "\n" effectRows ++ "\n")
    IO.FS.writeFile s!"{dir}/residual-capabilities.tsv"
      ("field\tmachine_instances\tsemantic_projection\tfull_residual\tcapability_class\n" ++
        String.intercalate "\n" ((residualFields ++ machineBoundaryProjectionFields).eraseDups.map fun field =>
          let count := (instances.filter fun inst => inst.field == field).length
          let projection := if instances.any (fun inst => inst.field == field &&
            (queryCapability inst == "partial-projection" ||
              queryCapability inst == "indexed-error-projection")) then "yes" else "no"
          s!"{field}\t{count}\t{projection}\tno\t{residualCapabilityClass instances field}") ++ "\n")
    IO.FS.writeFile s!"{dir}/error-physical-sites.tsv"
      ("pc\tmachine_cause\tconstructibility\n" ++
        String.intercalate "\n" (errorPhysicalSites.map fun (pc, cause, status) =>
          s!"0x{String.ofList (Nat.toDigits 16 pc)}\t{cause}\t{status}") ++ "\n")
    IO.FS.writeFile s!"{dir}/error-indexed-premises.tsv"
      ("premise\tcoverage_kind\tfixed_pc\n" ++
        String.intercalate "\n" (errorIndexedPremises.map fun premise =>
          let kind := if premise == "hBadClosure" then "spec-only-unconstructible"
            else "focused-semantic-witness"
          s!"{premise}\t{kind}\tno") ++
        "\nhTopAbrupt\tseparate-top-level-obligation\tno-jal\n")
    let nComplete := (rows.filter (fun r => (r.splitOn "\t").getD 9 "" == "true")).length
    Lean.logInfo m!"#emit_bmc → {dir}: {toString instances.length} machine instances, {nComplete} COMPLETE at {rounds} rounds, {done.length} summaries: {done.length - assumedSyms.length - opaqueSyms.length} mined, {assumedSyms.length} assumed contracts, {opaqueSyms.length} opaque"


open Vsa.ReflectResiduals Vsa.ReflectSpan in
elab "#bmc_trace " loStx:num hiStx:num stopStx:num rStx:num : command => do
  Lean.Elab.Command.liftTermElabM do
    let img ← loadElf elfPath
    let starts := funcStarts img 0x80000000 0x80018be0
    let (rlo, rhi) := funcRange starts 0x80000000 0x80018be0 loStx.getNat
    let noret := noReturnTargets img starts
    let tr := bmcTrace img rlo rhi loStx.getNat [stopStx.getNat] starts noret true rStx.getNat
    let mut i : Nat := 0
    for f in tr do
      let pcs := f.map (fun q => String.ofList (Nat.toDigits 16 q))
      Lean.logInfo s!"round {i}: {f.length} pcs {pcs}"
      i := i + 1
