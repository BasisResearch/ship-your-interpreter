export const meta = {
  name: 'evalgt-block-reflection',
  description: 'Fan out block_mem_sound lemma authoring for EvalGtRow straight-line blocks across CoW-cloned /tmp projects, then merge the verified lemmas into the main repo',
  phases: [
    { title: 'Author', detail: 'one agent per block, each in its own cp -c CoW clone, builds+verifies' },
    { title: 'Merge', detail: 'collect verified block lemmas into Vsa/Sim/EvalGtBlocks.lean, build serially in main repo' },
  ],
}

const REPO = '/Users/kirancodes/Documents/code/verified-semantic-abstraction'

// Straight-line bodies only (no terminator) — the proven EvalGtBlk1Pilot pattern via block_mem_sound.
// Terminators (jr/bne/beq) are composed later at assembly. Each block is an independent standalone lemma.
const BLOCKS = [
  { label: 'Blk2', def: 'evalGtBlk2', thm: 'evalGtBlk2_run',
    entryPC: '0x80003538', endPC: '0x80003558',
    body: 'slli x14,x15,0x20 (0x3538); srli x15,x14,0x1e (0x353c); auipc x14,0x17 (0x3540); addi x14,x14,-1468 (0x3544); add x15,x15,x14 (0x3548); lw x15,0(x15) (0x354c, 4-byte load); ld x16,0(x2) (0x3550, 8-byte load); add x15,x15,x14 (0x3554)',
    loads: 'two: lw@0x354c reads 4 bytes at (x15+0), ld@0x3550 reads 8 bytes at (x2+0)',
    stores: 'none' },
  { label: 'BlkLdSt', def: 'evalGtBlkLdSt', thm: 'evalGtBlkLdSt_run',
    entryPC: '0x8000367c', endPC: '0x80003694',
    body: 'ld x14,0x90(x2) (0x367c); ld x11,0x98(x2) (0x3680); ld x15,0xa0(x2) (0x3684); sd x14,0xf0(x2) (0x3688); sd x11,0xf8(x2) (0x368c); sd x15,0x100(x2) (0x3690)',
    loads: 'three 8-byte loads off x2 at 0x90/0x98/0xa0',
    stores: 'three 8-byte stores off x2 at 0xf0/0xf8/0x100 (need StOK window facts: bounds, align%8, tohostAddr+16 <= addr)' },
  { label: 'BlkCmp', def: 'evalGtBlkCmp', thm: 'evalGtBlkCmp_run',
    entryPC: '0x80003698', endPC: '0x800036a8',
    body: 'slt x14,x17,x19 (0x3698); slt x15,x19,x17 (0x369c); subw x11,x14,x15 (0x36a0); li x15,0x15 (0x36a4)',
    loads: 'none', stores: 'none (pure ALU)' },
]

const BLOCK_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['label', 'ok', 'elabSeconds', 'axiomsClean', 'lemmaText', 'notes'],
  properties: {
    label: { type: 'string' },
    ok: { type: 'boolean', description: 'true iff the lemma built GREEN (no errors) in the clone' },
    elabSeconds: { type: 'number', description: 'wall seconds to `lake env lean` the block file in the clone' },
    axiomsClean: { type: 'boolean', description: 'true iff #print axioms shows only propext/Classical.choice/Quot.sound' },
    lemmaText: { type: 'string', description: 'the COMPLETE verified .lean file content (imports+opens+def+theorem), or the best partial if not green' },
    notes: { type: 'string', description: 'what worked, what did not, any residual sorry/errors' },
  },
}

const MERGE_SCHEMA = {
  type: 'object',
  additionalProperties: false,
  required: ['ok', 'built', 'notes'],
  properties: {
    ok: { type: 'boolean' },
    built: { type: 'boolean', description: 'true iff `lake build Vsa.Sim.EvalGtBlocks` succeeded in the main repo' },
    notes: { type: 'string' },
  },
}

function authorPrompt(b) {
  return `You are authoring ONE verified Lean 4 block-reflection lemma, working in your OWN throwaway clone of the project so you can BUILD and ITERATE. Follow this exactly.

SETUP (do first):
1. CoW-clone the project into a unique temp dir (instant on APFS, near-zero disk):
   \`cp -c -R ${REPO} /tmp/wf-${b.label}\`
   Then \`cd /tmp/wf-${b.label}\` and do ALL work there. NEVER touch ${REPO} (the main repo).
2. Read the TEMPLATE you must mirror: \`Vsa/Sim/EvalGtBlk1Pilot.lean\` (a straight-line block via ONE \`block_mem_sound\`). Also skim \`Vsa/Sim/BlockMemDemo.lean\` (has STORES — the \`sd\` MemFacts pattern \`⟨lo,hi,win,al⟩\` where win is \`tohostAddr+16 ≤ addr\`, and the writeMap8 output memory). Both are the canonical patterns.

YOUR BLOCK: ${b.label} — entry PC ${b.entryPC}, straight-line body ending BEFORE ${b.endPC} (NO terminator; body only via \`block_mem_sound\`).
  Body instructions: ${b.body}
  Loads: ${b.loads}
  Stores: ${b.stores}

TASK:
1. Get the exact (pc, word) for each body instruction: grep the site definitions in \`Vsa/Sim/AddTailSites.lean\` (and siblings) for \`site_<pc>_ee\` — each contains its \`(0x<word>#32)\`. Build the block as \`def ${b.def} : List MInstr := [mkLine 0x<pc>#64 0x<word>#32, …]\` (mkLine auto-decodes; do NOT hand-write byte/kind fields).
2. Write a standalone theorem \`${b.thm}\` in a NEW file \`Vsa/Sim/${b.label}Pilot.lean\` (in your clone), mirroring EvalGtBlk1Pilot: entry σ with GoodState/PC/minstret + register pins (one hypothesis per register the body reads — e.g. x2, x15, x17, x19 as needed) + \`Vsa.Sim.Code.Eval_exprLoaded σ.mem\`, then the load/store MemFacts hypotheses (bounds+align+pins for each load; bounds+align+window for each store), then \`(hi : i < 2)\`. Conclusion: just \`∃ σ' i', Steps ⟨σ,i,u⟩ ⟨σ',i',u+<N>⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.regs.get? Register.PC = some ${b.endPC}#64\` where N = number of body instructions.
3. Proof: \`obtain ⟨σ',i',hsteps,hi',hG',hmem',hout',hpc',hmi',hGH,hframe⟩ := block_mem_sound ${b.def} σ i u ${b.entryPC}#64 vm [(reg,val)…pins] [[loadbytes]…] hG hpc hmi ⟨pins…,trivial⟩ (show KeysOK […] by decide) (by block_facts hmem with "Vsa.Sim.Code.eval_expr_at_"; · exact <load/store memfacts in program order>) (show BlockOKM ${b.entryPC}#64 […] ${b.def} by decide) hi\` then \`rw [show endPCM ${b.entryPC}#64 ${b.def} = (${b.endPC}#64 : BitVec 64) from by decide] at hpc'\` and close with \`exact ⟨σ',i',hsteps,hi',hG',hpc'⟩\`. The block_facts leaves one goal per load/store in PROGRAM ORDER; a 4-byte load goal is \`⟨⟨lo,hi,ht,al⟩,p0,p1,p2,p3⟩\`, an 8-byte load \`⟨⟨lo,hi,ht,al⟩,p0..p7⟩\`, an 8-byte store \`⟨lo,hi,win,al⟩\` (window = tohostAddr+16 ≤ addr; stores have NO byte pins). Imports: mirror EvalGtBlk1Pilot exactly (\`import Vsa.Sim.AddTailSites / BlockMem / BlockTactics / BlockDecode\`) plus any DecodeTable batch the build says is missing.
4. BUILD + ITERATE in your clone: \`pkill -9 lean; lake env lean Vsa/Sim/${b.label}Pilot.lean\`. Fix errors and rebuild until GREEN (no errors). Common fixes: wrong register-pin list vs KeysOK order; wrong load width (4 vs 8) or memfact nesting; store window vs load htif disjunct; a missing DecodeTable import (add \`import Vsa.Sim.DecodeTable.Batch..\` — find which by the "unknown identifier Vsa.Sim.DecodeTable.decode_<word>" error). Iterate patiently; you have build feedback.
5. When green, time it (\`time lake env lean …\`) and axiom-check: \`lake build Vsa.Sim.${b.label}Pilot\` then a scratch file \`import Vsa.Sim.${b.label}Pilot\\nopen Vsa.Sim in\\n#print axioms ${b.thm}\` via \`lake env lean\`.

Return the schema: label="${b.label}", ok=(green?), elabSeconds, axiomsClean, lemmaText=(the COMPLETE final file content), notes. If you cannot get it green, return ok=false with the closest attempt as lemmaText and the blocking error in notes. NEVER write to ${REPO}. Clean up your clone at the end (\`rm -rf /tmp/wf-${b.label}\`) ONLY after you have captured the full lemmaText.`;
}

phase('Author')
const authored = (await parallel(BLOCKS.map(b => () =>
  agent(authorPrompt(b), { label: `author:${b.label}`, phase: 'Author', schema: BLOCK_SCHEMA, agentType: 'general-purpose' })
))).filter(Boolean)

log(`authored ${authored.length}/${BLOCKS.length}; green: ${authored.filter(a => a.ok).length}`)

const green = authored.filter(a => a && a.ok)

phase('Merge')
let merged = { ok: false, built: false, notes: 'no green blocks to merge' }
if (green.length > 0) {
  merged = await agent(
    `Merge verified block-reflection lemmas into the MAIN repo ${REPO} (work directly there, serial, no clone).
The following ${green.length} block lemma file(s) built GREEN in isolated clones. Each is a self-contained standalone lemma:

${green.map(g => `=== ${g.label} (elab ${g.elabSeconds}s, axiomsClean=${g.axiomsClean}) ===\n${g.lemmaText}`).join('\n\n')}

TASK:
1. Combine them into ONE new file ${REPO}/Vsa/Sim/EvalGtBlocks.lean: use the union of their imports (dedup), one shared \`open …\` + \`namespace Vsa.Sim\` block, and paste each file's \`def\`+\`theorem\` bodies (drop the per-file imports/opens/namespace wrappers; keep the defs/theorems, rename if any name collides). Keep the \`set_option maxHeartbeats\`/\`maxRecDepth\` lines once at top.
2. Add \`import Vsa.Sim.EvalGtBlocks\` to ${REPO}/Vsa.lean right after the \`import Vsa.Sim.EvalGtBlk1Pilot\` line (append-only, that ONE line).
3. Build serially in the main repo: \`cd ${REPO}; pkill -9 lean; lake build Vsa.Sim.EvalGtBlocks\`. If it fails, fix (usually a dedup/name/import issue) and rebuild until green. Do NOT run a full \`lake build\` (no args). Do NOT git commit.
4. Report ok (file assembled), built (lake build Vsa.Sim.EvalGtBlocks succeeded), and notes (per-block status, any rename, residual errors).`,
    { label: 'merge', phase: 'Merge', schema: MERGE_SCHEMA, agentType: 'general-purpose' }
  )
}

return { authored, green: green.map(g => g.label), merged }
