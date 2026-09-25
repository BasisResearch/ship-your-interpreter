# P3 inputs: the call graph of `Vsa.stepOnce`

`Closure.lean` (run from the repository root with `lake env lean
experiments/densify/Closure.lean`) walks the constants used by `Vsa.stepOnce`
through the executable Sail model (`LeanRV64DExecutable`), lean-sail (`Sail`)
and `Vsa`, and writes `closure.tsv`: one line per monadic function (result in
`SailM`/`SailME`/`PreSailM`/`PreSailME`), in dependency order (callees first),
as `name <TAB> arity <TAB> flag <TAB> monadic callees`.

`scripts/gen_resp.py` turns it into `Vsa/Densify/Gen{A,B,C}.lean` (one `Resp`
theorem per function, `unfold` + `resp_auto`); the recursive groups
(`currentlyEnabled`'s mutual block, `pt_walk`) are proved by hand in
`Vsa/Densify/RecMutual.lean` and `RecPt.lean`. `scripts/check_all.sh` stage a3
checks the generated files against `closure.tsv`.

Regenerate `closure.tsv` whenever the model or `Vsa/Elf.lean` changes.
