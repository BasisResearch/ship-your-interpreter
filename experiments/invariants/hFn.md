# hFn — mined invariant candidate (invgen.py)

- cluster: `str-seam`  entry: `0x800033c4`
- target field: `TermResidualsCore.hFn`
- verdict: **candidate-mined+SURVIVED**

## Mined conjuncts (T1-T5)

```
# mine — 43 events in 1 segments, vocab=['a0', 'a1', 'a2', 'a3', 'a4', 'a5', 'ra', 's0', 's1', 's2', 'sp']

== MINED CANDIDATE CONJUNCTS (intersection across segments) ==
  * T1 m0b1 : per-call constant
  * T1 m0b2 : per-call constant
  * T1 m0b3 : per-call constant
  * T2 m0b0 = m0b1 + 9   (entry offset)
  * T2 m0b0 = m0b2 + 9   (entry offset)
  * T2 m0b0 = m0b3 + 9   (entry offset)
  * T2 m0b1 = m0b0 + -9   (entry offset)
  * T2 m0b1 = m0b2 + m0b3   (entry linear)
  * T2 m0b2 = m0b0 + -9   (entry offset)
  * T2 m0b2 = m0b1 + m0b3   (entry linear)
  * T2 m0b3 = m0b0 + -9   (entry offset)
  * T2 m0b3 = m0b1 + m0b2   (entry linear)
  * T5 m0b1 = 0x0   (mem-window constant / slot pin)
  * T5 m0b2 = 0x0   (mem-window constant / slot pin)
  * T5 m0b3 = 0x0   (mem-window constant / slot pin)

```

## Relational (machine×spec) conjuncts

```
# mine_relational — hFn (expr side)

machine dispatch events: 43   spec events: 52

kind | name     | machine cnt | spec cnt | agree
-----+----------+-------------+----------+------
   0 | int      |          2  |       2  | YES
   1 | str      |         15  |      15  | YES
   4 | var      |         10  |      10  | YES
   6 | binary   |          8  |       8  | YES
   9 | call     |          8  |       8  | YES

== MINED RELATIONAL CONJUNCTS (per-seam ordinal alignment) ==
  * read32[node] & 0xff = 0 = kindOfExpr (.int)  [machine 2 = spec 2]  MATCH
  * read32[node] & 0xff = 1 = kindOfExpr (.str)  [machine 15 = spec 15]  MATCH
  * read32[node] & 0xff = 4 = kindOfExpr (.var)  [machine 10 = spec 10]  MATCH
  * read32[node] & 0xff = 6 = kindOfExpr (.binary)  [machine 8 = spec 8]  MATCH
  * read32[node] & 0xff = 9 = kindOfExpr (.call)  [machine 8 = spec 8]  MATCH

== SUMMARY ==
kinds agreeing (machine==spec count): ['int', 'str', 'var', 'binary', 'call']
VERDICT: candidate-mined

```
