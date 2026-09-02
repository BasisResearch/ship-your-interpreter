# io_putc_r — mined invariant candidate (invgen.py)

- cluster: `io-loop-fold`  entry: `0x8000e6a4`
- target field: `TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts`
- verdict: **mining-silent-needs-LLM**


## invgen machine-loop pass (wave 45, 2026-09-02)

- verdict: **unreachable — no machine-loop trace path; 0x8000e6a4 dead on every print driver (interp bypasses buffered putc)**
