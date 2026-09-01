# Residual dashboard

A zero-build, single-page d3 dashboard that live-polls `experiments/residuals.tsv` (every 5s) and shows headline counts, a burn-down of open residuals per wave, per-wave created-vs-closed flow, and open residuals grouped by class (classes with ≥3 open instances and no generator are flagged as combinator/generator candidates).

Start: `./tools/residual_dashboard/serve.sh` then open http://localhost:8642/tools/residual_dashboard/ (serves the repo root so the page can fetch `/experiments/residuals.tsv` same-origin).

TSV contract: tab-separated, header `id class status created_wave closed_wave description` (+ optional 7th column `gen`). `status` ∈ {open, closed}; `created_wave` always an integer; `closed_wave` an integer iff closed. Optional `gen` ∈ {yes, no, ""} marks whether a class already has a generator/combinator (any `gen=yes` row marks its whole class; missing/empty = no); the coordinator just appends/edits rows and the dashboard re-reads live.
