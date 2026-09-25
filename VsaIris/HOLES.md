# IrisHoles ledger

Every assumption left in the Iris route is a field of `structure IrisHoles` and has a row here. `scripts/check_iris_holes.py` checks the two agree. A hole is discharged by proving the field and deleting both the field and its row in the same commit.

| field | what it assumes | owner | satisfiability evidence | discharge plan |
|---|---|---|---|---|
