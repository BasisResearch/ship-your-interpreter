import VsaIris.Interp.BinArm
import VsaIris.Interp.ErrArm
import VsaIris.Interp.ProofValueKindName
import VsaIris.Interp.Case.BinaryLtIntT
import VsaIris.Interp.Case.BinaryLeIntT
import VsaIris.Interp.Case.BinaryGtIntT
import VsaIris.Interp.Case.BinaryGeIntT
import VsaIris.Interp.Case.BinaryEqT
import VsaIris.Interp.Case.BinaryNeT
import VsaIris.Interp.Case.BinaryEqP
import VsaIris.Interp.Case.BinaryNeP
import VsaIris.Interp.Case.BinarySubP
import VsaIris.Interp.Case.BinaryLtStrT
import VsaIris.Interp.Case.BinaryLeStrT
import VsaIris.Interp.Case.BinaryGtStrT
import VsaIris.Interp.Case.BinaryGeStrT
import VsaIris.Interp.Case.BinaryLtP
import VsaIris.Interp.Case.BinaryLeP
import VsaIris.Interp.Case.BinaryGtP
import VsaIris.Interp.Case.BinaryGeP

/-!
# Lane E2's cases (the binary operators), in the build

INTERP_DESIGN.md §8 family E2. Rows: `scripts/iris_arms/arms.d/e2-binary.tsv`;
families: `scripts/iris_arms/families/e2_binary.py`; status: `LANE.md`.
-/
