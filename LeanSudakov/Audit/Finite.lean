import LeanSudakov.SudakovFernique
import LeanSudakov.SudakovFerniqueDrift

-- Audit the completed finite theorem for unexpected axioms, especially `sorryAx`.
/--
info: 'sudakov_fernique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sudakov_fernique

/--
info: 'gaussian_interpolation_lse_mono_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms gaussian_interpolation_lse_mono_drift

/--
info: 'sudakov_fernique_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sudakov_fernique_drift
