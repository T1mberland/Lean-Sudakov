import LeanSudakov.SudakovFernique
import LeanSudakov.SudakovFerniqueDrift

namespace LeanSudakov.Audit

/--
info: 'LeanSudakov.gaussian_ibp_softmax' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.gaussian_ibp_softmax

/--
info: 'LeanSudakov.gaussian_ibp_softmax_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.gaussian_ibp_softmax_affine

/--
info: 'LeanSudakov.gaussian_interpolation_lse_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.gaussian_interpolation_lse_mono

-- Audit the completed finite theorem for unexpected axioms, especially `sorryAx`.
/--
info: 'LeanSudakov.sudakov_fernique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.sudakov_fernique

/--
info: 'LeanSudakov.gaussian_interpolation_lse_mono_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.gaussian_interpolation_lse_mono_drift

/--
info: 'LeanSudakov.sudakov_fernique_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanSudakov.sudakov_fernique_drift

end LeanSudakov.Audit
