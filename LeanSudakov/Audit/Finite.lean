import LeanSudakov.SudakovFernique

-- Audit the completed finite theorem for unexpected axioms, especially `sorryAx`.
/--
info: 'sudakov_fernique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sudakov_fernique
