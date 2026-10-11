import LeanSudakov.CountableSudakov

-- Audit the countable extension and its finite-projection entry point for unexpected axioms.
/--
info: 'countable_sudakov_of_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov_of_finset

/--
info: 'countable_sudakov_of_projected_gaussian'' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov_of_projected_gaussian'
