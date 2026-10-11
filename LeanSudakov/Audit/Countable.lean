import LeanSudakov.CountableSudakovExtended

open MeasureTheory
open scoped ENNReal

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

/--
info: 'countable_sudakov' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov

/--
info: 'countable_sudakov_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov_lintegral

/--
info: 'lintegral_countableSupGap_anchor_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lintegral_countableSupGap_anchor_independent

/--
info: 'countableExpectedSup_eq_ofReal_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countableExpectedSup_eq_ofReal_integral

-- An unbounded path has a genuinely infinite supremum, rather than the real `sSup` fallback.
example : countableSupGap 0 (fun n : ℕ => (n : ℝ)) = ∞ := by
  simpa [countableSupGap] using ENNReal.iSup_natCast

-- The monotone-convergence integral can likewise be infinite.
example :
    (∫⁻ x, countableSupGap 0 x ∂(Measure.dirac (fun n : ℕ => (n : ℝ)))) = ∞ := by
  rw [lintegral_dirac' _ (measurable_countableSupGap 0)]
  simpa [countableSupGap] using ENNReal.iSup_natCast
