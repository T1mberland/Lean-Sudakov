import LeanSudakov.CountableSudakovDrift

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

/--
info: 'countable_sudakov_drift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov_drift

/--
info: 'countable_sudakov_drift_lintegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countable_sudakov_drift_lintegral

/--
info: 'countableExpectedSupDrift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countableExpectedSupDrift_eq

/--
info: 'countableExpectedSupDrift_anchor_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countableExpectedSupDrift_anchor_independent

/--
info: 'countableExpectedSupEReal_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countableExpectedSupEReal_eq_integral

/--
info: 'countableExpectedSupDrift_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms countableExpectedSupDrift_zero

-- An unbounded path has a genuinely infinite supremum, rather than the real `sSup` fallback.
example : countableSupGap 0 (fun n : ℕ => (n : ℝ)) = ∞ := by
  simpa [countableSupGap] using ENNReal.iSup_natCast

-- The monotone-convergence integral can likewise be infinite.
example :
    (∫⁻ x, countableSupGap 0 x ∂(Measure.dirac (fun n : ℕ => (n : ℝ)))) = ∞ := by
  rw [lintegral_dirac' _ (measurable_countableSupGap 0)]
  simpa [countableSupGap] using ENNReal.iSup_natCast

-- A negative deterministic drift must retain its negative expected supremum.
example : countableExpectedSupDrift (fun _ : Unit => (-3 : ℝ))
    (Measure.dirac (0 : Unit → ℝ)) = (-3 : EReal) := by
  rw [countableExpectedSupDrift_eq _ _ () (fun _ => integrable_dirac (by simp)) (by simp)]
  rw [lintegral_dirac' (0 : Unit → ℝ)
    (f := fun x => countableSupGap () ((fun _ : Unit => (-3 : ℝ)) + x))
    ((measurable_countableSupGap ()).comp (measurable_const.add measurable_id))]
  simp [countableSupGap]
  rfl

-- No boundedness assumption on the drift is needed; an unbounded drift gives `+∞`.
example : countableExpectedSupDrift (fun n : ℕ => (n : ℝ))
    (Measure.dirac (0 : ℕ → ℝ)) = ⊤ := by
  rw [countableExpectedSupDrift_eq _ _ 0 (fun _ => integrable_dirac (by simp)) (by simp)]
  rw [lintegral_dirac' (0 : ℕ → ℝ)
    (f := fun x => countableSupGap 0 ((fun n : ℕ => (n : ℝ)) + x))
    ((measurable_countableSupGap 0).comp (measurable_const.add measurable_id))]
  simp [countableSupGap, ENNReal.iSup_natCast]
