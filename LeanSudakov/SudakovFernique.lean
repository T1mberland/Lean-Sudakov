import LeanSudakov.Deterministic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem le_of_forall_pos_le_add_div
    {a b c : ℝ}
    (h : ∀ β : ℝ, 0 < β → a ≤ b + c / β) :
    a ≤ b := by
  by_contra hab
  have hba : b < a := lt_of_not_ge hab
  let ε : ℝ := (a - b) / 2
  have hε : 0 < ε := div_pos (sub_pos.2 hba) zero_lt_two
  obtain ⟨n : ℕ, hn : c / ε < n⟩ := exists_nat_gt (c / ε)
  let β : ℝ := n + 1
  have hβ : 0 < β := by positivity
  have hβ_gt : c / ε < β := by
    exact hn.trans_le (by simp [β])
  have hεβ : c / β < ε := by
    have hmul : c < ε * β := by
      have := (div_lt_iff₀ hε).1 hβ_gt
      simpa [mul_comm] using this
    exact (div_lt_iff₀ hβ).2 (by simpa [mul_comm] using hmul)
  have hmain := h β hβ
  have hbeps : b + ε = a - ε := by
    dsimp [ε]
    ring
  have : a < a := by
    calc
      a ≤ b + c / β := hmain
      _ < b + ε := by gcongr
      _ = a - ε := hbeps
      _ < a := by exact sub_lt_self a hε
  exact (lt_irrefl a this)

/-- Final Sudakov-Fernique reduction from log-sum-exp monotonicity.

The deterministic bounds prove that it is enough to know monotonicity of
`∫ x, lse β x` for every `β > 0`. The later Gaussian interpolation theorem should supply
`hlse_mono` from the Gaussian hypotheses. -/
theorem sudakov_fernique_of_lse_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μY]
    (hmaxX_int : Integrable (fun x => vecMax x) μX)
    (hmaxY_int : Integrable (fun y => vecMax y) μY)
    (hlseX_int : ∀ {β : ℝ}, 0 < β → Integrable (fun x => lse β x) μX)
    (hlseY_int : ∀ {β : ℝ}, 0 < β → Integrable (fun y => lse β y) μY)
    (hlse_mono : ∀ {β : ℝ}, 0 < β →
      ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY) :
    ∫ x, vecMax x ∂μX ≤ ∫ y, vecMax y ∂μY := by
  refine le_of_forall_pos_le_add_div
    (a := ∫ x, vecMax x ∂μX)
    (b := ∫ y, vecMax y ∂μY)
    (c := Real.log (Fintype.card ι))
    ?_
  intro β hβ
  calc
    ∫ x, vecMax x ∂μX
        ≤ ∫ x, lse β x ∂μX := by
      exact integral_mono hmaxX_int (hlseX_int hβ) (fun x => vecMax_le_lse hβ x)
    _ ≤ ∫ y, lse β y ∂μY := hlse_mono hβ
    _ ≤ ∫ y, (vecMax y + Real.log (Fintype.card ι) / β) ∂μY := by
      exact integral_mono (hlseY_int hβ) (hmaxY_int.add (integrable_const _))
        (fun y => lse_le_vecMax_add hβ y)
    _ = ∫ y, vecMax y ∂μY + Real.log (Fintype.card ι) / β := by
      rw [integral_add hmaxY_int (integrable_const _), integral_const]
      simp

/-- Gaussian-shaped finite Sudakov-Fernique statement, reduced to the still-missing
Gaussian interpolation monotonicity for `lse`.

Once `gaussian_interpolation_lse_mono` is available, `hlse_mono` should be discharged by that
lemma, and the remaining integrability hypotheses should follow from Fernique/moment bounds for
finite-dimensional Gaussian measures. -/
theorem sudakov_fernique_of_gaussian_interpolation
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [ProbabilityTheory.IsGaussian μX] [ProbabilityTheory.IsGaussian μY]
    (_hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (_hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (_hinc : ∀ i j,
      ProbabilityTheory.variance (fun x : ι → ℝ => x i - x j) μX
        ≤ ProbabilityTheory.variance (fun y : ι → ℝ => y i - y j) μY)
    (hmaxX_int : Integrable (fun x => vecMax x) μX)
    (hmaxY_int : Integrable (fun y => vecMax y) μY)
    (hlseX_int : ∀ {β : ℝ}, 0 < β → Integrable (fun x => lse β x) μX)
    (hlseY_int : ∀ {β : ℝ}, 0 < β → Integrable (fun y => lse β y) μY)
    (hlse_mono : ∀ {β : ℝ}, 0 < β →
      ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY) :
    ∫ x, vecMax x ∂μX ≤ ∫ y, vecMax y ∂μY := by
  exact sudakov_fernique_of_lse_mono μX μY
    hmaxX_int hmaxY_int hlseX_int hlseY_int hlse_mono

-- TODO: Prove Gaussian interpolation for `lse`, then use it to remove `hlse_mono`
-- from `sudakov_fernique_of_gaussian_interpolation`.

end
