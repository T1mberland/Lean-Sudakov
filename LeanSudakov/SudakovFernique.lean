import LeanSudakov.Deterministic
import LeanSudakov.GaussianVectorIBP
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The linear interpolation map
`(x, y) ↦ sqrt (1 - t) • x + sqrt t • y` used in the Gaussian interpolation argument. -/
noncomputable def gaussianInterpMap
    {ι : Type*} (t : ℝ) :
    ((ι → ℝ) × (ι → ℝ)) →L[ℝ] (ι → ℝ) :=
  Real.sqrt (1 - t) • ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) +
    Real.sqrt t • ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)

@[simp]
theorem gaussianInterpMap_apply
    {ι : Type*} (t : ℝ) (p : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    gaussianInterpMap (ι := ι) t p i =
      Real.sqrt (1 - t) * p.1 i + Real.sqrt t * p.2 i := by
  simp [gaussianInterpMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The Gaussian interpolation measure, realized as a linear image of the independent product
coupling of the endpoint laws. -/
noncomputable def gaussianInterpMeasure
    {ι : Type*} (μX μY : Measure (ι → ℝ)) (t : ℝ) : Measure (ι → ℝ) :=
  (μX.prod μY).map (gaussianInterpMap (ι := ι) t)

/-- The expected log-sum-exp along the Gaussian interpolation path. -/
noncomputable def gaussianInterpolationLSE
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ)) (β t : ℝ) : ℝ :=
  ∫ z, lse β z ∂gaussianInterpMeasure μX μY t

@[simp]
theorem gaussianInterpMap_zero
    {ι : Type*} :
    gaussianInterpMap (ι := ι) 0 = ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ) := by
  apply ContinuousLinearMap.ext
  intro p
  ext i
  simp [gaussianInterpMap]

@[simp]
theorem gaussianInterpMap_one
    {ι : Type*} :
    gaussianInterpMap (ι := ι) 1 = ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ) := by
  apply ContinuousLinearMap.ext
  intro p
  ext i
  simp [gaussianInterpMap]

@[simp]
theorem gaussianInterpMeasure_zero
    {ι : Type*} (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] :
    gaussianInterpMeasure μX μY 0 = μX := by
  rw [gaussianInterpMeasure, gaussianInterpMap_zero]
  change Measure.map Prod.fst (μX.prod μY) = μX
  rw [Measure.map_fst_prod]
  simp [measure_univ]

@[simp]
theorem gaussianInterpMeasure_one
    {ι : Type*} (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] :
    gaussianInterpMeasure μX μY 1 = μY := by
  rw [gaussianInterpMeasure, gaussianInterpMap_one]
  change Measure.map Prod.snd (μX.prod μY) = μY
  rw [Measure.map_snd_prod]
  simp [measure_univ]

@[simp]
theorem gaussianInterpolationLSE_zero
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (β : ℝ) :
    gaussianInterpolationLSE μX μY β 0 = ∫ x, lse β x ∂μX := by
  simp [gaussianInterpolationLSE]

@[simp]
theorem gaussianInterpolationLSE_one
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY] (β : ℝ) :
    gaussianInterpolationLSE μX μY β 1 = ∫ y, lse β y ∂μY := by
  simp [gaussianInterpolationLSE]

/-- Real-analysis bridge for Gaussian interpolation.

If an interpolation functional `F` connects the two log-sum-exp expectations and has nonnegative
derivative on the open interpolation interval, then the desired log-sum-exp comparison follows.

The remaining Gaussian interpolation work is to construct such an `F` from the centered Gaussian
pair and prove the derivative formula/sign using `gaussian_ibp_softmax` and
`softmax_hessian_cov_contraction_nonneg_of_variance_le`. -/
theorem gaussian_interpolation_lse_mono_of_deriv_nonneg
    {ι : Type*} [Fintype ι]
    (μX μY : Measure (ι → ℝ)) (β : ℝ)
    (F : ℝ → ℝ)
    (hF0 : F 0 = ∫ x, lse β x ∂μX)
    (hF1 : F 1 = ∫ y, lse β y ∂μY)
    (hFcont : ContinuousOn F (Set.Icc 0 1))
    (hFdiff : DifferentiableOn ℝ F (interior (Set.Icc (0 : ℝ) 1)))
    (hFderiv_nonneg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ deriv F t) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
  have hmono : MonotoneOn F (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hFcont ?_ ?_
    · intro t ht
      exact hFdiff t ht
    · intro t ht
      exact hFderiv_nonneg t (by simpa using ht)
  calc
    ∫ x, lse β x ∂μX = F 0 := hF0.symm
    _ ≤ F 1 := hmono (by norm_num) (by norm_num) (by norm_num)
    _ = ∫ y, lse β y ∂μY := hF1

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
lemma. The integrability hypotheses in `sudakov_fernique_of_lse_mono` are discharged by the
finite-dimensional Gaussian moment bounds in `GaussianVectorIBP`. -/
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
    (hlse_mono : ∀ {β : ℝ}, 0 < β →
      ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY) :
    ∫ x, vecMax x ∂μX ≤ ∫ y, vecMax y ∂μY := by
  exact sudakov_fernique_of_lse_mono μX μY
    (gaussian_integrable_vecMax μX) (gaussian_integrable_vecMax μY)
    (fun {_β} hβ => gaussian_integrable_lse μX hβ)
    (fun {_β} hβ => gaussian_integrable_lse μY hβ)
    hlse_mono

-- TODO: Prove Gaussian interpolation for `lse`, then use it to remove `hlse_mono`.

end
