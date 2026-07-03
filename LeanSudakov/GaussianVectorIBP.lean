import LeanSudakov.Deterministic
import LeanSudakov.GaussianIBP
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.CovarianceBilinDual

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- The `i`-th coordinate projection as a continuous linear map. -/
def coordCLM {ι : Type*} (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

@[simp]
theorem coordCLM_apply {ι : Type*} (i : ι) (x : ι → ℝ) :
    coordCLM i x = x i := rfl

/-- Softmax is continuous as a function on finite-dimensional Euclidean coordinate space. -/
theorem continuous_softmax
    {ι : Type*} [Fintype ι]
    (β : ℝ) (i : ι) :
    Continuous fun x : ι → ℝ => softmax β x i := by
  refine Continuous.div ?_ ?_ ?_
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))
  · exact continuous_finset_sum Finset.univ fun k _ =>
      Real.continuous_exp.comp (continuous_const.mul (continuous_apply k))
  · intro x
    exact (softmax_den_pos β x i).ne'

theorem aestronglyMeasurable_softmax
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) (i : ι) :
    AEStronglyMeasurable (fun x : ι → ℝ => softmax β x i) μ :=
  (continuous_softmax β i).aestronglyMeasurable

theorem memLp_top_softmax
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) (i : ι) :
    MemLp (fun x : ι → ℝ => softmax β x i) ∞ μ := by
  refine memLp_top_of_bound (aestronglyMeasurable_softmax μ β i) 1 ?_
  exact ae_of_all μ fun x => by
    simpa [Real.norm_eq_abs] using abs_softmax_le_one β x i

theorem integrable_softmax
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (β : ℝ) (i : ι) :
    Integrable (fun x : ι → ℝ => softmax β x i) μ := by
  refine Integrable.of_bound (aestronglyMeasurable_softmax μ β i) 1 ?_
  exact ae_of_all μ fun x => by
    simpa [Real.norm_eq_abs] using abs_softmax_le_one β x i

/-- The softmax Hessian entry appearing in the `j`-coordinate derivative of
`softmax β · i` is continuous. -/
theorem continuous_softmax_deriv_term
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (i j : ι) :
    Continuous fun x : ι → ℝ =>
      β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j) := by
  by_cases hij : i = j
  · simpa [hij] using
      continuous_const.mul
        ((continuous_softmax β i).sub ((continuous_softmax β i).mul (continuous_softmax β j)))
  · simpa [hij] using
      (continuous_const.mul ((continuous_softmax β i).mul (continuous_softmax β j))).neg

theorem aestronglyMeasurable_softmax_deriv_term
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) (i j : ι) :
    AEStronglyMeasurable
      (fun x : ι → ℝ =>
        β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j))
      μ :=
  (continuous_softmax_deriv_term β i j).aestronglyMeasurable

theorem abs_softmax_deriv_term_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i j : ι) :
    |β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j)|
      ≤ |β| * 2 := by
  have ha :
      |(if i = j then softmax β x i else 0)| ≤ 1 := by
    by_cases hij : i = j
    · simpa [hij] using abs_softmax_le_one β x i
    · simp [hij]
  have hb : |softmax β x i * softmax β x j| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ (abs_softmax_le_one β x i)
      (abs_nonneg _) (abs_softmax_le_one β x j)
  calc
    |β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j)|
        = |β| * |(if i = j then softmax β x i else 0) - softmax β x i * softmax β x j| := by
          rw [abs_mul]
    _ ≤ |β| * (|(if i = j then softmax β x i else 0)| + |softmax β x i * softmax β x j|) := by
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg β)
    _ ≤ |β| * 2 := by
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg β)

theorem integrable_softmax_deriv_term
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ] (β : ℝ) (i j : ι) :
    Integrable
      (fun x : ι → ℝ =>
        β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j))
      μ := by
  refine Integrable.of_bound (aestronglyMeasurable_softmax_deriv_term μ β i j) (|β| * 2) ?_
  exact ae_of_all μ fun x => by
    simpa [Real.norm_eq_abs] using abs_softmax_deriv_term_le β x i j

theorem integrable_coord_mul_softmax_of_integrable_coord
    {ι : Type*} [Fintype ι]
    {μ : Measure (ι → ℝ)} {β : ℝ} {i j : ι}
    (hi : Integrable (fun x : ι → ℝ => x i) μ) :
    Integrable (fun x : ι → ℝ => x i * softmax β x j) μ := by
  simpa [Pi.mul_apply] using hi.mul_of_top_left (memLp_top_softmax μ β j)

theorem gaussian_integrable_coord
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (i : ι) :
    Integrable (fun x : ι → ℝ => x i) μ := by
  simpa [coordCLM] using IsGaussian.integrable_dual μ (coordCLM i)

theorem gaussian_integrable_coord_mul_softmax
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (β : ℝ) (i j : ι) :
    Integrable (fun x : ι → ℝ => x i * softmax β x j) μ :=
  integrable_coord_mul_softmax_of_integrable_coord
    (gaussian_integrable_coord μ i)

/-- Coordinate covariance matrix of a finite-dimensional Gaussian measure. -/
def gaussianCov {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (i j : ι) : ℝ :=
  covarianceBilinDual μ (coordCLM i) (coordCLM j)

/-- A finite-dimensional Gaussian measure has finite second moment as a vector-valued random
variable. -/
theorem gaussian_memLp_id_two
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] :
    MemLp (id : (ι → ℝ) → (ι → ℝ)) 2 μ := by
  rw [memLp_pi_iff]
  intro i
  simpa [Function.comp_def, coordCLM] using
    (IsGaussian.memLp_dual μ (coordCLM i) 2 (by simp))

/-- The coordinate covariance matrix agrees with scalar covariance. -/
theorem gaussianCov_eq_covariance
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (i j : ι) :
    gaussianCov μ i j = cov[(fun x : ι → ℝ => x i), (fun x : ι → ℝ => x j); μ] := by
  rw [gaussianCov]
  exact covarianceBilinDual_eq_covariance (gaussian_memLp_id_two μ) (coordCLM i) (coordCLM j)

/-- The coordinate covariance matrix as a centered second moment. -/
theorem gaussianCov_eq_integral_centered_mul
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (i j : ι) :
    gaussianCov μ i j =
      ∫ x, (x i - ∫ y, y i ∂μ) * (x j - ∫ y, y j ∂μ) ∂μ := by
  rw [gaussianCov]
  simpa [coordCLM] using
    (covarianceBilinDual_apply (gaussian_memLp_id_two μ) (coordCLM i) (coordCLM j))

/-- For a centered finite-dimensional Gaussian, coordinate covariance is the raw second moment. -/
theorem gaussianCov_eq_integral_mul_of_centered
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hμ0 : ∀ i, ∫ x, x i ∂μ = 0) (i j : ι) :
    gaussianCov μ i j = ∫ x, x i * x j ∂μ := by
  rw [gaussianCov_eq_integral_centered_mul μ i j]
  simp [hμ0]

/-- The vector Gaussian integration-by-parts formula for linear coordinate test functions.

This is the checked finite-dimensional Stein base case. The remaining nonlinear Stein lemma should
replace the Kronecker delta here by the coordinate derivatives of a smooth test function. -/
theorem gaussian_ibp_linear_coord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hμ0 : ∀ i, ∫ x, x i ∂μ = 0) (i j : ι) :
    ∫ x, x i * x j ∂μ =
      Finset.univ.sum fun k => gaussianCov μ i k * (if j = k then 1 else 0) := by
  rw [← gaussianCov_eq_integral_mul_of_centered μ hμ0 i j]
  symm
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk.symm]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

-- TODO: Prove the full finite-dimensional Gaussian Stein identity:
--
--   ∫ x, x i * f x ∂μ =
--     ∑ j, gaussianCov μ i j * ∫ x, ∂ⱼ f x ∂μ
--
-- for centered Gaussian `μ : Measure (ι → ℝ)` and sufficiently smooth/integrable `f`.
-- The theorem above proves this identity for the linear coordinate test function `f x = x j`.

end
