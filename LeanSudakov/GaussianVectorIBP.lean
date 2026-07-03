import LeanSudakov.Deterministic
import LeanSudakov.GaussianIBP
import LeanSudakov.LSECalculus
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Order.Lattice
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Moments.CovarianceBilinDual
import Mathlib.Probability.Moments.Variance

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

/-- The first Gaussian density moment is integrable against Lebesgue measure. -/
theorem integrable_gaussianPDFReal_mul_id
    (m : ℝ) (v : ℝ≥0) :
    Integrable (fun t : ℝ => gaussianPDFReal m v t * t) := by
  by_cases hv : v = 0
  · simp [hv, gaussianPDFReal_zero_var]
  have hid : Integrable (fun t : ℝ => t) (gaussianReal m v) := by
    simpa [id] using
      (memLp_one_iff_integrable.mp
        (memLp_id_gaussianReal' (μ := m) (v := v) 1 (by simp)))
  rw [gaussianReal_of_var_ne_zero m hv] at hid
  have h :=
    (integrable_withDensity_iff_integrable_smul'
      (μ := volume) (f := gaussianPDF m v) (g := fun t : ℝ => t)
      (measurable_gaussianPDF m v)
      (ae_of_all _ fun _ => gaussianPDF_lt_top)).1 hid
  simpa [gaussianPDF, smul_eq_mul] using h

private theorem memLp_top_softmax_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i j : ι) :
    MemLp (fun t : ℝ => softmax β (Function.update x i t) j) ∞ volume := by
  have hcont : Continuous fun t : ℝ => softmax β (Function.update x i t) j :=
    (continuous_softmax β j).comp (continuous_const.update i continuous_id)
  refine memLp_top_of_bound hcont.aestronglyMeasurable 1 ?_
  exact ae_of_all _ fun t => by
    simpa [Real.norm_eq_abs] using abs_softmax_le_one β (Function.update x i t) j

private theorem memLp_top_softmax_deriv_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i j : ι) :
    MemLp
      (fun t : ℝ =>
        β * ((if j = i then softmax β (Function.update x i t) j else 0) -
          softmax β (Function.update x i t) j *
            softmax β (Function.update x i t) i))
      ∞ volume := by
  have hcont : Continuous fun t : ℝ =>
      β * ((if j = i then softmax β (Function.update x i t) j else 0) -
        softmax β (Function.update x i t) j *
          softmax β (Function.update x i t) i) :=
    (continuous_softmax_deriv_term β j i).comp (continuous_const.update i continuous_id)
  refine memLp_top_of_bound hcont.aestronglyMeasurable (|β| * 2) ?_
  exact ae_of_all _ fun t => by
    simpa [Real.norm_eq_abs] using
      abs_softmax_deriv_term_le β (Function.update x i t) j i

/-- One-dimensional Gaussian Stein identity for a softmax coordinate slice.

This is the coordinate-wise analytic input supplied by the one-dimensional Gaussian integration by
parts theorem. It does not yet assemble the full finite-dimensional arbitrary-covariance Stein
identity. -/
theorem gaussianReal_ibp_softmax_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v : ℝ≥0} (hv : v ≠ 0) (β : ℝ) (x : ι → ℝ) (i j : ι) :
    ∫ t, t * softmax β (Function.update x i t) j ∂gaussianReal 0 v =
      (v : ℝ) *
        ∫ t,
          β * ((if j = i then softmax β (Function.update x i t) j else 0) -
            softmax β (Function.update x i t) j *
              softmax β (Function.update x i t) i) ∂gaussianReal 0 v := by
  have hf : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => softmax β (Function.update x i s) j)
        (β * ((if j = i then softmax β (Function.update x i t) j else 0) -
          softmax β (Function.update x i t) j *
            softmax β (Function.update x i t) i)) t := by
    intro t
    simpa using
      (hasDerivAt_softmax_update β (Function.update x i t) j i)
  have h_deriv :
      Integrable
        (fun t : ℝ =>
          gaussianPDFReal 0 v t *
            (β * ((if j = i then softmax β (Function.update x i t) j else 0) -
              softmax β (Function.update x i t) j *
                softmax β (Function.update x i t) i))) := by
    exact (integrable_gaussianPDFReal 0 v).mul_of_top_right
      (memLp_top_softmax_deriv_update β x i j)
  have h_center_base :
      Integrable (fun t : ℝ => -(t - 0) / (v : ℝ) * gaussianPDFReal 0 v t) := by
    have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
    have h := (integrable_gaussianPDFReal_mul_id 0 v).const_mul (-(1 / (v : ℝ)))
    convert h using 1
    ext t
    field_simp [hv']
    ring
  have h_center_deriv :
      Integrable
        (fun t : ℝ =>
          (-(t - 0) / (v : ℝ) * gaussianPDFReal 0 v t) *
            softmax β (Function.update x i t) j) := by
    exact h_center_base.mul_of_top_right (memLp_top_softmax_update β x i j)
  have h_prod :
      Integrable
        (fun t : ℝ => gaussianPDFReal 0 v t *
          softmax β (Function.update x i t) j) := by
    exact (integrable_gaussianPDFReal 0 v).mul_of_top_right
      (memLp_top_softmax_update β x i j)
  simpa using
    (gaussianReal_integral_centered_mul_eq_var_mul_integral_deriv
      (μ := 0) (v := v) hv
      (f := fun t : ℝ => softmax β (Function.update x i t) j)
      (f' := fun t : ℝ =>
        β * ((if j = i then softmax β (Function.update x i t) j else 0) -
          softmax β (Function.update x i t) j *
            softmax β (Function.update x i t) i))
      hf h_deriv h_center_deriv h_prod)

/-- Centered one-dimensional Gaussian Stein identity for a softmax coordinate slice, including the
degenerate variance case. -/
theorem gaussianReal_ibp_softmax_update_centered
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ℝ≥0) (β : ℝ) (x : ι → ℝ) (i j : ι) :
    ∫ t, t * softmax β (Function.update x i t) j ∂gaussianReal 0 v =
      (v : ℝ) *
        ∫ t,
          β * ((if j = i then softmax β (Function.update x i t) j else 0) -
            softmax β (Function.update x i t) j *
              softmax β (Function.update x i t) i) ∂gaussianReal 0 v := by
  by_cases hv : v = 0
  · subst v
    simp
  · exact gaussianReal_ibp_softmax_update hv β x i j

/-- The product of centered one-dimensional Gaussian measures is Gaussian. -/
theorem isGaussian_pi_gaussianReal_centered
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ≥0) :
    IsGaussian (Measure.pi fun i => gaussianReal 0 (v i)) := by
  classical
  let μ : ι → Measure ℝ := fun i => gaussianReal 0 (v i)
  have hcoord : ∀ i, HasGaussianLaw (fun x : ι → ℝ => x i) (Measure.pi μ) := by
    intro i
    exact HasLaw.hasGaussianLaw
      (MeasurePreserving.hasLaw (measurePreserving_eval μ i))
  have hindep : iIndepFun (fun i (x : ι → ℝ) => x i) (Measure.pi μ) := by
    simpa [μ] using
      (iIndepFun_pi (μ := μ) (X := fun _ : ι => id)
        (fun _ => measurable_id.aemeasurable))
  have hjoint := iIndepFun.hasGaussianLaw hcoord hindep
  simpa [μ, Function.comp_def] using hjoint.isGaussian_map

/-- Coordinates of the centered product Gaussian have the prescribed variances. -/
theorem variance_pi_gaussianReal_centered_coord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ≥0) (i : ι) :
    variance (fun x : ι → ℝ => x i) (Measure.pi fun k => gaussianReal 0 (v k)) =
      (v i : ℝ) := by
  let μ : ι → Measure ℝ := fun k => gaussianReal 0 (v k)
  have hmp : MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) :=
    measurePreserving_eval μ i
  rw [hmp.variance_fun_comp (f := id) measurable_id.aemeasurable]
  simp [μ]

/-- Coordinate covariance matrix of an independent centered Gaussian product measure. -/
theorem gaussianCov_pi_gaussianReal_centered
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℝ≥0) (i j : ι) :
    letI : IsGaussian (Measure.pi fun k => gaussianReal 0 (v k)) :=
      isGaussian_pi_gaussianReal_centered v
    gaussianCov (Measure.pi fun k => gaussianReal 0 (v k)) i j =
      if i = j then (v i : ℝ) else 0 := by
  classical
  let μ : ι → Measure ℝ := fun k => gaussianReal 0 (v k)
  letI : IsGaussian (Measure.pi μ) := isGaussian_pi_gaussianReal_centered v
  have hcoord_memLp (k : ι) :
      MemLp (fun x : ι → ℝ => x k) 2 (Measure.pi μ) := by
    simpa [μ, coordCLM] using
      IsGaussian.memLp_dual (Measure.pi μ) (coordCLM k) 2 (by simp)
  by_cases hij : i = j
  · subst j
    rw [gaussianCov_eq_covariance]
    rw [covariance_self (hcoord_memLp i).aemeasurable]
    simp [variance_pi_gaussianReal_centered_coord, μ]
  · rw [gaussianCov_eq_covariance]
    have hindep : iIndepFun (fun k (x : ι → ℝ) => x k) (Measure.pi μ) := by
      simpa [μ] using
        (iIndepFun_pi (μ := μ) (X := fun _ : ι => id)
          (fun _ => measurable_id.aemeasurable))
    have hpair : (fun x : ι → ℝ => x i) ⟂ᵢ[Measure.pi μ] (fun x : ι → ℝ => x j) :=
      hindep.indepFun hij
    rw [hpair.covariance_eq_zero (hcoord_memLp i) (hcoord_memLp j)]
    simp [hij, μ]

theorem measurable_vecMax
    {ι : Type*} [Fintype ι] [Nonempty ι] :
    Measurable fun x : ι → ℝ => vecMax x := by
  have h : Measurable
      ((Finset.univ : Finset ι).sup' Finset.univ_nonempty
        (fun i => fun x : ι → ℝ => x i)) :=
    Finset.measurable_sup'
    (s := (Finset.univ : Finset ι)) Finset.univ_nonempty
    (f := fun i => fun x : ι → ℝ => x i)
    (fun i _ => measurable_pi_apply i)
  convert h using 1
  ext x
  simp [vecMax]

theorem aestronglyMeasurable_vecMax
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) :
    AEStronglyMeasurable (fun x : ι → ℝ => vecMax x) μ :=
  measurable_vecMax.aestronglyMeasurable

theorem measurable_lse
    {ι : Type*} [Fintype ι]
    (β : ℝ) :
    Measurable fun x : ι → ℝ => lse β x := by
  change Measurable fun x : ι → ℝ =>
    Real.log ((Finset.univ).sum fun i => Real.exp (β * x i)) / β
  exact (Real.measurable_log.comp
    (Finset.measurable_sum (s := (Finset.univ : Finset ι)) fun i _ =>
      Real.measurable_exp.comp (measurable_const.mul (measurable_pi_apply i)))).div_const β

theorem aestronglyMeasurable_lse
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) :
    AEStronglyMeasurable (fun x : ι → ℝ => lse β x) μ :=
  (measurable_lse β).aestronglyMeasurable

theorem gaussian_integrable_sum_abs_coord
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] :
    Integrable (fun x : ι → ℝ => (Finset.univ).sum fun i => |x i|) μ :=
  integrable_finset_sum (s := (Finset.univ : Finset ι)) fun i _ =>
    (gaussian_integrable_coord μ i).abs

theorem gaussian_integrable_vecMax
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] :
    Integrable (fun x : ι → ℝ => vecMax x) μ := by
  refine Integrable.mono' (gaussian_integrable_sum_abs_coord μ)
    (aestronglyMeasurable_vecMax μ) ?_
  exact ae_of_all μ fun x => by
    simpa [Real.norm_eq_abs] using abs_vecMax_le_sum_abs x

theorem gaussian_integrable_lse
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ι → ℝ => lse β x) μ := by
  let c : ℝ := Real.log (Fintype.card ι) / β
  have hbound_int : Integrable (fun x : ι → ℝ => (Finset.univ).sum (fun i => |x i|) + c) μ :=
    (gaussian_integrable_sum_abs_coord μ).add (integrable_const c)
  refine Integrable.mono' hbound_int (aestronglyMeasurable_lse μ β) ?_
  exact ae_of_all μ fun x => by
    simpa [Real.norm_eq_abs, c] using abs_lse_le_sum_abs_add hβ x

/-- The integrated coordinate derivative of softmax, rewritten using the explicit Hessian
entry from `LSECalculus`. -/
theorem integral_deriv_softmax_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) (i j : ι) :
    ∫ x, deriv (fun t => softmax β (Function.update x j t) i) (x j) ∂μ =
      ∫ x, β * ((if i = j then softmax β x i else 0) -
        softmax β x i * softmax β x j) ∂μ := by
  refine integral_congr_ae ?_
  exact ae_of_all μ fun x => deriv_softmax_update β x i j

/-- Coordinate covariance matrix of a finite-dimensional Gaussian measure. -/
def gaussianCov {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) (i j : ι) : ℝ :=
  covarianceBilinDual μ (coordCLM i) (coordCLM j)

/-- A derivative-form Stein identity for `softmax` immediately gives the explicit
softmax-Hessian form.

The remaining analytic work is to prove the hypothesis from the full finite-dimensional Gaussian
Stein theorem. This lemma packages the derivative rewrite so the future proof can use the
coordinate derivative theorem directly. -/
theorem gaussian_ibp_softmax_of_deriv_form
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (β : ℝ) (i j : ι)
    (hstein :
      ∫ x, x i * softmax β x j ∂μ =
        Finset.univ.sum fun k =>
          gaussianCov μ i k *
            ∫ x, deriv (fun t => softmax β (Function.update x k t) j) (x k) ∂μ) :
    ∫ x, x i * softmax β x j ∂μ =
      Finset.univ.sum fun k =>
        gaussianCov μ i k *
          ∫ x, β * ((if j = k then softmax β x j else 0) -
            softmax β x j * softmax β x k) ∂μ := by
  rw [hstein]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [integral_deriv_softmax_update μ β j k]

/-- Specialization of a coordinate Stein identity to the softmax test functions.

This theorem is intentionally conditional: its hypothesis is exactly the nonlinear finite-dimensional
Gaussian Stein theorem applied to `f x = softmax β x j`. The conclusion is the explicit Hessian
form needed by the Sudakov-Fernique interpolation proof. -/
theorem gaussian_ibp_softmax_of_coordinate_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (β : ℝ)
    (hstein : ∀ i j,
      ∫ x, x i * softmax β x j ∂μ =
        Finset.univ.sum fun k =>
          gaussianCov μ i k *
            ∫ x, deriv (fun t => softmax β (Function.update x k t) j) (x k) ∂μ) :
    ∀ i j,
      ∫ x, x i * softmax β x j ∂μ =
        Finset.univ.sum fun k =>
          gaussianCov μ i k *
            ∫ x, β * ((if j = k then softmax β x j else 0) -
              softmax β x j * softmax β x k) ∂μ := by
  intro i j
  exact gaussian_ibp_softmax_of_deriv_form μ β i j (hstein i j)

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

/-- Variance of a coordinate increment in terms of the coordinate covariance matrix. -/
theorem gaussian_variance_sub_eq_cov
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (i j : ι) :
    variance (fun x : ι → ℝ => x i - x j) μ =
      gaussianCov μ i i - 2 * gaussianCov μ i j + gaussianCov μ j j := by
  have hi2 : MemLp (fun x : ι → ℝ => x i) 2 μ := by
    simpa [coordCLM] using IsGaussian.memLp_dual μ (coordCLM i) 2 (by simp)
  have hj2 : MemLp (fun x : ι → ℝ => x j) 2 μ := by
    simpa [coordCLM] using IsGaussian.memLp_dual μ (coordCLM j) 2 (by simp)
  rw [variance_fun_sub hi2 hj2]
  rw [← covariance_self hi2.aemeasurable]
  rw [← covariance_self hj2.aemeasurable]
  rw [← gaussianCov_eq_covariance μ i i]
  rw [← gaussianCov_eq_covariance μ i j]
  rw [← gaussianCov_eq_covariance μ j j]

/-- The Sudakov-Fernique variance increment hypothesis, translated to the pairwise covariance
form needed by the Hessian covariance sign lemma. -/
theorem gaussian_cov_pair_nonneg_of_variance_le
    {ι : Type*} [Fintype ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY) :
    ∀ i j,
      0 ≤
        (gaussianCov μY i i - gaussianCov μX i i) +
          (gaussianCov μY j j - gaussianCov μX j j) -
            2 * (gaussianCov μY i j - gaussianCov μX i j) := by
  intro i j
  have h := hinc i j
  rw [gaussian_variance_sub_eq_cov μX i j, gaussian_variance_sub_eq_cov μY i j] at h
  linarith

/-- The covariance-difference contraction with the log-sum-exp Hessian is pointwise
nonnegative under the Sudakov-Fernique variance increment hypothesis. -/
theorem softmax_hessian_cov_contraction_nonneg_of_variance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 ≤ β) (x : ι → ℝ) :
    0 ≤
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          β * ((if i = j then softmax β x i else 0) -
            softmax β x i * softmax β x j) *
              (gaussianCov μY i j - gaussianCov μX i j)) := by
  exact hessian_cov_nonneg_softmax hβ x
    (fun i j => gaussianCov μY i j - gaussianCov μX i j)
    (by
      intro i j
      simpa using gaussian_cov_pair_nonneg_of_variance_le μX μY hinc i j)

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
