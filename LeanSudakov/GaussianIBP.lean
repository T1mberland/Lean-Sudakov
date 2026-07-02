import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real

noncomputable section

/-- Derivative of the one-dimensional Gaussian density. -/
theorem hasDerivAt_gaussianPDFReal
    {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ x : ℝ, HasDerivAt (gaussianPDFReal μ v)
      (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) x := by
  intro x
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  unfold gaussianPDFReal
  have hderiv := ((hasDerivAt_const (x := x) ((√(2 * π * (v : ℝ)))⁻¹)).mul
    (((((hasDerivAt_id x).sub_const μ).pow 2).neg.div_const (2 * (v : ℝ))).exp))
  convert hderiv using 1
  simp only [id_eq]
  field_simp [hv']
  rw [show ((-(fun x : ℝ => x - μ) ^ 2) x / ((v : ℝ) * 2)) =
      -((x - μ) ^ 2 / ((v : ℝ) * 2)) by
        change -((x - μ) ^ 2) / ((v : ℝ) * 2) = -((x - μ) ^ 2 / ((v : ℝ) * 2))
        ring]
  ring

/-- One-dimensional Gaussian integration by parts, written against Lebesgue measure and the
Gaussian density. -/
theorem gaussianPDFReal_integral_centered_mul_eq_var_mul_integral_deriv
    {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h_deriv : Integrable (fun x => gaussianPDFReal μ v x * f' x))
    (h_center_deriv : Integrable (fun x => (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) * f x))
    (h_prod : Integrable (fun x => gaussianPDFReal μ v x * f x)) :
    ∫ x, (x - μ) * gaussianPDFReal μ v x * f x =
      (v : ℝ) * ∫ x, gaussianPDFReal μ v x * f' x := by
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  have hibp :
      ∫ x, gaussianPDFReal μ v x * f' x =
        - ∫ x, (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) * f x := by
    simpa only [Pi.mul_apply] using
      (MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := gaussianPDFReal μ v)
        (u' := fun x => -(x - μ) / (v : ℝ) * gaussianPDFReal μ v x)
        (v := f) (v' := f')
        (hasDerivAt_gaussianPDFReal hv) hf h_deriv h_center_deriv h_prod)
  rw [hibp]
  rw [← integral_neg]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  field_simp [hv']

/-- One-dimensional Gaussian integration by parts for `gaussianReal μ v`.

This is the Stein identity
`E[(X - μ) f X] = v E[f' X]` for non-degenerate real Gaussian law, under explicit
integrability hypotheses. -/
theorem gaussianReal_integral_centered_mul_eq_var_mul_integral_deriv
    {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (h_deriv : Integrable (fun x => gaussianPDFReal μ v x * f' x))
    (h_center_deriv : Integrable (fun x => (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) * f x))
    (h_prod : Integrable (fun x => gaussianPDFReal μ v x * f x)) :
    ∫ x, (x - μ) * f x ∂gaussianReal μ v =
      (v : ℝ) * ∫ x, f' x ∂gaussianReal μ v := by
  rw [integral_gaussianReal_eq_integral_smul (μ := μ) (v := v)
    (f := fun x => (x - μ) * f x) hv]
  rw [integral_gaussianReal_eq_integral_smul (μ := μ) (v := v) (f := f') hv]
  simp only [smul_eq_mul]
  rw [← gaussianPDFReal_integral_centered_mul_eq_var_mul_integral_deriv
    hv hf h_deriv h_center_deriv h_prod]
  apply integral_congr_ae
  filter_upwards with x
  ring

end
