import LeanSudakov.Deterministic
import LeanSudakov.GaussianVectorIBP
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Moments.Variance

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators Topology ENNReal

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

/-- Coordinate derivative of the interpolation path at interior times. -/
theorem hasDerivAt_gaussianInterpMap_apply
    {ι : Type*} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) (i : ι) :
    HasDerivAt (fun s => gaussianInterpMap (ι := ι) s p i)
      ((p.2 i) / (2 * Real.sqrt t) - (p.1 i) / (2 * Real.sqrt (1 - t))) t := by
  have ht_ne : t ≠ 0 := ne_of_gt ht.1
  have h1t_ne : 1 - t ≠ 0 := by linarith [ht.2]
  have hsqrt_t :
      HasDerivAt (fun s : ℝ => Real.sqrt s) (1 / (2 * Real.sqrt t)) t :=
    Real.hasDerivAt_sqrt ht_ne
  have hsqrt_1t :
      HasDerivAt (fun s : ℝ => Real.sqrt (1 - s))
        (-1 / (2 * Real.sqrt (1 - t))) t := by
    simpa using
      ((hasDerivAt_const (x := t) (1 : ℝ)).sub (hasDerivAt_id t)).sqrt h1t_ne
  have hx :=
    (hsqrt_1t.const_mul (p.1 i)).add (hsqrt_t.const_mul (p.2 i))
  convert hx using 1
  · ext s
    simp [gaussianInterpMap, mul_comm]
  · field_simp [ht_ne, h1t_ne]
    ring

/-- Pointwise derivative of log-sum-exp along the Gaussian interpolation path. -/
theorem hasDerivAt_lse_gaussianInterpMap
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) :
    HasDerivAt (fun s => lse β (gaussianInterpMap (ι := ι) s p))
      (Finset.univ.sum fun i =>
        softmax β (gaussianInterpMap (ι := ι) t p) i *
          ((p.2 i) / (2 * Real.sqrt t) - (p.1 i) / (2 * Real.sqrt (1 - t)))) t := by
  classical
  let z : ℝ → ι → ℝ := fun s => gaussianInterpMap (ι := ι) s p
  let dz : ι → ℝ := fun i =>
    (p.2 i) / (2 * Real.sqrt t) - (p.1 i) / (2 * Real.sqrt (1 - t))
  have hz (i : ι) : HasDerivAt (fun s => z s i) (dz i) t := by
    simpa [z, dz] using hasDerivAt_gaussianInterpMap_apply ht p i
  have hexp (i : ι) :
      HasDerivAt (fun s => Real.exp (β * z s i))
        (β * dz i * Real.exp (β * z t i)) t := by
    convert ((hz i).const_mul β).exp using 1
    ring
  have hsum :
      HasDerivAt
        (fun s => Finset.univ.sum fun i => Real.exp (β * z s i))
        (Finset.univ.sum fun i => β * dz i * Real.exp (β * z t i)) t :=
    HasDerivAt.fun_sum (u := (Finset.univ : Finset ι)) fun i _ => hexp i
  have hSpos : 0 < (Finset.univ.sum fun i => Real.exp (β * z t i)) := by
    classical
    let i : ι := Classical.choice inferInstance
    exact lt_of_lt_of_le (Real.exp_pos (β * z t i)) <|
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i => Real.exp (β * z t i))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i)
  have hlog := hsum.log hSpos.ne'
  have hdiv := hlog.div_const β
  have hdiv' :
      HasDerivAt (fun s => lse β (z s))
        ((Finset.univ.sum fun i => β * dz i * Real.exp (β * z t i)) /
          (Finset.univ.sum fun i => Real.exp (β * z t i)) / β) t := by
    simpa [lse] using hdiv
  change HasDerivAt (fun s => lse β (z s))
    (Finset.univ.sum fun i => softmax β (z t) i * dz i) t
  convert hdiv' using 1
  simp only [softmax]
  field_simp [hβ, hSpos.ne']
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp [hSpos.ne']

/-- Pointwise `deriv` form of the log-sum-exp derivative along the interpolation path. -/
theorem deriv_lse_gaussianInterpMap
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) :
    deriv (fun s => lse β (gaussianInterpMap (ι := ι) s p)) t =
      (1 / 2) *
        (Finset.univ.sum fun i =>
          softmax β (gaussianInterpMap (ι := ι) t p) i *
            (p.2 i / Real.sqrt t - p.1 i / Real.sqrt (1 - t))) := by
  rw [(hasDerivAt_lse_gaussianInterpMap hβ ht p).deriv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have ht_ne : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.2 ht.1
  have h1t_ne : Real.sqrt (1 - t) ≠ 0 := Real.sqrt_ne_zero'.2 (by linarith [ht.2])
  field_simp [ht_ne, h1t_ne]

/-- The pointwise derivative integrand for the log-sum-exp Gaussian interpolation functional. -/
noncomputable def gaussianInterpLSEDerivIntegrand
    {ι : Type*} [Fintype ι] (β t : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  Finset.univ.sum fun i =>
    softmax β (gaussianInterpMap (ι := ι) t p) i *
      ((p.2 i) / (2 * Real.sqrt t) - (p.1 i) / (2 * Real.sqrt (1 - t)))

theorem continuous_gaussianInterpLSEDerivIntegrand
    {ι : Type*} [Fintype ι] (β t : ℝ) :
    Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      gaussianInterpLSEDerivIntegrand (ι := ι) β t p := by
  classical
  refine continuous_finset_sum Finset.univ fun i _ => ?_
  have hfst_i : Continuous fun p : (ι → ℝ) × (ι → ℝ) => p.1 i :=
    (continuous_apply i).comp continuous_fst
  have hsnd_i : Continuous fun p : (ι → ℝ) × (ι → ℝ) => p.2 i :=
    (continuous_apply i).comp continuous_snd
  exact ((continuous_softmax β i).comp (gaussianInterpMap (ι := ι) t).continuous).mul
    ((hsnd_i.div_const (2 * Real.sqrt t)).sub
      (hfst_i.div_const (2 * Real.sqrt (1 - t))))

theorem hasDerivAt_lse_gaussianInterpMap_derivIntegrand
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) :
    HasDerivAt (fun s => lse β (gaussianInterpMap (ι := ι) s p))
      (gaussianInterpLSEDerivIntegrand β t p) t := by
  simpa [gaussianInterpLSEDerivIntegrand] using hasDerivAt_lse_gaussianInterpMap hβ ht p

/-- A local first-moment bound for the derivative integrand near an interior interpolation time. -/
noncomputable def gaussianInterpLSEDerivBound
    {ι : Type*} [Fintype ι] (t : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  Finset.univ.sum fun i =>
    (1 / (2 * Real.sqrt (t / 2))) * |p.2 i| +
      (1 / (2 * Real.sqrt ((1 - t) / 2))) * |p.1 i|

private theorem one_div_two_sqrt_le_one_div_two_sqrt
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    1 / (2 * Real.sqrt b) ≤ 1 / (2 * Real.sqrt a) := by
  have hsqrt_le : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hden_pos : 0 < 2 * Real.sqrt a := by positivity
  have hden_le : 2 * Real.sqrt a ≤ 2 * Real.sqrt b := by
    nlinarith [hsqrt_le]
  exact one_div_le_one_div_of_le hden_pos hden_le

theorem gaussianInterpLSEDerivIntegrand_le_bound
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) {t s : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s ∈ Set.Ioo (t / 2) ((t + 1) / 2))
    (p : (ι → ℝ) × (ι → ℝ)) :
    ‖gaussianInterpLSEDerivIntegrand (ι := ι) β s p‖ ≤
      gaussianInterpLSEDerivBound (ι := ι) t p := by
  classical
  have hs_pos : 0 < s := by linarith [ht.1, hs.1]
  have h1s_pos : 0 < 1 - s := by linarith [ht.2, hs.2]
  have ht_half_pos : 0 < t / 2 := by linarith [ht.1]
  have h1t_half_pos : 0 < (1 - t) / 2 := by linarith [ht.2]
  have hs_inv :
      1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt (t / 2)) :=
    one_div_two_sqrt_le_one_div_two_sqrt ht_half_pos hs.1.le
  have h1s_inv :
      1 / (2 * Real.sqrt (1 - s)) ≤
        1 / (2 * Real.sqrt ((1 - t) / 2)) := by
    have hle : (1 - t) / 2 ≤ 1 - s := by linarith [hs.2]
    exact one_div_two_sqrt_le_one_div_two_sqrt h1t_half_pos hle
  rw [gaussianInterpLSEDerivIntegrand, Real.norm_eq_abs]
  calc
    |Finset.univ.sum fun i =>
        softmax β (gaussianInterpMap (ι := ι) s p) i *
          (p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s)))|
        ≤ Finset.univ.sum fun i =>
            |softmax β (gaussianInterpMap (ι := ι) s p) i *
              (p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s)))| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ gaussianInterpLSEDerivBound (ι := ι) t p := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      calc
        |softmax β (gaussianInterpMap (ι := ι) s p) i| *
            |p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s))|
            ≤ 1 *
              |p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s))| := by
              exact mul_le_mul_of_nonneg_right
                (abs_softmax_le_one β (gaussianInterpMap (ι := ι) s p) i) (abs_nonneg _)
        _ = |p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s))| := by ring
        _ ≤ (1 / (2 * Real.sqrt (t / 2))) * |p.2 i| +
              (1 / (2 * Real.sqrt ((1 - t) / 2))) * |p.1 i| := by
          have hden_s_pos : 0 < 2 * Real.sqrt s := by positivity
          have hden_1s_pos : 0 < 2 * Real.sqrt (1 - s) := by positivity
          calc
            |p.2 i / (2 * Real.sqrt s) - p.1 i / (2 * Real.sqrt (1 - s))|
                ≤ |p.2 i / (2 * Real.sqrt s)| +
                    |p.1 i / (2 * Real.sqrt (1 - s))| := abs_sub _ _
            _ = |p.2 i| * (1 / (2 * Real.sqrt s)) +
                  |p.1 i| * (1 / (2 * Real.sqrt (1 - s))) := by
              rw [abs_div, abs_div]
              rw [abs_of_pos hden_s_pos, abs_of_pos hden_1s_pos]
              ring
            _ ≤ |p.2 i| * (1 / (2 * Real.sqrt (t / 2))) +
                  |p.1 i| * (1 / (2 * Real.sqrt ((1 - t) / 2))) := by
              gcongr
            _ = (1 / (2 * Real.sqrt (t / 2))) * |p.2 i| +
                  (1 / (2 * Real.sqrt ((1 - t) / 2))) * |p.1 i| := by
              ring

theorem integrable_gaussianInterpLSEDerivBound
    {ι : Type*} [Fintype ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (t : ℝ) :
    Integrable (gaussianInterpLSEDerivBound (ι := ι) t) (μX.prod μY) := by
  classical
  refine integrable_finset_sum (s := (Finset.univ : Finset ι)) fun i _ => ?_
  have hY :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) => |p.2 i|) (μX.prod μY) := by
    simpa using (gaussian_integrable_coord μY i).abs.comp_snd μX
  have hX :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) => |p.1 i|) (μX.prod μY) := by
    simpa using (gaussian_integrable_coord μX i).abs.comp_fst μY
  exact (hY.const_mul (1 / (2 * Real.sqrt (t / 2)))).add
    (hX.const_mul (1 / (2 * Real.sqrt ((1 - t) / 2))))

theorem integrable_lse_gaussianInterpMap
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
      lse β (gaussianInterpMap (ι := ι) t p)) (μX.prod μY) := by
  classical
  let c : ℝ := Real.log (Fintype.card ι) / β
  let bound : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    (Finset.univ.sum fun i =>
      Real.sqrt (1 - t) * |p.1 i| + Real.sqrt t * |p.2 i|) + c
  have hbound_int : Integrable bound (μX.prod μY) := by
    refine (integrable_finset_sum (s := (Finset.univ : Finset ι)) fun i _ => ?_).add
      (integrable_const c)
    have hX :
        Integrable (fun p : (ι → ℝ) × (ι → ℝ) => |p.1 i|) (μX.prod μY) := by
      simpa using (gaussian_integrable_coord μX i).abs.comp_fst μY
    have hY :
        Integrable (fun p : (ι → ℝ) × (ι → ℝ) => |p.2 i|) (μX.prod μY) := by
      simpa using (gaussian_integrable_coord μY i).abs.comp_snd μX
    exact (hX.const_mul (Real.sqrt (1 - t))).add (hY.const_mul (Real.sqrt t))
  refine Integrable.mono' hbound_int
    (((measurable_lse β).comp (gaussianInterpMap (ι := ι) t).measurable).aestronglyMeasurable) ?_
  exact ae_of_all (μX.prod μY) fun p => by
    rw [Real.norm_eq_abs]
    calc
      |lse β (gaussianInterpMap (ι := ι) t p)|
          ≤ (Finset.univ.sum fun i => |gaussianInterpMap (ι := ι) t p i|) + c := by
            simpa [c] using abs_lse_le_sum_abs_add hβ (gaussianInterpMap (ι := ι) t p)
      _ ≤ bound p := by
        dsimp [bound]
        have hsum :
            (Finset.univ.sum fun i => |gaussianInterpMap (ι := ι) t p i|) ≤
              Finset.univ.sum fun i =>
                Real.sqrt (1 - t) * |p.1 i| + Real.sqrt t * |p.2 i| := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [gaussianInterpMap_apply]
          calc
            |Real.sqrt (1 - t) * p.1 i + Real.sqrt t * p.2 i|
                ≤ |Real.sqrt (1 - t) * p.1 i| + |Real.sqrt t * p.2 i| := abs_add_le _ _
            _ = Real.sqrt (1 - t) * |p.1 i| + Real.sqrt t * |p.2 i| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
                abs_of_nonneg (Real.sqrt_nonneg _)]
        simpa [add_comm] using add_le_add_right hsum c

theorem memLp_top_softmax_gaussianInterpMap
    {ι : Type*} [Fintype ι]
    (μ : Measure ((ι → ℝ) × (ι → ℝ))) (β t : ℝ) (i : ι) :
    MemLp (fun p : (ι → ℝ) × (ι → ℝ) =>
      softmax β (gaussianInterpMap (ι := ι) t p) i) ∞ μ := by
  refine memLp_top_of_bound
    (((continuous_softmax β i).comp (gaussianInterpMap (ι := ι) t).continuous).aestronglyMeasurable)
    1 ?_
  exact ae_of_all μ fun p => by
    simpa [Real.norm_eq_abs] using
      abs_softmax_le_one β (gaussianInterpMap (ι := ι) t p) i

theorem integrable_gaussianInterpMap_coord_mul_softmax
    {ι : Type*} [Fintype ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (β t : ℝ) (i : ι) :
    Integrable
      (fun p : (ι → ℝ) × (ι → ℝ) =>
        p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i)
      (μX.prod μY) ∧
    Integrable
      (fun p : (ι → ℝ) × (ι → ℝ) =>
        p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i)
      (μX.prod μY) := by
  constructor
  · exact ((gaussian_integrable_coord μX i).comp_fst μY).mul_of_top_left
      (memLp_top_softmax_gaussianInterpMap (μX.prod μY) β t i)
  · exact ((gaussian_integrable_coord μY i).comp_snd μX).mul_of_top_left
      (memLp_top_softmax_gaussianInterpMap (μX.prod μY) β t i)

theorem integral_gaussianInterpLSEDerivIntegrand_eq_endpoint_terms
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (β t : ℝ) :
    (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) =
      Finset.univ.sum fun i =>
        (1 / (2 * Real.sqrt t)) *
            (∫ p : (ι → ℝ) × (ι → ℝ),
              p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) -
          (1 / (2 * Real.sqrt (1 - t))) *
            (∫ p : (ι → ℝ) × (ι → ℝ),
              p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) := by
  classical
  simp only [gaussianInterpLSEDerivIntegrand]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hX := (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).1
    have hY := (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).2
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
      (hY.const_mul (1 / (2 * Real.sqrt t)))
      (hX.const_mul (1 / (2 * Real.sqrt (1 - t))))]
    refine integral_congr_ae ?_
    exact ae_of_all (μX.prod μY) fun p => by
      simp
      ring_nf
  · intro i _
    have hX := (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).1
    have hY := (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).2
    convert (hY.const_mul (1 / (2 * Real.sqrt t))).sub
      (hX.const_mul (1 / (2 * Real.sqrt (1 - t)))) using 1
    ext p
    simp
    ring_nf

noncomputable def softmaxHessianTerm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (z : ι → ℝ) (i j : ι) : ℝ :=
  β * ((if i = j then softmax β z i else 0) - softmax β z i * softmax β z j)

noncomputable def softmaxHessianCovRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (β : ℝ) (z : ι → ℝ) (i : ι) : ℝ :=
  Finset.univ.sum fun j => softmaxHessianTerm β z i j * gaussianCov μ i j

noncomputable def softmaxHessianCovDiffSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) (β : ℝ) (z : ι → ℝ) : ℝ :=
  Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      softmaxHessianTerm β z i j * (gaussianCov μY i j - gaussianCov μX i j)

theorem softmaxHessianCovRow_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) (β : ℝ) (z : ι → ℝ) (i : ι) :
    softmaxHessianCovRow μY β z i - softmaxHessianCovRow μX β z i =
      Finset.univ.sum fun j =>
        softmaxHessianTerm β z i j * (gaussianCov μY i j - gaussianCov μX i j) := by
  rw [softmaxHessianCovRow, softmaxHessianCovRow, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem softmaxHessianCovDiffSum_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) (β : ℝ) (z : ι → ℝ) :
    softmaxHessianCovDiffSum μX μY β z =
      Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          β * ((if i = j then softmax β z i else 0) -
            softmax β z i * softmax β z j) *
              (gaussianCov μY i j - gaussianCov μX i j) := by
  simp [softmaxHessianCovDiffSum, softmaxHessianTerm]

theorem integrable_softmaxHessianCovRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [IsFiniteMeasure ν]
    (μ : Measure (ι → ℝ)) (β : ℝ) (i : ι) :
    Integrable (fun z : ι → ℝ => softmaxHessianCovRow μ β z i) ν := by
  classical
  refine integrable_finset_sum (s := (Finset.univ : Finset ι)) fun j _ => ?_
  convert (integrable_softmax_deriv_term ν β i j).const_mul (gaussianCov μ i j) using 1
  ext z
  simp [softmaxHessianTerm, mul_comm, mul_left_comm]

theorem integrable_softmaxHessianCovDiffSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ν : Measure (ι → ℝ)) [IsFiniteMeasure ν]
    (μX μY : Measure (ι → ℝ)) (β : ℝ) :
    Integrable (fun z : ι → ℝ => softmaxHessianCovDiffSum μX μY β z) ν := by
  classical
  refine integrable_finset_sum (s := (Finset.univ : Finset ι)) fun i _ => ?_
  rw [show (fun z : ι → ℝ =>
        Finset.univ.sum fun j =>
          softmaxHessianTerm β z i j * (gaussianCov μY i j - gaussianCov μX i j)) =
      fun z => softmaxHessianCovRow μY β z i - softmaxHessianCovRow μX β z i by
    funext z
    rw [softmaxHessianCovRow_sub]]
  exact (integrable_softmaxHessianCovRow ν μY β i).sub
    (integrable_softmaxHessianCovRow ν μX β i)

/-- The Gaussian interpolation measure, realized as a linear image of the independent product
coupling of the endpoint laws. -/
noncomputable def gaussianInterpMeasure
    {ι : Type*} (μX μY : Measure (ι → ℝ)) (t : ℝ) : Measure (ι → ℝ) :=
  (μX.prod μY).map (gaussianInterpMap (ι := ι) t)

/-- The expected log-sum-exp along the Gaussian interpolation path. -/
noncomputable def gaussianInterpolationLSE
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ)) (β t : ℝ) : ℝ :=
  ∫ z, lse β z ∂gaussianInterpMeasure μX μY t

theorem integral_gaussianInterpLSEDerivIntegrand_eq_hessian_of_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (β t : ℝ)
    (hYstein : ∀ i,
      (1 / (2 * Real.sqrt t)) *
          (∫ p : (ι → ℝ) × (ι → ℝ),
            p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
        (1 / 2) *
          ∫ z, softmaxHessianCovRow μY β z i ∂gaussianInterpMeasure μX μY t)
    (hXstein : ∀ i,
      (1 / (2 * Real.sqrt (1 - t))) *
          (∫ p : (ι → ℝ) × (ι → ℝ),
            p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
        (1 / 2) *
          ∫ z, softmaxHessianCovRow μX β z i ∂gaussianInterpMeasure μX μY t) :
    (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) =
      (1 / 2) *
        ∫ z, softmaxHessianCovDiffSum μX μY β z ∂gaussianInterpMeasure μX μY t := by
  classical
  let ν : Measure (ι → ℝ) := gaussianInterpMeasure μX μY t
  haveI : IsFiniteMeasure ν := by
    dsimp [ν, gaussianInterpMeasure]
    infer_instance
  rw [integral_gaussianInterpLSEDerivIntegrand_eq_endpoint_terms μX μY β t]
  calc
    (Finset.univ.sum fun i =>
        (1 / (2 * Real.sqrt t)) *
            (∫ p : (ι → ℝ) × (ι → ℝ),
              p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) -
          (1 / (2 * Real.sqrt (1 - t))) *
            (∫ p : (ι → ℝ) × (ι → ℝ),
              p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY))
        = Finset.univ.sum fun i =>
            (1 / 2) * ∫ z, softmaxHessianCovRow μY β z i ∂ν -
              (1 / 2) * ∫ z, softmaxHessianCovRow μX β z i ∂ν := by
          refine Finset.sum_congr rfl fun i _ => ?_
          dsimp [ν]
          rw [hYstein i, hXstein i]
    _ = (1 / 2) *
          Finset.univ.sum fun i =>
            (∫ z, softmaxHessianCovRow μY β z i ∂ν) -
              (∫ z, softmaxHessianCovRow μX β z i ∂ν) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
    _ = (1 / 2) *
          Finset.univ.sum fun i =>
            ∫ z, softmaxHessianCovRow μY β z i - softmaxHessianCovRow μX β z i ∂ν := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_sub
            (integrable_softmaxHessianCovRow ν μY β i)
            (integrable_softmaxHessianCovRow ν μX β i)]
    _ = (1 / 2) *
          Finset.univ.sum fun i =>
            ∫ z, (Finset.univ.sum fun j =>
              softmaxHessianTerm β z i j * (gaussianCov μY i j - gaussianCov μX i j)) ∂ν := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          refine integral_congr_ae ?_
          exact ae_of_all ν fun z => softmaxHessianCovRow_sub μX μY β z i
    _ = (1 / 2) *
          ∫ z, softmaxHessianCovDiffSum μX μY β z ∂ν := by
          change (1 / 2) *
              Finset.univ.sum (fun i =>
                ∫ z, (Finset.univ.sum fun j =>
                  softmaxHessianTerm β z i j *
                    (gaussianCov μY i j - gaussianCov μX i j)) ∂ν) =
            (1 / 2) *
              ∫ z, (Finset.univ.sum fun i =>
                Finset.univ.sum fun j =>
                  softmaxHessianTerm β z i j *
                    (gaussianCov μY i j - gaussianCov μX i j)) ∂ν
          rw [integral_finset_sum]
          · intro i _
            rw [show (fun z : ι → ℝ =>
                  Finset.univ.sum fun j =>
                    softmaxHessianTerm β z i j *
                      (gaussianCov μY i j - gaussianCov μX i j)) =
                fun z => softmaxHessianCovRow μY β z i - softmaxHessianCovRow μX β z i by
              funext z
              rw [softmaxHessianCovRow_sub]]
            exact (integrable_softmaxHessianCovRow ν μY β i).sub
              (integrable_softmaxHessianCovRow ν μX β i)

/-- Differentiating the Gaussian interpolation log-sum-exp functional under the product integral,
assuming a local dominated-derivative bound.

The remaining analytic work is to provide `hbound` and `hbound_int` from Gaussian first moments and
the fact that an interior interpolation time has `sqrt t` and `sqrt (1 - t)` bounded away from
zero locally. -/
theorem hasDerivAt_gaussianInterpolationLSE_of_dominated
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) {β t : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    {bound : (ι → ℝ) × (ι → ℝ) → ℝ}
    (hF_int :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
        lse β (gaussianInterpMap (ι := ι) t p)) (μX.prod μY))
    (hbound : ∀ᵐ p ∂μX.prod μY, ∀ s ∈ Set.Ioo (t / 2) ((t + 1) / 2),
      ‖gaussianInterpLSEDerivIntegrand (ι := ι) β s p‖ ≤ bound p)
    (hbound_int : Integrable bound (μX.prod μY)) :
    HasDerivAt (gaussianInterpolationLSE μX μY β)
      (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) t := by
  classical
  let μ : Measure ((ι → ℝ) × (ι → ℝ)) := μX.prod μY
  let F : ℝ → ((ι → ℝ) × (ι → ℝ)) → ℝ :=
    fun s p => lse β (gaussianInterpMap (ι := ι) s p)
  let F' : ℝ → ((ι → ℝ) × (ι → ℝ)) → ℝ :=
    fun s p => gaussianInterpLSEDerivIntegrand (ι := ι) β s p
  have ht_local : t ∈ Set.Ioo (t / 2) ((t + 1) / 2) := by
    constructor <;> linarith [ht.1, ht.2]
  have hs : Set.Ioo (t / 2) ((t + 1) / 2) ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht_local
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ := by
    exact Filter.Eventually.of_forall fun s => by
      exact ((measurable_lse β).comp (gaussianInterpMap (ι := ι) s).measurable).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' t) μ := by
    simpa [F'] using
      (continuous_gaussianInterpLSEDerivIntegrand (ι := ι) β t).aestronglyMeasurable
  have hdiff :
      ∀ᵐ p ∂μ, ∀ s ∈ Set.Ioo (t / 2) ((t + 1) / 2),
        HasDerivAt (F · p) (F' s p) s := by
    exact ae_of_all μ fun p s hs => by
      have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := by
        constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]
      simpa [F, F'] using hasDerivAt_lse_gaussianInterpMap_derivIntegrand hβ hs01 p
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (x₀ := t) (s := Set.Ioo (t / 2) ((t + 1) / 2))
    (bound := bound) hs hF_meas (by simpa [F, μ] using hF_int)
    (by simpa [F', μ] using hF'_meas) (by simpa [F', μ] using hbound)
    (by simpa [μ] using hbound_int) hdiff
  convert hmain.2 using 1
  · ext s
    rw [gaussianInterpolationLSE, gaussianInterpMeasure]
    rw [integral_map
      ((gaussianInterpMap (ι := ι) s).measurable.aemeasurable)
      ((measurable_lse β).aestronglyMeasurable)]

theorem hasDerivAt_gaussianInterpolationLSE_of_integrable
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY] {β t : ℝ}
    (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hF_int :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) =>
        lse β (gaussianInterpMap (ι := ι) t p)) (μX.prod μY)) :
    HasDerivAt (gaussianInterpolationLSE μX μY β)
      (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) t := by
  refine hasDerivAt_gaussianInterpolationLSE_of_dominated
    (μX := μX) (μY := μY) hβ ht hF_int
    (bound := gaussianInterpLSEDerivBound (ι := ι) t) ?_ ?_
  · exact ae_of_all (μX.prod μY) fun p s hs =>
      gaussianInterpLSEDerivIntegrand_le_bound β ht hs p
  · exact integrable_gaussianInterpLSEDerivBound μX μY t

theorem hasDerivAt_gaussianInterpolationLSE
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY] {β t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (gaussianInterpolationLSE μX μY β)
      (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) t := by
  exact hasDerivAt_gaussianInterpolationLSE_of_integrable μX μY hβ.ne' ht
    (integrable_lse_gaussianInterpMap μX μY hβ t)

theorem deriv_gaussianInterpolationLSE_eq_integral
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY] {β t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (gaussianInterpolationLSE μX μY β) t =
      ∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY := by
  exact (hasDerivAt_gaussianInterpolationLSE μX μY hβ ht).deriv

theorem differentiableOn_gaussianInterpolationLSE
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY] {β : ℝ}
    (hβ : 0 < β) :
    DifferentiableOn ℝ (gaussianInterpolationLSE μX μY β)
      (interior (Set.Icc (0 : ℝ) 1)) := by
  intro t ht
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by simpa using ht
  exact (hasDerivAt_gaussianInterpolationLSE μX μY hβ ht').differentiableAt.differentiableWithinAt

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

theorem gaussianInterpMeasure_centered
    {ι : Type*} [Fintype ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (t : ℝ) (i : ι) :
    ∫ z, z i ∂gaussianInterpMeasure μX μY t = 0 := by
  classical
  let μ : Measure ((ι → ℝ) × (ι → ℝ)) := μX.prod μY
  have hXint :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.1 i) μ := by
    simpa [μ, coordCLM] using (gaussian_integrable_coord μX i).comp_fst μY
  have hYint :
      Integrable (fun p : (ι → ℝ) × (ι → ℝ) => p.2 i) μ := by
    simpa [μ, coordCLM] using (gaussian_integrable_coord μY i).comp_snd μX
  have hXprod : ∫ p : (ι → ℝ) × (ι → ℝ), p.1 i ∂μ = 0 := by
    have hmap :
        ∫ x, x i ∂Measure.map Prod.fst μ =
          ∫ p : (ι → ℝ) × (ι → ℝ), p.1 i ∂μ := by
      rw [integral_map]
      · exact measurable_fst.aemeasurable
      · exact (measurable_pi_apply i).aestronglyMeasurable
    dsimp [μ] at hmap
    rw [Measure.map_fst_prod] at hmap
    simpa [measure_univ, hX0 i] using hmap.symm
  have hYprod : ∫ p : (ι → ℝ) × (ι → ℝ), p.2 i ∂μ = 0 := by
    have hmap :
        ∫ y, y i ∂Measure.map Prod.snd μ =
          ∫ p : (ι → ℝ) × (ι → ℝ), p.2 i ∂μ := by
      rw [integral_map]
      · exact measurable_snd.aemeasurable
      · exact (measurable_pi_apply i).aestronglyMeasurable
    dsimp [μ] at hmap
    rw [Measure.map_snd_prod] at hmap
    simpa [measure_univ, hY0 i] using hmap.symm
  rw [gaussianInterpMeasure, integral_map]
  · change
      ∫ p : (ι → ℝ) × (ι → ℝ),
        Real.sqrt (1 - t) * p.1 i + Real.sqrt t * p.2 i ∂μ = 0
    rw [integral_add (hXint.const_mul _) (hYint.const_mul _)]
    rw [integral_const_mul, integral_const_mul, hXprod, hYprod]
    simp
  · exact (gaussianInterpMap (ι := ι) t).measurable.aemeasurable
  · exact (measurable_pi_apply i).aestronglyMeasurable

noncomputable def scalarPiCLM
    {ι : Type*} (a : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  a • ContinuousLinearMap.id ℝ (ι → ℝ)

@[simp]
theorem scalarPiCLM_apply
    {ι : Type*} (a : ℝ) (x : ι → ℝ) (i : ι) :
    scalarPiCLM (ι := ι) a x i = a * x i := by
  simp [scalarPiCLM, Pi.smul_apply, smul_eq_mul]

theorem scalarPiCLM_map_centered
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hμ0 : ∀ i, ∫ x, x i ∂μ = 0)
    (a : ℝ) (i : ι) :
    ∫ z, z i ∂Measure.map (scalarPiCLM (ι := ι) a) μ = 0 := by
  rw [integral_map]
  · change ∫ x, a * x i ∂μ = 0
    rw [integral_const_mul, hμ0 i]
    simp
  · exact (scalarPiCLM (ι := ι) a).measurable.aemeasurable
  · exact (measurable_pi_apply i).aestronglyMeasurable

theorem gaussianCov_map_scalarPiCLM
    {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (a : ℝ) (i j : ι) :
    gaussianCov (Measure.map (scalarPiCLM (ι := ι) a) μ) i j =
      a ^ 2 * gaussianCov μ i j := by
  let L := scalarPiCLM (ι := ι) a
  rw [gaussianCov_eq_covariance]
  rw [covariance_map_fun
    (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable
    L.measurable.aemeasurable]
  change cov[(fun x : ι → ℝ => a * x i), (fun x : ι → ℝ => a * x j); μ] =
    a ^ 2 * gaussianCov μ i j
  rw [covariance_const_mul_left, covariance_const_mul_right]
  rw [← gaussianCov_eq_covariance μ i j]
  ring

theorem fixed_y_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μY : Measure (ι → ℝ)) [IsGaussian μY]
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (x : ι → ℝ) (i : ι) :
    (1 / (2 * Real.sqrt t)) *
        (∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY) =
      (1 / 2) *
        ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
  classical
  let a : ℝ := Real.sqrt t
  let c : ι → ℝ := fun k => Real.sqrt (1 - t) * x k
  let L : (ι → ℝ) →L[ℝ] (ι → ℝ) := scalarPiCLM (ι := ι) a
  let ν : Measure (ι → ℝ) := Measure.map L μY
  haveI : IsGaussian ν := by
    dsimp [ν, L]
    infer_instance
  have hν0 : ∀ k, ∫ z, z k ∂ν = 0 := by
    intro k
    simpa [ν, L] using scalarPiCLM_map_centered μY hY0 a k
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 ht.1
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have ht_sq : a ^ 2 = t := by
    dsimp [a]
    exact Real.sq_sqrt ht.1.le
  have hstein := gaussian_ibp_softmax_affine ν hν0 β c i i
  have hleft :
      ∫ z, z i * softmax β (fun k => c k + z k) i ∂ν =
        ∫ y, a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
    calc
      ∫ z, z i * softmax β (fun k => c k + z k) i ∂ν
          = ∫ y, L y i * softmax β (fun k => c k + L y k) i ∂μY := by
            simpa [ν] using integral_map_linear_coord_mul_softmax_affine μY β c L i i
      _ = ∫ y, a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
            refine integral_congr_ae ?_
            exact ae_of_all μY fun y => by
              have hz : (fun k => c k + L y k) = gaussianInterpMap (ι := ι) t (x, y) := by
                ext k
                change c k + L y k =
                  Real.sqrt (1 - t) * x k + Real.sqrt t * y k
                rw [scalarPiCLM_apply]
              change L y i * softmax β (fun k => c k + L y k) i =
                a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i
              rw [hz]
              have hLi : L y i = a * y i := by
                change scalarPiCLM (ι := ι) a y i = a * y i
                rw [scalarPiCLM_apply]
              rw [hLi]
  have hright :
      (Finset.univ.sum fun k =>
        gaussianCov ν i k *
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
            softmax β (fun r => c r + z r) i *
              softmax β (fun r => c r + z r) k) ∂ν) =
        t * ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
    change (Finset.univ.sum fun k =>
        gaussianCov ν i k *
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
            softmax β (fun r => c r + z r) i *
              softmax β (fun r => c r + z r) k) ∂ν) =
      t * ∫ y, (Finset.univ.sum fun k =>
        softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
          gaussianCov μY i k) ∂μY
    rw [integral_finset_sum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcov : gaussianCov ν i k = t * gaussianCov μY i k := by
        calc
          gaussianCov ν i k = a ^ 2 * gaussianCov μY i k := by
            simpa [ν, L] using gaussianCov_map_scalarPiCLM μY a i k
          _ = t * gaussianCov μY i k := by rw [ht_sq]
      have hint :
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
              softmax β (fun r => c r + z r) i *
                softmax β (fun r => c r + z r) k) ∂ν =
            ∫ y, β * ((if i = k then
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
              softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μY := by
        calc
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
              softmax β (fun r => c r + z r) i *
                softmax β (fun r => c r + z r) k) ∂ν
              = ∫ y, β * ((if i = k then softmax β (fun r => c r + L y r) i else 0) -
                  softmax β (fun r => c r + L y r) i *
                    softmax β (fun r => c r + L y r) k) ∂μY := by
                simpa [ν] using integral_map_linear_softmax_affine_deriv_term μY β c L i k
          _ = ∫ y, β * ((if i = k then
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
              softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μY := by
                refine integral_congr_ae ?_
                exact ae_of_all μY fun y => by
                  have hz : (fun r => c r + L y r) =
                      gaussianInterpMap (ι := ι) t (x, y) := by
                    ext r
                    change c r + L y r =
                      Real.sqrt (1 - t) * x r + Real.sqrt t * y r
                    rw [scalarPiCLM_apply]
                  change β * ((if i = k then softmax β (fun r => c r + L y r) i else 0) -
                      softmax β (fun r => c r + L y r) i *
                        softmax β (fun r => c r + L y r) k) =
                    β * ((if i = k then
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) k)
                  rw [hz]
      have hterm :
          ∫ y, softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
              gaussianCov μY i k ∂μY =
            gaussianCov μY i k *
              ∫ y, β * ((if i = k then
                  softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                  softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μY := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        exact ae_of_all μY fun y => by
          simp [softmaxHessianTerm]
          ring
      rw [hcov, hint, hterm]
      ring
    · intro k _
      have hcont : Continuous fun y : ι → ℝ =>
          softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
            gaussianCov μY i k := by
        exact ((continuous_softmax_deriv_term β i k).comp
          ((gaussianInterpMap (ι := ι) t).continuous.comp
            (Continuous.prodMk continuous_const continuous_id))).mul continuous_const
      refine Integrable.of_bound hcont.aestronglyMeasurable (|gaussianCov μY i k| * (|β| * 2)) ?_
      exact ae_of_all μY fun y => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k| *
              |gaussianCov μY i k|
              ≤ (|β| * 2) * |gaussianCov μY i k| := by
                exact mul_le_mul_of_nonneg_right
                  (by
                    simpa [softmaxHessianTerm] using
                      abs_softmax_deriv_term_le β (gaussianInterpMap (ι := ι) t (x, y)) i k)
                  (abs_nonneg _)
          _ = |gaussianCov μY i k| * (|β| * 2) := by ring
  have hmain :
      ∫ y, a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY =
        t * ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
    simpa [hleft, hright] using hstein
  have hscale :
      ∫ y, a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY =
        a * ∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
    calc
      ∫ y, a * y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY
          = ∫ y, a * (y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i) ∂μY := by
            refine integral_congr_ae ?_
            exact ae_of_all μY fun y => by ring
      _ = a * ∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
        rw [integral_const_mul]
  rw [hscale] at hmain
  have ht_eq : t = a * a := by
    rw [← ht_sq]
    ring
  have hI :
      (∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY) =
        a * ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
    have hmain' :
        a * (∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY) =
          a * (a *
            ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY) := by
      rw [hmain, ht_eq]
      ring
    exact (mul_right_inj' ha_ne).mp hmain'
  calc
    (1 / (2 * Real.sqrt t)) *
        (∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY)
        = (1 / (2 * a)) *
          (∫ y, y i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY) := by
          rfl
    _ = (1 / 2) *
        ∫ y, softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μY := by
      rw [hI]
      field_simp [ha_ne]

theorem fixed_x_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX : Measure (ι → ℝ)) [IsGaussian μX]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (y : ι → ℝ) (i : ι) :
    (1 / (2 * Real.sqrt (1 - t))) *
        (∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX) =
      (1 / 2) *
        ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
  classical
  let a : ℝ := Real.sqrt (1 - t)
  let c : ι → ℝ := fun k => Real.sqrt t * y k
  let L : (ι → ℝ) →L[ℝ] (ι → ℝ) := scalarPiCLM (ι := ι) a
  let ν : Measure (ι → ℝ) := Measure.map L μX
  haveI : IsGaussian ν := by
    dsimp [ν, L]
    infer_instance
  have hν0 : ∀ k, ∫ z, z k ∂ν = 0 := by
    intro k
    simpa [ν, L] using scalarPiCLM_map_centered μX hX0 a k
  have h1t_pos : 0 < 1 - t := by linarith [ht.2]
  have ha_pos : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 h1t_pos
  have ha_ne : a ≠ 0 := ha_pos.ne'
  have ht_sq : a ^ 2 = 1 - t := by
    dsimp [a]
    exact Real.sq_sqrt h1t_pos.le
  have hstein := gaussian_ibp_softmax_affine ν hν0 β c i i
  have hleft :
      ∫ z, z i * softmax β (fun k => c k + z k) i ∂ν =
        ∫ x, a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
    calc
      ∫ z, z i * softmax β (fun k => c k + z k) i ∂ν
          = ∫ x, L x i * softmax β (fun k => c k + L x k) i ∂μX := by
            simpa [ν] using integral_map_linear_coord_mul_softmax_affine μX β c L i i
      _ = ∫ x, a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
            refine integral_congr_ae ?_
            exact ae_of_all μX fun x => by
              have hz : (fun k => c k + L x k) = gaussianInterpMap (ι := ι) t (x, y) := by
                ext k
                change c k + L x k =
                  Real.sqrt (1 - t) * x k + Real.sqrt t * y k
                rw [scalarPiCLM_apply]
                dsimp [c, a]
                ring
              change L x i * softmax β (fun k => c k + L x k) i =
                a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i
              rw [hz]
              have hLi : L x i = a * x i := by
                change scalarPiCLM (ι := ι) a x i = a * x i
                rw [scalarPiCLM_apply]
              rw [hLi]
  have hright :
      (Finset.univ.sum fun k =>
        gaussianCov ν i k *
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
            softmax β (fun r => c r + z r) i *
              softmax β (fun r => c r + z r) k) ∂ν) =
        (1 - t) *
          ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
    change (Finset.univ.sum fun k =>
        gaussianCov ν i k *
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
            softmax β (fun r => c r + z r) i *
              softmax β (fun r => c r + z r) k) ∂ν) =
      (1 - t) * ∫ x, (Finset.univ.sum fun k =>
        softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
          gaussianCov μX i k) ∂μX
    rw [integral_finset_sum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcov : gaussianCov ν i k = (1 - t) * gaussianCov μX i k := by
        calc
          gaussianCov ν i k = a ^ 2 * gaussianCov μX i k := by
            simpa [ν, L] using gaussianCov_map_scalarPiCLM μX a i k
          _ = (1 - t) * gaussianCov μX i k := by rw [ht_sq]
      have hint :
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
              softmax β (fun r => c r + z r) i *
                softmax β (fun r => c r + z r) k) ∂ν =
            ∫ x, β * ((if i = k then
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
              softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μX := by
        calc
          ∫ z, β * ((if i = k then softmax β (fun r => c r + z r) i else 0) -
              softmax β (fun r => c r + z r) i *
                softmax β (fun r => c r + z r) k) ∂ν
              = ∫ x, β * ((if i = k then softmax β (fun r => c r + L x r) i else 0) -
                  softmax β (fun r => c r + L x r) i *
                    softmax β (fun r => c r + L x r) k) ∂μX := by
                simpa [ν] using integral_map_linear_softmax_affine_deriv_term μX β c L i k
          _ = ∫ x, β * ((if i = k then
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
              softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μX := by
                refine integral_congr_ae ?_
                exact ae_of_all μX fun x => by
                  have hz : (fun r => c r + L x r) =
                      gaussianInterpMap (ι := ι) t (x, y) := by
                    ext r
                    change c r + L x r =
                      Real.sqrt (1 - t) * x r + Real.sqrt t * y r
                    rw [scalarPiCLM_apply]
                    dsimp [c, a]
                    ring
                  change β * ((if i = k then softmax β (fun r => c r + L x r) i else 0) -
                      softmax β (fun r => c r + L x r) i *
                        softmax β (fun r => c r + L x r) k) =
                    β * ((if i = k then
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                        softmax β (gaussianInterpMap (ι := ι) t (x, y)) k)
                  rw [hz]
      have hterm :
          ∫ x, softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
              gaussianCov μX i k ∂μX =
            gaussianCov μX i k *
              ∫ x, β * ((if i = k then
                  softmax β (gaussianInterpMap (ι := ι) t (x, y)) i else 0) -
                softmax β (gaussianInterpMap (ι := ι) t (x, y)) i *
                  softmax β (gaussianInterpMap (ι := ι) t (x, y)) k) ∂μX := by
        rw [← integral_const_mul]
        refine integral_congr_ae ?_
        exact ae_of_all μX fun x => by
          simp [softmaxHessianTerm]
          ring
      rw [hcov, hint, hterm]
      ring
    · intro k _
      have hcont : Continuous fun x : ι → ℝ =>
          softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k *
            gaussianCov μX i k := by
        exact ((continuous_softmax_deriv_term β i k).comp
          ((gaussianInterpMap (ι := ι) t).continuous.comp
            (Continuous.prodMk continuous_id continuous_const))).mul continuous_const
      refine Integrable.of_bound hcont.aestronglyMeasurable (|gaussianCov μX i k| * (|β| * 2)) ?_
      exact ae_of_all μX fun x => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |softmaxHessianTerm β (gaussianInterpMap (ι := ι) t (x, y)) i k| *
              |gaussianCov μX i k|
              ≤ (|β| * 2) * |gaussianCov μX i k| := by
                exact mul_le_mul_of_nonneg_right
                  (by
                    simpa [softmaxHessianTerm] using
                      abs_softmax_deriv_term_le β (gaussianInterpMap (ι := ι) t (x, y)) i k)
                  (abs_nonneg _)
          _ = |gaussianCov μX i k| * (|β| * 2) := by ring
  have hmain :
      ∫ x, a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX =
        (1 - t) *
          ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
    simpa [hleft, hright] using hstein
  have hscale :
      ∫ x, a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX =
        a * ∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
    calc
      ∫ x, a * x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX
          = ∫ x, a * (x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i) ∂μX := by
            refine integral_congr_ae ?_
            exact ae_of_all μX fun x => by ring
      _ = a * ∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
        rw [integral_const_mul]
  rw [hscale] at hmain
  have ht_eq : 1 - t = a * a := by
    rw [← ht_sq]
    ring
  have hI :
      (∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX) =
        a * ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
    have hmain' :
        a * (∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX) =
          a * (a *
            ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX) := by
      rw [hmain, ht_eq]
      ring
    exact (mul_right_inj' ha_ne).mp hmain'
  calc
    (1 / (2 * Real.sqrt (1 - t))) *
        (∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX)
        = (1 / (2 * a)) *
          (∫ x, x i * softmax β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX) := by
          rfl
    _ = (1 / 2) *
        ∫ x, softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t (x, y)) i ∂μX := by
      rw [hI]
      field_simp [ha_ne]

theorem integrable_softmaxHessianCovRow_gaussianInterpMap_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY μ : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (β t : ℝ) (i : ι) :
    Integrable
      (fun p : (ι → ℝ) × (ι → ℝ) =>
        softmaxHessianCovRow μ β (gaussianInterpMap (ι := ι) t p) i)
      (μX.prod μY) := by
  classical
  refine integrable_finset_sum (s := (Finset.univ : Finset ι)) fun k _ => ?_
  have hcont : Continuous fun p : (ι → ℝ) × (ι → ℝ) =>
      softmaxHessianTerm β (gaussianInterpMap (ι := ι) t p) i k *
        gaussianCov μ i k := by
    exact ((continuous_softmax_deriv_term β i k).comp
      (gaussianInterpMap (ι := ι) t).continuous).mul continuous_const
  refine Integrable.of_bound hcont.aestronglyMeasurable (|gaussianCov μ i k| * (|β| * 2)) ?_
  exact ae_of_all (μX.prod μY) fun p => by
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |softmaxHessianTerm β (gaussianInterpMap (ι := ι) t p) i k| *
          |gaussianCov μ i k|
          ≤ (|β| * 2) * |gaussianCov μ i k| := by
            exact mul_le_mul_of_nonneg_right
              (by
                simpa [softmaxHessianTerm] using
                  abs_softmax_deriv_term_le β (gaussianInterpMap (ι := ι) t p) i k)
              (abs_nonneg _)
      _ = |gaussianCov μ i k| * (|β| * 2) := by ring

theorem product_y_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (i : ι) :
    (1 / (2 * Real.sqrt t)) *
        (∫ p : (ι → ℝ) × (ι → ℝ),
          p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
      (1 / 2) *
        ∫ z, softmaxHessianCovRow μY β z i ∂gaussianInterpMeasure μX μY t := by
  classical
  let f : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i
  let g : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    softmaxHessianCovRow μY β (gaussianInterpMap (ι := ι) t p) i
  have hf : Integrable f (μX.prod μY) := by
    simpa [f] using (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).2
  have hg : Integrable g (μX.prod μY) := by
    simpa [g] using
      integrable_softmaxHessianCovRow_gaussianInterpMap_prod μX μY μY β t i
  haveI : IsFiniteMeasure (gaussianInterpMeasure μX μY t) := by
    dsimp [gaussianInterpMeasure]
    infer_instance
  have hmap :
      ∫ z, softmaxHessianCovRow μY β z i ∂gaussianInterpMeasure μX μY t =
        ∫ p, g p ∂μX.prod μY := by
    rw [gaussianInterpMeasure, integral_map]
    · exact (gaussianInterpMap (ι := ι) t).measurable.aemeasurable
    · exact (integrable_softmaxHessianCovRow
        (gaussianInterpMeasure μX μY t) μY β i).aestronglyMeasurable
  calc
    (1 / (2 * Real.sqrt t)) *
        (∫ p : (ι → ℝ) × (ι → ℝ),
          p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY)
        = (1 / (2 * Real.sqrt t)) * ∫ p, f p ∂μX.prod μY := by rfl
    _ = (1 / (2 * Real.sqrt t)) * ∫ x, ∫ y, f (x, y) ∂μY ∂μX := by
      rw [integral_prod f hf]
    _ = ∫ x, (1 / (2 * Real.sqrt t)) * ∫ y, f (x, y) ∂μY ∂μX := by
      rw [integral_const_mul]
    _ = ∫ x, (1 / 2) * ∫ y, g (x, y) ∂μY ∂μX := by
      refine integral_congr_ae ?_
      exact ae_of_all μX fun x => by
        simpa [f, g] using fixed_y_endpoint_stein μY hY0 β ht x i
    _ = (1 / 2) * ∫ x, ∫ y, g (x, y) ∂μY ∂μX := by
      rw [integral_const_mul]
    _ = (1 / 2) * ∫ p, g p ∂μX.prod μY := by
      rw [integral_prod g hg]
    _ = (1 / 2) *
        ∫ z, softmaxHessianCovRow μY β z i ∂gaussianInterpMeasure μX μY t := by
      rw [hmap]

theorem product_x_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (i : ι) :
    (1 / (2 * Real.sqrt (1 - t))) *
        (∫ p : (ι → ℝ) × (ι → ℝ),
          p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
      (1 / 2) *
        ∫ z, softmaxHessianCovRow μX β z i ∂gaussianInterpMeasure μX μY t := by
  classical
  let f : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i
  let g : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    softmaxHessianCovRow μX β (gaussianInterpMap (ι := ι) t p) i
  have hf : Integrable f (μX.prod μY) := by
    simpa [f] using (integrable_gaussianInterpMap_coord_mul_softmax μX μY β t i).1
  have hg : Integrable g (μX.prod μY) := by
    simpa [g] using
      integrable_softmaxHessianCovRow_gaussianInterpMap_prod μX μY μX β t i
  haveI : IsFiniteMeasure (gaussianInterpMeasure μX μY t) := by
    dsimp [gaussianInterpMeasure]
    infer_instance
  have hmap :
      ∫ z, softmaxHessianCovRow μX β z i ∂gaussianInterpMeasure μX μY t =
        ∫ p, g p ∂μX.prod μY := by
    rw [gaussianInterpMeasure, integral_map]
    · exact (gaussianInterpMap (ι := ι) t).measurable.aemeasurable
    · exact (integrable_softmaxHessianCovRow
        (gaussianInterpMeasure μX μY t) μX β i).aestronglyMeasurable
  calc
    (1 / (2 * Real.sqrt (1 - t))) *
        (∫ p : (ι → ℝ) × (ι → ℝ),
          p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY)
        = (1 / (2 * Real.sqrt (1 - t))) * ∫ p, f p ∂μX.prod μY := by rfl
    _ = (1 / (2 * Real.sqrt (1 - t))) * ∫ y, ∫ x, f (x, y) ∂μX ∂μY := by
      rw [integral_prod_symm f hf]
    _ = ∫ y, (1 / (2 * Real.sqrt (1 - t))) * ∫ x, f (x, y) ∂μX ∂μY := by
      rw [integral_const_mul]
    _ = ∫ y, (1 / 2) * ∫ x, g (x, y) ∂μX ∂μY := by
      refine integral_congr_ae ?_
      exact ae_of_all μY fun y => by
        simpa [f, g] using fixed_x_endpoint_stein μX hX0 β ht y i
    _ = (1 / 2) * ∫ y, ∫ x, g (x, y) ∂μX ∂μY := by
      rw [integral_const_mul]
    _ = (1 / 2) * ∫ p, g p ∂μX.prod μY := by
      rw [integral_prod_symm g hg]
    _ = (1 / 2) *
        ∫ z, softmaxHessianCovRow μX β z i ∂gaussianInterpMeasure μX μY t := by
      rw [hmap]

/-- Coordinate covariance of the interpolation law, before simplifying the square roots.

The explicit `IsGaussian` assumption for the interpolation law avoids expensive typeclass search
through the product Gaussian instance; later uses can provide it locally once the interpolation law
has been constructed as a Gaussian linear image. -/
theorem gaussianCov_gaussianInterpMeasure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (t : ℝ) [IsGaussian (gaussianInterpMeasure μX μY t)]
    (i j : ι) :
    gaussianCov (gaussianInterpMeasure μX μY t) i j =
      (Real.sqrt (1 - t)) ^ 2 * gaussianCov μX i j +
        (Real.sqrt t) ^ 2 * gaussianCov μY i j := by
  classical
  let a : ℝ := Real.sqrt (1 - t)
  let b : ℝ := Real.sqrt t
  let μ : Measure ((ι → ℝ) × (ι → ℝ)) := μX.prod μY
  have hXi2 (k : ι) : MemLp (fun p : (ι → ℝ) × (ι → ℝ) => p.1 k) 2 μ := by
    simpa [μ, coordCLM] using
      (IsGaussian.memLp_dual μX (coordCLM k) 2 (by simp)).comp_fst μY
  have hYi2 (k : ι) : MemLp (fun p : (ι → ℝ) × (ι → ℝ) => p.2 k) 2 μ := by
    simpa [μ, coordCLM] using
      (IsGaussian.memLp_dual μY (coordCLM k) 2 (by simp)).comp_snd μX
  rw [gaussianCov_eq_covariance]
  rw [gaussianInterpMeasure]
  rw [covariance_map_fun
    (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable
    (gaussianInterpMap (ι := ι) t).measurable.aemeasurable]
  change
    cov[(fun p : (ι → ℝ) × (ι → ℝ) => a * p.1 i + b * p.2 i),
        (fun p : (ι → ℝ) × (ι → ℝ) => a * p.1 j + b * p.2 j); μ] =
      a ^ 2 * gaussianCov μX i j + b ^ 2 * gaussianCov μY i j
  change
    cov[(fun p : (ι → ℝ) × (ι → ℝ) => a * p.1 i) + (fun p => b * p.2 i),
        (fun p : (ι → ℝ) × (ι → ℝ) => a * p.1 j) + (fun p => b * p.2 j); μ] =
      a ^ 2 * gaussianCov μX i j + b ^ 2 * gaussianCov μY i j
  rw [covariance_add_left ((hXi2 i).const_mul a) ((hYi2 i).const_mul b)
    (((hXi2 j).const_mul a).add ((hYi2 j).const_mul b))]
  rw [covariance_add_right ((hXi2 i).const_mul a)
    ((hXi2 j).const_mul a) ((hYi2 j).const_mul b)]
  rw [covariance_add_right ((hYi2 i).const_mul b)
    ((hXi2 j).const_mul a) ((hYi2 j).const_mul b)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  have hcross₁ :
      cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.1 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.2 j); μ] = 0 := by
    simpa [μ] using covariance_fst_snd_prod (μ := μX) (ν := μY)
      (X := fun x : ι → ℝ => x i) (Y := fun y : ι → ℝ => y j)
      (by simpa [coordCLM] using IsGaussian.memLp_dual μX (coordCLM i) 2 (by simp))
      (by simpa [coordCLM] using IsGaussian.memLp_dual μY (coordCLM j) 2 (by simp))
  have hcross₂ :
      cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.2 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.1 j); μ] = 0 := by
    rw [covariance_comm]
    simpa [μ] using covariance_fst_snd_prod (μ := μX) (ν := μY)
      (X := fun x : ι → ℝ => x j) (Y := fun y : ι → ℝ => y i)
      (by simpa [coordCLM] using IsGaussian.memLp_dual μX (coordCLM j) 2 (by simp))
      (by simpa [coordCLM] using IsGaussian.memLp_dual μY (coordCLM i) 2 (by simp))
  have hfst :
      cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.1 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.1 j); μ] =
        cov[(fun x : ι → ℝ => x i), (fun x : ι → ℝ => x j); μX] := by
    have hmap := covariance_map_fun
      (μ := μ) (Z := Prod.fst)
      (X := fun x : ι → ℝ => x i) (Y := fun x : ι → ℝ => x j)
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
      measurable_fst.aemeasurable
    change
      cov[(fun x : ι → ℝ => x i), (fun x : ι → ℝ => x j); Measure.map Prod.fst μ] =
        cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.1 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.1 j); μ] at hmap
    dsimp [μ] at hmap
    rw [Measure.map_fst_prod] at hmap
    simpa [measure_univ] using hmap.symm
  have hsnd :
      cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.2 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.2 j); μ] =
        cov[(fun y : ι → ℝ => y i), (fun y : ι → ℝ => y j); μY] := by
    have hmap := covariance_map_fun
      (μ := μ) (Z := Prod.snd)
      (X := fun y : ι → ℝ => y i) (Y := fun y : ι → ℝ => y j)
      (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable
      measurable_snd.aemeasurable
    change
      cov[(fun y : ι → ℝ => y i), (fun y : ι → ℝ => y j); Measure.map Prod.snd μ] =
        cov[(fun p : (ι → ℝ) × (ι → ℝ) => p.2 i),
          (fun p : (ι → ℝ) × (ι → ℝ) => p.2 j); μ] at hmap
    dsimp [μ] at hmap
    rw [Measure.map_snd_prod] at hmap
    simpa [measure_univ] using hmap.symm
  rw [hcross₁, hcross₂]
  rw [hfst, hsnd]
  rw [← gaussianCov_eq_covariance μX i j]
  rw [← gaussianCov_eq_covariance μY i j]
  ring

/-- Coordinate covariance of the interpolation law on the interpolation interval. -/
theorem gaussianCov_gaussianInterpMeasure_of_mem_Icc
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (t : ℝ) [IsGaussian (gaussianInterpMeasure μX μY t)]
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i j : ι) :
    gaussianCov (gaussianInterpMeasure μX μY t) i j =
      (1 - t) * gaussianCov μX i j + t * gaussianCov μY i j := by
  rw [gaussianCov_gaussianInterpMeasure μX μY t i j]
  rw [Real.sq_sqrt (by linarith [ht.2]), Real.sq_sqrt ht.1]

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

/-- Gaussian interpolation monotonicity, reduced to the concrete derivative formula for
`gaussianInterpolationLSE`.

The remaining analytic step is to prove `hderiv` by differentiating the integral along the
interpolation path and applying `gaussian_ibp_softmax` to the interpolated Gaussian law. -/
theorem gaussian_interpolation_lse_mono_of_deriv_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 < β)
    (hFcont : ContinuousOn (gaussianInterpolationLSE μX μY β) (Set.Icc 0 1))
    (hFdiff : DifferentiableOn ℝ (gaussianInterpolationLSE μX μY β)
      (interior (Set.Icc (0 : ℝ) 1)))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      deriv (gaussianInterpolationLSE μX μY β) t =
        (1 / 2) *
          ∫ z,
            (Finset.univ.sum fun i =>
              Finset.univ.sum fun j =>
                β * ((if i = j then softmax β z i else 0) -
                  softmax β z i * softmax β z j) *
                    (gaussianCov μY i j - gaussianCov μX i j))
            ∂gaussianInterpMeasure μX μY t) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
  refine gaussian_interpolation_lse_mono_of_deriv_nonneg
    μX μY β (gaussianInterpolationLSE μX μY β) ?_ ?_ hFcont hFdiff ?_
  · exact gaussianInterpolationLSE_zero μX μY β
  · exact gaussianInterpolationLSE_one μX μY β
  · intro t ht
    rw [hderiv t ht]
    refine mul_nonneg ?_ ?_
    · norm_num
    · exact integral_nonneg fun z =>
        softmax_hessian_cov_contraction_nonneg_of_variance_le μX μY hinc hβ.le z

theorem gaussian_interpolation_lse_mono_of_deriv_formula'
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 < β)
    (hFcont : ContinuousOn (gaussianInterpolationLSE μX μY β) (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      deriv (gaussianInterpolationLSE μX μY β) t =
        (1 / 2) *
          ∫ z,
            (Finset.univ.sum fun i =>
              Finset.univ.sum fun j =>
                β * ((if i = j then softmax β z i else 0) -
                  softmax β z i * softmax β z j) *
                    (gaussianCov μY i j - gaussianCov μX i j))
            ∂gaussianInterpMeasure μX μY t) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY :=
  gaussian_interpolation_lse_mono_of_deriv_formula μX μY hinc hβ hFcont
    (differentiableOn_gaussianInterpolationLSE μX μY hβ) hderiv

theorem gaussian_interpolation_lse_mono_of_integrand_formula
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 < β)
    (hFcont : ContinuousOn (gaussianInterpolationLSE μX μY β) (Set.Icc 0 1))
    (hintegrand : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY) =
        (1 / 2) *
          ∫ z,
            (Finset.univ.sum fun i =>
              Finset.univ.sum fun j =>
                β * ((if i = j then softmax β z i else 0) -
                  softmax β z i * softmax β z j) *
                    (gaussianCov μY i j - gaussianCov μX i j))
            ∂gaussianInterpMeasure μX μY t) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
  refine gaussian_interpolation_lse_mono_of_deriv_formula' μX μY hinc hβ hFcont ?_
  intro t ht
  rw [deriv_gaussianInterpolationLSE_eq_integral μX μY hβ ht]
  exact hintegrand t ht

theorem gaussian_interpolation_lse_mono_of_endpoint_stein
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 < β)
    (hFcont : ContinuousOn (gaussianInterpolationLSE μX μY β) (Set.Icc 0 1))
    (hYstein : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i,
      (1 / (2 * Real.sqrt t)) *
          (∫ p : (ι → ℝ) × (ι → ℝ),
            p.2 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
        (1 / 2) *
          ∫ z, softmaxHessianCovRow μY β z i ∂gaussianInterpMeasure μX μY t)
    (hXstein : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∀ i,
      (1 / (2 * Real.sqrt (1 - t))) *
          (∫ p : (ι → ℝ) × (ι → ℝ),
            p.1 i * softmax β (gaussianInterpMap (ι := ι) t p) i ∂μX.prod μY) =
        (1 / 2) *
          ∫ z, softmaxHessianCovRow μX β z i ∂gaussianInterpMeasure μX μY t) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
  refine gaussian_interpolation_lse_mono_of_integrand_formula μX μY hinc hβ hFcont ?_
  intro t ht
  calc
    (∫ p, gaussianInterpLSEDerivIntegrand (ι := ι) β t p ∂μX.prod μY)
        = (1 / 2) *
            ∫ z, softmaxHessianCovDiffSum μX μY β z ∂gaussianInterpMeasure μX μY t := by
          exact integral_gaussianInterpLSEDerivIntegrand_eq_hessian_of_endpoint_stein
            μX μY β t (hYstein t ht) (hXstein t ht)
    _ = (1 / 2) *
          ∫ z,
            (Finset.univ.sum fun i =>
              Finset.univ.sum fun j =>
                β * ((if i = j then softmax β z i else 0) -
                  softmax β z i * softmax β z j) *
                    (gaussianCov μY i j - gaussianCov μX i j))
            ∂gaussianInterpMeasure μX μY t := by
          apply congrArg (fun r => (1 / 2) * r)
          refine integral_congr_ae ?_
          exact ae_of_all (gaussianInterpMeasure μX μY t) fun z =>
            softmaxHessianCovDiffSum_eq μX μY β z

theorem gaussian_interpolation_lse_mono_of_continuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX
        ≤ variance (fun y : ι → ℝ => y i - y j) μY)
    {β : ℝ} (hβ : 0 < β)
    (hFcont : ContinuousOn (gaussianInterpolationLSE μX μY β) (Set.Icc 0 1)) :
    ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
  refine gaussian_interpolation_lse_mono_of_endpoint_stein μX μY hinc hβ hFcont ?_ ?_
  · intro t ht i
    exact product_y_endpoint_stein μX μY hY0 β ht i
  · intro t ht i
    exact product_x_endpoint_stein μX μY hX0 β ht i

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
