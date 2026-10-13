import LeanSudakov.SudakovFernique

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal

namespace LeanSudakov

noncomputable section

/-- Interpolation with a common deterministic drift held fixed. -/
def gaussianDriftInterp {ι : Type*} (a : ι → ℝ) (t : ℝ)
    (p : (ι → ℝ) × (ι → ℝ)) : ι → ℝ :=
  a + gaussianInterpMap t p

theorem continuous_gaussianDriftInterp {ι : Type*} (a : ι → ℝ) (t : ℝ) :
    Continuous (gaussianDriftInterp a t) :=
  continuous_const.add (gaussianInterpMap t).continuous

def gaussianDriftInterpDeriv {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (β t : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  ∑ i, softmax β (gaussianDriftInterp a t p) i *
    (p.2 i / (2 * Real.sqrt t) - p.1 i / (2 * Real.sqrt (1 - t)))

theorem hasDerivAt_lse_gaussianDriftInterp
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    {β t : ℝ} (hβ : β ≠ 0) (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) :
    HasDerivAt (fun s => lse β (gaussianDriftInterp a s p))
      (gaussianDriftInterpDeriv a β t p) t := by
  apply hasDerivAt_lse_of_coord hβ
  intro i
  exact (hasDerivAt_gaussianInterpMap_apply ht p i).const_add (a i)

theorem continuous_gaussianDriftInterpDeriv
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (β t : ℝ) :
    Continuous (gaussianDriftInterpDeriv a β t) := by
  apply continuous_finset_sum
  intro i _
  exact ((continuous_softmax β i).comp (continuous_gaussianDriftInterp a t)).mul
    ((((continuous_apply i).comp continuous_snd).div_const _).sub
      (((continuous_apply i).comp continuous_fst).div_const _))

def gaussianDriftInterpBound {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (β : ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  (∑ i, |a i|) + gaussianInterpLSEBound β p

theorem norm_lse_gaussianDriftInterp_le
    {ι : Type*} [Fintype ι] [Nonempty ι] (a : ι → ℝ)
    {β t : ℝ} (hβ : 0 < β) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (p : (ι → ℝ) × (ι → ℝ)) :
    ‖lse β (gaussianDriftInterp a t p)‖ ≤ gaussianDriftInterpBound a β p := by
  have hs : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht.2
  have h1s : Real.sqrt (1 - t) ≤ 1 := Real.sqrt_le_one.mpr (by linarith [ht.1])
  have hb (i : ι) : |gaussianDriftInterp a t p i| ≤ |a i| + (|p.1 i| + |p.2 i|) := by
    change |a i + gaussianInterpMap t p i| ≤ _
    rw [gaussianInterpMap_apply]
    calc
      _ ≤ |a i| + (|Real.sqrt (1 - t) * p.1 i| + |Real.sqrt t * p.2 i|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ = |a i| + (Real.sqrt (1 - t) * |p.1 i| + Real.sqrt t * |p.2 i|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
          abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ _ := by
        apply add_le_add le_rfl
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) h1s)
          (mul_le_of_le_one_left (abs_nonneg _) hs)
  rw [Real.norm_eq_abs]
  calc
    _ ≤ (∑ i, |gaussianDriftInterp a t p i|) + Real.log (Fintype.card ι) / β :=
      abs_lse_le_sum_abs_add hβ _
    _ ≤ (∑ i, (|a i| + (|p.1 i| + |p.2 i|))) + Real.log (Fintype.card ι) / β :=
      add_le_add (Finset.sum_le_sum fun i _ => hb i) le_rfl
    _ = _ := by simp [gaussianDriftInterpBound, gaussianInterpLSEBound, Finset.sum_add_distrib,
      add_assoc]

theorem integrable_gaussianDriftInterpBound
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ))
    [IsGaussian μX] [IsGaussian μY] (a : ι → ℝ) (β : ℝ) :
    Integrable (gaussianDriftInterpBound a β) (μX.prod μY) :=
  (integrable_const _).add (integrable_gaussianInterpLSEBound μX μY β)

theorem integrable_lse_gaussianDriftInterp
    {ι : Type*} [Fintype ι] [Nonempty ι] (μX μY : Measure (ι → ℝ))
    [IsGaussian μX] [IsGaussian μY] (a : ι → ℝ)
    {β t : ℝ} (hβ : 0 < β) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun p => lse β (gaussianDriftInterp a t p)) (μX.prod μY) := by
  exact (integrable_gaussianDriftInterpBound μX μY a β).mono'
    (((continuous_lse β).comp (continuous_gaussianDriftInterp a t)).aestronglyMeasurable)
    (ae_of_all _ (norm_lse_gaussianDriftInterp_le a hβ ht))

theorem continuousOn_integral_lse_gaussianDriftInterp
    {ι : Type*} [Fintype ι] [Nonempty ι] (μX μY : Measure (ι → ℝ))
    [IsGaussian μX] [IsGaussian μY] (a : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    ContinuousOn (fun t => ∫ p, lse β (gaussianDriftInterp a t p) ∂μX.prod μY)
      (Set.Icc 0 1) := by
  apply continuousOn_of_dominated (bound := gaussianDriftInterpBound a β)
  · intro t _
    exact ((continuous_lse β).comp (continuous_gaussianDriftInterp a t)).aestronglyMeasurable
  · intro t ht
    exact ae_of_all _ (norm_lse_gaussianDriftInterp_le a hβ ht)
  · exact integrable_gaussianDriftInterpBound μX μY a β
  · exact ae_of_all _ fun p => by
      apply Continuous.continuousOn
      apply (continuous_lse β).comp
      apply continuous_pi
      intro i
      change Continuous fun t => a i + gaussianInterpMap t p i
      simp only [gaussianInterpMap_apply]
      fun_prop

theorem hasDerivAt_integral_lse_gaussianDriftInterp
    {ι : Type*} [Fintype ι] [Nonempty ι] (μX μY : Measure (ι → ℝ))
    [IsGaussian μX] [IsGaussian μY] (a : ι → ℝ)
    {β t : ℝ} (hβ : 0 < β) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => ∫ p, lse β (gaussianDriftInterp a s p) ∂μX.prod μY)
      (∫ p, gaussianDriftInterpDeriv a β t p ∂μX.prod μY) t := by
  have hlocal : Set.Ioo (t / 2) ((t + 1) / 2) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds (by constructor <;> linarith [ht.1, ht.2])
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (t / 2) ((t + 1) / 2))
    (bound := gaussianInterpLSEDerivBound (ι := ι) t) hlocal
    (Eventually.of_forall fun s =>
      ((continuous_lse β).comp (continuous_gaussianDriftInterp a s)).aestronglyMeasurable)
    (integrable_lse_gaussianDriftInterp μX μY a hβ ⟨ht.1.le, ht.2.le⟩)
    (continuous_gaussianDriftInterpDeriv a β t).aestronglyMeasurable
    (ae_of_all _ fun p s hs =>
      softmax_interp_deriv_le_bound β (gaussianDriftInterp a s p) ht hs p)
    (integrable_gaussianInterpLSEDerivBound μX μY t)
    (ae_of_all _ fun p s hs =>
      hasDerivAt_lse_gaussianDriftInterp a hβ.ne'
        (by constructor <;> linarith [ht.1, ht.2, hs.1, hs.2]) p)).2

theorem integrable_gaussianDriftInterp_coord_mul_softmax
    {ι : Type*} [Fintype ι] (μX μY : Measure (ι → ℝ))
    [IsGaussian μX] [IsGaussian μY] (a : ι → ℝ) (β t : ℝ) (i : ι) :
    Integrable (fun p => p.1 i * softmax β (gaussianDriftInterp a t p) i) (μX.prod μY) ∧
    Integrable (fun p => p.2 i * softmax β (gaussianDriftInterp a t p) i) (μX.prod μY) := by
  have hs : MemLp (fun p => softmax β (gaussianDriftInterp a t p) i) ∞ (μX.prod μY) :=
    memLp_top_of_bound
      (((continuous_softmax β i).comp (continuous_gaussianDriftInterp a t)).aestronglyMeasurable)
      1 (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using abs_softmax_le_one β _ i)
  exact ⟨((gaussian_integrable_coord μX i).comp_fst μY).mul_of_top_left hs,
    ((gaussian_integrable_coord μY i).comp_snd μX).mul_of_top_left hs⟩

theorem integrable_gaussianDriftInterp_covRow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure ((ι → ℝ) × (ι → ℝ))) [IsFiniteMeasure μ]
    (ν : Measure (ι → ℝ)) (a : ι → ℝ) (β t : ℝ) (i : ι) :
    Integrable (fun p => softmaxHessianCovRow ν β (gaussianDriftInterp a t p) i) μ := by
  have h := integrable_softmaxHessianCovRow (μ.map (gaussianDriftInterp a t)) ν β i
  exact (integrable_map_measure h.aestronglyMeasurable
    (continuous_gaussianDriftInterp a t).measurable.aemeasurable).mp h

theorem fixed_y_endpoint_stein_drift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μY : Measure (ι → ℝ)) [IsGaussian μY]
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0) (a : ι → ℝ)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : ι → ℝ) (i : ι) :
    (1 / (2 * Real.sqrt t)) *
        (∫ y, y i * softmax β (gaussianDriftInterp a t (x, y)) i ∂μY) =
      (1 / 2) * ∫ y, softmaxHessianCovRow μY β (gaussianDriftInterp a t (x, y)) i ∂μY := by
  have hs : Real.sqrt (1 - t) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith [ht.2])
  have heq (y : ι → ℝ) :
      gaussianInterpMap t ((fun k => x k + a k / Real.sqrt (1 - t)), y) =
        gaussianDriftInterp a t (x, y) := by
    ext k
    simp only [gaussianInterpMap_apply, gaussianDriftInterp, Pi.add_apply]
    field_simp [hs]
    ring
  simpa only [heq] using
    fixed_y_endpoint_stein μY hY0 β ht (fun k => x k + a k / Real.sqrt (1 - t)) i

theorem fixed_x_endpoint_stein_drift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX : Measure (ι → ℝ)) [IsGaussian μX]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (a : ι → ℝ)
    (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (y : ι → ℝ) (i : ι) :
    (1 / (2 * Real.sqrt (1 - t))) *
        (∫ x, x i * softmax β (gaussianDriftInterp a t (x, y)) i ∂μX) =
      (1 / 2) * ∫ x, softmaxHessianCovRow μX β (gaussianDriftInterp a t (x, y)) i ∂μX := by
  have hs : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht.1
  have heq (x : ι → ℝ) :
      gaussianInterpMap t (x, (fun k => y k + a k / Real.sqrt t)) =
        gaussianDriftInterp a t (x, y) := by
    ext k
    simp only [gaussianInterpMap_apply, gaussianDriftInterp, Pi.add_apply]
    field_simp [hs]
    ring
  simpa only [heq] using
    fixed_x_endpoint_stein μX hX0 β ht (fun k => y k + a k / Real.sqrt t) i

theorem product_endpoint_stein_drift
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (a : ι → ℝ) (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) (i : ι) :
    ((1 / (2 * Real.sqrt t)) *
        (∫ p, p.2 i * softmax β (gaussianDriftInterp a t p) i ∂μX.prod μY) =
      (1 / 2) * ∫ p, softmaxHessianCovRow μY β (gaussianDriftInterp a t p) i ∂μX.prod μY) ∧
    ((1 / (2 * Real.sqrt (1 - t))) *
        (∫ p, p.1 i * softmax β (gaussianDriftInterp a t p) i ∂μX.prod μY) =
      (1 / 2) * ∫ p, softmaxHessianCovRow μX β (gaussianDriftInterp a t p) i ∂μX.prod μY) := by
  obtain ⟨hX, hY⟩ := integrable_gaussianDriftInterp_coord_mul_softmax μX μY a β t i
  have hrowX := integrable_gaussianDriftInterp_covRow (μX.prod μY) μX a β t i
  have hrowY := integrable_gaussianDriftInterp_covRow (μX.prod μY) μY a β t i
  constructor
  · rw [integral_prod _ hY, integral_prod _ hrowY, ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => fixed_y_endpoint_stein_drift μY hY0 a β ht x i)
  · rw [integral_prod_symm _ hX, integral_prod_symm _ hrowX,
      ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => fixed_x_endpoint_stein_drift μX hX0 a β ht y i)

theorem integral_gaussianDriftInterpDeriv_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (a : ι → ℝ) (β : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ p, gaussianDriftInterpDeriv a β t p ∂μX.prod μY) =
      (1 / 2) * ∫ p, softmaxHessianCovDiffSum μX μY β (gaussianDriftInterp a t p) ∂μX.prod μY := by
  have hterm (i : ι) :
      Integrable (fun p => softmax β (gaussianDriftInterp a t p) i *
        (p.2 i / (2 * Real.sqrt t) - p.1 i / (2 * Real.sqrt (1 - t)))) (μX.prod μY) := by
    obtain ⟨hX, hY⟩ := integrable_gaussianDriftInterp_coord_mul_softmax μX μY a β t i
    convert (hY.const_mul (1 / (2 * Real.sqrt t))).sub
      (hX.const_mul (1 / (2 * Real.sqrt (1 - t)))) using 1
    ext p
    dsimp
    ring
  have hrow (i : ι) : Integrable (fun p =>
      softmaxHessianCovRow μY β (gaussianDriftInterp a t p) i -
        softmaxHessianCovRow μX β (gaussianDriftInterp a t p) i) (μX.prod μY) :=
    (integrable_gaussianDriftInterp_covRow (μX.prod μY) μY a β t i).sub
      (integrable_gaussianDriftInterp_covRow (μX.prod μY) μX a β t i)
  have heq (p : (ι → ℝ) × (ι → ℝ)) :
      softmaxHessianCovDiffSum μX μY β (gaussianDriftInterp a t p) =
        ∑ i, (softmaxHessianCovRow μY β (gaussianDriftInterp a t p) i -
          softmaxHessianCovRow μX β (gaussianDriftInterp a t p) i) := by
    simp only [softmaxHessianCovDiffSum, softmaxHessianCovRow_sub]
  simp_rw [heq]
  simp only [gaussianDriftInterpDeriv]
  rw [integral_finset_sum Finset.univ (fun i _ => hterm i),
    integral_finset_sum Finset.univ (fun i _ => hrow i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨hX, hY⟩ := integrable_gaussianDriftInterp_coord_mul_softmax μX μY a β t i
  obtain ⟨hSY, hSX⟩ := product_endpoint_stein_drift μX μY hX0 hY0 a β ht i
  rw [integral_sub (integrable_gaussianDriftInterp_covRow _ μY a β t i)
    (integrable_gaussianDriftInterp_covRow _ μX a β t i), mul_sub, ← hSY, ← hSX]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hY.const_mul _) (hX.const_mul _)]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by dsimp; ring

/-- Log-sum-exp comparison with an arbitrary common deterministic drift. -/
theorem gaussian_interpolation_lse_mono_drift
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY)
    (a : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    ∫ x, lse β (a + x) ∂μX ≤ ∫ y, lse β (a + y) ∂μY := by
  let F := fun t => ∫ p, lse β (gaussianDriftInterp a t p) ∂μX.prod μY
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :=
    hasDerivAt_integral_lse_gaussianDriftInterp μX μY a hβ ht
  have hmono : MonotoneOn F (Set.Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuousOn_integral_lse_gaussianDriftInterp μX μY a hβ)
    · intro t ht
      exact (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (by simpa using ht)).deriv,
        integral_gaussianDriftInterpDeriv_eq μX μY hX0 hY0 a β (by simpa using ht)]
      apply mul_nonneg (by norm_num)
      apply integral_nonneg
      intro p
      exact softmax_hessian_cov_contraction_nonneg_of_variance_le μX μY hinc hβ.le _
  have hmain := hmono (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) ≤ 1)
  have h0 : F 0 = ∫ x, lse β (a + x) ∂μX := by
    simp only [F, gaussianDriftInterp, gaussianInterpMap_zero]
    change (∫ p, lse β (a + p.1) ∂μX.prod μY) = _
    rw [integral_fun_fst (fun x => lse β (a + x))]
    simp
  have h1 : F 1 = ∫ y, lse β (a + y) ∂μY := by
    simp only [F, gaussianDriftInterp, gaussianInterpMap_one]
    change (∫ p, lse β (a + p.2) ∂μX.prod μY) = _
    rw [integral_fun_snd (fun y => lse β (a + y))]
    simp
  rwa [h0, h1] at hmain

theorem gaussian_integrable_vecMax_drift
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (a : ι → ℝ) :
    Integrable (fun x => vecMax (a + x)) μ := by
  have h := gaussian_integrable_vecMax (μ.map (fun x => a + x))
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_const.add measurable_id).aemeasurable).mp h

theorem gaussian_integrable_lse_drift
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ] (a : ι → ℝ) {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x => lse β (a + x)) μ := by
  have h := gaussian_integrable_lse (μ.map (fun x => a + x)) hβ
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_const.add measurable_id).aemeasurable).mp h

/-- Finite Sudakov-Fernique for `a i + X i` and `a i + Y i`, with the same arbitrary drift. -/
theorem sudakov_fernique_drift
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY)
    (a : ι → ℝ) :
    ∫ x, vecMax (a + x) ∂μX ≤ ∫ y, vecMax (a + y) ∂μY := by
  apply le_of_forall_pos_le_add_div (c := Real.log (Fintype.card ι))
  intro β hβ
  have hX := gaussian_integrable_vecMax_drift μX a
  have hY := gaussian_integrable_vecMax_drift μY a
  have hlX := gaussian_integrable_lse_drift μX a hβ
  have hlY := gaussian_integrable_lse_drift μY a hβ
  calc
    _ ≤ ∫ x, lse β (a + x) ∂μX := integral_mono hX hlX (fun x => vecMax_le_lse hβ _)
    _ ≤ ∫ y, lse β (a + y) ∂μY := gaussian_interpolation_lse_mono_drift μX μY hX0 hY0 hinc a hβ
    _ ≤ ∫ y, (vecMax (a + y) + Real.log (Fintype.card ι) / β) ∂μY :=
      integral_mono hlY (hY.add (integrable_const _)) (fun y => lse_le_vecMax_add hβ _)
    _ = _ := by rw [integral_add hY (integrable_const _), integral_const]; simp

end

end LeanSudakov
