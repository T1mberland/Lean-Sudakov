import LeanSudakov.CountableSudakovExtended
import LeanSudakov.SudakovFerniqueDrift
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Monotone

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

noncomputable section

/-- Extended expected supremum, retaining negative finite values as well as `+∞`.
With integrable coordinates, `countableExpectedSupEReal_eq` gives its integral interpretation. -/
def countableExpectedSupEReal {ι : Type*} (μ : Measure (ι → ℝ)) : EReal :=
  ⨆ (s : Finset ι) (hs : s.Nonempty), (((∫ x, finsetMax s hs x ∂μ) : ℝ) : EReal)

/-- Extended expected supremum of the process `a i + X i`. -/
def countableExpectedSupDrift {ι : Type*} (a : ι → ℝ) (μ : Measure (ι → ℝ)) : EReal :=
  countableExpectedSupEReal (μ.map (fun x => a + x))

theorem countableExpectedSupEReal_ne_bot
    {ι : Type*} [Nonempty ι] (μ : Measure (ι → ℝ)) :
    countableExpectedSupEReal μ ≠ ⊥ := by
  classical
  let i : ι := Classical.choice inferInstance
  have h : (((∫ x, finsetMax {i} (Finset.singleton_nonempty i) x ∂μ) : ℝ) : EReal) ≤
      countableExpectedSupEReal μ :=
    le_iSup_of_le {i} (le_iSup_of_le (Finset.singleton_nonempty i) le_rfl)
  exact (lt_of_lt_of_le (EReal.bot_lt_coe _) h).ne'

theorem measurable_finsetMax {ι : Type*} (s : Finset ι) (hs : s.Nonempty) :
    Measurable (finsetMax s hs) := by
  have h := Finset.measurable_sup' hs (fun i _ =>
    measurable_pi_apply (X := fun _ : ι => ℝ) i)
  have heq : s.sup' hs (fun i (x : ι → ℝ) => x i) = finsetMax s hs := by
    funext x
    exact Finset.sup'_apply hs _ x
  rwa [heq] at h

/-- An integrable lower bound permits a nonnegative integral without losing its mean. -/
theorem ereal_integral_eq_add_lintegral_sub
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f g : Ω → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hle : g ≤ᵐ[μ] f) :
    (((∫ x, f x ∂μ) : ℝ) : EReal) =
      (((∫ x, g x ∂μ) : ℝ) : EReal) + ((∫⁻ x, ENNReal.ofReal (f x - g x) ∂μ) : EReal) := by
  have hn : 0 ≤ (∫ x, f x ∂μ) - ∫ x, g x ∂μ :=
    sub_nonneg.mpr (integral_mono_ae hg hf hle)
  rw [← ofReal_integral_eq_lintegral_ofReal (f := fun x => f x - g x)
    (hf.sub hg) (hle.mono fun x hx => sub_nonneg.mpr hx), integral_sub hf hg,
    EReal.coe_ennreal_ofReal, max_eq_left hn, ← EReal.coe_add]
  congr 1
  ring

private theorem ereal_add_coe_iSup (c : ℝ) (f : ℕ → ℝ≥0∞) :
    (c : EReal) + (((⨆ n, f n) : ℝ≥0∞) : EReal) = ⨆ n, (c : EReal) + (f n : EReal) := by
  apply Monotone.map_ciSup_of_continuousAt
    (f := fun y : ℝ≥0∞ => (c : EReal) + (y : EReal)) (g := f)
  · exact (EReal.continuousAt_add (Or.inl (EReal.coe_ne_top c))
      (Or.inl (EReal.coe_ne_bot c))).comp
      (continuous_const.prodMk continuous_coe_ennreal_ereal).continuousAt
  · intro x y h
    exact add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr h)

/-- Monotone convergence identifies the extended expectation with an anchored integral,
without boundedness, centering, or integrability of the supremum. -/
theorem countableExpectedSupEReal_eq
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ) :
    countableExpectedSupEReal μ =
      (((∫ x, x i0 ∂μ) : ℝ) : EReal) + ((∫⁻ x, countableSupGap i0 x ∂μ) : EReal) := by
  apply le_antisymm
  · refine iSup_le fun s => iSup_le fun hs => ?_
    let t := insert i0 s
    have ht : t.Nonempty := Finset.insert_nonempty _ _
    calc
      (((∫ x, finsetMax s hs x ∂μ) : ℝ) : EReal)
          ≤ (((∫ x, finsetMax t ht x ∂μ) : ℝ) : EReal) := by
        apply EReal.coe_le_coe
        apply integral_mono (integrable_finsetMax μ hcoord s hs)
          (integrable_finsetMax μ hcoord t ht)
        intro x
        exact Finset.sup'_le _ _ fun i hi => Finset.le_sup' (f := x)
          (Finset.mem_insert_of_mem hi)
      _ = (((∫ x, x i0 ∂μ) : ℝ) : EReal) +
          ((∫⁻ x, ENNReal.ofReal (finsetMax t ht x - x i0) ∂μ) : EReal) :=
        ereal_integral_eq_add_lintegral_sub μ _ _ (integrable_finsetMax μ hcoord t ht)
          (hcoord i0) (ae_of_all _ fun x => Finset.le_sup' (f := x) (Finset.mem_insert_self _ _))
      _ ≤ _ := by
        apply add_le_add le_rfl
        apply EReal.coe_ennreal_le_coe_ennreal_iff.mpr
        apply lintegral_mono
        intro x
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' ht x
        change ENNReal.ofReal (t.sup' ht x - x i0) ≤ _
        rw [hi]
        exact le_iSup (fun j : ι => ENNReal.ofReal (x j - x i0)) i
  · rw [lintegral_countableSupGap_eq_iSup μ i0, ereal_add_coe_iSup]
    refine iSup_le fun n => ?_
    change (((∫ x, x i0 ∂μ) : ℝ) : EReal) +
      ((∫⁻ x, ENNReal.ofReal (finsetMax (countableApproxFinset i0 n)
        (countableApproxFinset_nonempty i0 n) x - x i0) ∂μ) : EReal) ≤ _
    rw [← ereal_integral_eq_add_lintegral_sub μ _ _
      (integrable_finsetMax μ hcoord _ _) (hcoord i0)
      (ae_of_all _ fun x => coord_le_countableApproxMax i0 n x)]
    exact le_iSup_of_le (countableApproxFinset i0 n)
      (le_iSup_of_le (countableApproxFinset_nonempty i0 n) le_rfl)

theorem countableExpectedSupEReal_eq_centered
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0) :
    countableExpectedSupEReal μ = (countableExpectedSup μ : EReal) := by
  rw [countableExpectedSupEReal_eq μ i0 hcoord, h0,
    lintegral_countableSupGap_eq μ i0 hcoord h0]
  simp

theorem countableExpectedSupDrift_zero
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0) :
    countableExpectedSupDrift 0 μ = (countableExpectedSup μ : EReal) := by
  unfold countableExpectedSupDrift
  simp only [zero_add]
  change countableExpectedSupEReal (μ.map id) = _
  rw [Measure.map_id]
  exact countableExpectedSupEReal_eq_centered μ i0 hcoord h0

/-- Compatibility with the real Bochner integral when the supremum is finite and integrable. -/
theorem countableExpectedSupEReal_eq_integral
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (hbd : ∀ᵐ x ∂μ, BddAbove (Set.range x))
    (hint : Integrable (fun x : ι → ℝ => countableSup x) μ) :
    countableExpectedSupEReal μ = (((∫ x, countableSup x ∂μ) : ℝ) : EReal) := by
  rw [countableExpectedSupEReal_eq μ i0 hcoord]
  have heq : (∫⁻ x, countableSupGap i0 x ∂μ) =
      ∫⁻ x, ENNReal.ofReal (countableSup x - x i0) ∂μ :=
    lintegral_congr_ae (hbd.mono fun x hx => countableSupGap_eq_ofReal_sub i0 x hx)
  rw [heq]
  exact (ereal_integral_eq_add_lintegral_sub μ _ _ hint (hcoord i0)
    (hbd.mono fun x hx => le_csSup hx ⟨i0, rfl⟩)).symm

/-- The shifted expectation is `a i0` plus the nonnegative integral above the shifted anchor.
This retains negative expectations and allows `+∞`, with no conditions on the deterministic drift. -/
theorem countableExpectedSupDrift_eq
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (a : ι → ℝ) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0) :
    countableExpectedSupDrift a μ =
      (a i0 : EReal) + ((∫⁻ x, countableSupGap i0 (a + x) ∂μ) : EReal) := by
  have hc (i : ι) : Integrable (fun z : ι → ℝ => z i) (μ.map (fun x => a + x)) := by
    apply (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
      (measurable_const.add measurable_id).aemeasurable).mpr
    exact (integrable_const (a i)).add (hcoord i)
  rw [countableExpectedSupDrift, countableExpectedSupEReal_eq _ i0 hc,
    integral_map (φ := fun x : ι → ℝ => a + x) (f := fun z : ι → ℝ => z i0)
      (measurable_const.add measurable_id).aemeasurable
      (measurable_pi_apply i0).aestronglyMeasurable,
    lintegral_map (g := fun x : ι → ℝ => a + x)
      (measurable_countableSupGap i0) (measurable_const.add measurable_id)]
  change (((∫ x, a i0 + x i0 ∂μ) : ℝ) : EReal) + _ = _
  rw [integral_add (integrable_const _) (hcoord i0), integral_const, h0]
  simp

theorem countableExpectedSupDrift_anchor_independent
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ] (a : ι → ℝ) (i0 j0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∀ i, ∫ x, x i ∂μ = 0) :
    (a i0 : EReal) + ((∫⁻ x, countableSupGap i0 (a + x) ∂μ) : EReal) =
      (a j0 : EReal) + ((∫⁻ x, countableSupGap j0 (a + x) ∂μ) : EReal) := by
  rw [← countableExpectedSupDrift_eq μ a i0 hcoord (h0 i0),
    ← countableExpectedSupDrift_eq μ a j0 hcoord (h0 j0)]

theorem integral_vecMax_finset_restrict_map_drift
    {ι : Type*} [DecidableEq ι] (μ : Measure (ι → ℝ)) (a : ι → ℝ)
    (s : Finset ι) (hs : s.Nonempty) :
    ∫ z, @vecMax {i // i ∈ s} _ hs.to_subtype (s.restrict a + z)
        ∂(μ.map (s.restrict (π := fun _ => ℝ))) =
      ∫ x, finsetMax s hs (a + x) ∂μ := by
  letI : Nonempty s := hs.to_subtype
  rw [integral_map (Finset.measurable_restrict s).aemeasurable
    ((measurable_vecMax.comp (measurable_const.add measurable_id)).aestronglyMeasurable)]
  apply integral_congr_ae
  exact ae_of_all _ fun x => vecMax_finset_restrict s hs (a + x)

theorem countable_sudakov_finite_comparison_drift
    {ι : Type*} [DecidableEq ι] (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY)
    (a : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    ∫ x, finsetMax s hs (a + x) ∂μX ≤ ∫ y, finsetMax s hs (a + y) ∂μY := by
  letI : Nonempty s := hs.to_subtype
  letI := hXgauss s hs
  letI := hYgauss s hs
  have hXm := (Finset.measurable_restrict (X := fun _ : ι => ℝ) s).aemeasurable (μ := μX)
  have hYm := (Finset.measurable_restrict (X := fun _ : ι => ℝ) s).aemeasurable (μ := μY)
  have hXcenter (i : s) : ∫ z, z i ∂μX.map (s.restrict (π := fun _ => ℝ)) = 0 := by
    rw [integral_map hXm (measurable_pi_apply i).aestronglyMeasurable]
    exact hX0 i
  have hYcenter (i : s) : ∫ z, z i ∂μY.map (s.restrict (π := fun _ => ℝ)) = 0 := by
    rw [integral_map hYm (measurable_pi_apply i).aestronglyMeasurable]
    exact hY0 i
  have hprojinc (i j : s) :
      variance (fun z : s → ℝ => z i - z j) (μX.map (s.restrict (π := fun _ => ℝ))) ≤
        variance (fun z : s → ℝ => z i - z j) (μY.map (s.restrict (π := fun _ => ℝ))) := by
    rw [variance_map (X := fun z : s → ℝ => z i - z j)
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).aemeasurable hXm,
      variance_map (X := fun z : s → ℝ => z i - z j)
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).aemeasurable hYm]
    exact hinc i j
  have h := sudakov_fernique_drift _ _ hXcenter hYcenter hprojinc (s.restrict a)
  rwa [integral_vecMax_finset_restrict_map_drift μX a s hs,
    integral_vecMax_finset_restrict_map_drift μY a s hs] at h

/-- Countable Sudakov-Fernique for a common arbitrary deterministic drift `a`.
The extended expected suprema can be negative or `+∞`; no pathwise boundedness or
supremum-integrability hypotheses are needed. -/
theorem countable_sudakov_drift
    {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY)
    (a : ι → ℝ) :
    countableExpectedSupDrift a μX ≤ countableExpectedSupDrift a μY := by
  apply iSup_mono
  intro s
  apply iSup_mono
  intro hs
  apply EReal.coe_le_coe
  rw [integral_map (μ := μX) (φ := fun x : ι → ℝ => a + x) (f := finsetMax s hs)
      (measurable_const.add measurable_id).aemeasurable
      (measurable_finsetMax s hs).aestronglyMeasurable,
    integral_map (μ := μY) (φ := fun x : ι → ℝ => a + x) (f := finsetMax s hs)
      (measurable_const.add measurable_id).aemeasurable
      (measurable_finsetMax s hs).aestronglyMeasurable]
  exact countable_sudakov_finite_comparison_drift μX μY hXgauss hYgauss hX0 hY0 hinc a s hs

/-- Anchored nonnegative integral form of the uncentered comparison. The common deterministic
anchor value cancels; the Gaussian coordinate means remain zero. -/
theorem countable_sudakov_drift_lintegral
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY)
    (a : ι → ℝ) (i0 : ι) :
    ∫⁻ x, countableSupGap i0 (a + x) ∂μX ≤ ∫⁻ y, countableSupGap i0 (a + y) ∂μY := by
  letI : Nonempty ι := ⟨i0⟩
  have h := countable_sudakov_drift μX μY hXgauss hYgauss hX0 hY0 hinc a
  rw [countableExpectedSupDrift_eq μX a i0
      (integrable_coord_of_projected_gaussian μX hXgauss) (hX0 i0),
    countableExpectedSupDrift_eq μY a i0
      (integrable_coord_of_projected_gaussian μY hYgauss) (hY0 i0),
    (EReal.addLECancellable_coe (a i0)).add_le_add_iff_left,
    EReal.coe_ennreal_le_coe_ennreal_iff] at h
  exact h

end
