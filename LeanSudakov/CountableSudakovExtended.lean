import LeanSudakov.CountableSudakov
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace LeanSudakov

noncomputable section

/-- The nonnegative extended supremum above a fixed coordinate. Including `i0` in the
supremum makes truncation by `ENNReal.ofReal` harmless. This can equal `∞`. -/
def countableSupGap {ι : Type*} (i0 : ι) (x : ι → ℝ) : ℝ≥0∞ :=
  ⨆ i, ENNReal.ofReal (x i - x i0)

/-- Extended expected supremum of a centered process, defined by its finite expected maxima.
For countably many integrable centered coordinates, `lintegral_countableSupGap_eq` identifies
this with the nonnegative integral of `sup_i (x i - x i0)`, for any base coordinate `i0`.
Centering is essential to this interpretation. No boundedness or supremum integrability is
required, and the value can be `∞`. -/
def countableExpectedSup {ι : Type*} (μ : Measure (ι → ℝ)) : ℝ≥0∞ :=
  ⨆ (s : Finset ι) (hs : s.Nonempty), ENNReal.ofReal (∫ x, finsetMax s hs x ∂μ)

theorem measurable_countableSupGap
    {ι : Type*} [Countable ι] (i0 : ι) :
    Measurable (countableSupGap i0) := by
  exact Measurable.iSup fun i =>
    ((measurable_pi_apply i).sub (measurable_pi_apply i0)).ennreal_ofReal

theorem countableSupGap_eq_iSup_approx
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (x : ι → ℝ) :
    countableSupGap i0 x =
      ⨆ n, ENNReal.ofReal (countableApproxMax i0 n x - x i0) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    obtain ⟨n, hn⟩ := (eventually_mem_countableApproxFinset i0 i).exists
    have hle : x i ≤ countableApproxMax i0 n x := Finset.le_sup' (f := x) hn
    exact (ENNReal.ofReal_le_ofReal (sub_le_sub_right hle _)).trans
      (le_iSup (fun n => ENNReal.ofReal (countableApproxMax i0 n x - x i0)) n)
  · refine iSup_le fun n => ?_
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup'
      (countableApproxFinset_nonempty i0 n) x
    change ENNReal.ofReal ((countableApproxFinset i0 n).sup'
      (countableApproxFinset_nonempty i0 n) x - x i0) ≤ _
    rw [hi]
    unfold countableSupGap
    exact le_iSup (fun j : ι => ENNReal.ofReal (x j - x i0)) i

/-- Monotone convergence for the anchored finite maxima, including infinite limits. -/
theorem lintegral_countableSupGap_eq_iSup
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι) :
    ∫⁻ x, countableSupGap i0 x ∂μ =
      ⨆ n, ∫⁻ x, ENNReal.ofReal (countableApproxMax i0 n x - x i0) ∂μ := by
  simp_rw [countableSupGap_eq_iSup_approx i0]
  apply lintegral_iSup
  · intro n
    exact ((measurable_countableApproxMax i0 n).sub
      (measurable_pi_apply i0)).ennreal_ofReal
  · intro m n hmn x
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_right (monotone_countableApproxMax i0 x hmn) _)

theorem integrable_finsetMax
    {ι : Type*} (μ : Measure (ι → ℝ))
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (s : Finset ι) (hs : s.Nonempty) :
    Integrable (fun x => finsetMax s hs x) μ := by
  have h : Integrable (s.sup' hs (fun i (x : ι → ℝ) => x i)) μ :=
    Finset.sup'_induction (p := fun f : (ι → ℝ) → ℝ => Integrable f μ)
      hs _ (fun _ hf _ hg => hf.sup hg) (fun i _ => hcoord i)
  have hEq : s.sup' hs (fun i (x : ι → ℝ) => x i) =
      (fun x => s.sup' hs x) := by
    funext x
    exact Finset.sup'_apply hs _ x
  simpa only [hEq, finsetMax] using h

theorem lintegral_finsetMax_sub_eq
    {ι : Type*} (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0)
    (s : Finset ι) (hs : s.Nonempty) (hi0 : i0 ∈ s) :
    ∫⁻ x, ENNReal.ofReal (finsetMax s hs x - x i0) ∂μ =
      ENNReal.ofReal (∫ x, finsetMax s hs x ∂μ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (f := fun x => finsetMax s hs x - x i0)
    ((integrable_finsetMax μ hcoord s hs).sub (hcoord i0))
    (ae_of_all μ fun x => sub_nonneg.mpr (Finset.le_sup' (f := x) hi0))]
  rw [integral_sub (integrable_finsetMax μ hcoord s hs) (hcoord i0), h0, sub_zero]

/-- For centered integrable coordinates, the extended expected supremum is the integral of
the nonnegative anchored supremum. In particular, it is independent of the base coordinate. -/
theorem lintegral_countableSupGap_eq
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0) :
    ∫⁻ x, countableSupGap i0 x ∂μ = countableExpectedSup μ := by
  apply le_antisymm
  · rw [lintegral_countableSupGap_eq_iSup μ i0]
    refine iSup_le fun n => ?_
    change (∫⁻ x, ENNReal.ofReal (finsetMax (countableApproxFinset i0 n)
      (countableApproxFinset_nonempty i0 n) x - x i0) ∂μ) ≤ _
    rw [lintegral_finsetMax_sub_eq μ i0 hcoord h0 _ _ (by simp [countableApproxFinset])]
    exact le_iSup_of_le (countableApproxFinset i0 n)
      (le_iSup_of_le (countableApproxFinset_nonempty i0 n) le_rfl)
  · refine iSup_le fun s => iSup_le fun hs => ?_
    let t := insert i0 s
    have ht : t.Nonempty := Finset.insert_nonempty _ _
    calc
      ENNReal.ofReal (∫ x, finsetMax s hs x ∂μ)
          ≤ ENNReal.ofReal (∫ x, finsetMax t ht x ∂μ) := by
        apply ENNReal.ofReal_le_ofReal
        apply integral_mono (integrable_finsetMax μ hcoord s hs)
          (integrable_finsetMax μ hcoord t ht)
        intro x
        exact Finset.sup'_le _ _ fun i hi =>
          Finset.le_sup' (f := x) (Finset.mem_insert_of_mem hi)
      _ = ∫⁻ x, ENNReal.ofReal (finsetMax t ht x - x i0) ∂μ :=
        (lintegral_finsetMax_sub_eq μ i0 hcoord h0 t ht (Finset.mem_insert_self _ _)).symm
      _ ≤ ∫⁻ x, countableSupGap i0 x ∂μ := by
        apply lintegral_mono
        intro x
        obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' ht x
        change ENNReal.ofReal (t.sup' ht x - x i0) ≤ _
        rw [hi]
        unfold countableSupGap
        exact le_iSup (fun j : ι => ENNReal.ofReal (x j - x i0)) i

theorem lintegral_countableSupGap_anchor_independent
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 j0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∀ i, ∫ x, x i ∂μ = 0) :
    ∫⁻ x, countableSupGap i0 x ∂μ = ∫⁻ x, countableSupGap j0 x ∂μ := by
  rw [lintegral_countableSupGap_eq μ i0 hcoord (h0 i0),
    lintegral_countableSupGap_eq μ j0 hcoord (h0 j0)]

theorem countableSupGap_eq_ofReal_sub
    {ι : Type*} (i0 : ι) (x : ι → ℝ) (hbd : BddAbove (Set.range x)) :
    countableSupGap i0 x = ENNReal.ofReal (countableSup x - x i0) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_right (le_csSup hbd ⟨i, rfl⟩) _)
  · by_cases htop : countableSupGap i0 x = ∞
    · rw [htop]
      exact le_top
    apply (ENNReal.ofReal_le_iff_le_toReal htop).mpr
    apply sub_le_iff_le_add.mpr
    change sSup (Set.range x) ≤ _
    refine csSup_le ⟨x i0, ⟨i0, rfl⟩⟩ ?_
    rintro _ ⟨i, rfl⟩
    exact sub_le_iff_le_add.mp ((ENNReal.ofReal_le_iff_le_toReal htop).mp
      (le_iSup (fun j : ι => ENNReal.ofReal (x j - x i0)) i))

/-- Compatibility with the existing real-valued expected supremum when it is finite.
These boundedness and integrability assumptions are needed only for this Bochner-integral
specialization, not for the extended comparison theorem. -/
theorem countableExpectedSup_eq_ofReal_integral
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μ)
    (h0 : ∫ x, x i0 ∂μ = 0)
    (hbd : ∀ᵐ x ∂μ, BddAbove (Set.range x))
    (hint : Integrable (fun x : ι → ℝ => countableSup x) μ) :
    countableExpectedSup μ = ENNReal.ofReal (∫ x, countableSup x ∂μ) := by
  rw [← lintegral_countableSupGap_eq μ i0 hcoord h0]
  calc
    ∫⁻ x, countableSupGap i0 x ∂μ =
        ∫⁻ x, ENNReal.ofReal (countableSup x - x i0) ∂μ :=
      lintegral_congr_ae (hbd.mono fun x hx => countableSupGap_eq_ofReal_sub i0 x hx)
    _ = ENNReal.ofReal (∫ x, countableSup x ∂μ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (f := fun x => countableSup x - x i0) (hint.sub (hcoord i0))
        (hbd.mono fun x hx => sub_nonneg.mpr (le_csSup hx ⟨i0, rfl⟩))]
      rw [integral_sub hint (hcoord i0), h0, sub_zero]

/-- Finite maximum comparisons imply comparison of extended expected suprema. -/
theorem countable_sudakov_extended_of_finset
    {ι : Type*} (μX μY : Measure (ι → ℝ))
    (hfinite : ∀ (s : Finset ι) (hs : s.Nonempty),
      ∫ x, finsetMax s hs x ∂μX ≤ ∫ y, finsetMax s hs y ∂μY) :
    countableExpectedSup μX ≤ countableExpectedSup μY := by
  exact iSup_mono fun s => iSup_mono fun hs => ENNReal.ofReal_le_ofReal (hfinite s hs)

/-- Countable Sudakov-Fernique with extended expected suprema. No pathwise boundedness or
integrability of the supremum is assumed. The expected suprema may equal `∞`.
The finite-dimensional comparison also gives this statement for arbitrary index types;
countability is used to identify it with the measurable supremum integral above. -/
theorem countable_sudakov
    {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX ≤
        variance (fun y : ι → ℝ => y i - y j) μY) :
    countableExpectedSup μX ≤ countableExpectedSup μY := by
  exact countable_sudakov_extended_of_finset μX μY
    (countable_sudakov_finite_comparison_of_projected_gaussian
      μX μY hXgauss hYgauss hX0 hY0 hinc)

/-- Integral form of countable Sudakov-Fernique, using any anchor coordinate.
Subtracting the centered coordinate preserves the expected supremum and permits direct use
of the nonnegative integral and monotone convergence, even when the expectation is infinite. -/
theorem countable_sudakov_lintegral
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j,
      variance (fun x : ι → ℝ => x i - x j) μX ≤
        variance (fun y : ι → ℝ => y i - y j) μY)
    (i0 : ι) :
    ∫⁻ x, countableSupGap i0 x ∂μX ≤ ∫⁻ y, countableSupGap i0 y ∂μY := by
  letI : Nonempty ι := ⟨i0⟩
  rw [lintegral_countableSupGap_eq μX i0
      (integrable_coord_of_projected_gaussian μX hXgauss) (hX0 i0),
    lintegral_countableSupGap_eq μY i0
      (integrable_coord_of_projected_gaussian μY hYgauss) (hY0 i0)]
  exact countable_sudakov μX μY hXgauss hYgauss hX0 hY0 hinc

end

end LeanSudakov
