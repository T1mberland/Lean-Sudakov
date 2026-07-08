import LeanSudakov.SudakovFernique
import Mathlib.Data.Set.Countable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.MonotoneConvergence

open Filter MeasureTheory
open ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

/-- Supremum of a countable real family. The countable theorem below assumes this family is
almost surely bounded above and integrable, so this `sSup` has its intended real value there. -/
def countableSup {ι : Type*} (x : ι → ℝ) : ℝ :=
  sSup (Set.range x)

/-- Maximum over a nonempty finite subset of an arbitrary index type. -/
def finsetMax {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ) : ℝ :=
  s.sup' hs x

/-- The finite sets used to exhaust a countable type, with a fixed base point inserted to make
each set nonempty and to provide a uniform lower bound for the finite maxima. -/
def countableApproxFinset {ι : Type*} [Countable ι] [DecidableEq ι]
    (i0 : ι) (n : ℕ) : Finset ι :=
  insert i0 <|
    (Finset.range (n + 1)).image
      (Set.enumerateCountable (s := Set.univ) Set.countable_univ i0)

theorem countableApproxFinset_nonempty
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) :
    (countableApproxFinset i0 n).Nonempty := by
  exact ⟨i0, by simp [countableApproxFinset]⟩

theorem countableApproxFinset_mono
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) :
    Monotone fun n => countableApproxFinset i0 n := by
  intro m n hmn i hi
  simp only [countableApproxFinset, Finset.mem_insert, Finset.mem_image,
    Finset.mem_range] at hi ⊢
  rcases hi with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k, lt_of_lt_of_le hk (Nat.succ_le_succ hmn), rfl⟩

theorem eventually_mem_countableApproxFinset
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 i : ι) :
    ∀ᶠ n in atTop, i ∈ countableApproxFinset i0 n := by
  let e : ℕ → ι := Set.enumerateCountable (s := Set.univ) Set.countable_univ i0
  have hi : i ∈ Set.range e := by
    simpa [e] using
      (Set.subset_range_enumerate (s := Set.univ) Set.countable_univ i0 (by simp : i ∈ Set.univ))
  rcases hi with ⟨k, rfl⟩
  filter_upwards [eventually_ge_atTop k] with n hn
  simp only [countableApproxFinset, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
  exact Or.inr ⟨k, Nat.lt_succ_of_le hn, rfl⟩

/-- Finite-max approximation of `countableSup`, formed from the canonical countable exhaustion. -/
def countableApproxMax
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) (x : ι → ℝ) : ℝ :=
  finsetMax (countableApproxFinset i0 n) (countableApproxFinset_nonempty i0 n) (fun i => x i)

theorem coord_le_countableApproxMax
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) (x : ι → ℝ) :
    x i0 ≤ countableApproxMax i0 n x := by
  exact Finset.le_sup' (s := countableApproxFinset i0 n) (f := x)
    (by simp [countableApproxFinset])

theorem monotone_countableApproxMax
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (x : ι → ℝ) :
    Monotone fun n => countableApproxMax i0 n x := by
  intro m n hmn
  simp only [countableApproxMax, finsetMax]
  refine Finset.sup'_le _ _ ?_
  intro i hi
  exact Finset.le_sup' (s := countableApproxFinset i0 n) (f := x)
    ((countableApproxFinset_mono i0 hmn) hi)

theorem countableApproxMax_le_countableSup
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) (x : ι → ℝ)
    (hbd : BddAbove (Set.range x)) :
    countableApproxMax i0 n x ≤ countableSup x := by
  rw [countableApproxMax, finsetMax]
  refine Finset.sup'_le _ _ ?_
  intro i _hi
  exact le_csSup hbd ⟨i, rfl⟩

theorem countableApproxMax_tendsto_countableSup
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (x : ι → ℝ)
    (hbd : BddAbove (Set.range x)) :
    Tendsto (fun n => countableApproxMax i0 n x) atTop (𝓝 (countableSup x)) := by
  refine tendsto_atTop_isLUB (monotone_countableApproxMax i0 x) ?_
  constructor
  · rintro _ ⟨n, rfl⟩
    exact countableApproxMax_le_countableSup i0 n x hbd
  · intro b hb
    letI : Nonempty ι := ⟨i0⟩
    rw [countableSup]
    refine csSup_le (Set.range_nonempty x) ?_
    rintro y ⟨i, rfl⟩
    have hmem : ∀ᶠ n in atTop, i ∈ countableApproxFinset i0 n :=
      eventually_mem_countableApproxFinset i0 i
    rcases hmem.exists with ⟨n, hn⟩
    exact (Finset.le_sup' (s := countableApproxFinset i0 n) (f := x) hn).trans
      (hb ⟨n, rfl⟩)

theorem measurable_countableApproxMax
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) :
    Measurable fun x : ι → ℝ => countableApproxMax i0 n x := by
  let s := countableApproxFinset i0 n
  let hs := countableApproxFinset_nonempty i0 n
  let F : ι → (ι → ℝ) → ℝ := fun i x => x i
  have hmeas : Measurable (s.sup' hs F) :=
    Finset.measurable_sup' hs
      (fun i _ => measurable_pi_apply (X := fun _ : ι => ℝ) i)
  have hEq :
      (s.sup' hs F) = (fun x : ι → ℝ => s.sup' hs (fun i => x i)) := by
    funext x
    exact Finset.sup'_apply hs F x
  simpa [countableApproxMax, finsetMax, s, hs, F] using hEq ▸ hmeas

theorem aestronglyMeasurable_countableSup
    {ι : Type*} [Countable ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} (i0 : ι)
    (hbd : ∀ᵐ x ∂μ, BddAbove (Set.range x)) :
    AEStronglyMeasurable (fun x : ι → ℝ => countableSup x) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (measurable_countableApproxMax i0 n).aestronglyMeasurable) ?_
  exact hbd.mono fun x hx => countableApproxMax_tendsto_countableSup i0 x hx

theorem norm_countableApproxMax_le
    {ι : Type*} [Countable ι] [DecidableEq ι] (i0 : ι) (n : ℕ) (x : ι → ℝ)
    (hbd : BddAbove (Set.range x)) :
    ‖countableApproxMax i0 n x‖ ≤ ‖x i0‖ + ‖countableSup x‖ := by
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  have hlow : x i0 ≤ countableApproxMax i0 n x := coord_le_countableApproxMax i0 n x
  have hhigh : countableApproxMax i0 n x ≤ countableSup x :=
    countableApproxMax_le_countableSup i0 n x hbd
  refine abs_le.2 ⟨?_, ?_⟩
  · linarith [neg_abs_le (x i0), abs_nonneg (countableSup x)]
  · linarith [hhigh, le_abs_self (countableSup x), abs_nonneg (x i0)]

theorem tendsto_integral_countableApproxMax
    {ι : Type*} [Countable ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) (i0 : ι)
    (hcoord_int : Integrable (fun x : ι → ℝ => x i0) μ)
    (hbd : ∀ᵐ x ∂μ, BddAbove (Set.range x))
    (hint : Integrable (fun x : ι → ℝ => countableSup x) μ) :
    Tendsto (fun n => ∫ x, countableApproxMax i0 n x ∂μ)
      atTop (𝓝 (∫ x, countableSup x ∂μ)) := by
  let bound : (ι → ℝ) → ℝ := fun x => ‖x i0‖ + ‖countableSup x‖
  have hbound_int : Integrable bound μ := hcoord_int.norm.add hint.norm
  refine tendsto_integral_of_dominated_convergence bound
    (fun n => (measurable_countableApproxMax i0 n).aestronglyMeasurable)
    hbound_int ?_ ?_
  · intro n
    exact hbd.mono fun x hx => norm_countableApproxMax_le i0 n x hx
  · exact hbd.mono fun x hx => countableApproxMax_tendsto_countableSup i0 x hx

theorem vecMax_finset_restrict
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty) (x : ι → ℝ) :
    @vecMax {i // i ∈ s} _ hs.to_subtype (s.restrict (π := fun _ => ℝ) x) =
      finsetMax s hs x := by
  classical
  letI : Nonempty s := hs.to_subtype
  apply le_antisymm
  · dsimp [vecMax]
    refine Finset.sup'_le _ _ ?_
    intro i _hi
    exact Finset.le_sup' (s := s) (f := x) i.2
  · rw [finsetMax]
    refine Finset.sup'_le _ _ ?_
    intro i hi
    have hle :
        x i ≤ @vecMax {i // i ∈ s} _ hs.to_subtype
          (s.restrict (π := fun _ => ℝ) x) := by
      dsimp [vecMax]
      exact Finset.le_sup'
        (s := (Finset.univ : Finset {i // i ∈ s}))
        (f := s.restrict (π := fun _ => ℝ) x)
        (Finset.mem_univ ⟨i, hi⟩)
    simpa [Finset.restrict] using hle

theorem integral_vecMax_finset_restrict_map
    {ι : Type*} [DecidableEq ι] (μ : Measure (ι → ℝ))
    (s : Finset ι) (hs : s.Nonempty) :
    ∫ z, @vecMax {i // i ∈ s} _ hs.to_subtype z
        ∂(μ.map (s.restrict (π := fun _ => ℝ))) =
      ∫ x, finsetMax s hs x ∂μ := by
  letI : Nonempty s := hs.to_subtype
  rw [integral_map (Finset.measurable_restrict (X := fun _ : ι => ℝ) s).aemeasurable
    measurable_vecMax.aestronglyMeasurable]
  simp_rw [vecMax_finset_restrict s hs]

theorem countable_sudakov_finite_comparison_of_projected_gaussian
    {ι : Type*} [DecidableEq ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      ProbabilityTheory.IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      ProbabilityTheory.IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j,
      ProbabilityTheory.variance (fun x : ι → ℝ => x i - x j) μX
        ≤ ProbabilityTheory.variance (fun y : ι → ℝ => y i - y j) μY)
    (s : Finset ι) (hs : s.Nonempty) :
    ∫ x, finsetMax s hs x ∂μX ≤ ∫ y, finsetMax s hs y ∂μY := by
  classical
  letI : Nonempty {i // i ∈ s} := hs.to_subtype
  let νX : Measure ({i // i ∈ s} → ℝ) := μX.map (s.restrict (π := fun _ => ℝ))
  let νY : Measure ({i // i ∈ s} → ℝ) := μY.map (s.restrict (π := fun _ => ℝ))
  have hproj_meas :
      AEMeasurable (s.restrict (π := fun _ => ℝ)) μX :=
    (Finset.measurable_restrict (X := fun _ : ι => ℝ) s).aemeasurable
  have hproj_measY :
      AEMeasurable (s.restrict (π := fun _ => ℝ)) μY :=
    (Finset.measurable_restrict (X := fun _ : ι => ℝ) s).aemeasurable
  letI : IsProbabilityMeasure νX := by
    dsimp [νX]
    exact Measure.isProbabilityMeasure_map hproj_meas
  letI : IsProbabilityMeasure νY := by
    dsimp [νY]
    exact Measure.isProbabilityMeasure_map hproj_measY
  letI : ProbabilityTheory.IsGaussian νX := by
    simpa [νX] using hXgauss s hs
  letI : ProbabilityTheory.IsGaussian νY := by
    simpa [νY] using hYgauss s hs
  have hνX0 : ∀ i : {i // i ∈ s}, ∫ z, z i ∂νX = 0 := by
    intro i
    dsimp [νX]
    rw [integral_map hproj_meas (measurable_pi_apply i).aestronglyMeasurable]
    simpa [Finset.restrict] using hX0 i
  have hνY0 : ∀ i : {i // i ∈ s}, ∫ z, z i ∂νY = 0 := by
    intro i
    dsimp [νY]
    rw [integral_map hproj_measY (measurable_pi_apply i).aestronglyMeasurable]
    simpa [Finset.restrict] using hY0 i
  have hνinc : ∀ i j : {i // i ∈ s},
      ProbabilityTheory.variance (fun z : {i // i ∈ s} → ℝ => z i - z j) νX
        ≤ ProbabilityTheory.variance (fun z : {i // i ∈ s} → ℝ => z i - z j) νY := by
    intro i j
    have hXm :
        ProbabilityTheory.variance (fun z : {i // i ∈ s} → ℝ => z i - z j) νX =
          ProbabilityTheory.variance (fun x : ι → ℝ => x i - x j) μX := by
      dsimp [νX]
      rw [ProbabilityTheory.variance_map
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).aemeasurable hproj_meas]
      rfl
    have hYm :
        ProbabilityTheory.variance (fun z : {i // i ∈ s} → ℝ => z i - z j) νY =
          ProbabilityTheory.variance (fun y : ι → ℝ => y i - y j) μY := by
      dsimp [νY]
      rw [ProbabilityTheory.variance_map
        ((measurable_pi_apply i).sub (measurable_pi_apply j)).aemeasurable hproj_measY]
      rfl
    rw [hXm, hYm]
    exact hinc i j
  have hfinite := sudakov_fernique νX νY hνX0 hνY0 hνinc
  dsimp [νX, νY] at hfinite
  rw [integral_vecMax_finset_restrict_map μX s hs,
    integral_vecMax_finset_restrict_map μY s hs] at hfinite
  exact hfinite

/-- Countable Sudakov-Fernique extension from all finite nonempty max comparisons.

For countably many indices, mathlib currently cannot state Gaussianity directly on the product
space `ι → ℝ` using `ProbabilityTheory.IsGaussian`, because that class is formulated for normed
real vector spaces. This theorem isolates the deterministic/measure-theoretic extension step:
once every finite-dimensional maximum comparison is known, dominated convergence upgrades it to
the countable supremum comparison. -/
theorem countable_sudakov_of_finset
    {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    (hfinite : ∀ (s : Finset ι) (hs : s.Nonempty),
      ∫ x, finsetMax s hs x ∂μX ≤ ∫ y, finsetMax s hs y ∂μY)
    (hXcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μX)
    (hYcoord : ∀ i, Integrable (fun y : ι → ℝ => y i) μY)
    (hXbdd : ∀ᵐ x ∂μX, BddAbove (Set.range x))
    (hYbdd : ∀ᵐ y ∂μY, BddAbove (Set.range y))
    (hXint : Integrable (fun x : ι → ℝ => countableSup x) μX)
    (hYint : Integrable (fun y : ι → ℝ => countableSup y) μY) :
    ∫ x, countableSup x ∂μX ≤ ∫ y, countableSup y ∂μY := by
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hlimX := tendsto_integral_countableApproxMax μX i0 (hXcoord i0) hXbdd hXint
  have hlimY := tendsto_integral_countableApproxMax μY i0 (hYcoord i0) hYbdd hYint
  refine le_of_tendsto_of_tendsto' hlimX hlimY ?_
  intro n
  exact hfinite (countableApproxFinset i0 n) (countableApproxFinset_nonempty i0 n)

/-- Countable Sudakov-Fernique from Gaussian finite-dimensional projection laws.

The Gaussian hypotheses are stated for every finite projection law because mathlib's
`ProbabilityTheory.IsGaussian` is currently formulated for normed real vector spaces, while the
full countable product `ι → ℝ` is not a normed space in general. -/
theorem countable_sudakov_of_projected_gaussian
    {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ))
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      ProbabilityTheory.IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      ProbabilityTheory.IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
    (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j,
      ProbabilityTheory.variance (fun x : ι → ℝ => x i - x j) μX
        ≤ ProbabilityTheory.variance (fun y : ι → ℝ => y i - y j) μY)
    (hXcoord : ∀ i, Integrable (fun x : ι → ℝ => x i) μX)
    (hYcoord : ∀ i, Integrable (fun y : ι → ℝ => y i) μY)
    (hXbdd : ∀ᵐ x ∂μX, BddAbove (Set.range x))
    (hYbdd : ∀ᵐ y ∂μY, BddAbove (Set.range y))
    (hXint : Integrable (fun x : ι → ℝ => countableSup x) μX)
    (hYint : Integrable (fun y : ι → ℝ => countableSup y) μY) :
    ∫ x, countableSup x ∂μX ≤ ∫ y, countableSup y ∂μY := by
  refine countable_sudakov_of_finset μX μY ?_ hXcoord hYcoord hXbdd hYbdd hXint hYint
  intro s hs
  exact countable_sudakov_finite_comparison_of_projected_gaussian
    μX μY hXgauss hYgauss hX0 hY0 hinc s hs

end
