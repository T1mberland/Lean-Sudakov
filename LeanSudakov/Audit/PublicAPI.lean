import LeanSudakov

namespace LeanSudakov.Audit

open MeasureTheory ProbabilityTheory

-- Deliberately use fully qualified project names, without `open LeanSudakov`.
example {ι : Type*} [Fintype ι] [Nonempty ι]
    {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    LeanSudakov.vecMax x ≤ LeanSudakov.lse β x :=
  LeanSudakov.vecMax_le_lse hβ x

example {ι : Type*} [Fintype ι] [Nonempty ι]
    {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    LeanSudakov.lse β x ≤
      LeanSudakov.vecMax x + Real.log (Fintype.card ι) / β :=
  LeanSudakov.lse_le_vecMax_add hβ x

example {ι : Type*} [Fintype ι] [Nonempty ι] (β : ℝ) (x : ι → ℝ) :
    (Finset.univ.sum fun i => LeanSudakov.softmax β x i) = 1 :=
  LeanSudakov.sum_softmax β x

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Measure ℝ) [∀ k, IsProbabilityMeasure (μ k)] (i : ι) :
    Measure.map (fun p : (ι → ℝ) × ℝ => Function.update p.1 i p.2)
      ((Measure.pi μ).prod (μ i)) = Measure.pi μ :=
  LeanSudakov.map_update_prod_pi μ i

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hμ0 : ∀ i, ∫ x, x i ∂μ = 0) (β : ℝ) (i j : ι) :
    ∫ x, x i * LeanSudakov.softmax β x j ∂μ =
      Finset.univ.sum fun k => LeanSudakov.gaussianCov μ i k *
        ∫ x, β * ((if j = k then LeanSudakov.softmax β x j else 0) -
          LeanSudakov.softmax β x j * LeanSudakov.softmax β x k) ∂μ :=
  LeanSudakov.gaussian_ibp_softmax μ hμ0 β i j

example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY) {β : ℝ} (hβ : 0 < β) :
    ∫ x, LeanSudakov.lse β x ∂μX ≤ ∫ y, LeanSudakov.lse β y ∂μY :=
  LeanSudakov.gaussian_interpolation_lse_mono μX μY hX0 hY0 hinc hβ

example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY) :
    ∫ x, LeanSudakov.vecMax x ∂μX ≤ ∫ y, LeanSudakov.vecMax y ∂μY :=
  LeanSudakov.sudakov_fernique μX μY hX0 hY0 hinc

example {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsGaussian μX] [IsGaussian μY]
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY) (a : ι → ℝ) :
    ∫ x, LeanSudakov.vecMax (a + x) ∂μX ≤
      ∫ y, LeanSudakov.vecMax (a + y) ∂μY :=
  LeanSudakov.sudakov_fernique_drift μX μY hX0 hY0 hinc a

example {ι : Type*} [Countable ι] [DecidableEq ι] [Nonempty ι]
    (μX μY : Measure (ι → ℝ)) [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    (hXgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μX.map (s.restrict (π := fun _ => ℝ))))
    (hYgauss : ∀ (s : Finset ι) (_hs : s.Nonempty),
      IsGaussian (μY.map (s.restrict (π := fun _ => ℝ))))
    (hX0 : ∀ i, ∫ x, x i ∂μX = 0) (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
    (hinc : ∀ i j, variance (fun x : ι → ℝ => x i - x j) μX ≤
      variance (fun y : ι → ℝ => y i - y j) μY) (a : ι → ℝ) :
    LeanSudakov.countableExpectedSupDrift a μX ≤
      LeanSudakov.countableExpectedSupDrift a μY :=
  LeanSudakov.countable_sudakov_drift μX μY hXgauss hYgauss hX0 hY0 hinc a

end LeanSudakov.Audit
