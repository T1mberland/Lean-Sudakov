import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

noncomputable section

def vecMax {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

def lse {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → ℝ) : ℝ :=
  Real.log ((Finset.univ).sum fun i => Real.exp (β * x i)) / β

theorem vecMax_le_lse
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    vecMax x ≤ lse β x := by
  let S : ℝ := (Finset.univ).sum fun i => Real.exp (β * x i)
  have hSpos : 0 < S := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (Real.exp_pos (β * x i₀)) <|
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i => Real.exp (β * x i))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i₀)
  obtain ⟨i₀, hi₀, hmax⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset ι))
      Finset.univ_nonempty x
  have hexp_le : Real.exp (β * vecMax x) ≤ S := by
    have hsingle :
        Real.exp (β * x i₀) ≤
          (Finset.univ).sum fun i => Real.exp (β * x i) :=
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i => Real.exp (β * x i))
        (fun _ _ => Real.exp_nonneg _) hi₀
    simpa [S, vecMax, hmax] using hsingle
  have hlog : β * vecMax x ≤ Real.log S := by
    exact (Real.le_log_iff_exp_le hSpos).2 hexp_le
  rw [lse]
  change vecMax x ≤ Real.log S / β
  exact (le_div_iff₀ hβ).2 (by simpa [mul_comm] using hlog)

theorem lse_le_vecMax_add
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {β : ℝ} (hβ : 0 < β) (x : ι → ℝ) :
    lse β x ≤ vecMax x + Real.log (Fintype.card ι) / β := by
  let S : ℝ := (Finset.univ).sum fun i => Real.exp (β * x i)
  let m : ℝ := vecMax x
  have hSpos : 0 < S := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (Real.exp_pos (β * x i₀)) <|
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i => Real.exp (β * x i))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i₀)
  have hcard_nat : 0 < Fintype.card ι := Fintype.card_pos
  have hcard : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.2 hcard_nat
  have hsum_le : S ≤ (Fintype.card ι : ℝ) * Real.exp (β * m) := by
    calc
      S ≤ (Finset.univ).sum fun _ : ι => Real.exp (β * m) := by
        refine Finset.sum_le_sum ?_
        intro i _
        exact Real.exp_monotone (mul_le_mul_of_nonneg_left
          (Finset.le_sup' x (Finset.mem_univ i)) hβ.le)
      _ = (Fintype.card ι : ℝ) * Real.exp (β * m) := by simp
  have hlog_le :
      Real.log S ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (β * m)) :=
    Real.log_le_log hSpos hsum_le
  have hlog_prod :
      Real.log ((Fintype.card ι : ℝ) * Real.exp (β * m)) =
        Real.log (Fintype.card ι) + β * m := by
    rw [Real.log_mul hcard.ne' (Real.exp_pos (β * m)).ne']
    simp [Real.log_exp]
  rw [lse]
  change Real.log S / β ≤ m + Real.log (Fintype.card ι) / β
  calc
    Real.log S / β
        ≤ Real.log ((Fintype.card ι : ℝ) * Real.exp (β * m)) / β :=
      div_le_div_of_nonneg_right hlog_le hβ.le
    _ = m + Real.log (Fintype.card ι) / β := by
      rw [hlog_prod]
      field_simp [hβ.ne']
      ring

def softmax {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (β * x i) /
    ((Finset.univ).sum fun k => Real.exp (β * x k))

theorem sum_softmax
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (β : ℝ) (x : ι → ℝ) :
    (Finset.univ.sum fun i => softmax β x i) = 1 := by
  let S : ℝ := (Finset.univ).sum fun k => Real.exp (β * x k)
  have hSpos : 0 < S := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    exact lt_of_lt_of_le (Real.exp_pos (β * x i₀)) <|
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun i => Real.exp (β * x i))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i₀)
  calc
    (Finset.univ.sum fun i => softmax β x i)
        = ((Finset.univ).sum fun i => Real.exp (β * x i)) / S := by
      simp [softmax, S, div_eq_mul_inv, Finset.sum_mul]
    _ = 1 := by
      rw [div_self hSpos.ne']

theorem softmax_nonneg
    {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → ℝ) (i : ι) :
    0 ≤ softmax β x i := by
  have hden_pos :
      0 < (Finset.univ).sum fun k => Real.exp (β * x k) :=
    lt_of_lt_of_le (Real.exp_pos (β * x i)) <|
      Finset.single_le_sum
        (s := (Finset.univ : Finset ι))
        (f := fun k => Real.exp (β * x k))
        (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i)
  exact div_nonneg (Real.exp_nonneg _) hden_pos.le

theorem hessian_cov_rewrite
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (p : ι → ℝ) (A : ι → ι → ℝ)
    (hsum : Finset.univ.sum p = 1) :
    (Finset.univ.sum fun i =>
      Finset.univ.sum fun j =>
        β * ((if i = j then p i else 0) - p i * p j) * A i j)
      =
    (β / 2) *
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          p i * p j * (A i i + A j j - 2 * A i j)) := by
  let D : ℝ := Finset.univ.sum fun i => p i * A i i
  let C : ℝ := Finset.univ.sum fun i =>
    Finset.univ.sum fun j => p i * p j * A i j
  have hdiag :
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j => (if i = j then p i else 0) * A i j) = D := by
    simp [D]
  have hleft :
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          β * ((if i = j then p i else 0) - p i * p j) * A i j)
        = β * (D - C) := by
    rw [← hdiag]
    dsimp [C]
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  have hfirst :
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j => p i * p j * A i i) = D := by
    calc
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j => p i * p j * A i i)
          = Finset.univ.sum fun i => (p i * A i i) * Finset.univ.sum p := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ = D := by simp [D, hsum]
  have hsecond :
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j => p i * p j * A j j) = D := by
    calc
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j => p i * p j * A j j)
          = Finset.univ.sum fun j =>
            Finset.univ.sum fun i => p i * p j * A j j := by
        rw [Finset.sum_comm]
      _ = Finset.univ.sum fun j => (p j * A j j) * Finset.univ.sum p := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        ring
      _ = D := by simp [D, hsum]
  have hquad :
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          p i * p j * (A i i + A j j - 2 * A i j)) = 2 * D - 2 * C := by
    calc
      (Finset.univ.sum fun i =>
        Finset.univ.sum fun j =>
          p i * p j * (A i i + A j j - 2 * A i j))
          =
        (Finset.univ.sum fun i =>
          Finset.univ.sum fun j =>
            p i * p j * A i i + p i * p j * A j j -
              2 * (p i * p j * A i j)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      _ =
        (Finset.univ.sum fun i =>
          Finset.univ.sum fun j => p i * p j * A i i) +
        (Finset.univ.sum fun i =>
          Finset.univ.sum fun j => p i * p j * A j j) -
        2 * C := by
        dsimp [C]
        simp_rw [Finset.sum_sub_distrib]
        simp_rw [Finset.sum_add_distrib]
        simp_rw [Finset.mul_sum]
      _ = 2 * D - 2 * C := by
        rw [hfirst, hsecond]
        ring
  rw [hleft, hquad]
  ring

-- TODO: Prove the Gaussian interpolation monotonicity for log-sum-exp.
-- The intended statement is:
--
-- theorem gaussian_interpolation_lse_mono
--     {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
--     (μX μY : Measure (ι → ℝ))
--     [MeasureTheory.IsProbabilityMeasure μX]
--     [MeasureTheory.IsProbabilityMeasure μY]
--     [ProbabilityTheory.IsGaussian μX]
--     [ProbabilityTheory.IsGaussian μY]
--     (hX0 : ∀ i, ∫ x, x i ∂μX = 0)
--     (hY0 : ∀ i, ∫ y, y i ∂μY = 0)
--     (hinc : ∀ i j,
--       ProbabilityTheory.variance (fun x : ι → ℝ => x i - x j) μX
--         ≤ ProbabilityTheory.variance (fun y : ι → ℝ => y i - y j) μY)
--     {β : ℝ} (hβ : 0 < β) :
--     ∫ x, lse β x ∂μX ≤ ∫ y, lse β y ∂μY := by
--   sorry

end
