import LeanSudakov.Deterministic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators

noncomputable section

private lemma expSum_pos {ι : Type*} [Fintype ι]
    (β : ℝ) (x : ι → ℝ) (i : ι) :
    0 < (Finset.univ.sum fun k => Real.exp (β * x k)) := by
  exact lt_of_lt_of_le (Real.exp_pos (β * x i)) <|
    Finset.single_le_sum
      (s := (Finset.univ : Finset ι))
      (f := fun k => Real.exp (β * x k))
      (fun _ _ => Real.exp_nonneg _) (Finset.mem_univ i)

private lemma update_self {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (i : ι) : Function.update x i (x i) = x := by
  ext k
  by_cases h : k = i
  · subst k
    simp
  · simp [Function.update, h]

private lemma hasDerivAt_exp_update_coord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i k : ι) :
    HasDerivAt (fun t => Real.exp (β * Function.update x i t k))
      (if k = i then β * Real.exp (β * x i) else 0) (x i) := by
  by_cases h : k = i
  · subst k
    simpa [Function.update, mul_comm] using ((hasDerivAt_const_mul (x := x i) β).exp)
  · have hconst : (fun t : ℝ => Real.exp (β * Function.update x i t k)) =
        fun _ => Real.exp (β * x k) := by
      ext t
      simp [Function.update, h]
    rw [hconst]
    simpa [h] using (hasDerivAt_const (x := x i) (Real.exp (β * x k)))

private lemma hasDerivAt_expSum_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i : ι) :
    HasDerivAt
      (fun t => (Finset.univ.sum fun k => Real.exp (β * Function.update x i t k)))
      (β * Real.exp (β * x i)) (x i) := by
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset ι))
    (fun k _ => hasDerivAt_exp_update_coord β x i k)
  convert hsum using 1
  simp

/-- Coordinate derivative of log-sum-exp. -/
theorem hasDerivAt_lse_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => lse β (Function.update x i t))
      (softmax β x i) (x i) := by
  have hSpos : 0 < (Finset.univ.sum fun k => Real.exp (β * x k)) := expSum_pos β x i
  have hlog := (hasDerivAt_expSum_update β x i).log ?_
  · have hdiv := hlog.div_const β
    convert hdiv using 1
    rw [update_self x i]
    simp [softmax]
    field_simp [hβ, hSpos.ne']
  · simpa [update_self x i] using hSpos.ne'

/-- Coordinate derivative of log-sum-exp, as a `deriv` identity. -/
theorem deriv_lse_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : ℝ} (hβ : β ≠ 0) (x : ι → ℝ) (i : ι) :
    deriv (fun t => lse β (Function.update x i t)) (x i) =
      softmax β x i :=
  (hasDerivAt_lse_update hβ x i).deriv

/-- Coordinate derivative of softmax. This is the Hessian entry of log-sum-exp after
`hasDerivAt_lse_update`. -/
theorem hasDerivAt_softmax_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i j : ι) :
    HasDerivAt (fun t => softmax β (Function.update x j t) i)
      (β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j))
      (x j) := by
  let S : ℝ := Finset.univ.sum fun k => Real.exp (β * x k)
  have hSpos : 0 < S := by simpa [S] using expSum_pos β x j
  have hquot := (hasDerivAt_exp_update_coord β x j i).div
    (hasDerivAt_expSum_update β x j) ?_
  · convert hquot using 1
    rw [update_self x j]
    simp [softmax]
    by_cases hij : i = j
    · subst j
      field_simp [S, hSpos.ne']
      simp
      have hsum_ne : (Finset.univ.sum fun k => Real.exp (β * x k)) ≠ 0 := by
        simpa [S] using hSpos.ne'
      field_simp [hsum_ne]
    · field_simp [S, hSpos.ne', hij]
      simp [hij]
      ring_nf
  · simpa [S, update_self x j] using hSpos.ne'

/-- Hessian entry of log-sum-exp, as a `deriv` identity for softmax. -/
theorem deriv_softmax_update
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (x : ι → ℝ) (i j : ι) :
    deriv (fun t => softmax β (Function.update x j t) i) (x j) =
      β * ((if i = j then softmax β x i else 0) - softmax β x i * softmax β x j) :=
  (hasDerivAt_softmax_update β x i j).deriv

end
