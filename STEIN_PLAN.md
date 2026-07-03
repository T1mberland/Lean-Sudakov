# Full finite-dimensional Stein plan

Goal:

```lean
∫ x, x i * softmax β x j ∂μ =
  ∑ k, gaussianCov μ i k *
    ∫ x, β * ((if j = k then softmax β x j else 0)
      - softmax β x j * softmax β x k) ∂μ
```

for centered finite-dimensional Gaussian `μ : Measure (ι → ℝ)`.

## Items

1. Finish the scalar centered Stein input. **Done.**
   - Keep the nondegenerate one-dimensional Gaussian IBP lemma.
   - Add the degenerate `v = 0` case, so the scalar softmax-slice theorem has no `v ≠ 0`
     assumption.

2. Prove the diagonal/product Gaussian Stein theorem. **Done.**
   - Work with `Measure.pi fun k => gaussianReal 0 (v k)`.
   - Done: register this product measure as Gaussian.
   - Done: prove its coordinate covariance matrix is diagonal with entries `(v k : ℝ)`.
   - Done: prove a Bochner-valued coordinate Fubini lemma peeling off one coordinate from
     `Measure.pi`.
   - Use Fubini / marginal integration to isolate the `k`-th coordinate.
   - Apply item 1 to the softmax slice.
   - Show off-diagonal covariance terms vanish and diagonal covariance is `(v k : ℝ)`.

3. Prove the Gaussian linear-image transport lemma. **Next.**
   - If `Z` satisfies the product theorem and `L : (κ → ℝ) →L[ℝ] (ι → ℝ)`, prove Stein
     for `μ = (Measure.pi fun k => gaussianReal 0 (v k)).map L`.
   - Use the chain rule for coordinate derivatives of `softmax β (L z)`.
   - Rewrite the resulting coefficients as `gaussianCov μ i k`.

4. Build a representation theorem for finite-dimensional centered Gaussian measures.
   - From `IsGaussian μ`, extract the positive semidefinite covariance bilinear form.
   - Construct a positive square root / factorization in finite dimension.
   - Show the linear image of an independent standard Gaussian has the same mean and covariance.
   - Use `IsGaussian.ext_covarianceBilinDual` or characteristic functions to identify it with `μ`.

5. Combine items 3 and 4 into the arbitrary-covariance softmax Stein theorem.
   - Feed it into `gaussian_ibp_softmax_of_deriv_form`.
   - Remove the conditional `hstein` hypothesis from the interpolation proof.

## Current status

The repo already has the deterministic Hessian algebra, softmax derivative formulas, Gaussian
integrability of `vecMax`/`lse`, and the nondegenerate scalar softmax-slice Stein lemma.
