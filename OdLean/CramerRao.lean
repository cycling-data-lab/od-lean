import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The Cramér–Rao step, discharged (Bound 1, closing the `hcr` input)

`OdLean.Basic` proves the `q⁻¹` information limit (Bound 1) taking the **Cramér–Rao
inequality** `Var ≥ 1 / info` as an explicit hypothesis `hcr`, exactly as the paper states
it. That hypothesis is the only measure-theoretic step of Bound 1. Here we **discharge it
from first principles**, so the bound rests on genuinely statistical inputs rather than an
assumed inequality.

The mathematical content of Cramér–Rao is a single application of **Cauchy–Schwarz** to the
estimator and the score, plus the algebra of the resulting quadratic. We give it in two
layers, in the `sbf-lean` style (abstract deductive core + honest analytic instantiation):

| Lean name | Statement |
|---|---|
| `OD.cramer_rao_inner` | **Abstract core.** In any real inner-product space, `⟪T,S⟫ = 1` and `⟪S,S⟫ = I > 0` force `⟪T,T⟫ ≥ 1/I`. Pure Cauchy–Schwarz. |
| `OD.covariance_sq_le_variance_mul_variance` | **Covariance Cauchy–Schwarz** for genuine `ProbabilityTheory` random variables, via the nonnegative-quadratic / discriminant argument. |
| `OD.cramer_rao_variance` | **Measure-theoretic Cramér–Rao.** For real random variables with `cov[T,S] = 1` (regularity/unbiasedness) and `Var[S] = I > 0` (Fisher information `=` score variance), `Var[T] ≥ 1/I`. |
| `OD.var_ge_q_inv_of_score` | **Capstone.** With the score's variance equal to the persistence-linear information `Var[S] = q·I₁`, the estimator variance obeys `Var[T] ≥ (1/I₁)·q⁻¹` — Bound 1's `q⁻¹` law, now with the Cramér–Rao input *derived*, not assumed. |

The remaining inputs — `cov[T,S] = 1` and `Var[S] = q·I₁` — are precisely the regularity
conditions of Cramér–Rao (differentiation under the integral giving a unit score
covariance, and the Fisher information realised as the score variance). They are genuine
measure-theoretic quantities here (`ProbabilityTheory.covariance`, `.variance`), not
abstractions; what was an assumed inequality in `Basic.lean` is now a theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OD

/-! ### Abstract core: Cramér–Rao is Cauchy–Schwarz -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Cramér–Rao, abstract form.** In a real inner-product space, if an estimator vector `T`
has unit inner product with the score vector `S` (`⟪T,S⟫ = 1`) and the score carries
information `⟪S,S⟫ = I > 0`, then `⟪T,T⟫ ≥ 1/I`. This is exactly Cauchy–Schwarz:
`1 = ⟪T,S⟫² ≤ ‖T‖²‖S‖² = ⟪T,T⟫·I`. -/
theorem cramer_rao_inner (T S : F) (I : ℝ) (hI : 0 < I)
    (hcov : ⟪T, S⟫ = 1) (hinfo : ⟪S, S⟫ = I) :
    1 / I ≤ ⟪T, T⟫ := by
  have hcs : |⟪T, S⟫| ≤ ‖T‖ * ‖S‖ := abs_real_inner_le_norm T S
  have hsq : ⟪T, S⟫ ^ 2 ≤ ‖T‖ ^ 2 * ‖S‖ ^ 2 := by
    rw [← sq_abs ⟪T, S⟫, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hcs 2
  have hS2 : ‖S‖ ^ 2 = I := by rw [← real_inner_self_eq_norm_sq S, hinfo]
  have hcs1 : ⟪T, S⟫ ^ 2 = 1 := by rw [hcov]; norm_num
  rw [hS2] at hsq
  rw [real_inner_self_eq_norm_sq T, div_le_iff₀ hI]
  linarith [hsq, hcs1]

/-! ### Measure-theoretic instantiation via covariance / variance -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Covariance Cauchy–Schwarz.** For square-integrable real random variables,
`cov[X,Y]² ≤ Var[X]·Var[Y]`. Proof: the variance of `X − tY` is a nonnegative quadratic in
`t`, so its discriminant is `≤ 0`. -/
theorem covariance_sq_le_variance_mul_variance [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    cov[X, Y; μ] ^ 2 ≤ Var[X; μ] * Var[Y; μ] := by
  have hquad : ∀ t : ℝ,
      0 ≤ Var[Y; μ] * (t * t) + (-(2 * cov[X, Y; μ])) * t + Var[X; μ] := by
    intro t
    have h := variance_nonneg (X - t • Y) μ
    rw [variance_sub hX (hY.const_smul t), covariance_smul_right, variance_smul,
      pow_two] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  simp only [discrim] at hd
  nlinarith [hd]

/-- **Cramér–Rao, measure-theoretic form.** Let `T` be a square-integrable estimator and `S`
a square-integrable score with `cov[T,S] = 1` (the regularity/unbiasedness condition) and
Fisher information `Var[S] = I > 0`. Then the estimator variance obeys `Var[T] ≥ 1/I`. This
is `cramer_rao_inner` realised in the `L²(μ)` geometry, with the covariance Cauchy–Schwarz
above as the inner-product inequality. -/
theorem cramer_rao_variance [IsProbabilityMeasure μ]
    {T S : Ω → ℝ} (I : ℝ) (hI : 0 < I)
    (hT : MemLp T 2 μ) (hS : MemLp S 2 μ)
    (hcov : cov[T, S; μ] = 1) (hinfo : Var[S; μ] = I) :
    1 / I ≤ Var[T; μ] := by
  have hCS := covariance_sq_le_variance_mul_variance hT hS
  rw [hcov, hinfo] at hCS
  rw [div_le_iff₀ hI]
  nlinarith [hCS]

/-- **Capstone: Bound 1's `q⁻¹` law with Cramér–Rao derived.** When the score's information
is linear in the identifier-persistence rate, `Var[S] = q·I₁` (`I₁ > 0` the per-unit
information, `q > 0` the persistence), the variance of any regular unbiased estimator of the
cost satisfies `Var[T] ≥ (1/I₁)·q⁻¹` — diverging as `q → 0`. This is exactly
`OdLean.Basic`'s `var_ge_q_inv`, but with its `hcr` hypothesis now *proved* from Cauchy–Schwarz
and the score covariance. -/
theorem var_ge_q_inv_of_score [IsProbabilityMeasure μ]
    {T S : Ω → ℝ} (I1 q : ℝ) (hI1 : 0 < I1) (hq : 0 < q)
    (hT : MemLp T 2 μ) (hS : MemLp S 2 μ)
    (hcov : cov[T, S; μ] = 1) (hinfo : Var[S; μ] = q * I1) :
    (1 / I1) * q⁻¹ ≤ Var[T; μ] := by
  have hIpos : 0 < q * I1 := by positivity
  have h := cramer_rao_variance (q * I1) hIpos hT hS hcov hinfo
  have heq : (1 : ℝ) / (q * I1) = (1 / I1) * q⁻¹ := by
    rw [one_div, one_div, mul_inv]; ring
  rwa [heq] at h

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms cramer_rao_inner
#print axioms covariance_sq_le_variance_mul_variance
#print axioms cramer_rao_variance
#print axioms var_ge_q_inv_of_score

end OD
