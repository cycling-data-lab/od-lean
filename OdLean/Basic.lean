import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Identifiability limit of GBFS OD reconstruction (Bound 1)

Lean 4 / Mathlib formalisation of the **central, estimator-free bound** of
Fossé–Pallares, `gbfs-od-reconstruction` — *identifier rotation switches off the only
channel that can resolve the OD interior*.

## Architecture (zero `sorry`)

Mirroring the `sbf-lean` style, the **statistical inputs** are taken as hypotheses /
definitions, exactly as the paper states them:

* the tracked micro-channel's Fisher information about the cost is **linear in the
  identifier-persistence rate `q`**: `info q = q · I₁`, with per-unit information `I₁ > 0`;
* **Cramér–Rao**: any unbiased estimator's variance is `≥ 1 / info q` when `info q > 0`.

The **deterministic consequences** — the heart of the bound — are then pure finite real
algebra:

| Lean name | Paper statement |
|---|---|
| `OD.info_pos_iff` | identifiability dichotomy: information `> 0` ⟺ `q > 0`; at `q = 0` the channel is off |
| `OD.cr_bound_q_inv` | the Cramér–Rao floor equals `(1/I₁)·q⁻¹` — the **`q⁻¹` law** |
| `OD.cr_bound_antitone` | the floor grows as persistence shrinks |
| `OD.cr_bound_gt` | the floor exceeds any threshold for small enough `q` — **divergence** as `q → 0` |
| `OD.var_ge_q_inv` | end-to-end: under Cramér–Rao, `Var ≥ (1/I₁)·q⁻¹` |

This is the *fundamental term* of the three separated bounds. The other two — the bias
structure (Bound 2, a kernel/quotient statement) and the entropic-OT collection-horizon
rate `δ⁻⁴`/`δ⁻²·K²` (Bound 3, genuinely analytic, à la sample-complexity of optimal
transport) — are out of scope here, the latter being beyond current Mathlib (the analogue
of `sbf-lean`'s pending Theorem 2/3).
-/

namespace OD

/-- Fisher information of the tracked channel about the cost: **linear in persistence `q`**,
with fixed per-unit information `I₁` (the paper's micro-channel information rate). -/
noncomputable def info (I1 q : ℝ) : ℝ := q * I1

/-- **Identifiability dichotomy.** The information is positive iff persistence is positive;
at `q = 0` the channel carries zero information, so the OD interior is unidentified for any
estimator and any model. -/
theorem info_pos_iff (I1 : ℝ) (hI1 : 0 < I1) (q : ℝ) :
    0 < info I1 q ↔ 0 < q := by
  unfold info
  constructor
  · intro h
    by_contra hq
    rw [not_lt] at hq
    nlinarith [mul_nonneg (neg_nonneg.mpr hq) hI1.le]
  · intro hq; positivity

/-- The Cramér–Rao floor `1 / info q` is exactly `(1/I₁)·q⁻¹` — the **`q⁻¹` law**. -/
theorem cr_bound_q_inv (I1 : ℝ) (hI1 : 0 < I1) (q : ℝ) (hq : 0 < q) :
    1 / info I1 q = (1 / I1) * q⁻¹ := by
  unfold info
  field_simp

/-- The floor is **antitone** in persistence: less persistence ⇒ larger lower bound. -/
theorem cr_bound_antitone (I1 : ℝ) (hI1 : 0 < I1) {q1 q2 : ℝ}
    (hq1 : 0 < q1) (h : q1 ≤ q2) :
    1 / info I1 q2 ≤ 1 / info I1 q1 := by
  unfold info
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right h hI1.le)

/-- **Divergence.** The floor exceeds any threshold `M` once persistence is small enough
(`q < 1/(M·I₁)`): no finite variance bound survives `q → 0`. This is the precise sense in
which identifier rotation (`q → 0`) defeats reconstruction. -/
theorem cr_bound_gt (I1 : ℝ) (hI1 : 0 < I1) {M q : ℝ} (hM : 0 < M)
    (hq : 0 < q) (hsmall : q < 1 / (M * I1)) :
    M < 1 / info I1 q := by
  unfold info
  have hMI : 0 < M * I1 := by positivity
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < q * I1)]
  have hkey := (lt_div_iff₀ hMI).mp hsmall
  nlinarith [hkey]

/-- **End-to-end.** Under the Cramér–Rao input `hcr`, the variance of any unbiased
estimator of the cost is at least `(1/I₁)·q⁻¹` — diverging as `q → 0`. -/
theorem var_ge_q_inv (I1 : ℝ) (hI1 : 0 < I1) (q : ℝ) (hq : 0 < q)
    (Var : ℝ) (hcr : 1 / info I1 q ≤ Var) :
    (1 / I1) * q⁻¹ ≤ Var := by
  rw [← cr_bound_q_inv I1 hI1 q hq]; exact hcr

/-! ### Misspecification robustness: the `q⁻¹` law survives a wrong model

The Cramér–Rao floor above is computed *within* the Gibbs class. When the truth is not Gibbs,
the M-estimator targets the pseudo-true parameter and the relevant variance is the
Huber–White **sandwich** `A⁻¹ B A⁻¹ / n_eff`, with `A = E[∂²ℓ]` the per-observation Hessian
and `B = Var(∂ℓ)` the per-observation score variance (both `q`-free). Since `n_eff ∝ q`, the
`q⁻¹` divergence is unchanged — only the constant differs (paper, "Misspecification: the
sandwich form"). This is pure algebra, with `A, B` taken as the model's per-observation
inputs, exactly as the well-specified bound takes `I₁`. -/

/-- The Huber–White sandwich (asymptotic) variance `A⁻¹ B A⁻¹ / n` of an M-estimator. -/
noncomputable def sandwichVar (A B n : ℝ) : ℝ := A⁻¹ * B * A⁻¹ / n

/-- **Misspecification-robust `q⁻¹` law.** With effective sample size `n_eff = R·q·T` linear
in persistence, the sandwich variance factors as `(per-observation constant)·q⁻¹`: the same
`q⁻¹` divergence as the well-specified floor, with a different constant. Holds for any
per-observation `A, B`. -/
theorem sandwich_q_inv (A B R T q : ℝ) :
    sandwichVar A B (R * q * T) = (A⁻¹ * B * A⁻¹ / (R * T)) * q⁻¹ := by
  unfold sandwichVar
  rw [show R * q * T = R * T * q by ring, div_mul_eq_div_div]
  exact div_eq_mul_inv _ q

/-- The sandwich variance is the `q = 1` variance scaled by `q⁻¹`: the divergence shape is
**model-independent**, a property of the persistence channel, not of correct specification. -/
theorem sandwich_scales (A B R T q : ℝ) :
    sandwichVar A B (R * q * T) = sandwichVar A B (R * T) * q⁻¹ := by
  rw [sandwich_q_inv]; rfl

/-- The misspecified variance is **antitone** in persistence: less compliance ⇒ larger
variance (whenever the sandwich numerator `A⁻¹ B A⁻¹ ≥ 0`, i.e. `B ≥ 0`). -/
theorem sandwich_antitone_q (A B R T : ℝ) (hBA : 0 ≤ A⁻¹ * B * A⁻¹)
    (hR : 0 < R) (hT : 0 < T) {q1 q2 : ℝ} (hq1 : 0 < q1) (hle : q1 ≤ q2) :
    sandwichVar A B (R * q2 * T) ≤ sandwichVar A B (R * q1 * T) := by
  rw [sandwich_q_inv, sandwich_q_inv]
  have hinv : q2⁻¹ ≤ q1⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]; exact one_div_le_one_div_of_le hq1 hle
  exact mul_le_mul_of_nonneg_left hinv (div_nonneg hBA (by positivity))

/-- **Divergence under misspecification.** With a positive sandwich numerator, the variance
exceeds any threshold `M` once persistence is small enough — the `q → 0` blow-up is robust to
the model being wrong. -/
theorem sandwich_diverges (A B R T : ℝ) (hpos : 0 < A⁻¹ * B * A⁻¹)
    (hR : 0 < R) (hT : 0 < T) {M q : ℝ} (hM : 0 < M) (hq : 0 < q)
    (hsmall : q < (A⁻¹ * B * A⁻¹) / (M * R * T)) :
    M < sandwichVar A B (R * q * T) := by
  unfold sandwichVar
  rw [lt_div_iff₀ (by positivity : 0 < R * q * T)]
  have hkey := (lt_div_iff₀ (by positivity : 0 < M * R * T)).mp hsmall
  nlinarith [hkey]

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms info_pos_iff
#print axioms cr_bound_q_inv
#print axioms cr_bound_antitone
#print axioms cr_bound_gt
#print axioms var_ge_q_inv
#print axioms sandwich_q_inv
#print axioms sandwich_scales
#print axioms sandwich_antitone_q
#print axioms sandwich_diverges

end OD
