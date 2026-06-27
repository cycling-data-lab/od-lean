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

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms info_pos_iff
#print axioms cr_bound_q_inv
#print axioms cr_bound_antitone
#print axioms cr_bound_gt
#print axioms var_ge_q_inv

end OD
