import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# The collection-horizon law (Bound 3, deterministic skeleton)

Lean 4 / Mathlib formalisation of the **sampling-horizon theorem** of Fossé–Pallares,
`gbfs-od-reconstruction` (Thm. *Sampling horizon, per regime*; SI B) — *how long a feed must
be polled to reconstruct the OD to a target accuracy, per system type, and why the horizon
carries the same `q⁻¹` as Bound 1*.

## Architecture (zero `sorry`)

As with `OdLean.CramerRao`, the single genuinely analytic input — the **entropic-OT
sample-complexity** rate `O(ε⁻¹ n⁻¹ᐟ²)` of Genevay et al. and Mena–Niles-Weed (a deep
result, well beyond current Mathlib) — is **isolated as a hypothesis**: it appears only as
the variance term of the plug-in error budget `err(ε) = ε + B·ε⁻¹·n⁻¹ᐟ²` (entropic bias `+`
sampling error). Everything we *contribute* is then deterministic real analysis:

| Lean name | Paper content |
|---|---|
| `OD.amgm_two` | the two-term AM–GM `2√(ab) ≤ a + b` (the optimiser's engine) |
| `OD.entropic_balance` | **bias–variance balance**: `err(ε) = ε + V/ε ≥ 2√V`, minimised at `ε = √V` (`entropic_balance_eq`) |
| `OD.sample_complexity_quartic` | **free-floating `δ⁻⁴`**: balancing the `d=2` continuous OT error to accuracy `δ` needs `n ≥ 16B²·δ⁻⁴` |
| `OD.sample_complexity_quadratic` | **dock `δ⁻²`**: the finite-`K` parametric rate `C·n⁻¹ᐟ²` needs `n ≥ C²·δ⁻²` |
| `OD.horizon_min` | the **minimal horizon** `T⋆ = Φ/(R q)` is exactly the feasibility threshold `Φ ≤ n_eff(T)` |
| `OD.Tstar_q_inv`, `OD.Tstar_antitone_q` | `T⋆ ∝ q⁻¹`: the horizon inherits Bound 1's persistence law |
| `OD.regime_crossover` | docks beat free-floating iff `K²δ² < C₄` — the crossover `K⋆ ∝ δ⁻¹` |
| `OD.Tstar_free_scaling` | **capstone**: `T⋆ = 16B²·(R δ⁴)⁻¹·q⁻¹` — the `q⁻¹·δ⁻⁴` collection cost |

The effective sample size `n_eff = R·q·T` (with `R = Λ·κ(Δ)·(1−β)(1−γ)` the feed-specific
trip-yield constant) is the paper's Eq. (n_eff); the `δ⁻⁴` exponent emerges *only* from
balancing the isolated OT variance against the entropic bias, and the `q⁻¹` is the same
estimator-free factor proved in `OdLean.Basic` / `OdLean.CramerRao`. No optimal-transport
theory is invoked: the bound's content is the algebra of the horizon, with the OT
sample-complexity rate isolated as the input `B·ε⁻¹·n⁻¹ᐟ²`.
-/

namespace OD

/-! ### The bias–variance optimiser -/

/-- **Two-term AM–GM**: `2√(ab) ≤ a + b`. The engine of the bias–variance balance. -/
theorem amgm_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h := sq_nonneg (Real.sqrt a - Real.sqrt b)
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  rw [Real.sqrt_mul ha]
  nlinarith [h, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

/-- **Bias–variance balance.** With entropic bias `ε` and sampling variance term `V/ε`, the
plug-in error `ε + V/ε` is bounded below by `2√V`. This is the lower envelope whose
`n`-dependence produces the regime exponents below. -/
theorem entropic_balance {V ε : ℝ} (hV : 0 ≤ V) (hε : 0 < ε) :
    2 * Real.sqrt V ≤ ε + V / ε := by
  have hb : 0 ≤ V / ε := div_nonneg hV hε.le
  have h := amgm_two hε.le hb
  have he : ε * (V / ε) = V := by field_simp
  rwa [he] at h

/-- The balance is **attained** at `ε = √V`: the optimal entropic regulariser, where bias
equals standard deviation, gives error exactly `2√V`. -/
theorem entropic_balance_eq {V : ℝ} (hV : 0 < V) :
    Real.sqrt V + V / Real.sqrt V = 2 * Real.sqrt V := by
  have hs : Real.sqrt V ≠ 0 := (Real.sqrt_pos.mpr hV).ne'
  have h : V / Real.sqrt V = Real.sqrt V := by
    rw [div_eq_iff hs, Real.mul_self_sqrt hV.le]
  rw [h]; ring

/-! ### Sample-complexity exponents, per regime -/

/-- **Free-floating regime (`δ⁻⁴`).** The optimally-balanced continuous-OT plug-in error is
`2√(B/√n) = 2√B·n⁻¹ᐟ⁴`. Reaching accuracy `δ` therefore requires `n ≥ 16B²·δ⁻⁴`: halving
the target multiplies the sample by `2⁴ = 16` (the Genevay/Mena–Niles-Weed exponent for
`d = 2`). -/
theorem sample_complexity_quartic {B δ n : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hn : 0 < n)
    (hacc : 2 * Real.sqrt (B / Real.sqrt n) ≤ δ) :
    16 * B ^ 2 / δ ^ 4 ≤ n := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  set x := B / Real.sqrt n with hxdef
  have hx : 0 ≤ x := by rw [hxdef]; positivity
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hsnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have h1 : 4 * x ≤ δ ^ 2 := by nlinarith [hacc, hsx, hsnn, hδ.le]
  have h1' : 4 * B ≤ δ ^ 2 * Real.sqrt n := by
    rw [hxdef, ← mul_div_assoc, div_le_iff₀ hsn] at h1; exact h1
  have h3 : (4 * B) ^ 2 ≤ (δ ^ 2 * Real.sqrt n) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1' 2
  have hexp : (δ ^ 2 * Real.sqrt n) ^ 2 = δ ^ 4 * n := by
    rw [mul_pow, Real.sq_sqrt hn.le]; ring
  rw [hexp] at h3
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 4)]
  nlinarith [h3]

/-- **Dock regime (`δ⁻²`).** For a finite `K`-station network the OD error follows the
standard parametric rate `C·n⁻¹ᐟ²`; reaching accuracy `δ` requires `n ≥ C²·δ⁻²` (with
`C ∝ K`, giving the `K²·δ⁻²` of the theorem). Exponent `2`, not `4`. -/
theorem sample_complexity_quadratic {C δ n : ℝ} (hC : 0 < C) (hδ : 0 < δ) (hn : 0 < n)
    (hacc : C / Real.sqrt n ≤ δ) :
    C ^ 2 / δ ^ 2 ≤ n := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  rw [div_le_iff₀ hsn] at hacc
  have h2 : C ^ 2 ≤ (δ * Real.sqrt n) ^ 2 := pow_le_pow_left₀ hC.le hacc 2
  have hexp : (δ * Real.sqrt n) ^ 2 = δ ^ 2 * n := by rw [mul_pow, Real.sq_sqrt hn.le]
  rw [hexp] at h2
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)]
  nlinarith [h2]

/-! ### The collection horizon -/

/-- Effective clean-trip count after a polling horizon `T`: `n_eff = R·q·T`, with the
feed-specific yield `R = Λ·κ(Δ)·(1−β)(1−γ)` and persistence `q` (paper Eq. n_eff). -/
noncomputable def nEff (R q T : ℝ) : ℝ := R * q * T

/-- The minimal horizon to collect `Φ` effective trips: `T⋆ = Φ / (R q)`. -/
noncomputable def Tstar (R q Φ : ℝ) : ℝ := Φ / (R * q)

/-- **`T⋆` is exactly the feasibility threshold.** The required sample `Φ` is reached by
horizon `T` iff `T ≥ T⋆`: `n_eff` grows linearly in `T`, so the horizon law is sharp. -/
theorem horizon_min {R q Φ T : ℝ} (hR : 0 < R) (hq : 0 < q) :
    Φ ≤ nEff R q T ↔ Tstar R q Φ ≤ T := by
  unfold nEff Tstar
  rw [div_le_iff₀ (by positivity : 0 < R * q)]
  constructor <;> intro h <;> nlinarith [h]

/-- **`T⋆` carries the `q⁻¹` law.** The collection horizon is `(Φ/R)·q⁻¹`: the same
estimator-free persistence divergence as Bound 1, now in wall-clock collection time. -/
theorem Tstar_q_inv (R q Φ : ℝ) :
    Tstar R q Φ = (Φ / R) * q⁻¹ := by
  unfold Tstar
  rw [div_mul_eq_div_div]
  exact div_eq_mul_inv (Φ / R) q

/-- **`T⋆` is antitone in persistence**: less compliance (smaller `q`) means a strictly
longer horizon, diverging as `q → 0`. -/
theorem Tstar_antitone_q {R Φ q1 q2 : ℝ} (hR : 0 < R) (hΦ : 0 ≤ Φ)
    (hq1 : 0 < q1) (hle : q1 ≤ q2) :
    Tstar R q2 Φ ≤ Tstar R q1 Φ := by
  unfold Tstar
  rw [div_le_div_iff₀ (mul_pos hR (lt_of_lt_of_le hq1 hle)) (mul_pos hR hq1)]
  nlinarith [mul_nonneg (mul_nonneg hΦ hR.le) (by linarith : (0 : ℝ) ≤ q2 - q1)]

/-- **Regime crossover.** With free-floating cost `Φ_free = C₄·δ⁻⁴` and dock cost
`Φ_dock = K²·δ⁻²`, a dock network is cheaper to reconstruct iff `K²δ² < C₄`, i.e.
`K < √C₄·δ⁻¹` — the crossover station count scales as `K⋆ ∝ δ⁻¹`. -/
theorem regime_crossover {C4 δ K : ℝ} (hδ : 0 < δ) :
    K ^ 2 / δ ^ 2 < C4 / δ ^ 4 ↔ K ^ 2 * δ ^ 2 < C4 := by
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hδ4 : (0 : ℝ) < δ ^ 4 := by positivity
  rw [div_lt_div_iff₀ hδ2 hδ4]
  constructor
  · intro h; nlinarith [h, hδ2]
  · intro h; nlinarith [h, hδ2]

/-- **Capstone: the free-floating collection cost.** Reconstructing a continuous
free-floating OD to accuracy `δ` takes minimal polling horizon
`T⋆ = 16B²·(R δ⁴)⁻¹·q⁻¹` — the full `q⁻¹·δ⁻⁴` law: linear in the inverse trip-yield, quartic
in the inverse target, and carrying Bound 1's inverse-persistence divergence. -/
theorem Tstar_free_scaling (R q B δ : ℝ) :
    Tstar R q (16 * B ^ 2 / δ ^ 4) = (16 * B ^ 2 / (R * δ ^ 4)) * q⁻¹ := by
  rw [Tstar_q_inv, div_div, mul_comm (δ ^ 4) R]

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms amgm_two
#print axioms entropic_balance
#print axioms entropic_balance_eq
#print axioms sample_complexity_quartic
#print axioms sample_complexity_quadratic
#print axioms horizon_min
#print axioms Tstar_q_inv
#print axioms Tstar_antitone_q
#print axioms regime_crossover
#print axioms Tstar_free_scaling

end OD
