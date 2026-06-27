import Mathlib

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Cost identifiability and the structure of observation bias (Bound 2)

Lean 4 / Mathlib formalisation of the **identifiability / selection-bias bound** of
Fossé–Pallares, `gbfs-od-reconstruction` (SI Appendix A) — *the OD cost is identifiable
only modulo additive station effects, and the observation bias is exactly the
non-separable part of the log-selection, so station-emptiness censoring cancels while
`60`-second polling aliasing does not*.

## Architecture (zero `sorry`)

Mirroring the `sbf-lean` / `OdLean.Basic` style, the whole bound is **finite linear
algebra over `ℝ`** on the `N × N` design (pair) space, modelled as `Fin N → Fin N → ℝ`.
The single structural object is the **two-way centring** (the entropic-OT *interaction*
operator)
`(center M)ᵢⱼ = Mᵢⱼ − M̄ᵢ· − M̄·ⱼ + M̄··`,
which is the orthogonal projection `Π_{𝒩^⊥}` off the **separable subspace**
`𝒩 = {(i,j) ↦ fᵢ + gⱼ}` of additive station effects (`dim 𝒩 = 2N−1`). Everything below is
the algebra of this projection.

| Lean name | Paper statement |
|---|---|
| `OD.center_separable` | `𝒩 ⊆ ker(center)`: every additive station effect is annihilated |
| `OD.center_add_separable` | **gauge freedom** (Lemma A.1 / A.2): adding a separable term — a cost gauge *or* a Sinkhorn rebalancing potential — leaves the interaction unchanged |
| `OD.center_idem` | `center` is idempotent: it is a genuine projection onto the identifiable class |
| `OD.center_unique` | `center M` is the **unique** representative of `M + 𝒩` orthogonal to `𝒩`: it is *the* orthogonal projection `Π_{𝒩^⊥}` |
| `OD.bias_decomposition` | **Prop. (bias = non-separable log-selection)**: `Π⊥ ĉ = Π⊥ c⋆ − ε·Π⊥ log S` |
| `OD.bias_cancels_separable` | **station-emptiness cancels**: separable selection `S = aᵢbⱼ` injects no interaction bias |
| `OD.bias_attenuation` | **polling aliasing attenuates**: duration-dependent selection scales the identifiable cost by `1 − εητ < 1` |

The statistical inputs (consistency of the empirical coupling, the Gibbs/Sinkhorn form)
are taken as the hypotheses of `bias_decomposition` — the separable calibration/normaliser
term `D` — exactly as the paper states them; the *deterministic content* of the bound, the
gauge algebra and the separable/non-separable dichotomy, is then proved from first
principles. This is the bias-structure companion to `OdLean.Basic`'s `q⁻¹` information
limit (Bound 1), and the design-matrix kernel/quotient analogue of `sbf-lean`'s projection
lemmas.
-/

open Finset

namespace OD

variable {N : ℕ}

/-- Row mean of a pair-indexed array `M : Fin N → Fin N → ℝ` (origin-station effect). -/
noncomputable def rowMean (M : Fin N → Fin N → ℝ) (i : Fin N) : ℝ := (N : ℝ)⁻¹ * ∑ j, M i j

/-- Column mean (destination-station effect). -/
noncomputable def colMean (M : Fin N → Fin N → ℝ) (j : Fin N) : ℝ := (N : ℝ)⁻¹ * ∑ i, M i j

/-- Grand mean over all ordered pairs. -/
noncomputable def grandMean (M : Fin N → Fin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * ∑ i, ∑ j, M i j

/-- **Two-way centring** `Π_{𝒩^⊥}` (the entropic-OT *interaction* of the cost):
`(center M)ᵢⱼ = Mᵢⱼ − M̄ᵢ· − M̄·ⱼ + M̄··`. This is the only identifiable part of the cost. -/
noncomputable def center (M : Fin N → Fin N → ℝ) (i j : Fin N) : ℝ :=
  M i j - rowMean M i - colMean M j + grandMean M

/-- **Separable** (additive station-effect) arrays: the gauge subspace `𝒩 = {fᵢ + gⱼ}`. -/
def Separable (M : Fin N → Fin N → ℝ) : Prop := ∃ f g : Fin N → ℝ, ∀ i j, M i j = f i + g j

/-- `∑` of a constant over `Fin N` is `N` times it. -/
private lemma sum_const_fin (a : ℝ) : ∑ _x : Fin N, a = (N : ℝ) * a := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Gauge kernel** (Lemma A.1). Two-way centring annihilates every separable array:
the additive station-effect class `𝒩` is invisible to the interaction, so a cost is
identifiable only through `center`. -/
theorem center_separable [NeZero N] (f g : Fin N → ℝ) :
    center (fun i j => f i + g j) = fun _ _ => (0 : ℝ) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  funext i j
  simp only [center, rowMean, colMean, grandMean]
  have r : (∑ j, (f i + g j)) = (N : ℝ) * f i + ∑ j, g j := by
    rw [Finset.sum_add_distrib, sum_const_fin]
  have c : (∑ i, (f i + g j)) = (∑ i, f i) + (N : ℝ) * g j := by
    rw [Finset.sum_add_distrib, sum_const_fin]
  have gd : (∑ i, ∑ j, (f i + g j)) = (N : ℝ) * (∑ i, f i) + (N : ℝ) * (∑ j, g j) := by
    have inner : ∀ i, (∑ j, (f i + g j)) = (N : ℝ) * f i + ∑ j, g j :=
      fun i => by rw [Finset.sum_add_distrib, sum_const_fin]
    simp_rw [inner]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_const_fin (∑ j, g j)]
  rw [r, c, gd]
  field_simp
  ring

/-- Centring is additive. -/
theorem center_add (M M' : Fin N → Fin N → ℝ) :
    center (fun i j => M i j + M' i j) = fun i j => center M i j + center M' i j := by
  funext i j
  simp only [center, rowMean, colMean, grandMean, Finset.sum_add_distrib]
  ring

/-- Centring respects subtraction. -/
theorem center_sub (M M' : Fin N → Fin N → ℝ) :
    center (fun i j => M i j - M' i j) = fun i j => center M i j - center M' i j := by
  funext i j
  simp only [center, rowMean, colMean, grandMean, Finset.sum_sub_distrib]
  ring

/-- Centring is homogeneous. -/
theorem center_smul (c : ℝ) (M : Fin N → Fin N → ℝ) :
    center (fun i j => c * M i j) = fun i j => c * center M i j := by
  funext i j
  simp only [center, rowMean, colMean, grandMean, ← Finset.mul_sum]
  ring

/-- **Gauge freedom** (Lemma A.1 *and* the rebalancing lynchpin Lemma A.2). Adding any
separable array `D` — whether a cost gauge `cᵢⱼ ↦ cᵢⱼ + fᵢ + gⱼ` or the Sinkhorn
potentials `−ε(log αᵢ + log βⱼ)` injected by calibrating to the macro margins — leaves the
identifiable interaction `center M` **unchanged**. Calibration injects no interaction
bias. -/
theorem center_add_separable [NeZero N] (M D : Fin N → Fin N → ℝ) (hD : Separable D) :
    center (fun i j => M i j + D i j) = center M := by
  obtain ⟨f, g, hfg⟩ := hD
  have hDfun : D = fun i j => f i + g j := by funext i j; exact hfg i j
  rw [center_add, hDfun, center_separable f g]
  funext i j; simp

/-- The non-identifiable remainder `M − center M` (the row/column/grand means) is
separable: it lives in the gauge subspace `𝒩`. Together with orthogonality this is the
orthogonal decomposition `M = (M − Π⊥M) + Π⊥M` with the first summand in `𝒩`. -/
theorem sub_center_separable (M : Fin N → Fin N → ℝ) :
    Separable (fun i j => M i j - center M i j) :=
  ⟨fun i => rowMean M i, fun j => colMean M j - grandMean M, by
    intro i j; simp only [center]; ring⟩

/-- **Idempotence**: `center` is a genuine projection — re-centring an interaction returns
it unchanged. The identifiable cost is a fixed point of the gauge. -/
theorem center_idem [NeZero N] (M : Fin N → Fin N → ℝ) :
    center (center M) = center M := by
  have h := center_add_separable (center M) (fun i j => M i j - center M i j)
    (sub_center_separable M)
  have heq : (fun i j => center M i j + (M i j - center M i j)) = M := by funext i j; ring
  rw [heq] at h
  exact h.symm

/-- **Frobenius inner product** on the pair space. -/
noncomputable def frob (A B : Fin N → Fin N → ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

/-- `frob` is left-subtractive. -/
theorem frob_sub_left (A B C : Fin N → Fin N → ℝ) :
    frob (fun i j => A i j - B i j) C = frob A C - frob B C := by
  simp only [frob, sub_mul, Finset.sum_sub_distrib]

/-- Every row of a centred array sums to zero. -/
theorem row_sum_center [NeZero N] (M : Fin N → Fin N → ℝ) (i : Fin N) :
    ∑ j, center M i j = 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hcol : (∑ j, colMean M j) = (N : ℝ)⁻¹ * ∑ i, ∑ j, M i j := by
    simp only [colMean]; rw [← Finset.mul_sum, Finset.sum_comm]
  have hrowc : (∑ _j : Fin N, rowMean M i) = (N : ℝ) * rowMean M i := sum_const_fin _
  have hgrc : (∑ _j : Fin N, grandMean M) = (N : ℝ) * grandMean M := sum_const_fin _
  have hexp : ∑ j, center M i j
      = (∑ j, M i j) - (∑ _j : Fin N, rowMean M i) - (∑ j, colMean M j)
        + (∑ _j : Fin N, grandMean M) := by
    simp only [center]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hexp, hrowc, hgrc, hcol]
  simp only [rowMean, grandMean]
  field_simp
  ring

/-- Every column of a centred array sums to zero. -/
theorem col_sum_center [NeZero N] (M : Fin N → Fin N → ℝ) (j : Fin N) :
    ∑ i, center M i j = 0 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hrow : (∑ i, rowMean M i) = (N : ℝ)⁻¹ * ∑ i, ∑ j, M i j := by
    simp only [rowMean]; rw [← Finset.mul_sum]
  have hcolc : (∑ _i : Fin N, colMean M j) = (N : ℝ) * colMean M j := sum_const_fin _
  have hgrc : (∑ _i : Fin N, grandMean M) = (N : ℝ) * grandMean M := sum_const_fin _
  have hexp : ∑ i, center M i j
      = (∑ i, M i j) - (∑ i, rowMean M i) - (∑ _i : Fin N, colMean M j)
        + (∑ _i : Fin N, grandMean M) := by
    simp only [center]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [hexp, hcolc, hgrc, hrow]
  simp only [colMean, grandMean]
  field_simp
  ring

/-- **Orthogonality**: the interaction `center M` is Frobenius-orthogonal to every
separable array. With `sub_center_separable` this exhibits `center` as the genuine
orthogonal projection `Π_{𝒩^⊥}`. -/
theorem center_orthogonal_separable [NeZero N] (M D : Fin N → Fin N → ℝ) (hD : Separable D) :
    frob (center M) D = 0 := by
  obtain ⟨f, g, hfg⟩ := hD
  have hrow := row_sum_center M
  have hcol := col_sum_center M
  have key : ∀ i j, center M i j * D i j = center M i j * f i + center M i j * g j := by
    intro i j; rw [hfg]; ring
  calc ∑ i, ∑ j, center M i j * D i j
      = ∑ i, ∑ j, (center M i j * f i + center M i j * g j) := by simp_rw [key]
    _ = ∑ i, ((∑ j, center M i j) * f i + ∑ j, center M i j * g j) := by
        refine Finset.sum_congr rfl ?_; intro i _
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = ∑ i, ∑ j, center M i j * g j := by
        refine Finset.sum_congr rfl ?_; intro i _
        rw [hrow i, zero_mul, zero_add]
    _ = ∑ j, ∑ i, center M i j * g j := Finset.sum_comm
    _ = ∑ j, (∑ i, center M i j) * g j := by
        refine Finset.sum_congr rfl ?_; intro j _; rw [← Finset.sum_mul]
    _ = 0 := by
        refine Finset.sum_eq_zero ?_; intro j _; rw [hcol j, zero_mul]

/-- **`center` is *the* orthogonal projection** onto `𝒩^⊥`. Any representative `M'` of the
identifiable class `M + 𝒩` (i.e. `M − M'` separable) that is itself orthogonal to every
station-effect array must equal `center M`. So the identifiable interaction is unique and
well defined as a quotient representative — the precise sense in which the cost is
identifiable *only modulo* additive station effects. -/
theorem center_unique [NeZero N] (M M' : Fin N → Fin N → ℝ)
    (hsep : Separable (fun i j => M i j - M' i j))
    (horth : ∀ D : Fin N → Fin N → ℝ, Separable D → frob M' D = 0) :
    M' = center M := by
  obtain ⟨f1, g1, h1⟩ := sub_center_separable M
  obtain ⟨f2, g2, h2⟩ := hsep
  have hEsep : Separable (fun i j => M' i j - center M i j) :=
    ⟨fun i => f1 i - f2 i, fun j => g1 j - g2 j, by
      intro i j; have a1 := h1 i j; have a2 := h2 i j; simp only at a1 a2 ⊢; linarith⟩
  have hEorth : ∀ D, Separable D → frob (fun i j => M' i j - center M i j) D = 0 := by
    intro D hD
    rw [frob_sub_left, horth D hD, center_orthogonal_separable M D hD, sub_zero]
  have hEE := hEorth _ hEsep
  have hsum0 : ∑ i, ∑ j, (M' i j - center M i j) ^ 2 = 0 := by
    rw [← hEE]; simp only [frob]
    refine Finset.sum_congr rfl ?_; intro i _
    refine Finset.sum_congr rfl ?_; intro j _; ring
  funext i j
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      (0 : ℝ) ≤ ∑ j, (M' i j - center M i j) ^ 2 :=
    fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg (M' i j - center M i j))).mp hi j (Finset.mem_univ j)
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hj)

/-- **Bias = non-separable log-selection** (SI Prop., Eq. bias). The identifier-tracked
trips are drawn from the tilted law `P̃ ∝ P⋆ ⊙ S`; fitting the Gibbs model and calibrating
to any feasible margins recovers `ĉ = c⋆ − ε·log S` *up to a separable term* `D` (the
Sinkhorn potentials + normaliser, harmless by `center_add_separable`). On the identifiable
interaction this reads
`center ĉ = center c⋆ − ε · center (log S)`. -/
theorem bias_decomposition [NeZero N]
    (cstar logS D chat : Fin N → Fin N → ℝ) (ε : ℝ) (hD : Separable D)
    (hchat : ∀ i j, chat i j = cstar i j - ε * logS i j + D i j) :
    center chat = fun i j => center cstar i j - ε * center logS i j := by
  have h1 : chat = fun i j => (cstar i j - ε * logS i j) + D i j := by
    funext i j; exact hchat i j
  rw [h1, center_add_separable _ D hD]
  funext i j
  simp only [center, rowMean, colMean, grandMean, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **Station-emptiness censoring cancels** (Corollary, separable half). If the selection
is separable, `Sᵢⱼ = aᵢ bⱼ` (censoring acting at the origin/destination level), then
`log S ∈ 𝒩`, its interaction vanishes, and the recovered cost is asymptotically unbiased on
the identifiable part: `center ĉ = center c⋆`. -/
theorem bias_cancels_separable [NeZero N]
    (cstar logS D chat : Fin N → Fin N → ℝ) (ε : ℝ) (hD : Separable D)
    (hS : Separable logS)
    (hchat : ∀ i j, chat i j = cstar i j - ε * logS i j + D i j) :
    center chat = center cstar := by
  rw [bias_decomposition cstar logS D chat ε hD hchat]
  have h0 : center logS = fun _ _ => (0 : ℝ) := by
    obtain ⟨f, g, h⟩ := hS
    have : logS = fun i j => f i + g j := by funext i j; exact h i j
    rw [this]; exact center_separable f g
  rw [h0]; funext i j; simp

/-- **Polling aliasing attenuates** (Corollary, non-separable half). Under the linearised
duration-dependent capture `log Sᵢⱼ = (η τ)·c⋆ᵢⱼ + (separable)` (log-capture `≈ η t`, travel
time `t = τ c⋆`), the recovered interaction is the truth **multiplicatively attenuated** by
`1 − ε η τ`: `center ĉ = (1 − ε η τ) · center c⋆`. The selection is correlated with the very
estimand, so unlike separable censoring it does not cancel — it shrinks the cost–distance
relationship. -/
theorem bias_attenuation [NeZero N]
    (cstar logS D chat E : Fin N → Fin N → ℝ) (ε η τ : ℝ) (hD : Separable D)
    (hE : Separable E)
    (hS : ∀ i j, logS i j = (η * τ) * cstar i j + E i j)
    (hchat : ∀ i j, chat i j = cstar i j - ε * logS i j + D i j) :
    center chat = fun i j => (1 - ε * η * τ) * center cstar i j := by
  rw [bias_decomposition cstar logS D chat ε hD hchat]
  have hSfun : logS = fun i j => (η * τ) * cstar i j + E i j := by funext i j; exact hS i j
  have hcl : center logS = fun i j => (η * τ) * center cstar i j := by
    rw [hSfun, center_add_separable _ E hE]; exact center_smul (η * τ) cstar
  rw [hcl]; funext i j; ring

/-- The attenuation factor is **strictly below one** whenever `0 < ε η τ`: duration-dependent
polling provably contracts the identifiable cost, never leaving it unmoved. -/
theorem attenuation_factor_lt_one {ε η τ : ℝ} (h : 0 < ε * η * τ) :
    (1 - ε * η * τ) < 1 := by linarith

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms center_separable
#print axioms center_add_separable
#print axioms center_idem
#print axioms center_unique
#print axioms bias_decomposition
#print axioms bias_cancels_separable
#print axioms bias_attenuation
#print axioms attenuation_factor_lt_one

end OD
