import Mathlib
import OdLean.Basic
import OdLean.Bias

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Score, projection, Fisher information (the Bound 1 ↔ Bound 2 bridge)

Lean 4 / Mathlib formalisation of the SI B derivation that *links the two bounds*: for the
calibrated Gibbs model `p_θ(i,j) = α_i(θ)β_j(θ)e^{−c_{ij}(θ)/ε}` with `c(θ) = Σ_k θ_k φ^{(k)}`
and `θ`-independent margins, the efficient score is

  `∂_θ log p_θ = −ε⁻¹ · Π_⊥^{(p)} φ`,

so the per-trip Fisher information is `I₁ = ε⁻² · Var_{p_θ}(Π_⊥^{(p)} φ)` — the **same**
interaction projection as Bound 2's identifiability gauge, only in the `p_θ`-weighted inner
product. This *derives* the inputs that `OdLean.Basic` (Bound 1) took as hypotheses: the
Fisher information `I₁ > 0` is exactly the projected features being active, and `info q = q·I₁`
is Fisher additivity over the `n_eff ∝ q` linked trips.

## Architecture (zero `sorry`)

The genuinely measure-theoretic facts are isolated as hypotheses, exactly as in the paper:

* the **differentiated margin constraints** `∂_θ(Σ_j p_θ) = 0`, `∂_θ(Σ_i p_θ) = 0` appear as
  the score's zero weighted row/column sums (`hrow`, `hcol`);
* the score's **additive (potential) part** is separable, `S = sep − ε⁻¹ φ` (`hS`).

Everything else is the linear algebra of the `p`-weighted projection `Π_⊥^{(p)}`:

| Lean name | Content |
|---|---|
| `OD.frobP` | the `L²(p)`-weighted inner product `⟨A,B⟩_p = Σ p_{ij} A_{ij} B_{ij}` |
| `OD.frobP_orthogonal_separable` | margin constraints ⟹ score is `p`-orthogonal to every station effect |
| `OD.proj_unique` | the `p`-orthogonal representative of a class mod `𝒩` is **unique** (needs `p > 0`) |
| `OD.score_is_projection` | the score satisfies the two defining properties of `Π_⊥^{(p)}(−ε⁻¹φ)` |
| `OD.score_unique` | hence `S = −ε⁻¹ Π_⊥^{(p)} φ`, the unique efficient score |
| `OD.score_mean_zero` | `E_p[S] = 0` (orthogonality to the constants ⊂ `𝒩`) |
| `OD.fisher_eq_proj_var` | `I₁ = ⟨S,S⟩_p = ε⁻²·⟨Π_⊥φ, Π_⊥φ⟩_p` |
| `OD.fisher_pos_iff` | `I₁ > 0 ⟺ S ≠ 0` — projected-feature non-degeneracy |
| `OD.fisher_pos_gives_info_pos` | **bridge**: feeds the derived `I₁ > 0` into Bound 1's `info_pos_iff` |

This is the `p`-weighted companion of `OdLean.Bias`'s unweighted centring `Π_{𝒩^⊥}`, and it
closes the loop from the GBFS likelihood to the inputs of `OdLean.Basic`.
-/

open Finset

namespace OD

variable {N : ℕ}

/-- The `L²(p)`-weighted (Frobenius) inner product on the pair space — the `p_θ`-weighted
interaction inner product of SI B. -/
noncomputable def frobP (p A B : Fin N → Fin N → ℝ) : ℝ := ∑ i, ∑ j, p i j * A i j * B i j

/-- `frobP` is subtractive in its middle (first vector) argument. -/
theorem frobP_sub_mid (p A A' B : Fin N → Fin N → ℝ) :
    frobP p (fun i j => A i j - A' i j) B = frobP p A B - frobP p A' B := by
  simp only [frobP, mul_sub, sub_mul, Finset.sum_sub_distrib]

/-- **Margin constraints ⟹ score orthogonality.** A score `S` whose `p`-weighted row sums and
column sums all vanish (the differentiated margin constraints `Σ_j ∂p = 0`, `Σ_i ∂p = 0`) is
`p`-orthogonal to every separable station-effect array. The `p`-weighted analogue of
`Bias.center_orthogonal_separable`. -/
theorem frobP_orthogonal_separable
    (p S : Fin N → Fin N → ℝ)
    (hrow : ∀ i, ∑ j, p i j * S i j = 0)
    (hcol : ∀ j, ∑ i, p i j * S i j = 0)
    {D : Fin N → Fin N → ℝ} (hD : Separable D) :
    frobP p S D = 0 := by
  obtain ⟨f, g, hfg⟩ := hD
  unfold frobP
  calc ∑ i, ∑ j, p i j * S i j * D i j
      = ∑ i, ∑ j, (p i j * S i j * f i + p i j * S i j * g j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hfg]; ring
    _ = ∑ i, ((∑ j, p i j * S i j) * f i + ∑ j, p i j * S i j * g j) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = ∑ i, ∑ j, p i j * S i j * g j := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hrow i, zero_mul, zero_add]
    _ = ∑ j, ∑ i, p i j * S i j * g j := Finset.sum_comm
    _ = ∑ j, (∑ i, p i j * S i j) * g j := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [← Finset.sum_mul]
    _ = 0 := by refine Finset.sum_eq_zero (fun j _ => ?_); rw [hcol j, zero_mul]

/-- **Uniqueness of the `p`-orthogonal projection.** With strictly positive weights `p`, any
two representatives `M'`, `M''` of the same class `M + 𝒩` that are both `p`-orthogonal to `𝒩`
coincide. (`p`-weighted analogue of `Bias.center_unique`; `p > 0` supplies definiteness.) -/
theorem proj_unique
    (p : Fin N → Fin N → ℝ) (hp : ∀ i j, 0 < p i j)
    (M M' M'' : Fin N → Fin N → ℝ)
    (hsep' : Separable (fun i j => M i j - M' i j))
    (hsep'' : Separable (fun i j => M i j - M'' i j))
    (horth' : ∀ D, Separable D → frobP p M' D = 0)
    (horth'' : ∀ D, Separable D → frobP p M'' D = 0) :
    M' = M'' := by
  obtain ⟨f1, g1, h1⟩ := hsep'
  obtain ⟨f2, g2, h2⟩ := hsep''
  have hEsep : Separable (fun i j => M' i j - M'' i j) :=
    ⟨fun i => f2 i - f1 i, fun j => g2 j - g1 j, by
      intro i j; have a1 := h1 i j; have a2 := h2 i j; simp only at a1 a2 ⊢; linarith⟩
  have hEorth : frobP p (fun i j => M' i j - M'' i j) (fun i j => M' i j - M'' i j) = 0 := by
    rw [frobP_sub_mid, horth' _ hEsep, horth'' _ hEsep, sub_zero]
  have hsum0 : ∑ i, ∑ j, p i j * (M' i j - M'' i j) * (M' i j - M'' i j) = 0 := hEorth
  funext i j
  have hnn : ∀ i ∈ (univ : Finset (Fin N)),
      0 ≤ ∑ j, p i j * (M' i j - M'' i j) * (M' i j - M'' i j) :=
    fun i _ => Finset.sum_nonneg fun j _ => by
      nlinarith [hp i j, mul_self_nonneg (M' i j - M'' i j)]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i (mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => by nlinarith [hp i j, mul_self_nonneg (M' i j - M'' i j)])).mp hi j (mem_univ j)
  have hEEij : (M' i j - M'' i j) * (M' i j - M'' i j) = 0 := by
    rcases mul_eq_zero.mp (by rw [mul_assoc] at hj; exact hj) with h0 | h0
    · exact absurd h0 (hp i j).ne'
    · exact h0
  exact sub_eq_zero.mp (mul_self_eq_zero.mp hEEij)

/-- **The score is the projection `Π_⊥^{(p)}(−ε⁻¹φ)`.** The efficient score `S = sep − ε⁻¹φ`
satisfies the two defining properties of the `p`-orthogonal projection of `−ε⁻¹φ` off `𝒩`:
its complement `(−ε⁻¹φ) − S` is separable, and it is `p`-orthogonal to every station
effect. -/
theorem score_is_projection
    (p S φ sep : Fin N → Fin N → ℝ) (ε : ℝ) (hsep : Separable sep)
    (hS : ∀ i j, S i j = sep i j - ε⁻¹ * φ i j)
    (hrow : ∀ i, ∑ j, p i j * S i j = 0)
    (hcol : ∀ j, ∑ i, p i j * S i j = 0) :
    Separable (fun i j => -(ε⁻¹ * φ i j) - S i j) ∧
      (∀ D, Separable D → frobP p S D = 0) := by
  refine ⟨?_, fun D hD => frobP_orthogonal_separable p S hrow hcol hD⟩
  obtain ⟨f, g, hfg⟩ := hsep
  exact ⟨fun i => -f i, fun j => -g j, by
    intro i j
    show -(ε⁻¹ * φ i j) - S i j = -f i + -g j
    rw [hS i j]; have hfgij := hfg i j; linarith⟩

/-- **The efficient score is unique**: any `P'` that is also a `p`-orthogonal representative of
`−ε⁻¹φ` mod `𝒩` equals the score `S`. Combined with `score_is_projection`, this is
`S = −ε⁻¹ Π_⊥^{(p)} φ`. -/
theorem score_unique
    (p S φ sep : Fin N → Fin N → ℝ) (ε : ℝ) (hp : ∀ i j, 0 < p i j) (hsep : Separable sep)
    (hS : ∀ i j, S i j = sep i j - ε⁻¹ * φ i j)
    (hrow : ∀ i, ∑ j, p i j * S i j = 0)
    (hcol : ∀ j, ∑ i, p i j * S i j = 0)
    (P' : Fin N → Fin N → ℝ)
    (hP'sep : Separable (fun i j => -(ε⁻¹ * φ i j) - P' i j))
    (hP'orth : ∀ D, Separable D → frobP p P' D = 0) :
    P' = S := by
  obtain ⟨hScompl, hSorth⟩ := score_is_projection p S φ sep ε hsep hS hrow hcol
  exact proj_unique p hp (fun i j => -(ε⁻¹ * φ i j)) P' S hP'sep hScompl hP'orth hSorth

/-- Per-trip Fisher information of the calibrated Gibbs model: `I₁ = ⟨S, S⟩_p`. -/
noncomputable def fisherInfo (p S : Fin N → Fin N → ℝ) : ℝ := frobP p S S

/-- **The score has zero mean** under `p`: `E_p[S] = Σ p_{ij} S_{ij} = 0`, since the constants
lie in `𝒩` and the score is `p`-orthogonal to `𝒩`. Hence the Fisher information `⟨S,S⟩_p` is
genuinely the *variance* of the score. -/
theorem score_mean_zero (p S : Fin N → Fin N → ℝ)
    (horth : ∀ D, Separable D → frobP p S D = 0) :
    ∑ i, ∑ j, p i j * S i j = 0 := by
  have h := horth (fun _ _ => 1) ⟨fun _ => 1, fun _ => 0, by intro i j; norm_num⟩
  unfold frobP at h
  simpa using h

/-- **Fisher information `=` projected-feature variance.** With the projected feature
`Φ_⊥ = Π_⊥^{(p)} φ = −ε·S`, `I₁ = ⟨S,S⟩_p = ε⁻²·⟨Φ_⊥, Φ_⊥⟩_p` — the paper's
`I₁ = ε⁻² Var_{p}(Π_⊥φ)`. -/
theorem fisher_eq_proj_var (p S Φ : Fin N → Fin N → ℝ) (ε : ℝ) (hε : ε ≠ 0)
    (hrel : ∀ i j, Φ i j = -ε * S i j) :
    fisherInfo p S = (ε⁻¹) ^ 2 * frobP p Φ Φ := by
  unfold fisherInfo frobP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hrel]
  have hcancel : (ε⁻¹) ^ 2 * ε ^ 2 = 1 := by
    rw [inv_pow]; exact inv_mul_cancel₀ (pow_ne_zero 2 hε)
  have h1 : (ε⁻¹) ^ 2 * (p i j * (-ε * S i j) * (-ε * S i j))
          = ((ε⁻¹) ^ 2 * ε ^ 2) * (p i j * S i j * S i j) := by ring
  rw [h1, hcancel, one_mul]

/-- **Non-degeneracy.** With positive weights, `I₁ > 0` iff the score is not identically zero,
i.e. iff the projected features `Π_⊥^{(p)} φ` are active. This is exactly the `I₁ > 0`
hypothesis of Bound 1, here characterised. -/
theorem fisher_pos_iff (p S : Fin N → Fin N → ℝ) (hp : ∀ i j, 0 < p i j) :
    0 < fisherInfo p S ↔ ∃ i j, S i j ≠ 0 := by
  unfold fisherInfo frobP
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    have : ∑ i, ∑ j, p i j * S i j * S i j = 0 := by
      refine Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => ?_))
      rw [hcon i j]; ring
    linarith
  · rintro ⟨i0, j0, hne⟩
    have hterm : 0 < p i0 j0 * S i0 j0 * S i0 j0 := by
      rw [mul_assoc]; exact mul_pos (hp i0 j0) (mul_self_pos.mpr hne)
    have hrownn : ∀ i ∈ (univ : Finset (Fin N)),
        0 ≤ ∑ j, p i j * S i j * S i j :=
      fun i _ => Finset.sum_nonneg fun j _ => by nlinarith [hp i j, mul_self_nonneg (S i j)]
    calc (0 : ℝ)
        < ∑ j, p i0 j * S i0 j * S i0 j :=
          Finset.sum_pos' (fun j _ => by nlinarith [hp i0 j, mul_self_nonneg (S i0 j)])
            ⟨j0, mem_univ j0, hterm⟩
      _ ≤ ∑ i, ∑ j, p i j * S i j * S i j := Finset.single_le_sum hrownn (mem_univ i0)

/-- **Bridge to Bound 1.** The non-degeneracy assumed throughout `OdLean.Basic` — `I₁ > 0` in
`info_pos_iff`, `var_ge_q_inv` — is *derived* here from the projected features being active.
Feeding the derived `I₁ = fisherInfo p S` into Bound 1 closes the loop from the GBFS
likelihood to the `q⁻¹` information limit. -/
theorem fisher_pos_gives_info_pos (p S : Fin N → Fin N → ℝ) (hp : ∀ i j, 0 < p i j)
    (hS : ∃ i j, S i j ≠ 0) (q : ℝ) (hq : 0 < q) :
    0 < info (fisherInfo p S) q :=
  (info_pos_iff (fisherInfo p S) ((fisher_pos_iff p S hp).mpr hS) q).mpr hq

-- Axiom audit: these must NOT list `sorryAx` (i.e. genuinely sorry-free).
#print axioms frobP_orthogonal_separable
#print axioms proj_unique
#print axioms score_is_projection
#print axioms score_unique
#print axioms score_mean_zero
#print axioms fisher_eq_proj_var
#print axioms fisher_pos_iff
#print axioms fisher_pos_gives_info_pos

end OD
