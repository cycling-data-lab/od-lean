# od-lean — Lean 4 formalisation of the OD identifiability bounds

Machine-checked (Lean 4 + Mathlib) formalisation of the theoretical content of
[**`gbfs-od-reconstruction`**](https://github.com/cycling-data-lab/gbfs-od-reconstruction) (Fossé–Pallares, *Standard
compliance bounds origin–destination identifiability in GBFS bike-sharing feeds*) — the
companion proof artifact to that manuscript, living alongside it in `cycling-data-lab`:

- **Bound 1** — the persistence bottleneck: *identifier rotation switches off the only
  channel that can resolve the OD interior* (`OdLean/Basic.lean`).
- **Bound 2** — the structure of observation bias: *the cost is identifiable only modulo
  additive station effects, and the bias is the non-separable part of the log-selection, so
  station-emptiness censoring cancels while `60`-second polling does not* (`OdLean/Bias.lean`).
- **Bound 3** — the collection-horizon law: *how long a feed must be polled to reconstruct
  the OD to a target accuracy, per system type (`δ⁻⁴` free-floating vs `δ⁻²` dock), and why
  the horizon carries the same `q⁻¹`* (`OdLean/Bound3.lean`).

All are formalised **with zero `sorry`**, depending only on the three standard Lean axioms.

## What is verified, and where it sits in the manuscript

The formalisation certifies the **deductive content** of each result — the algebra and the
deterministic consequences — taking the genuinely analytic / statistical inputs as explicit
hypotheses (as the paper does). The map to the manuscript (`paper.tex` / `paper_si.tex` in
[`gbfs-od-reconstruction`](https://github.com/cycling-data-lab/gbfs-od-reconstruction)):

| Manuscript result | Lean file | Key theorem(s) |
|---|---|---|
| Prop. (`prop:crb`) `q⁻¹` Cramér–Rao | `OdLean/Basic.lean` | `var_ge_q_inv`, `cr_bound_gt` |
| Cramér–Rao step itself (SI B) | `OdLean/CramerRao.lean` | `cramer_rao_variance`, `var_ge_q_inv_of_score` |
| Score / Fisher derivation (`prop:crb` proof, SI B) | `OdLean/Fisher.lean` | `score_unique`, `fisher_eq_proj_var`, `fisher_pos_iff` |
| Rem. misspecification sandwich (`rem:sandwich`) | `OdLean/Basic.lean` | `sandwich_q_inv`, `sandwich_diverges` |
| Lem. gauge freedom (`lem:gauge`) | `OdLean/Bias.lean` | `center_separable`, `center_add_separable`, `center_unique` |
| Prop. bias = log-selection (`prop:bias`) | `OdLean/Bias.lean` | `bias_decomposition` |
| Cor. which censoring hurts (`cor:aliasing`) | `OdLean/Bias.lean` | `bias_cancels_separable`, `bias_attenuation` |
| Thm. sampling horizon (`thm:horizon`) | `OdLean/Bound3.lean` | `sample_complexity_quartic`, `horizon_min`, `Tstar_q_inv`, `regime_crossover` |

What is **not** re-proved (isolated as hypotheses, exactly as cited in the paper): the
entropic-OT sample-complexity rate (Genevay / Mena–Niles-Weed), the Cramér–Rao regularity
conditions, and the Gibbs/Sinkhorn structural model. See *Not formalised here* below.

## Bound 1 — the `q⁻¹` information limit (`OdLean/Basic.lean`)

| Lean name | Paper statement |
|---|---|
| `OD.info_pos_iff` | Identifiability dichotomy: Fisher information `> 0` ⟺ `q > 0`; at `q = 0` the channel is off |
| `OD.cr_bound_q_inv` | The Cramér–Rao floor equals `(1/I₁)·q⁻¹` — the **`q⁻¹` law** |
| `OD.cr_bound_antitone` | The floor grows as persistence shrinks |
| `OD.cr_bound_gt` | The floor exceeds any threshold for small enough `q` — **divergence** as `q → 0` |
| `OD.var_ge_q_inv` | End-to-end: under Cramér–Rao, `Var ≥ (1/I₁)·q⁻¹` |
| `OD.sandwich_q_inv` | **Misspecification-robust**: the Huber–White sandwich `A⁻¹BA⁻¹/n_eff` also factors as `(const)·q⁻¹` — the `q⁻¹` survives a wrong model, only the constant differs |
| `OD.sandwich_scales`, `OD.sandwich_antitone_q`, `OD.sandwich_diverges` | the misspecified variance scales/diverges in `q` exactly as the well-specified floor |

Architecture (mirroring `sbf-lean`): the **statistical inputs** are taken as
hypotheses / definitions, exactly as the paper states them — the tracked micro-channel's
Fisher information is **linear in the identifier-persistence rate**, `info q = q · I₁` with
`I₁ > 0`, and the **Cramér–Rao** inequality `Var ≥ 1/info q`. The **deterministic
consequences** (the `q⁻¹` divergence and the `q = 0` non-identifiability) are then pure
finite real algebra. No probability theory is invoked: the bound's content is the algebra
of the information limit, with the measure-theoretic Cramér–Rao step isolated as the input
`hcr` — itself **discharged** in `OdLean/CramerRao.lean` (below).

## The Cramér–Rao step, discharged (`OdLean/CramerRao.lean`)

Bound 1 takes the Cramér–Rao inequality `Var ≥ 1/info` as the hypothesis `hcr` — its only
measure-theoretic step. That step is **derived from first principles**, so the `q⁻¹` law
rests on genuinely statistical inputs rather than an assumed inequality. The content of
Cramér–Rao is one application of **Cauchy–Schwarz** to estimator and score, plus the algebra
of the resulting quadratic, given in two layers (abstract core + honest instantiation):

| Lean name | Statement |
|---|---|
| `OD.cramer_rao_inner` | **Abstract core**: in any real inner-product space, `⟪T,S⟫ = 1`, `⟪S,S⟫ = I > 0` ⟹ `⟪T,T⟫ ≥ 1/I` (pure Cauchy–Schwarz) |
| `OD.covariance_sq_le_variance_mul_variance` | **Covariance Cauchy–Schwarz** for `ProbabilityTheory` random variables, via the nonnegative-quadratic / discriminant argument |
| `OD.cramer_rao_variance` | **Measure-theoretic Cramér–Rao**: `cov[T,S] = 1`, `Var[S] = I > 0` ⟹ `Var[T] ≥ 1/I` |
| `OD.var_ge_q_inv_of_score` | **Capstone**: with `Var[S] = q·I₁`, `Var[T] ≥ (1/I₁)·q⁻¹` — Bound 1's `q⁻¹` law with `hcr` *proved* |

Built on Mathlib's genuine `ProbabilityTheory.covariance` / `.variance`: the only remaining
inputs are `cov[T,S] = 1` (regularity/unbiasedness) and `Var[S] = q·I₁` (Fisher information
as score variance) — precisely the standard Cramér–Rao regularity conditions, now genuine
measure-theoretic quantities rather than an assumed bound.

## Bound 2 — cost identifiability and observation bias (`OdLean/Bias.lean`)

The bias structure is **finite linear algebra** on the `N × N` pair (design) space,
modelled as `Fin N → Fin N → ℝ`. The one structural object is the **two-way centring** —
the entropic-OT *interaction* operator and the genuine orthogonal projection `Π_{𝒩^⊥}` off
the **separable subspace** `𝒩 = {(i,j) ↦ fᵢ + gⱼ}` of additive station effects
(`dim 𝒩 = 2N−1`):

```text
(center M)ᵢⱼ = Mᵢⱼ − M̄ᵢ· − M̄·ⱼ + M̄··
```

| Lean name | Paper statement |
|---|---|
| `OD.center_separable` | **Gauge kernel** (SI Lemma A.1): centring annihilates every station effect, `𝒩 ⊆ ker(center)` |
| `OD.center_add_separable` | **Gauge freedom** (Lemma A.1 / A.2): a cost gauge *or* a Sinkhorn rebalancing potential leaves the interaction unchanged — calibration injects no interaction bias |
| `OD.center_idem` | Centring is **idempotent**: a genuine projection onto the identifiable class |
| `OD.center_orthogonal_separable` | The interaction is Frobenius-**orthogonal** to every station effect |
| `OD.center_unique` | `center M` is *the* **unique** representative of `M + 𝒩` orthogonal to `𝒩` — the precise sense of *identifiable only modulo station effects* |
| `OD.bias_decomposition` | **Bias = non-separable log-selection** (SI Prop.): `Π⊥ĉ = Π⊥c⋆ − ε·Π⊥ log S` |
| `OD.bias_cancels_separable` | **Station-emptiness cancels**: separable `S = aᵢbⱼ` is asymptotically unbiased on the interaction |
| `OD.bias_attenuation` | **Polling aliasing attenuates**: duration-dependent `S` scales the cost by `1 − εητ < 1` |

Architecture (mirroring `sbf-lean`'s `bessel`/`starProjection` split): the
**statistical inputs** — consistency of the empirical coupling and the Gibbs/Sinkhorn form —
enter only as the separable calibration/normaliser term `D` in `bias_decomposition`, exactly
as the paper states them. The **deterministic content** — the gauge algebra, the projection
being genuinely orthogonal (`center_unique`), and the separable / non-separable dichotomy
that decides *which censoring hurts* — is proved from first principles in pure finite real
algebra. No optimal-transport or measure theory is invoked: the bound's content is the
linear algebra of the interaction subspace.

## Score → projection → Fisher: the Bound 1 ↔ Bound 2 bridge (`OdLean/Fisher.lean`)

The SI B derivation linking the two bounds: for the calibrated Gibbs model the efficient
score is `∂_θ log p_θ = −ε⁻¹·Π_⊥^{(p)} φ`, so `I₁ = ε⁻²·Var_{p}(Π_⊥^{(p)} φ)` — the **same**
interaction projection as Bound 2's gauge, now in the `p_θ`-weighted inner product. This
*derives* the inputs `OdLean/Basic.lean` (Bound 1) took as hypotheses. The measure-theoretic
facts (the differentiated margin constraints; the score's separable potential part) are
isolated as hypotheses; the rest is the algebra of the weighted projection.

| Lean name | Content |
|---|---|
| `OD.frobP` | the `L²(p)`-weighted inner product `⟨A,B⟩_p = Σ p_{ij} A_{ij} B_{ij}` |
| `OD.frobP_orthogonal_separable` | margin constraints ⟹ the score is `p`-orthogonal to every station effect |
| `OD.proj_unique` | the `p`-orthogonal representative mod `𝒩` is **unique** (`p > 0`) |
| `OD.score_is_projection`, `OD.score_unique` | hence `S = −ε⁻¹·Π_⊥^{(p)} φ`, the unique efficient score |
| `OD.score_mean_zero` | `E_p[S] = 0`, so `I₁ = ⟨S,S⟩_p` is genuinely the score variance |
| `OD.fisher_eq_proj_var` | `I₁ = ε⁻²·⟨Π_⊥φ, Π_⊥φ⟩_p` (the paper's `I₁ = ε⁻² Var_p(Π_⊥φ)`) |
| `OD.fisher_pos_iff` | `I₁ > 0 ⟺ S ≠ 0` — projected-feature non-degeneracy |
| `OD.fisher_pos_gives_info_pos` | **bridge**: feeds the *derived* `I₁ > 0` into Bound 1's `info_pos_iff` |

This is the `p`-weighted companion of Bound 2's unweighted centring `Π_{𝒩^⊥}`: it closes the
loop from the GBFS likelihood to the inputs of Bound 1.

## Bound 3 — the collection-horizon law (`OdLean/Bound3.lean`)

The single genuinely analytic input — the **entropic-OT sample-complexity** `O(ε⁻¹n⁻¹ᐟ²)` of
Genevay et al. / Mena–Niles-Weed (well beyond current Mathlib) — is **isolated as a
hypothesis**: it appears only as the variance term of the plug-in error budget
`err(ε) = ε + B·ε⁻¹·n⁻¹ᐟ²`. Everything we contribute is then deterministic real analysis.

| Lean name | Paper content |
|---|---|
| `OD.entropic_balance` (+`_eq`) | **bias–variance balance**: `ε + V/ε ≥ 2√V`, attained at `ε = √V` |
| `OD.sample_complexity_quartic` | **free-floating `δ⁻⁴`**: reaching accuracy `δ` needs `n ≥ 16B²·δ⁻⁴` |
| `OD.sample_complexity_quadratic` | **dock `δ⁻²`**: the finite-`K` rate needs `n ≥ C²·δ⁻²` |
| `OD.horizon_min` | the **minimal horizon** `T⋆ = Φ/(R q)` is exactly the feasibility threshold |
| `OD.Tstar_q_inv`, `OD.Tstar_antitone_q` | `T⋆ ∝ q⁻¹`: the horizon inherits Bound 1's persistence law |
| `OD.regime_crossover` | docks beat free-floating iff `K²δ² < C₄` — crossover `K⋆ ∝ δ⁻¹` |
| `OD.Tstar_free_scaling` | **capstone**: `T⋆ = 16B²·(R δ⁴)⁻¹·q⁻¹` — the `q⁻¹·δ⁻⁴` collection cost |

The `δ⁻⁴` exponent emerges *only* from balancing the isolated OT variance against the
entropic bias (AM–GM); the `q⁻¹` is the same estimator-free factor as Bound 1. No
optimal-transport theory is invoked — only the algebra of the horizon.

## Sorry-free certificate

```text
-- Bound 1
'OD.info_pos_iff'             depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_q_inv'           depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_antitone'        depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_gt'              depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.var_ge_q_inv'             depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sandwich_q_inv'           depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sandwich_scales'          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sandwich_antitone_q'      depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sandwich_diverges'        depends on axioms: [propext, Classical.choice, Quot.sound]
-- Score → projection → Fisher (Bound 1 ↔ Bound 2 bridge)
'OD.frobP_orthogonal_separable'  depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.proj_unique'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.score_unique'                depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.fisher_eq_proj_var'          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.fisher_pos_iff'              depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.fisher_pos_gives_info_pos'   depends on axioms: [propext, Classical.choice, Quot.sound]
-- Bound 2
'OD.center_separable'         depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.center_add_separable'     depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.center_idem'              depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.center_unique'            depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.bias_decomposition'       depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.bias_cancels_separable'   depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.bias_attenuation'         depends on axioms: [propext, Classical.choice, Quot.sound]
-- Cramér–Rao step
'OD.cramer_rao_inner'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.covariance_sq_le_variance_mul_variance'    depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cramer_rao_variance'                       depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.var_ge_q_inv_of_score'                     depends on axioms: [propext, Classical.choice, Quot.sound]
-- Bound 3
'OD.entropic_balance'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sample_complexity_quartic'                 depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.sample_complexity_quadratic'               depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.horizon_min'                               depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.Tstar_q_inv'                               depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.Tstar_antitone_q'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.regime_crossover'                          depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.Tstar_free_scaling'                        depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the three standard Lean axioms — **no `sorryAx`**.

## Independent cross-check (SymPy)

`verification/cross_check.py` re-derives the same closed-form algebra in a computer-algebra
system, independently of Lean. The scalar information laws (Bound 1) are checked fully
symbolically; the centring/projection and bias-decomposition identities (Bound 2) are
checked on an `N × N` matrix of *symbols*, so each assertion is a genuine polynomial
identity, not a numeric coincidence. A surviving error would have to corrupt both a
Mathlib-checked proof and a SymPy run in the same direction.

```bash
python3 verification/cross_check.py   # deps: sympy
```

## Build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get   # precompiled Mathlib oleans (first time only)
lake build
```

Toolchain: Lean `v4.31.0` (see `lean-toolchain`), Mathlib pinned in `lake-manifest.json`
(same pin as `sbf-lean`, so the olean cache is shared).

> Note: keep this project on the nvme/btrfs disk (`/home`). The build's `.lake`
> (~several GB of Mathlib oleans) must NOT live under `/tmp` or `$HOME`-tmpfs paths,
> which are RAM-backed with a ~6 GB quota on this machine.

## Not formalised here

- The **entropic-OT sample-complexity rate** itself — the `O(ε⁻¹n⁻¹ᐟ²)` plug-in error of
  Genevay et al. / Mena–Niles-Weed that feeds `Bound3`'s error budget — is an isolated
  hypothesis, not proved here: it is a deep analytic result beyond current Mathlib (the
  analogue of `sbf-lean`'s pending Theorem 2/3). `Bound3` proves everything *downstream* of
  it: the balancing, the `δ⁻⁴`/`δ⁻²` exponents, and the `q⁻¹` horizon law.
- The *regularity conditions* feeding `cramer_rao_variance` — the unit score covariance
  `cov[T,S] = 1` (differentiation under the integral) and the Fisher information realised as
  the score variance `Var[S] = q·I₁` — are taken as hypotheses. They are the standard
  Cramér–Rao regularity assumptions; deriving them from the GBFS likelihood is a modelling
  step, not a gap in the deductive chain.

## Siblings

- [`gbfs-od-reconstruction`](https://github.com/cycling-data-lab/gbfs-od-reconstruction) — **the manuscript this verifies**
  (paper + experiments d01–d14); this repo is its formal-proof companion.
- [`structural-bounds-framework`](https://github.com/cycling-data-lab/structural-bounds-framework) — the SBF manuscript,
  whose Theorem 1 is formalised in `sbf-lean`.
- [`sbf-lean`](https://github.com/cycling-data-lab/sbf-lean) — the same finite-algebra-core
  formalisation style applied to the structural-bounds-framework universal spectral lower
  bound (Theorem 1); shares the Mathlib olean cache (identical pin).
