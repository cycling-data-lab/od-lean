# od-lean — Lean 4 formalisation of the OD identifiability bounds

Machine-checked (Lean 4 + Mathlib) formalisation of the two **estimator-free** identifiability
results of *gbfs-od-reconstruction* (Fossé–Pallares):

- **Bound 1** — the persistence bottleneck: *identifier rotation switches off the only
  channel that can resolve the OD interior* (`OdLean/Basic.lean`).
- **Bound 2** — the structure of observation bias: *the cost is identifiable only modulo
  additive station effects, and the bias is the non-separable part of the log-selection, so
  station-emptiness censoring cancels while `60`-second polling does not* (`OdLean/Bias.lean`).

Both are formalised **with zero `sorry`**, depending only on the three standard Lean axioms.

## Bound 1 — the `q⁻¹` information limit (`OdLean/Basic.lean`)

| Lean name | Paper statement |
|---|---|
| `OD.info_pos_iff` | Identifiability dichotomy: Fisher information `> 0` ⟺ `q > 0`; at `q = 0` the channel is off |
| `OD.cr_bound_q_inv` | The Cramér–Rao floor equals `(1/I₁)·q⁻¹` — the **`q⁻¹` law** |
| `OD.cr_bound_antitone` | The floor grows as persistence shrinks |
| `OD.cr_bound_gt` | The floor exceeds any threshold for small enough `q` — **divergence** as `q → 0` |
| `OD.var_ge_q_inv` | End-to-end: under Cramér–Rao, `Var ≥ (1/I₁)·q⁻¹` |

Architecture (mirroring [`sbf-lean`](../sbf-lean)): the **statistical inputs** are taken as
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

Architecture (mirroring [`sbf-lean`](../sbf-lean)'s `bessel`/`starProjection` split): the
**statistical inputs** — consistency of the empirical coupling and the Gibbs/Sinkhorn form —
enter only as the separable calibration/normaliser term `D` in `bias_decomposition`, exactly
as the paper states them. The **deterministic content** — the gauge algebra, the projection
being genuinely orthogonal (`center_unique`), and the separable / non-separable dichotomy
that decides *which censoring hurts* — is proved from first principles in pure finite real
algebra. No optimal-transport or measure theory is invoked: the bound's content is the
linear algebra of the interaction subspace.

## Sorry-free certificate

```text
-- Bound 1
'OD.info_pos_iff'             depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_q_inv'           depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_antitone'        depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_gt'              depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.var_ge_q_inv'             depends on axioms: [propext, Classical.choice, Quot.sound]
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

- **Bound 3** (estimator collection-horizon rate `δ⁻⁴` free-floating / `δ⁻²·K²` dock). A
  genuine sample-complexity rate for entropic optimal transport (Genevay,
  Mena–Niles-Weed) — analytic, beyond current Mathlib. This is the analogue of
  `sbf-lean`'s pending Theorem 2 (concentration) / Theorem 3 (Berry–Esseen).
- The *regularity conditions* feeding `cramer_rao_variance` — the unit score covariance
  `cov[T,S] = 1` (differentiation under the integral) and the Fisher information realised as
  the score variance `Var[S] = q·I₁` — are taken as hypotheses. They are the standard
  Cramér–Rao regularity assumptions; deriving them from the GBFS likelihood is a modelling
  step, not a gap in the deductive chain.

## Sibling

- [`sbf-lean`](../sbf-lean) — the same finite-algebra-core formalisation style applied to
  the structural-bounds-framework universal spectral lower bound (Theorem 1).
