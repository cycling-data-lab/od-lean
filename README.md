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
`hcr`.

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
```

Only the three standard Lean axioms — **no `sorryAx`**.

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

## Sibling

- [`sbf-lean`](../sbf-lean) — the same finite-algebra-core formalisation style applied to
  the structural-bounds-framework universal spectral lower bound (Theorem 1).
