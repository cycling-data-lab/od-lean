# od-lean — Lean 4 formalisation of the OD identifiability bound

Machine-checked (Lean 4 + Mathlib) formalisation of **Bound 1** (the central,
estimator-free result) of *gbfs-od-reconstruction* (Fossé–Pallares) — *identifier rotation
switches off the only channel that can resolve the OD interior*.

## Result

`OdLean/Basic.lean` proves, **with zero `sorry`**:

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

### Sorry-free certificate

```text
'OD.info_pos_iff'      depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_q_inv'    depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.cr_bound_gt'       depends on axioms: [propext, Classical.choice, Quot.sound]
'OD.var_ge_q_inv'      depends on axioms: [propext, Classical.choice, Quot.sound]
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

- **Bound 2** (bias structure: the cost is identifiable only *modulo* additive station
  effects; station-emptiness censoring cancels, 60-second polling does not). This is a
  kernel/quotient statement on the design matrix — formalisable in the same finite
  linear-algebra style as `sbf-lean`'s projection lemmas, but needs the selection model
  set up; deferred.
- **Bound 3** (estimator collection-horizon rate `δ⁻⁴` free-floating / `δ⁻²·K²` dock). A
  genuine sample-complexity rate for entropic optimal transport (Genevay,
  Mena–Niles-Weed) — analytic, beyond current Mathlib. This is the analogue of
  `sbf-lean`'s pending Theorem 2 (concentration) / Theorem 3 (Berry–Esseen).

## Sibling

- [`sbf-lean`](../sbf-lean) — the same finite-algebra-core formalisation style applied to
  the structural-bounds-framework universal spectral lower bound (Theorem 1).
