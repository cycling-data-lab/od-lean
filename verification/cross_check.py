#!/usr/bin/env python3
"""
Symbolic cross-verification of the od-lean theorems (Bounds 1 & 2).

This script re-derives, *independently of Lean/Mathlib*, the closed-form algebra
that `OdLean/Basic.lean` and `OdLean/Bias.lean` prove. It is a cheap, reviewer-
readable second witness: a bug would have to corrupt both a Mathlib-checked proof
and a SymPy computer-algebra run in the same direction to survive.

Method:
  * the scalar information laws (Bound 1) are checked fully symbolically;
  * the two-way-centring / projection identities (Bound 2) are checked on an
    N×N matrix whose entries are *symbols* — so each `assert` is a genuine
    polynomial identity in 2N²+… indeterminates, not a numeric coincidence.

Run:  python3 verification/cross_check.py
Deps: sympy.
"""

import sympy as sp

N = 4  # matrix size for Bound 2; entries are symbolic, so identities are exact


# ======================================================================
# Bound 1 — the q^{-1} information limit  (OdLean/Basic.lean)
# ======================================================================
def check_bound1() -> None:
    q, I1 = sp.symbols("q I_1", positive=True)
    info = q * I1  # OD.info: Fisher information linear in persistence q

    # cr_bound_q_inv : 1/info = (1/I1) * q^{-1}
    assert sp.simplify(1 / info - (1 / I1) * q**-1) == 0

    # cr_bound_antitone : the floor 1/info strictly decreases in q
    #   (=> grows as persistence shrinks); derivative is < 0 for q,I1 > 0.
    d = sp.simplify(sp.diff(1 / info, q))
    assert d == -1 / (I1 * q**2)
    assert d.subs({q: 1, I1: 1}) < 0

    # cr_bound_gt / divergence : 1/info -> +oo as q -> 0+
    assert sp.limit(1 / info, q, 0, "+") == sp.oo

    # var_ge_q_inv : under hcr (1/info <= Var), the bound reads (1/I1) q^{-1} <= Var
    #   — same expression as cr_bound_q_inv, already checked above.

    # Misspecification sandwich: sandwichVar = A^{-1} B A^{-1} / n_eff, n_eff = R q T.
    #   sandwich_q_inv : = (A^{-1} B A^{-1} / (R T)) * q^{-1}  (q^{-1} survives misspec.)
    A, Bc, R, Tt = sp.symbols("A B_c R T", positive=True)
    sandwich = (A**-1 * Bc * A**-1) / (R * q * Tt)
    assert sp.simplify(sandwich - (A**-1 * Bc * A**-1 / (R * Tt)) * q**-1) == 0
    #   sandwich_scales : sandwich(q) = sandwich(q=1) * q^{-1}  (model-independent shape)
    sandwich_1 = (A**-1 * Bc * A**-1) / (R * Tt)
    assert sp.simplify(sandwich - sandwich_1 * q**-1) == 0
    print("[Bound 1]  q^{-1} law, antitonicity, divergence, sandwich .. OK")


# ======================================================================
# Bound 2 — two-way centring / projection algebra  (OdLean/Bias.lean)
# ======================================================================
def center(A: sp.Matrix) -> sp.Matrix:
    """Π_{N^⊥}: (center A)_{ij} = A_{ij} - rowMean_i - colMean_j + grandMean."""
    n = A.rows
    row = [sum(A[i, j] for j in range(n)) / n for i in range(n)]
    col = [sum(A[i, j] for i in range(n)) / n for j in range(n)]
    grand = sum(A[i, j] for i in range(n) for j in range(n)) / n**2
    return sp.Matrix(n, n, lambda i, j: A[i, j] - row[i] - col[j] + grand)


def frob(A: sp.Matrix, B: sp.Matrix) -> sp.Expr:
    return sum(A[i, j] * B[i, j] for i in range(A.rows) for j in range(A.cols))


def sep(prefix_f: str, prefix_g: str) -> sp.Matrix:
    """A separable (additive station-effect) array  (i,j) -> f_i + g_j  in N."""
    f = [sp.Symbol(f"{prefix_f}_{i}") for i in range(N)]
    g = [sp.Symbol(f"{prefix_g}_{j}") for j in range(N)]
    return sp.Matrix(N, N, lambda i, j: f[i] + g[j])


def zero() -> sp.Matrix:
    return sp.zeros(N, N)


def is_zero(A: sp.Matrix) -> bool:
    return sp.simplify(A) == zero()


def check_bound2_projection() -> None:
    M = sp.Matrix(N, N, lambda i, j: sp.Symbol(f"M_{i}_{j}"))
    C = center(M)
    S = sep("f", "g")

    # center_separable : center(f_i + g_j) = 0      (gauge kernel, Lemma A.1)
    assert is_zero(center(S))

    # center_add_separable : center(M + sep) = center(M)   (gauge freedom / A.2)
    assert is_zero(center(M + S) - C)

    # center_idem : center(center M) = center M     (idempotence; genuine projection)
    assert is_zero(center(C) - C)

    # row/col sums of a centred array vanish
    assert all(sp.simplify(sum(C[i, j] for j in range(N))) == 0 for i in range(N))
    assert all(sp.simplify(sum(C[i, j] for i in range(N))) == 0 for j in range(N))

    # center_orthogonal_separable : <center M, sep>_Frobenius = 0
    assert sp.simplify(frob(C, S)) == 0

    # sub_center_separable : M - center M is separable
    #   (its own interaction vanishes: second cross-differences are 0)
    R = M - C
    assert all(
        sp.simplify(R[i, j] - R[i, 0] - R[0, j] + R[0, 0]) == 0
        for i in range(N)
        for j in range(N)
    )

    # center_unique (orthogonal-projection witness): center M is, simultaneously,
    #   (a) congruent to M mod N  [M - center M separable, just checked] and
    #   (b) orthogonal to all of N [<C, sep>=0 for the generic separable, checked].
    #   These two properties pin it down uniquely (the Lean proof of center_unique).
    print("[Bound 2]  centring kernel, gauge, idempotence, orthogonality OK")


def check_bound2_bias() -> None:
    eps, eta, tau = sp.symbols("epsilon eta tau")
    cstar = sp.Matrix(N, N, lambda i, j: sp.Symbol(f"c_{i}_{j}"))
    logS = sp.Matrix(N, N, lambda i, j: sp.Symbol(f"s_{i}_{j}"))
    D = sep("d", "e")  # separable calibration / normaliser term (Lemma A.2)

    # bias_decomposition : center(c* - eps*logS + D) = center c* - eps*center logS
    chat = sp.Matrix(N, N, lambda i, j: cstar[i, j] - eps * logS[i, j] + D[i, j])
    assert is_zero(center(chat) - (center(cstar) - eps * center(logS)))

    # bias_cancels_separable : separable selection => center chat = center c*
    logS_sep = sep("a", "b")
    chat_s = sp.Matrix(N, N, lambda i, j: cstar[i, j] - eps * logS_sep[i, j] + D[i, j])
    assert is_zero(center(chat_s) - center(cstar))

    # bias_attenuation : logS = (eta*tau) c* + E (separable)
    #                    => center chat = (1 - eps*eta*tau) center c*
    E = sep("u", "v")
    logS_alias = sp.Matrix(N, N, lambda i, j: (eta * tau) * cstar[i, j] + E[i, j])
    chat_a = sp.Matrix(N, N, lambda i, j: cstar[i, j] - eps * logS_alias[i, j] + D[i, j])
    assert is_zero(center(chat_a) - (1 - eps * eta * tau) * center(cstar))

    print("[Bound 2]  bias = non-separable log-selection; cancel/attenuate OK")


# ======================================================================
# Bound 3 — collection-horizon law  (OdLean/Bound3.lean)
# ======================================================================
def check_bound3() -> None:
    # entropic_balance / entropic_balance_eq : ε + V/ε ≥ 2√V, attained at ε = √V
    V, eps = sp.symbols("V epsilon", positive=True)
    err = eps + V / eps
    # stationary point and minimum value
    eps_star = sp.solve(sp.diff(err, eps), eps)
    eps_star = [s for s in eps_star if s.is_positive][0]
    assert sp.simplify(eps_star - sp.sqrt(V)) == 0
    assert sp.simplify(err.subs(eps, sp.sqrt(V)) - 2 * sp.sqrt(V)) == 0
    # global lower bound: err - 2√V = (√ε - √(V/ε))² ≥ 0
    assert sp.simplify((err - 2 * sp.sqrt(V)) - (sp.sqrt(eps) - sp.sqrt(V / eps)) ** 2) == 0

    # sample_complexity_quartic : achievable accuracy 2√(B/√n) = 2√B·n^{-1/4}
    #   reaching δ needs n ≥ 16 B² δ^{-4}
    B, delta, n = sp.symbols("B delta n", positive=True)
    acc = 2 * sp.sqrt(B / sp.sqrt(n))
    assert sp.simplify(acc - 2 * sp.sqrt(B) * n ** sp.Rational(-1, 4)) == 0
    n_req4 = sp.solve(sp.Eq(acc, delta), n)[0]            # n at which accuracy = δ
    assert sp.simplify(n_req4 - 16 * B**2 / delta**4) == 0

    # sample_complexity_quadratic : dock rate C·n^{-1/2}, reaching δ needs n ≥ C² δ^{-2}
    C = sp.Symbol("C", positive=True)
    n_req2 = sp.solve(sp.Eq(C / sp.sqrt(n), delta), n)[0]
    assert sp.simplify(n_req2 - C**2 / delta**2) == 0

    # horizon: nEff = R q T ; Tstar = Φ / (R q) ; Tstar = (Φ/R)·q^{-1}
    R, q, T, Phi = sp.symbols("R q T Phi", positive=True)
    Tstar = Phi / (R * q)
    assert sp.simplify(Tstar - (Phi / R) * q**-1) == 0           # q^{-1} law
    assert sp.simplify(sp.solve(sp.Eq(Phi, R * q * T), T)[0] - Tstar) == 0  # feasibility
    # free-floating capstone: Tstar(16B²/δ⁴) = 16B²/(R δ⁴) · q^{-1}
    Tstar_free = (16 * B**2 / delta**4) / (R * q)
    assert sp.simplify(Tstar_free - (16 * B**2 / (R * delta**4)) * q**-1) == 0

    # regime crossover: K²/δ² < C₄/δ⁴  ⟺  K²δ² < C₄  ⟺ K < √C₄/δ
    C4, K = sp.symbols("C_4 K", positive=True)
    lhs = sp.simplify((K**2 / delta**2 < C4 / delta**4))
    # equivalent cross-multiplied form on the positive orthant
    assert sp.simplify((C4 / delta**4 - K**2 / delta**2) * delta**4 - (C4 - K**2 * delta**2)) == 0
    print("[Bound 3]  balance, δ⁻⁴/δ⁻² complexity, horizon q⁻¹, crossover OK")


def main() -> None:
    print(f"od-lean symbolic cross-check (SymPy {sp.__version__}, N={N})")
    print("-" * 60)
    check_bound1()
    check_bound2_projection()
    check_bound2_bias()
    check_bound3()
    print("-" * 60)
    print("ALL CROSS-CHECKS PASSED — SymPy agrees with the Lean theorems.")


if __name__ == "__main__":
    main()
