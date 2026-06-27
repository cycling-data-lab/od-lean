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
    print("[Bound 1]  q^{-1} law, antitonicity, divergence ............ OK")


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


def main() -> None:
    print(f"od-lean symbolic cross-check (SymPy {sp.__version__}, N={N})")
    print("-" * 60)
    check_bound1()
    check_bound2_projection()
    check_bound2_bias()
    print("-" * 60)
    print("ALL CROSS-CHECKS PASSED — SymPy agrees with the Lean theorems.")


if __name__ == "__main__":
    main()
