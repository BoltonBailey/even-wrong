import EvenWrong.TournamentGame.Basic

/-!
# Uniqueness of the tournament-game equilibrium (challenge)

The uniqueness ("at most one MSNE") half of `TournamentGame.hasUniqueNashEquilibrium`,
following the argument of Will Sawin's MathOverflow answer
<https://mathoverflow.net/a/506379/113060> (CC-BY-SA 4.0,
<https://creativecommons.org/licenses/by-sa/4.0/>).

This is a *challenge* statement; a comparator-friendly solution lives in
`NotWrong.TournamentGame` (paired by `comparator/TournamentGame.json`).
-/

/--
**A tournament game has at most one mixed-strategy Nash equilibrium.**

This is the uniqueness ("at most one MSNE") half of `TournamentGame.hasUniqueNashEquilibrium`,
formalising the argument of <https://mathoverflow.net/questions/506372>: in any equilibrium each
player's strategy `x` (as a real probability vector) is *optimal*, i.e. satisfies `M x ≤ 0` for the
payoff matrix `M`; and a tournament matrix admits at most one such `x`, because `x - y` would lie
in the kernel of `M` augmented by the all-ones row, which is nonsingular (it is so already mod 2).

NOTE. The current `TournamentGame` structure only encodes the zero-sum condition (`symmetric`) and
the `±1`-off-diagonal condition (`payoff_ne`). It does *not* encode invariance under swapping the
two players, which is part of the definition of a tournament game and is what makes the payoff
matrix antisymmetric (and the diagonal zero). That missing property is supplied here as the
hypothesis `hswap`.
-/
theorem TournamentGame.subsingleton_mixedNashEquilibrium
    {A : Type} [Fintype A] [DecidableEq A] (G : TournamentGame A)
    (hswap : ∀ a b : A, G.payoff 0 ![a, b] = G.payoff 1 ![b, a])
    (p q : Fin 2 → PMF A)
    (hp : G.toUniformActionNormalFormGame.IsMixedNashEquilibrium p)
    (hq : G.toUniformActionNormalFormGame.IsMixedNashEquilibrium q) :
    p = q := by
  sorry
