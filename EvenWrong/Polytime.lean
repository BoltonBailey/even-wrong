module

public import Mathlib

/-!
# Bitstring encodings and polynomial-time computability

Mathlib recently unbundled the alphabet from `Computability.Encoding` and deprecated
`FinEncoding`. Here we experiment with a different design for the common case: a typeclass
`BitstringEncoding` for types with a canonical encoding as bitstrings (`List Bool`).

Making the encoding a *class* lets complexity-theoretic statements be written succinctly,
e.g. "integer factorization is in P" is literally `IsPolytime Nat.primeFactorsList`.

## Main definitions

* `BitstringEncoding α` — a `class` packaging `encode : α → List Bool` with a left-inverse
  `decode : List Bool → Option α`.
* Instances for `ℕ` (binary), `Bool`, `α × β`, `List α`, subtypes (hence `ℕ+`), `ℤ` and `ℚ`.
* `IsPolytime f` — there is a polynomial-time Turing machine carrying the encoding of `a`
  to the encoding of `f a`.

## Conjectures ("challenges")

From [Wikipedia's list of unsolved problems in computer science](https://en.wikipedia.org/wiki/List_of_unsolved_problems_in_computer_science):

* `isPolytime_primeFactorsList` — integer factorization is in P (believed false).
* `isPolytime_discreteLog` — the discrete logarithm is in P (believed false).
* `isPolytime_sqrtSumLE` — square-root-sum is in P (open).
* `isPolytime_satDecision` — SAT is in P, i.e. P = NP (believed false).
* `isPolytime_graphIsoDecision` — graph isomorphism is in P (open).
* `isPolytime_svpDecision` — the shortest-vector problem for lattices is in P
  (believed false).
* `ParityGame.isPolytime_decision` — parity games are solvable in P (open).

And, for contrast, some classical problems that *turned out* to be in P — these statements
are known to be true, so unlike the conjectures above they are honest (if very hard)
formalization challenges:

* `isPolytime_primeDecision` — primality testing is in P (AKS, 2002).
* `isPolytime_lpDecision` — linear-programming feasibility is in P (Khachiyan, 1979).
* `isPolytime_twoSatDecision` — 2-SAT is in P (linear time, Aspvall–Plass–Tarjan 1979).
* `isPolytime_matchingDecision` — maximum matching is in P (Edmonds, 1965).
-/

@[expose] public section

/-- A canonical encoding of a type as bitstrings (`List Bool`).

This is a class version of Mathlib's (bundled) `Computability.Encoding`, specialized to the
alphabet `Bool`. -/
class BitstringEncoding (α : Type*) where
  /-- The encoding function. -/
  encode : α → List Bool
  /-- The decoding function; `none` on bitstrings that encode nothing. -/
  decode : List Bool → Option α
  /-- Decoding is a left inverse of encoding. -/
  decode_encode : ∀ x, decode (encode x) = some x

attribute [simp] BitstringEncoding.decode_encode

namespace BitstringEncoding

variable {α β : Type*}

theorem encode_injective [BitstringEncoding α] :
    Function.Injective (encode : α → List Bool) := fun _ _ h =>
  Option.some_injective _ (by rw [← decode_encode, ← decode_encode, h])

/-- The bundled `Computability.Encoding` corresponding to a `BitstringEncoding`. -/
def toEncoding (α : Type*) [BitstringEncoding α] : Computability.Encoding α where
  Γ := Bool
  encode := encode
  decode := decode
  decode_encode := decode_encode

/-- Transport a `BitstringEncoding` along an injection `f` with partial inverse `g`. -/
@[reducible]
def ofLeftInverse [BitstringEncoding β] (f : α → β) (g : β → Option α)
    (h : ∀ x, g (f x) = some x) : BitstringEncoding α where
  encode a := encode (f a)
  decode l := (decode l).bind g
  decode_encode a := by simp [h]

/-! ## Ground instances -/

/-- `ℕ` is encoded by its (little-endian) binary representation, as in
`Computability.encodeNat`. -/
instance : BitstringEncoding ℕ where
  encode := Computability.encodeNat
  decode l := some (Computability.decodeNat l)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- `Bool` is encoded as a singleton bitstring. -/
instance : BitstringEncoding Bool where
  encode b := [b]
  decode l := match l with
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-! ## Self-delimiting blocks

To concatenate encodings (for pairs and lists) we need each piece to announce its own end.
`delimit` writes each payload bit `b` as `true :: b :: ·` and terminates with `false`;
`undelimit` parses one such block off the front of the input. -/

/-- Make a bitstring self-delimiting: each payload bit `b` becomes the two bits
`[true, b]`, and the block is terminated by `false`. -/
def delimit : List Bool → List Bool
  | [] => [false]
  | b :: l => true :: b :: delimit l

/-- Parse one self-delimiting block from the front of the input, returning the payload
and the remaining input. -/
def undelimit : List Bool → Option (List Bool × List Bool)
  | false :: rest => some ([], rest)
  | true :: b :: input => (undelimit input).map fun p => (b :: p.1, p.2)
  | _ => none

@[simp]
theorem undelimit_delimit (l rest : List Bool) :
    undelimit (delimit l ++ rest) = some (l, rest) := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, undelimit, ih]

@[simp]
theorem delimit_length (l : List Bool) : (delimit l).length = 2 * l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [delimit, ih]; ring

/-- Parse a sequence of self-delimiting blocks. `fuel` bounds the number of blocks; since
every block is nonempty, `input.length` is always enough fuel. -/
def undelimitBlocks : ℕ → List Bool → Option (List (List Bool))
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, input => do
    let (block, rest) ← undelimit input
    let blocks ← undelimitBlocks fuel rest
    return block :: blocks

theorem undelimitBlocks_flatten_delimit (l : List (List Bool)) :
    ∀ fuel, l.length ≤ fuel → undelimitBlocks fuel ((l.map delimit).flatten) = some l := by
  induction l with
  | nil => intro fuel _; cases fuel <;> rfl
  | cons b t ih =>
    intro fuel hfuel
    rw [List.length_cons] at hfuel
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨hd, tl, hcons⟩ : ∃ hd tl, delimit b ++ (t.map delimit).flatten = hd :: tl := by
      cases b <;> exact ⟨_, _, rfl⟩
    simp only [List.map_cons, List.flatten_cons, hcons, undelimitBlocks]
    rw [← hcons, undelimit_delimit]
    simp [ih fuel (by omega)]

theorem length_le_length_flatten_delimit (l : List (List Bool)) :
    l.length ≤ ((l.map delimit).flatten).length := by
  induction l with
  | nil => simp
  | cons b t ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
      delimit_length]
    omega

/-- Decode every block in a list of bitstrings, failing if any block fails to decode.

(This is `List.mapM decode` in the `Option` monad, written out by hand so that it works
for `α` in any universe.) -/
def decodeAll [BitstringEncoding α] : List (List Bool) → Option (List α)
  | [] => some []
  | b :: t =>
    match decode b, decodeAll t with
    | some a, some l => some (a :: l)
    | _, _ => none

@[simp]
theorem decodeAll_map_encode [BitstringEncoding α] (l : List α) :
    decodeAll (l.map encode) = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [decodeAll, ih]

/-! ## Derived instances -/

/-- A pair is encoded as a self-delimiting block for the first component followed by the
encoding of the second. -/
instance [BitstringEncoding α] [BitstringEncoding β] : BitstringEncoding (α × β) where
  encode p := delimit (encode p.1) ++ encode p.2
  decode input :=
    match undelimit input with
    | none => none
    | some (block, rest) =>
      match decode block, decode rest with
      | some a, some b => some (a, b)
      | _, _ => none
  decode_encode p := by simp

/-- A list is encoded as the concatenation of self-delimiting blocks for its elements. -/
instance [BitstringEncoding α] : BitstringEncoding (List α) where
  encode l := ((l.map encode).map delimit).flatten
  decode input :=
    match undelimitBlocks input.length input with
    | none => none
    | some blocks => decodeAll blocks
  decode_encode l := by
    rw [undelimitBlocks_flatten_delimit (l.map encode) _
      (by simpa using length_le_length_flatten_delimit (l.map encode))]
    exact decodeAll_map_encode l

/-- A subtype inherits the encoding of the ambient type; decoding additionally checks the
defining predicate. This yields encodings for `ℕ+` and friends for free. -/
instance {p : α → Prop} [BitstringEncoding α] [DecidablePred p] :
    BitstringEncoding (Subtype p) where
  encode x := encode x.val
  decode input := (decode input).bind fun a => if h : p a then some ⟨a, h⟩ else none
  decode_encode x := by simp [x.property]

/-- `ℕ+` is encoded as the subtype `{n : ℕ // 0 < n}` it is defined to be. -/
instance : BitstringEncoding ℕ+ :=
  inferInstanceAs (BitstringEncoding {n : ℕ // 0 < n})

/-- `ℤ` is encoded via the pair `(n.toNat, (-n).toNat)` (one component is always `0`). -/
instance : BitstringEncoding ℤ :=
  ofLeftInverse (fun n : ℤ => (n.toNat, (-n).toNat))
    (fun p => some ((p.1 : ℤ) - (p.2 : ℤ))) (fun n => congrArg some (by omega))

/-- `ℚ` is encoded as its (reduced) numerator-denominator pair. -/
instance : BitstringEncoding ℚ :=
  ofLeftInverse (fun q : ℚ => (q.num, q.den))
    (fun p => some ((p.1 : ℚ) / (p.2 : ℚ))) (fun q => by simp [Rat.num_div_den])

end BitstringEncoding

/-! ## Polynomial-time computability -/

/-- A function between bitstring-encodable types is **polynomial-time computable** when some
polynomial-time Turing machine (in the sense of Mathlib's `Turing.TM2ComputableInPolyTime`,
over the alphabet `Bool`) carries the encoding of `a` to the encoding of `f a`.

(Mathlib's definition is restricted to `Type 0`, so this is too.) -/
def IsPolytime {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime
    (BitstringEncoding.encode (α := α)) (BitstringEncoding.encode (α := β)) f)

/-- Sanity check: the identity function is polynomial-time computable. -/
theorem isPolytime_id {α : Type} [BitstringEncoding α] : IsPolytime (id : α → α) :=
  ⟨Turing.idComputableInPolyTime BitstringEncoding.encode⟩

/-! ## Conjectures

The challenges below are stated as theorems with `sorry` proofs, following the `EvenWrong`
convention. The first two are believed **false** (their truth would break RSA and
Diffie–Hellman respectively); the third is a genuinely open problem. -/

/-- **Integer factorization is in P.**

`Nat.primeFactorsList` maps a natural number to its sorted list of prime factors, so this
says there is a polynomial-time algorithm producing the full factorization. -/
theorem isPolytime_primeFactorsList : IsPolytime Nat.primeFactorsList := by
  sorry

/-- The discrete logarithm: the least `x < p` with `g ^ x ≡ h [MOD p]`, or `0` if none
exists. -/
def discreteLog (p g h : ℕ) : ℕ :=
  if hx : ∃ x, x < p ∧ g ^ x % p = h % p then Nat.find hx else 0

/-- **The discrete logarithm is in P.** -/
theorem isPolytime_discreteLog :
    IsPolytime fun x : ℕ × ℕ × ℕ => discreteLog x.1 x.2.1 x.2.2 := by
  sorry

open Classical in
/-- The square-root-sum comparison: given lists `a b` of naturals, decides whether
`∑ i ∈ a, √i ≤ ∑ j ∈ b, √j`. -/
noncomputable def sqrtSumLE (a b : List ℕ) : Bool :=
  decide ((a.map fun n => Real.sqrt n).sum ≤ (b.map fun n => Real.sqrt n).sum)

/-- **Square-root-sum is in P.**

Comparing sums of square roots is a famous problem (Garey–Graham–Johnson 1976) not even
known to lie in NP; the difficulty is bounding the precision needed to separate the two
sums. -/
theorem isPolytime_sqrtSumLE :
    IsPolytime fun x : List ℕ × List ℕ => sqrtSumLE x.1 x.2 := by
  sorry

/-! ### Boolean satisfiability (P versus NP) -/

/-- A literal is a nonzero integer, DIMACS style: `(n : ℤ) + 1` stands for the variable
`n` and `-(n + 1)` for its negation (the literal `0` is unsatisfiable by convention). -/
def LiteralHolds (assignment : ℕ → Bool) (lit : ℤ) : Prop :=
  if 0 < lit then assignment (lit.toNat - 1) = true
  else if lit < 0 then assignment ((-lit).toNat - 1) = false
  else False

/-- A CNF formula, given as a list of clauses of literals, is satisfiable when some
assignment makes at least one literal of every clause hold. -/
def CNFSatisfiable (cnf : List (List ℤ)) : Prop :=
  ∃ assignment : ℕ → Bool, ∀ clause ∈ cnf, ∃ lit ∈ clause, LiteralHolds assignment lit

open Classical in
/-- The Boolean-satisfiability decision function. -/
noncomputable def satDecision (cnf : List (List ℤ)) : Bool :=
  decide (CNFSatisfiable cnf)

/-- **SAT is in P.**

Since SAT is NP-complete (Cook–Levin), this is equivalent to **P = NP**, the central open
problem of computer science — widely believed false. -/
theorem isPolytime_satDecision : IsPolytime satDecision := by
  sorry

/-! ### Graph isomorphism -/

/-- Two undirected graphs, each given by a finite list of edges over the vertex set `ℕ`,
are isomorphic when some permutation of the vertices identifies their edge sets. (Only
membership in the edge list matters, and both graphs have cofinitely many isolated
vertices, so this agrees with isomorphism of the finite graphs they describe.) -/
def EdgeListIso (G H : List (ℕ × ℕ)) : Prop :=
  ∃ π : Equiv.Perm ℕ, ∀ a b : ℕ,
    ((a, b) ∈ G ∨ (b, a) ∈ G) ↔ ((π a, π b) ∈ H ∨ (π b, π a) ∈ H)

open Classical in
/-- The graph-isomorphism decision function. -/
noncomputable def graphIsoDecision (x : List (ℕ × ℕ) × List (ℕ × ℕ)) : Bool :=
  decide (EdgeListIso x.1 x.2)

/-- **Graph isomorphism is in P.**

A genuinely open problem: graph isomorphism is in NP ∩ co-AM, not known to be
NP-complete nor in P. Babai (2016) gives a quasipolynomial-time algorithm. -/
theorem isPolytime_graphIsoDecision : IsPolytime graphIsoDecision := by
  sorry

/-! ### Shortest vector of a lattice -/

/-- Pointwise sum of integer vectors, zero-padding the shorter one. -/
def addVec : List ℤ → List ℤ → List ℤ
  | [], w => w
  | v, [] => v
  | x :: v, y :: w => (x + y) :: addVec v w

/-- The integer combination `∑ i, c i • B i` of the basis vectors `B` with coefficients
`c`. -/
def latticeCombo (c : List ℤ) (B : List (List ℤ)) : List ℤ :=
  (List.zipWith (fun a v => v.map (a * ·)) c B).foldr addVec []

/-- The squared Euclidean norm of an integer vector. -/
def sqNorm (v : List ℤ) : ℤ :=
  (v.map fun x => x * x).sum

/-- The lattice generated by the rows of `B` contains a nonzero vector of squared norm at
most `k`. -/
def ShortVectorLE (B : List (List ℤ)) (k : ℕ) : Prop :=
  ∃ c : List ℤ, (∃ x ∈ latticeCombo c B, x ≠ 0) ∧ sqNorm (latticeCombo c B) ≤ k

open Classical in
/-- The shortest-vector decision function. -/
noncomputable def svpDecision (x : List (List ℤ) × ℕ) : Bool :=
  decide (ShortVectorLE x.1 x.2)

/-- **The shortest-vector problem is in P.**

Believed false: exact SVP is NP-hard under randomized reductions (Ajtai), and the
presumed hardness of its approximate versions underpins lattice-based (post-quantum)
cryptography. -/
theorem isPolytime_svpDecision : IsPolytime svpDecision := by
  sorry

/-! ### Parity games -/

namespace ParityGame

/-- The step relation of a parity game with edge list `E`: follow an edge, or stay put at
a vertex with no outgoing edge (so that plays never get stuck; a dead end thus behaves
like a self-loop rather than a loss for the player to move). -/
def Step (E : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  (u, v) ∈ E ∨ ((∀ w, (u, w) ∉ E) ∧ v = u)

/-- The priority `d` (looked up in the association list `pr`, defaulting to `0`) is seen
infinitely often along the play. -/
def InfinitelyOften (pr : List (ℕ × ℕ)) (play : ℕ → ℕ) (d : ℕ) : Prop :=
  ∀ n, ∃ m, n ≤ m ∧ (pr.lookup (play m)).getD 0 = d

/-- Player Even wins a play when the greatest priority seen infinitely often is even. -/
def EvenWinsPlay (pr : List (ℕ × ℕ)) (play : ℕ → ℕ) : Prop :=
  ∃ d, Even d ∧ InfinitelyOften pr play d ∧ ∀ d', d < d' → ¬InfinitelyOften pr play d'

/-- Player Even has a winning strategy in the parity game with edge list `E`, Even-owned
vertices `even`, priorities `pr`, starting at `start`: a legal-move strategy (a function
of the history of vertices visited so far) such that every play following it satisfies
the parity winning condition. -/
def EvenWins (E : List (ℕ × ℕ)) (even : List ℕ) (pr : List (ℕ × ℕ)) (start : ℕ) : Prop :=
  ∃ σ : List ℕ → ℕ,
    (∀ h : List ℕ, ∀ u, h.getLast? = some u → Step E u (σ h)) ∧
    ∀ play : ℕ → ℕ, play 0 = start →
      (∀ i, Step E (play i) (play (i + 1))) →
      (∀ i, play i ∈ even → play (i + 1) = σ (List.ofFn fun j : Fin (i + 1) => play j)) →
      EvenWinsPlay pr play

open Classical in
/-- The parity-game decision function: does player Even win the game
`(edges, Even's vertices, priorities)` from the given start vertex? -/
noncomputable def decision (x : List (ℕ × ℕ) × List ℕ × List (ℕ × ℕ) × ℕ) : Bool :=
  decide (EvenWins x.1 x.2.1 x.2.2.1 x.2.2.2)

/-- **Parity games are solvable in P.**

Open: deciding the winner of a parity game is in NP ∩ co-NP (even UP ∩ co-UP), and
Calude–Jain–Khoussainov–Li–Stephan (2017) gave a quasipolynomial-time algorithm, but no
polynomial-time algorithm is known. Equivalent to the model checking problem for the
modal μ-calculus. -/
theorem isPolytime_decision : IsPolytime decision := by
  sorry

end ParityGame

/-! ## Problems that turned out to be in P

For contrast with the open (or believed-false) conjectures above, here are classical
problems whose membership in P was once unclear but is now a *theorem*. These challenges
are honest: a `NotWrong` proof "only" requires formalizing the corresponding algorithm
and its runtime analysis. -/

/-- The primality decision function. -/
def primeDecision (n : ℕ) : Bool :=
  decide n.Prime

/-- **Primality testing is in P.**

True: this is "PRIMES is in P", proved by Agrawal–Kayal–Saxena (2002). Before AKS,
primality was a canonical candidate for a problem in NP ∩ co-NP but not P. -/
theorem isPolytime_primeDecision : IsPolytime primeDecision := by
  sorry

/-- The dot product of two rational vectors (implicitly zero-padding the shorter, since
`zipWith` truncates to the shorter list). -/
def dotQ (v w : List ℚ) : ℚ :=
  (List.zipWith (· * ·) v w).sum

/-- A system of linear constraints, each given as a coefficient row `c.1` and bound
`c.2`, is feasible when some rational vector `x` satisfies `c.1 · x ≤ c.2` for every
constraint. -/
def LPFeasible (constraints : List (List ℚ × ℚ)) : Prop :=
  ∃ x : List ℚ, ∀ c ∈ constraints, dotQ c.1 x ≤ c.2

open Classical in
/-- The linear-programming feasibility decision function. -/
noncomputable def lpDecision (constraints : List (List ℚ × ℚ)) : Bool :=
  decide (LPFeasible constraints)

/-- **Linear-programming feasibility is in P.**

True: Khachiyan's ellipsoid method (1979) decides feasibility of rational linear
inequality systems in polynomial time — resolving a question left open by the exponential
worst case of the simplex method. (Whether LP admits a *strongly* polynomial algorithm,
Smale's 9th problem, remains open, but is not expressible as an `IsPolytime` statement.) -/
theorem isPolytime_lpDecision : IsPolytime lpDecision := by
  sorry

open Classical in
/-- The 2-SAT decision function: a 2-CNF formula is a list of two-literal clauses, with
literals as in `LiteralHolds`. -/
noncomputable def twoSatDecision (cnf : List (ℤ × ℤ)) : Bool :=
  decide (∃ assignment : ℕ → Bool,
    ∀ c ∈ cnf, LiteralHolds assignment c.1 ∨ LiteralHolds assignment c.2)

/-- **2-SAT is in P.**

True: solvable even in linear time (Aspvall–Plass–Tarjan 1979, via strongly connected
components of the implication graph) — in sharp contrast to 3-SAT, which is NP-complete. -/
theorem isPolytime_twoSatDecision : IsPolytime twoSatDecision := by
  sorry

/-- The undirected graph given by the edge list `G` contains a matching with `k` edges:
`k` edges of `G` (up to orientation) with pairwise distinct endpoints. (`Nodup` on the
concatenated endpoint list also rules out self-loops.) -/
def HasMatching (G : List (ℕ × ℕ)) (k : ℕ) : Prop :=
  ∃ M : List (ℕ × ℕ), M.length = k ∧ (∀ e ∈ M, e ∈ G ∨ (e.2, e.1) ∈ G) ∧
    (M.map Prod.fst ++ M.map Prod.snd).Nodup

open Classical in
/-- The maximum-matching decision function: does `G` have a matching of size `k`? -/
noncomputable def matchingDecision (x : List (ℕ × ℕ) × ℕ) : Bool :=
  decide (HasMatching x.1 x.2)

/-- **Maximum matching is in P.**

True: Edmonds' blossom algorithm (1965). "Paths, trees, and flowers" is the paper that
proposed polynomial time as the definition of tractability in the first place. -/
theorem isPolytime_matchingDecision : IsPolytime matchingDecision := by
  sorry
