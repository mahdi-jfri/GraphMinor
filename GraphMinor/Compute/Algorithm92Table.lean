module

public import GraphMinor.Compute.Specs9

/-!
# Graph Minors XIII, (9.2): the table of answers for small inputs (`Algorithm92Table.lean`)

Page 101 of Graph Minors XIII: "Since the size of $F$ is bounded (exept for divalent vertices) by a
function of $l, m$, and $p$, we can find an $(l, m)$-star or a model of $K_p$ in $H \cup F$ in time
$\le C\varepsilon(G)$." The compressed copy of `H ∪ F` has at most `B` vertices, with `B`
depending only on `h` and `k`. So there are only finitely many of them, and an answer for each one
can be stored in the program. This file sets up that table.

* `Key92 h B` is a finite type that holds the data of a compressed input that matters for the
  output: the number `N ≤ B` of vertices, the edges, and the wall. `ofKey92` reads the data back.
* `key92Of xK` is the key of an input `xK` whose graph has edge multiplicities at most `1`; then
  `ofKey92 (key92Of xK) = keyData xK` (`ofKey92_key92Of`).
* `table92 D` is an output that is correct for every input with the data of `D`, when such an input
  exists (`isAlg92Output_table92`). It is chosen with the axiom of choice from the fact that every
  input has a correct output (`exists_isAlg92Output`, from Graph Minors XIII, (9.2)).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable (h : ℕ)

/-- The data of an input that the output depends on: the number of vertices, the edge
multiplicities, the branch vertices and the inner vertices of the paths of the wall. -/
abbrev InputData : Type :=
  Σ N : ℕ, (Fin N → Fin N → ℕ) × (Fin (elemWallNumVerts h) → Fin N) ×
    (Fin (elemWallEdges h).length → List (Fin N))

variable {h}

/-- The data of an input. -/
def keyData {l m p k r : ℕ} (x : Alg92Input l m p h k r) : InputData h :=
  ⟨x.n, x.G.edgeMult, x.W.branchVert, x.W.internalVerts⟩

/-- The output condition of (9.2), read on the data of an input. -/
def IsDataOutput (l m p : ℕ) : InputData h → List ℕ → Prop
  | ⟨n, em, bv, iv⟩, out =>
    letI G : MultiDigraph n := ⟨em⟩
    letI W : WallOfHeight h G := ⟨bv, iv⟩
    (∃ (c : Fin n) (rays : Fin l → List (Fin n)),
      out = 0 :: c.1 :: encHPaths rays ∧
      (∀ i : Fin l, W.IsStarRay c (rays i)) ∧
      (∀ i j : Fin l, i ≠ j → ∀ v, v ∈ rays i → v ∈ rays j → v = c) ∧
      (∀ i j : Fin l, i ≠ j → ∀ u v,
        (rays i).getLast? = some u → (rays j).getLast? = some v → m ≤ W.brickDist u v)) ∨
    (∃ K : Fin p → Finset (Fin n),
      out = 1 :: encBitSetsUpTo K p ∧
      IsCliqueModel G.toSimpleGraph p K)

theorem isAlg92Output_iff_isDataOutput {l m p k r : ℕ} (x : Alg92Input l m p h k r)
    (out : List ℕ) : IsAlg92Output l m p x out ↔ IsDataOutput l m p (keyData x) out :=
  Iff.rfl

variable (h)

/-- The finite type of keys: inputs with at most `B` vertices and edge multiplicities `0` or `1`.
The inner vertices of a path of the wall are given by their number and the list itself. -/
abbrev Key92 (B : ℕ) : Type :=
  Σ N : Fin (B + 1), (Fin N → Fin N → Bool) × (Fin (elemWallNumVerts h) → Fin N) ×
    ((k : Fin (elemWallEdges h).length) → Σ len : Fin (N + 1), Fin len → Fin N)

variable {h}

/-- The data stored in a key. -/
def ofKey92 {B : ℕ} : Key92 h B → InputData h
  | ⟨N, adj, bv, iv⟩ =>
    ⟨N, fun i j => if adj i j then 1 else 0, bv, fun k => List.ofFn (iv k).2⟩

/-- The key of an input with at most `B` vertices, simple edges, and paths without repeated
vertices. -/
def key92Of {l m p k r : ℕ} (B : ℕ) (x : Alg92Input l m p h k r) (hN : x.n ≤ B)
    (hlen : ∀ k, (x.W.internalVerts k).length ≤ x.n) : Key92 h B :=
  ⟨⟨x.n, Nat.lt_succ_of_le hN⟩, fun i j => decide (0 < x.G.edgeMult i j), x.W.branchVert,
    fun k => ⟨⟨(x.W.internalVerts k).length, Nat.lt_succ_of_le (hlen k)⟩,
      fun t => (x.W.internalVerts k)[t.1]'t.2⟩⟩

theorem ofKey92_key92Of {l m p k r : ℕ} (B : ℕ) (x : Alg92Input l m p h k r) (hN : x.n ≤ B)
    (hlen : ∀ k, (x.W.internalVerts k).length ≤ x.n) (h01 : ∀ i j, x.G.edgeMult i j ≤ 1) :
    ofKey92 (key92Of B x hN hlen) = keyData x := by
  unfold ofKey92 key92Of keyData
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine Prod.ext ?_ (Prod.ext rfl ?_)
  · funext i j
    have := h01 i j
    simp only [decide_eq_true_eq]
    split_ifs with hp <;> omega
  · funext k
    exact List.ofFn_getElem

open Classical in
/-- The stored answer for a key: a correct output of an input with these data, if there is one. -/
noncomputable def table92 (l m p k r : ℕ) {B : ℕ} (D : Key92 h B) : List ℕ :=
  if hD : ∃ x : Alg92Input l m p h k r, keyData x = ofKey92 D then
    if hout : ∃ out, IsAlg92Output l m p hD.choose out then hout.choose else []
  else []

/-- **The stored answer is correct**, when every input has a correct output. -/
theorem isAlg92Output_table92 {l m p k r : ℕ}
    (hex : ∀ x : Alg92Input l m p h k r, ∃ out, IsAlg92Output l m p x out)
    {B : ℕ} (D : Key92 h B) (x : Alg92Input l m p h k r) (hx : keyData x = ofKey92 D) :
    IsAlg92Output l m p x (table92 l m p k r D) := by
  have hD : ∃ x : Alg92Input l m p h k r, keyData x = ofKey92 D := ⟨x, hx⟩
  have hout := hex hD.choose
  unfold table92
  rw [dite_eq_left_of_eq_true (eq_true hD), dite_eq_left_of_eq_true (eq_true hout)]
  have hc := hout.choose_spec
  rw [isAlg92Output_iff_isDataOutput] at hc ⊢
  have e : keyData hD.choose = keyData x := hD.choose_spec.trans hx.symm
  rw [← e]
  exact hc

end Alg92

end GraphMinor.Compute
