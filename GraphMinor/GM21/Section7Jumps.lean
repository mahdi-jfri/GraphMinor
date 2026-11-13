module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.PortraitDefs
public import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM21.LinkagePaths
import GraphMinor.GM21.Section2
public import GraphMinor.GM21.SeparationGluing

/-!
# Graph Minors XXI, proof of (7.3): paths that start a `Σ`-jump

The proof of (7.3) (page 31 of the preprint) says: "Every other component of $L \cap \Gamma$
either is a $\Sigma$-jump in $\Gamma'$, or has an end some vertex $v \in V(\Gamma) \setminus
bd(\Sigma)$ which is a terminal of $L$". A component whose two ends lie in $bd(\Sigma)$ may have
further vertices in $bd(\Sigma)$; then it is not itself a `Σ`-jump, but its first segment is.
This file proves that a path `P` with distinct ends `a, b` in a set `B` has a subpath from `a` to
the next vertex of `B` (`exists_subpath_to_next`), whose inner vertices avoid `B`.

The proof indexes the vertices of `P` as `v 0 = a, …, v m = b` (`exists_isIndexedPath_of_isPathGraph`)
and keeps the vertices `v 0, …, v k`, where `k ≥ 1` is least with `v k ∈ B`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-- In a loopless graph, the terminals are the vertices with at most one incident edge. -/
theorem terminals_eq_of_loopless {P : Hypergraph α β}
    (hloop : ∀ e ∈ P.edgeSet, (P.ends e).ncard = 2) :
    terminals P = {x | x ∈ P.vertexSet ∧ (incidentEdges P x).ncard ≤ 1} := by
  ext x
  simp only [terminals, IsTerminal, mem_ofPred_eq, vertexDegree_eq_ncard_incidentEdges hloop]

/-- The subhypergraph of `P` on the vertex set `W`: its edges are the edges of `P` with all ends
in `W`. -/
def inducedOn (P : Hypergraph α β) (W : Set α) (hW : W ⊆ P.vertexSet) : Hypergraph α β where
  vertexSet := W
  edgeSet := {e ∈ P.edgeSet | P.ends e ⊆ W}
  Inc e x := P.Inc e x ∧ e ∈ P.edgeSet ∧ P.ends e ⊆ W
  vertex_mem_of_inc _ _ h := h.2.2 h.1
  edge_mem_of_inc _ _ h := h.2
  vertexSet_finite := P.vertexSet_finite.subset hW
  edgeSet_finite := P.edgeSet_finite.subset fun _ h => h.1

theorem inducedOn_le (P : Hypergraph α β) (W : Set α) (hW : W ⊆ P.vertexSet) :
    inducedOn P W hW ≤ P where
  vertexSet_subset := hW
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext x
    simp only [ends, inducedOn, mem_ofPred_eq]
    exact ⟨fun h => ⟨h, he.1, he.2⟩, fun h => h.1⟩

/-- A path `P` whose terminals are two distinct vertices `a, b` of a set `B` has a subpath `Q`
from `a` to some `b' ∈ B` with `b' ≠ a`, and with no vertex in `B` other than `a` and `b'`. -/
theorem exists_subpath_to_next {P : Hypergraph α β} (hP : IsPathGraph P) {B : Set α} {a b : α}
    (hab : a ≠ b) (hterm : terminals P = {a, b}) (hbB : b ∈ B) :
    ∃ Q : Hypergraph α β, Q ≤ P ∧ IsPathGraph Q ∧ ∃ b' ∈ B, b' ≠ a ∧
      terminals Q = {a, b'} ∧ ∀ x ∈ Q.vertexSet, x ∈ B → x = a ∨ x = b' := by
  classical
  obtain ⟨hPg, _, hPconn, h2, hinjE, _, _⟩ := id hP
  have hterm' := hterm
  rw [terminals_eq_of_loopless h2] at hterm'
  have haP : a ∈ P.vertexSet := by
    have h : a ∈ ({a, b} : Set α) := Or.inl rfl
    rw [← hterm'] at h
    exact h.1
  have hbP : b ∈ P.vertexSet := by
    have h : b ∈ ({a, b} : Set α) := Or.inr rfl
    rw [← hterm'] at h
    exact h.1
  -- `P` has an edge, since it has two distinct vertices and is connected.
  have hE : P.edgeSet.Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty] at hE
    have hreach := hPconn a haP b hbP
    obtain ⟨w⟩ := hreach
    cases w with
    | nil => exact hab rfl
    | cons hadj _ =>
      obtain ⟨_, e, he, _⟩ := hadj
      have := P.edge_mem_of_inc he
      rw [hE] at this
      exact this
  obtain ⟨x₁, hx₁, x₂, hx₂, -, hpath, hdeg⟩ := exists_isIndexedPath_of_isPathGraph hP hE
  -- The ends of the indexed path are `a` and `b`.
  have hends : ({x₁, x₂} : Set α) = {a, b} := by
    rw [← hterm]
    rw [terminals_eq_of_loopless h2]
    ext y
    simp only [mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨hx₁, (hdeg y hx₁).2 (Or.inl rfl)⟩
      · exact ⟨hx₂, (hdeg y hx₂).2 (Or.inr rfl)⟩
    · rintro ⟨hy, hy1⟩
      exact (hdeg y hy).1 hy1
  have hpath_a : IsIndexedPath P a b := by
    have ha : a = x₁ ∨ a = x₂ := by
      have : a ∈ ({x₁, x₂} : Set α) := hends ▸ (Or.inl rfl : a ∈ ({a, b} : Set α))
      simpa using this
    have hb : b = x₁ ∨ b = x₂ := by
      have : b ∈ ({x₁, x₂} : Set α) := hends ▸ (Or.inr rfl : b ∈ ({a, b} : Set α))
      simpa using this
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact hpath
    · exact hpath.symm
    · exact absurd rfl hab
  obtain ⟨m, hm, vv, hv_inj, hv0, hvm, hV_eq, hadj⟩ := hpath_a
  -- The least index `k ≥ 1` with `vv k ∈ B`.
  have hex : ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ ∀ hk : k < m + 1, vv ⟨k, hk⟩ ∈ B :=
    ⟨m, hm, le_rfl, fun _ => hvm ▸ hbB⟩
  let k := Nat.find hex
  obtain ⟨hk1, hkm, hkB⟩ := Nat.find_spec hex
  have hk_min : ∀ j : ℕ, 1 ≤ j → j < k → ∀ hj : j < m + 1, vv ⟨j, hj⟩ ∉ B := by
    intro j hj1 hjk hj hjB
    exact Nat.find_min hex hjk ⟨hj1, by omega, fun hj' => hjB⟩
  let W : Set α := vv '' {i | i.1 ≤ k}
  have hW : W ⊆ P.vertexSet := by
    rintro _ ⟨i, -, rfl⟩
    rw [hV_eq]
    exact mem_range_self i
  let Q := inducedOn P W hW
  have hQle : Q ≤ P := inducedOn_le P W hW
  have hQ_ends : ∀ e ∈ Q.edgeSet, Q.ends e = P.ends e := fun e he =>
    (hQle.ends_eq e he).symm
  have hQg : Q.IsGraph := fun e he => by
    rw [hQ_ends e he]
    exact hPg e (hQle.edgeSet_subset he)
  have hQ2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2 := fun e he => by
    rw [hQ_ends e he]
    exact h2 e (hQle.edgeSet_subset he)
  have hQinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂ :=
    fun e₁ he₁ e₂ he₂ h => by
      rw [hQ_ends e₁ he₁, hQ_ends e₂ he₂] at h
      exact hinjE e₁ (hQle.edgeSet_subset he₁) e₂ (hQle.edgeSet_subset he₂) h
  -- Adjacency in `Q` between vertices of `W` is adjacency in `P`.
  have hadjQ : ∀ x ∈ W, ∀ y ∈ W, Q.skeleton.Adj x y ↔ P.skeleton.Adj x y := by
    intro x hx y hy
    constructor
    · rintro ⟨hxy, e, hex, hey⟩
      exact ⟨hxy, e, hex.1, hey.1⟩
    · rintro ⟨hxy, e, hex, hey⟩
      have heP := P.edge_mem_of_inc hex
      have hsub : P.ends e ⊆ W := by
        have hpair : ({x, y} : Set α) ⊆ P.ends e := by
          rintro z (rfl | rfl)
          · exact hex
          · exact hey
        have hfin : (P.ends e).Finite := Set.finite_of_ncard_pos (by rw [h2 e heP]; omega)
        have heq : ({x, y} : Set α) = P.ends e :=
          eq_of_subset_of_ncard_le hpair (by rw [h2 e heP, ncard_pair hxy]) hfin
        rw [← heq]
        rintro z (rfl | rfl)
        · exact hx
        · exact hy
      exact ⟨hxy, e, ⟨hex, heP, hsub⟩, ⟨hey, heP, hsub⟩⟩
  let w : Fin (k + 1) → α := fun i => vv ⟨i.1, by omega⟩
  have hw_inj : Injective w := by
    intro i j h
    have := hv_inj h
    exact Fin.ext (by simpa using congrArg Fin.val this)
  have hQ_V : Q.vertexSet = range w := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i.1, by simp only [mem_ofPred_eq] at hi; omega⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨⟨i.1, by omega⟩, by simp only [mem_ofPred_eq]; omega, rfl⟩
  have hw_mem : ∀ i : Fin (k + 1), w i ∈ W := fun i => by
    rw [← show Q.vertexSet = W from rfl, hQ_V]
    exact mem_range_self i
  have hQpath : IsIndexedPath Q a (vv ⟨k, by omega⟩) := by
    refine ⟨k, hk1, w, hw_inj, ?_, rfl, hQ_V, ?_⟩
    · rw [← hv0]
      rfl
    · intro i j
      rw [hadjQ _ (hw_mem i) _ (hw_mem j)]
      exact hadj ⟨i.1, by omega⟩ ⟨j.1, by omega⟩
  obtain ⟨hQP, hQdeg⟩ := isPathGraph_of_isIndexedPath hQg hQ2 hQinj hQpath
  have hb'_ne : vv ⟨k, by omega⟩ ≠ a := by
    rw [← hv0]
    intro h
    have := congrArg Fin.val (hv_inj h)
    simp only [Fin.val_zero] at this
    omega
  refine ⟨Q, hQle, hQP, vv ⟨k, by omega⟩, hkB _, hb'_ne, ?_, ?_⟩
  · rw [terminals_eq_of_loopless hQ2]
    ext x
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx1⟩
      exact (hQdeg x hx).1 hx1
    · intro hx
      have hxQ : x ∈ Q.vertexSet := by
        rcases hx with rfl | rfl
        · rw [hQ_V, ← hv0]
          exact ⟨0, rfl⟩
        · rw [hQ_V]
          exact ⟨⟨k, by omega⟩, rfl⟩
      exact ⟨hxQ, (hQdeg x hxQ).2 hx⟩
  · rintro x ⟨i, hi, rfl⟩ hxB
    simp only [mem_ofPred_eq] at hi
    by_cases hi0 : i.1 = 0
    · left
      rw [← hv0]
      exact congrArg vv (Fin.ext hi0)
    · right
      have hik : ¬ i.1 < k := fun hlt => hk_min i.1 (by omega) hlt i.2 hxB
      exact congrArg vv (Fin.ext (by simp only; omega))

/-! ## Restricting a vital linkage to a subgraph -/

/-- For `G' ≤ G`, the subgraph of `G` with all vertices of `G` and the edges of `G` not in `G'`. -/
def edgeCompl (G G' : Hypergraph α β) : Hypergraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ G'.edgeSet
  Inc e v := e ∈ G.edgeSet \ G'.edgeSet ∧ G.Inc e v
  vertex_mem_of_inc _ _ h := G.vertex_mem_of_inc h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

theorem edgeCompl_le (G G' : Hypergraph α β) : edgeCompl G G' ≤ G where
  vertexSet_subset := subset_rfl
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [ends, edgeCompl, mem_ofPred_eq]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

/-- For `G' ≤ G`, the pair `(edgeCompl G G', G')` is a separation of `G`. -/
theorem isSeparation_edgeCompl {G G' : Hypergraph α β} (h : G' ≤ G) :
    G.IsSeparation (edgeCompl G G') G' := by
  rw [isSeparation_iff_of_le (edgeCompl_le G G') h]
  refine ⟨union_eq_left.2 h.vertexSet_subset, ?_, ?_⟩
  · exact sdiff_union_of_subset h.edgeSet_subset
  · exact sdiff_inter_self

/-- A vital linkage of `G` meets every subgraph `G'` of `G` in a vital linkage of `G'`. This is
(2.3) applied to the separation `(edgeCompl G G', G')`. -/
theorem isVitalLinkage_inter_of_le {G G' L : Hypergraph α β} (hL : IsVitalLinkage G L)
    (h : G' ≤ G) : IsVitalLinkage G' (L ∩ G') :=
  isVitalLinkage_inter_right_of_isSeparation hL (isSeparation_edgeCompl h)

/-- A subgraph of `K` whose vertices avoid `W` is a subgraph of `K \ W`. -/
theorem le_deleteVertices_of_disjoint {C K : Hypergraph α β} {W : Set α} (hC : C ≤ K)
    (hW : Disjoint C.vertexSet W) : C ≤ K.deleteVertices W := by
  have hnot : ∀ e ∈ C.edgeSet, ∀ w ∈ W, ¬ K.Inc e w := fun e he w hw hinc =>
    disjoint_left.1 hW (C.vertex_mem_of_inc ((GM10.inc_iff_of_le hC he).2 hinc)) hw
  refine ⟨fun x hx => ⟨hC.vertexSet_subset hx, disjoint_left.1 hW hx⟩,
    fun e he => ⟨hC.edgeSet_subset he, hnot e he⟩, fun e he => ?_⟩
  ext v
  simp only [ends, deleteVertices, mem_ofPred_eq]
  rw [GM10.inc_iff_of_le hC he]
  exact ⟨fun h => h.1, fun h => ⟨h, hnot e he⟩⟩

/-! ## Union bounds -/

/-- A union of sets `f i`, `i ∈ I`, each with at most two elements, has at most `2 |I|`
elements. -/
theorem encard_biUnion_le_two_mul {ι : Type*} {I : Set ι} {f : ι → Set α}
    (hf : ∀ i ∈ I, (f i).encard ≤ 2) : (⋃ i ∈ I, f i).encard ≤ 2 * I.encard := by
  rcases I.finite_or_infinite with hI | hI
  · induction I, hI using Set.Finite.induction_on with
    | empty => simp
    | @insert i I hiI hI ih =>
      rw [biUnion_insert, encard_insert_of_notMem hiI, mul_add, mul_one, add_comm]
      exact (encard_union_le _ _).trans (add_le_add (hf i (mem_insert i I))
        (ih fun j hj => hf j (mem_insert_of_mem i hj)))
  · rw [hI.encard_eq]
    simp

/-- If `A` is covered by sets `f i`, `i ∈ I`, each with at most two elements, then
`|A| ≤ 2 |I|`. -/
theorem encard_le_two_mul_of_subset_biUnion {ι : Type*} {A : Set α} {I : Set ι}
    {f : ι → Set α} (hA : A ⊆ ⋃ i ∈ I, f i) (hf : ∀ i ∈ I, (f i).encard ≤ 2) :
    A.encard ≤ 2 * I.encard :=
  (encard_le_encard hA).trans (encard_biUnion_le_two_mul hf)

/-! ## Neighbours in a component -/

/-- If `C` is a component of a graph `L` and `x ∈ V(C)`, then every `L`-neighbour of `x` is a
`C`-neighbour of `x`: the edge joining them is incident with `x`, so it is an edge of `C`. -/
theorem adj_component_of_adj {L C : Hypergraph α β} (hLg : L.IsGraph) (hC : IsComponentOf L C)
    {x y : α} (hx : x ∈ C.vertexSet) (hxy : L.skeleton.Adj x y) : C.skeleton.Adj x y := by
  obtain ⟨hne, e, hex, hey⟩ := hxy
  have he : e ∈ incidentEdges L x := ⟨L.edge_mem_of_inc hex, hex⟩
  rw [← incidentEdges_component_eq hLg hC hx] at he
  exact ⟨hne, e, he.2, (GM10.inc_iff_of_le hC.1 he.1).2 hey⟩

/-! ## Cutting off the tails of a linkage

Let `(A, C)` be a separation of `G` with `B = V(A ∩ C)`, and let `L` be a vital linkage in `G`.
In the proof of (7.3), `A = H₁ ∪ … ∪ H_r` and `C = Γ`. A *tail* is a vertex `w ∈ V(C) \ B`
that can be reached from a terminal `t ∈ V(C) \ B` of `L` along edges of `L ∩ C` without
touching `B`. Deleting the tails from `L` leaves `L ∩ G'`, where `G' = ((L ∩ C) \ W) ∪ A`. The
paper's `Γ'` is "the union of all paths in $L \cap \Gamma$ with both ends in $bd(\Sigma)$ and no
internal vertex in $bd(\Sigma)$ (including one-vertex paths)". `GM21.jumpUnion_eq`
(`GraphMinor/GM21/Section7JumpUnion.lean`) proves that it is `(L ∩ C) \ W`, so the properties of
`(L ∩ C) \ W` proved below are properties of the paper's `Γ'`. -/

/-- The tails of `L` with respect to `C` and `B`. -/
def tailSet (L C : Hypergraph α β) (B : Set α) : Set α :=
  {w | w ∈ C.vertexSet \ B ∧ ∃ t ∈ terminals L, t ∈ C.vertexSet \ B ∧
    ((L ∩ C).deleteVertices B).skeleton.Reachable t w}

/-- An edge with exactly two ends `w ≠ x` has no other end. -/
theorem eq_or_eq_of_ends_ncard_eq_two {L : Hypergraph α β} {e : β}
    (h2 : (L.ends e).ncard = 2) {w x b : α} (hw : L.Inc e w) (hx : L.Inc e x) (hwx : w ≠ x)
    (hb : L.Inc e b) : b = w ∨ b = x := by
  have hfin : (L.ends e).Finite := Set.finite_of_ncard_pos (by rw [h2]; omega)
  have hpair : ({w, x} : Set α) ⊆ L.ends e := by
    rintro z (rfl | rfl)
    · exact hw
    · exact hx
  have heq : ({w, x} : Set α) = L.ends e :=
    eq_of_subset_of_ncard_le hpair (by rw [h2, ncard_pair hwx]) hfin
  have : b ∈ ({w, x} : Set α) := heq ▸ hb
  simpa using this

section tails

variable {G A C L : Hypergraph α β}

theorem tailSet_subset (L C : Hypergraph α β) (B : Set α) :
    tailSet L C B ⊆ C.vertexSet \ B := fun _ h => h.1

theorem disjoint_tailSet (A C L : Hypergraph α β) :
    Disjoint A.vertexSet (tailSet L C (A.vertexSet ∩ C.vertexSet)) := by
  rw [disjoint_left]
  intro x hxA hxW
  exact hxW.1.2 ⟨hxA, hxW.1.1⟩

/-- A terminal of `L` in `V(C) \ B` is a tail. -/
theorem mem_tailSet_of_mem_terminals {B : Set α} {t : α} (ht : t ∈ terminals L)
    (htC : t ∈ C.vertexSet \ B) : t ∈ tailSet L C B :=
  ⟨htC, t, ht, htC, SimpleGraph.Reachable.refl t⟩

/-- An `L`-neighbour of a tail is a tail or lies in `B`. -/
theorem mem_B_of_adj_tail (hsep : G.IsSeparation A C) (hL : IsLinkage G L)
    {w x : α} (hw : w ∈ tailSet L C (A.vertexSet ∩ C.vertexSet)) (hadj : L.skeleton.Adj w x)
    (hx : x ∉ tailSet L C (A.vertexSet ∩ C.vertexSet)) : x ∈ A.vertexSet ∩ C.vertexSet := by
  obtain ⟨⟨hwC, hwB⟩, t, ht, htC, hreach⟩ := hw
  obtain ⟨hne, e, hew, hex⟩ := hadj
  have heL : e ∈ L.edgeSet := L.edge_mem_of_inc hew
  have heG : e ∈ G.edgeSet := hL.1.edgeSet_subset heL
  -- The edge `e` is an edge of `C`: an edge of `A` at `w` would put `w` in `A`, hence in `B`.
  have heC : e ∈ C.edgeSet := by
    rw [← hsep.edgeSet_union] at heG
    rcases heG with heA | heC
    · exfalso
      have hwA : A.Inc e w := (GM10.inc_iff_of_le hsep.left_le heA).2 (GM10.inc_of_le hL.1 hew)
      exact hwB ⟨A.vertex_mem_of_inc hwA, hwC⟩
    · exact heC
  have hCinc : ∀ {y}, L.Inc e y → C.Inc e y := fun hy =>
    (GM10.inc_iff_of_le hsep.right_le heC).2 (GM10.inc_of_le hL.1 hy)
  have hxC : x ∈ C.vertexSet := C.vertex_mem_of_inc (hCinc hex)
  by_contra hxB
  apply hx
  -- Otherwise `e` is an edge of `(L ∩ C) \ B`, so `x` is reachable from `t` as well.
  have hnoB : ∀ b ∈ A.vertexSet ∩ C.vertexSet, ¬ (L ∩ C).Inc e b := by
    intro b hb hinc
    rcases eq_or_eq_of_ends_ncard_eq_two (hL.ends_ncard_eq_two heL) hew hex hne hinc.1 with
      rfl | rfl
    · exact hwB hb
    · exact hxB hb
  have hadj' : ((L ∩ C).deleteVertices (A.vertexSet ∩ C.vertexSet)).skeleton.Adj w x :=
    ⟨hne, e, ⟨⟨hew, hCinc hew⟩, hnoB⟩, ⟨⟨hex, hCinc hex⟩, hnoB⟩⟩
  exact ⟨⟨hxC, hxB⟩, t, ht, htC, hreach.trans hadj'.reachable⟩

/-- `L ∩ (((L ∩ C) \ W) ∪ A) = L \ W`, where `W` is the set of tails. -/
theorem inter_eq_deleteVertices_tailSet (hsep : G.IsSeparation A C) (hL : IsLinkage G L) :
    L ∩ (((L ∩ C).deleteVertices (tailSet L C (A.vertexSet ∩ C.vertexSet))) ∪ A) =
      L.deleteVertices (tailSet L C (A.vertexSet ∩ C.vertexSet)) := by
  set W := tailSet L C (A.vertexSet ∩ C.vertexSet)
  have hLG := hL.1
  have hC'C : (L ∩ C).deleteVertices W ≤ C :=
    (GM10.deleteVertices_le _ W).trans (GM10.inter_le_right hLG hsep.right_le)
  have hG'G : (L ∩ C).deleteVertices W ∪ A ≤ G :=
    GM10.union_le (hC'C.trans hsep.right_le) hsep.left_le
  have hAW := disjoint_tailSet A C L
  apply GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.inter_le hLG hG'G)
    ((GM10.deleteVertices_le L W).trans hLG)
  · ext x
    simp only [GM10.inter_vertexSet, GM10.union_vertexSet, deleteVertices, mem_inter_iff,
      mem_union, mem_sdiff]
    constructor
    · rintro ⟨hxL, (⟨⟨_, _⟩, hxW⟩ | hxA)⟩
      · exact ⟨hxL, hxW⟩
      · exact ⟨hxL, disjoint_left.1 hAW hxA⟩
    · rintro ⟨hxL, hxW⟩
      have hxG : x ∈ G.vertexSet := hLG.vertexSet_subset hxL
      rw [← hsep.vertexSet_union] at hxG
      rcases hxG with hxA | hxC
      · exact ⟨hxL, Or.inr hxA⟩
      · exact ⟨hxL, Or.inl ⟨⟨hxL, hxC⟩, hxW⟩⟩
  · ext e
    simp only [GM10.inter_edgeSet, GM10.union_edgeSet, deleteVertices, mem_inter_iff,
      mem_union, mem_ofPred_eq]
    constructor
    · rintro ⟨heL, (⟨⟨_, heC⟩, hnoW⟩ | heA)⟩
      · refine ⟨heL, fun w hw hinc => hnoW w hw ⟨hinc, ?_⟩⟩
        exact (GM10.inc_iff_of_le hsep.right_le heC).2 (GM10.inc_of_le hLG hinc)
      · refine ⟨heL, fun w hw hinc => disjoint_left.1 hAW ?_ hw⟩
        exact A.vertex_mem_of_inc ((GM10.inc_iff_of_le hsep.left_le heA).2 (GM10.inc_of_le hLG hinc))
    · rintro ⟨heL, hnoW⟩
      have heG : e ∈ G.edgeSet := hLG.edgeSet_subset heL
      rw [← hsep.edgeSet_union] at heG
      rcases heG with heA | heC
      · exact ⟨heL, Or.inr heA⟩
      · exact ⟨heL, Or.inl ⟨⟨heL, heC⟩, fun w hw hinc => hnoW w hw hinc.1⟩⟩

/-- A terminal of `L \ W` that is not a terminal of `L` is an `L`-neighbour of a tail. -/
theorem exists_adj_tail_of_mem_terminals (hL : IsLinkage G L) {W : Set α} {x : α}
    (hx : x ∈ terminals (L.deleteVertices W)) (hxL : x ∉ terminals L) :
    ∃ w ∈ W, L.skeleton.Adj w x := by
  have hDL : L.deleteVertices W ≤ L := GM10.deleteVertices_le L W
  have hloopL : ∀ e ∈ L.edgeSet, (L.ends e).ncard = 2 := fun e he => hL.ends_ncard_eq_two he
  have hloopD : ∀ e ∈ (L.deleteVertices W).edgeSet, ((L.deleteVertices W).ends e).ncard = 2 :=
    fun e he => by rw [← hDL.ends_eq e he]; exact hloopL e (hDL.edgeSet_subset he)
  obtain ⟨hxD, hdegD⟩ := hx
  have hxV : x ∈ L.vertexSet := hDL.vertexSet_subset hxD
  rw [vertexDegree_eq_ncard_incidentEdges hloopD] at hdegD
  by_contra hno
  push Not at hno
  apply hxL
  refine ⟨hxV, ?_⟩
  rw [vertexDegree_eq_ncard_incidentEdges hloopL]
  -- Every edge of `L` at `x` misses `W`, so it is an edge of `L \ W` at `x`.
  have heq : incidentEdges L x = incidentEdges (L.deleteVertices W) x := by
    apply Subset.antisymm _ (incidentEdges_subset_of_le hDL x)
    rintro e ⟨he, hinc⟩
    have hnoW : ∀ w ∈ W, ¬ L.Inc e w := by
      intro w hw hw'
      have hwx : w ≠ x := fun h => hxD.2 (h ▸ hw)
      exact hno w hw ⟨hwx, e, hw', hinc⟩
    exact ⟨⟨he, hnoW⟩, hinc, hnoW⟩
  rw [heq]
  exact hdegD

/-- The terminals of `L \ W` lie in `A`. This is the step "it is exhaustive" of the proof of
(7.3): every vertex of `C` outside `B` that is not a tail keeps its degree. -/
theorem terminals_deleteVertices_tailSet_subset (hsep : G.IsSeparation A C)
    (hL : IsLinkage G L) :
    terminals (L.deleteVertices (tailSet L C (A.vertexSet ∩ C.vertexSet))) ⊆ A.vertexSet := by
  intro x hx
  by_contra hxA
  have hxD := hx.1
  have hxG : x ∈ G.vertexSet := hL.1.vertexSet_subset hxD.1
  rw [← hsep.vertexSet_union] at hxG
  have hxC : x ∈ C.vertexSet \ (A.vertexSet ∩ C.vertexSet) :=
    ⟨hxG.resolve_left hxA, fun h => hxA h.1⟩
  by_cases hxL : x ∈ terminals L
  · exact hxD.2 (mem_tailSet_of_mem_terminals hxL hxC)
  · obtain ⟨w, hw, hadj⟩ := exists_adj_tail_of_mem_terminals hL hx hxL
    exact hxA (mem_B_of_adj_tail hsep hL hw hadj hxD.2).1

/-- A walk in `M ≤ L` inside an indexed component `v 0, …, v m` of `L` moves one index at a time,
so it passes through every index between its first and its last. -/
theorem mem_support_of_isIndexed {L M P : Hypergraph α β} (hLg : L.IsGraph)
    (hP : IsComponentOf L P) (hM : M ≤ L) {m : ℕ} {v : Fin (m + 1) → α} (hv : Injective v)
    (hV : P.vertexSet = range v)
    (hadj : ∀ i j : Fin (m + 1), P.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1)) :
    ∀ {a c : α} (q : M.skeleton.Walk a c) (l k s : Fin (m + 1)), v l = a → v k = c →
      (l.1 ≤ s.1 ∧ s.1 ≤ k.1 ∨ k.1 ≤ s.1 ∧ s.1 ≤ l.1) → v s ∈ q.support := by
  intro a c q
  induction q with
  | nil =>
    intro l k s hl hk hs
    have hlk : l = k := hv (hl.trans hk.symm)
    subst hlk
    have hsl : s = l := Fin.ext (by omega)
    rw [hsl, hl]
    exact SimpleGraph.Walk.start_mem_support _
  | @cons a b c hab q ih =>
    intro l k s hl hk hs
    by_cases hsl : s.1 = l.1
    · rw [show s = l from Fin.ext hsl, hl]
      exact SimpleGraph.Walk.start_mem_support _
    have haP : a ∈ P.vertexSet := by rw [hV, ← hl]; exact mem_range_self l
    have hadjP := adj_component_of_adj hLg hP haP (skeleton_le_of_le hM hab)
    have hbP : b ∈ P.vertexSet := by
      obtain ⟨_, e, _, heb⟩ := hadjP
      exact P.vertex_mem_of_inc heb
    rw [hV] at hbP
    obtain ⟨l', rfl⟩ := hbP
    have hll' := (hadj l l').1 (hl ▸ hadjP)
    rw [SimpleGraph.Walk.support_cons]
    exact List.mem_cons_of_mem _ (ih l' k s rfl hk (by omega))

/-- **Each component of `L` includes at most one component of `L \ W`**, when every vertex of `W`
is joined in `M ≤ L` to a terminal of `L` and `W` is closed under walks in `M`. Let `x, y ∉ W` be
joined in `L`, so they lie on one component, indexed as `v 0, …, v m`. A vertex `v s` between them
cannot be in `W`: it would be joined in `M` to a terminal of `L`, which is `v 0` or `v m`, and the
walk would pass through `x` or `y`, putting it in `W`. So the vertices between `x` and `y` give a
walk in `L \ W`. -/
theorem reachable_deleteVertices_of_closed {G L M : Hypergraph α β} (hL : IsLinkage G L)
    (hM : M ≤ L) {W : Set α} (hW : ∀ w ∈ W, ∃ t ∈ terminals L, M.skeleton.Reachable w t)
    (hclosed : ∀ w ∈ W, ∀ u, M.skeleton.Reachable w u → u ∈ W)
    {x y : α} (hxL : x ∈ L.vertexSet) (hxW : x ∉ W) (hyW : y ∉ W)
    (hxy : L.skeleton.Reachable x y) : (L.deleteVertices W).skeleton.Reachable x y := by
  classical
  have hLg := hL.2.1
  have hP : IsComponentOf L (reachableComponent L x) := isComponentOf_reachableComponent hLg hxL
  have hxP : x ∈ (reachableComponent L x).vertexSet := self_mem_reachableComponent hxL
  by_cases hxy' : x = y
  · subst hxy'
    exact SimpleGraph.Reachable.refl x
  have hyL : y ∈ L.vertexSet := by
    obtain ⟨p⟩ := hxy.symm
    cases p with
    | nil => exact (hxy' rfl).elim
    | cons h _ =>
      obtain ⟨_, e, hey, _⟩ := h
      exact L.vertex_mem_of_inc hey
  have hyP : y ∈ (reachableComponent L x).vertexSet := ⟨hyL, hxy⟩
  rcases eq_empty_or_nonempty (reachableComponent L x).edgeSet with hemp | hne
  · obtain ⟨a, -, hVa, -, -⟩ := isPathGraph_of_edgeSet_empty (hL.2.2 _ hP) hemp
    rw [hVa] at hxP hyP
    exact (hxy' (hxP.trans hyP.symm)).elim
  obtain ⟨x₁, -, x₂, -, -, ⟨m, -, v, hv, hv0, hvm, hV, hadj⟩, hdeg⟩ :=
    exists_isIndexedPath_of_isPathGraph (hL.2.2 _ hP) hne
  have hvP : ∀ s, v s ∈ (reachableComponent L x).vertexSet := fun s ↦ by
    rw [hV]; exact mem_range_self s
  have hxP' := hxP
  have hyP' := hyP
  rw [hV] at hxP' hyP'
  obtain ⟨i, hi⟩ := hxP'
  obtain ⟨j, hj⟩ := hyP'
  -- No vertex between `x` and `y` is in `W`.
  have hnot : ∀ s : Fin (m + 1), (i.1 ≤ s.1 ∧ s.1 ≤ j.1 ∨ j.1 ≤ s.1 ∧ s.1 ≤ i.1) → v s ∉ W := by
    intro s hs hsW
    obtain ⟨t, ht, hst⟩ := hW _ hsW
    obtain ⟨q⟩ := hst
    have htP : t ∈ (reachableComponent L x).vertexSet :=
      ⟨ht.1, (hvP s).2.trans (reachable_of_le hM ⟨q⟩)⟩
    have hdeg_t : (incidentEdges (reachableComponent L x) t).ncard ≤ 1 := by
      rw [incidentEdges_component_eq hLg hP htP]
      have h := ht.2
      rwa [vertexDegree_eq_ncard_incidentEdges (fun e he => hL.ends_ncard_eq_two he)] at h
    have htP' := htP
    rw [hV] at htP'
    obtain ⟨k, rfl⟩ := htP'
    have hk : k.1 = 0 ∨ k.1 = m := by
      rcases (hdeg _ htP).1 hdeg_t with h | h
      · rw [← hv0] at h
        exact Or.inl (congrArg Fin.val (hv h))
      · rw [← hvm] at h
        exact Or.inr (congrArg Fin.val (hv h))
    -- The walk from `v s` to `v k` meets `x` or `y`, which would then be in `W`.
    have hhit : ∀ r : Fin (m + 1), (v r = x ∨ v r = y) →
        (s.1 ≤ r.1 ∧ r.1 ≤ k.1 ∨ k.1 ≤ r.1 ∧ r.1 ≤ s.1) → False := by
      intro r hr hrs
      have hmem := mem_support_of_isIndexed hLg hP hM hv hV hadj q s k r rfl rfl hrs
      have hrW : v r ∈ W := hclosed _ hsW _ ⟨q.takeUntil _ hmem⟩
      rcases hr with h | h
      · exact hxW (h ▸ hrW)
      · exact hyW (h ▸ hrW)
    have hjm := j.2
    have him := i.2
    rcases hk with hk | hk
    · rcases hs with hs | hs
      · exact hhit i (Or.inl hi) (Or.inr ⟨by omega, hs.1⟩)
      · exact hhit j (Or.inr hj) (Or.inr ⟨by omega, hs.1⟩)
    · rcases hs with hs | hs
      · exact hhit j (Or.inr hj) (Or.inl ⟨hs.2, by omega⟩)
      · exact hhit i (Or.inl hi) (Or.inl ⟨hs.2, by omega⟩)
  -- Consecutive vertices outside `W` are adjacent in `L \ W`.
  have hstep : ∀ (s : Fin (m + 1)) (hs : s.1 + 1 < m + 1), v s ∉ W → v ⟨s.1 + 1, hs⟩ ∉ W →
      (L.deleteVertices W).skeleton.Adj (v s) (v ⟨s.1 + 1, hs⟩) := by
    intro s hs h₁ h₂
    have hPadj := (hadj s ⟨s.1 + 1, hs⟩).2 (Or.inl rfl)
    obtain ⟨hne', e, he₁, he₂⟩ := skeleton_le_of_le hP.1 hPadj
    have hnoW : ∀ w ∈ W, ¬ L.Inc e w := by
      intro w hw hew
      rcases eq_or_eq_of_ends_ncard_eq_two (hL.ends_ncard_eq_two (L.edge_mem_of_inc he₁))
        he₁ he₂ hne' hew with rfl | rfl
      · exact h₁ hw
      · exact h₂ hw
    exact ⟨hne', e, ⟨he₁, hnoW⟩, ⟨he₂, hnoW⟩⟩
  have key : ∀ a b : Fin (m + 1), a.1 ≤ b.1 →
      (∀ s : Fin (m + 1), a.1 ≤ s.1 → s.1 ≤ b.1 → v s ∉ W) →
      (L.deleteVertices W).skeleton.Reachable (v a) (v b) := by
    intro a b hab hout
    have hb := b.2
    have hchain : ∀ d (hd : a.1 + d < m + 1), a.1 + d ≤ b.1 →
        (L.deleteVertices W).skeleton.Reachable (v a) (v ⟨a.1 + d, hd⟩) := by
      intro d
      induction d with
      | zero => intro hd _; exact SimpleGraph.Reachable.refl _
      | succ d ih =>
        intro hd hdb
        have h1 := ih (by omega) (by omega)
        have h2 := hstep ⟨a.1 + d, by omega⟩ (by simp only; omega)
          (hout _ (by simp only; omega) (by simp only; omega))
          (hout _ (by simp only; omega) (by simp only; omega))
        exact h1.trans h2.reachable
    have := hchain (b.1 - a.1) (by omega) (by omega)
    rwa [show (⟨a.1 + (b.1 - a.1), by omega⟩ : Fin (m + 1)) = b from Fin.ext (by simp only; omega)]
      at this
  rcases le_total i.1 j.1 with hij | hij
  · have := key i j hij fun s h1 h2 ↦ hnot s (Or.inl ⟨h1, h2⟩)
    rwa [hi, hj] at this
  · have := key j i hij fun s h1 h2 ↦ hnot s (Or.inr ⟨h1, h2⟩)
    rw [hi, hj] at this
    exact this.symm

/-- **The count after the claim**: if every component of a linkage `L` includes at most one
component of `L \ W`, then `L \ W` has at most as many terminals as `L`. In each component `P` of
`L`, the terminals of `L \ W` lie in one component of `L \ W`, so there are at most two of them,
and at most one if `P` is a single vertex. These are the numbers of terminals of `L` in `P`. -/
theorem ncard_terminals_deleteVertices_le_of_reachable {G L : Hypergraph α β}
    (hL : IsLinkage G L) {W : Set α}
    (hreach : ∀ x y, x ∈ L.vertexSet → x ∉ W → y ∉ W → L.skeleton.Reachable x y →
      (L.deleteVertices W).skeleton.Reachable x y) :
    (terminals (L.deleteVertices W)).ncard ≤ (terminals L).ncard := by
  classical
  set K := L.deleteVertices W
  have hKL : K ≤ L := GM10.deleteVertices_le L W
  have hK : IsLinkage G K := isLinkage_of_le hL hKL (hKL.trans hL.1)
  have hLg := hL.2.1
  set f : α → Set α := fun x ↦ (reachableComponent L x).vertexSet with hf
  have hT₁ : (terminals K).Finite := L.vertexSet_finite.subset fun x hx ↦ hx.1.1
  have hT₂ : (terminals L).Finite := L.vertexSet_finite.subset fun x hx ↦ hx.1
  -- The bound in one component.
  have hfiber : ∀ x₀ ∈ L.vertexSet,
      (terminals K ∩ f x₀).ncard ≤ (terminals L ∩ f x₀).ncard := by
    intro x₀ hx₀
    have hP : IsComponentOf L (reachableComponent L x₀) := isComponentOf_reachableComponent hLg hx₀
    have hS₂ : terminals L ∩ f x₀ ∈ linkagePattern L := ⟨_, hP, rfl⟩
    rcases hL.mem_linkagePattern_structure hS₂ with ⟨a, -, hS, h0⟩ | ⟨a, -, b, -, hab, hS, -, -⟩
    · -- `P` is the single vertex `a`.
      have haP : a ∈ f x₀ := (hS ▸ mem_singleton a : a ∈ terminals L ∩ f x₀).2
      have hinc : incidentEdges L a = ∅ :=
        (ncard_eq_zero (L.edgeSet_finite.subset fun _ he ↦ he.1)).1 h0
      have hsub : terminals K ∩ f x₀ ⊆ {a} := by
        rintro u ⟨-, hu⟩
        by_contra hua
        obtain ⟨p⟩ := haP.2.symm.trans hu.2
        cases p with
        | nil => exact hua rfl
        | cons h _ =>
          obtain ⟨_, e, hea, _⟩ := h
          have : e ∈ incidentEdges L a := ⟨L.edge_mem_of_inc hea, hea⟩
          rw [hinc] at this
          exact this
      rw [hS, ncard_singleton]
      exact (ncard_le_ncard hsub (finite_singleton a)).trans (ncard_singleton a).le
    · rw [hS, ncard_pair hab]
      rcases (terminals K ∩ f x₀).eq_empty_or_nonempty with hemp | ⟨z, hz⟩
      · rw [hemp, ncard_empty]; omega
      have hzK : z ∈ K.vertexSet := hz.1.1
      have hQ : IsComponentOf K (reachableComponent K z) :=
        isComponentOf_reachableComponent hK.2.1 hzK
      have hsub : terminals K ∩ f x₀ ⊆ terminals K ∩ (reachableComponent K z).vertexSet := by
        rintro u ⟨huT, hu⟩
        refine ⟨huT, huT.1, hreach z u hzK.1 hzK.2 huT.1.2 ?_⟩
        exact hz.2.2.symm.trans hu.2
      have hB : terminals K ∩ (reachableComponent K z).vertexSet ∈ linkagePattern K :=
        ⟨_, hQ, rfl⟩
      refine (ncard_le_ncard hsub (hT₁.subset inter_subset_left)).trans ?_
      rcases hK.mem_linkagePattern_structure hB with ⟨c, -, hc, -⟩ | ⟨c, -, d, -, hcd, hc, -, -⟩
      · rw [hc, ncard_singleton]; omega
      · rw [hc, ncard_pair hcd]
  -- Sum over the components.
  have hsame : ∀ {x₀ z}, z ∈ f x₀ → f z = f x₀ := by
    intro x₀ z hz
    ext u
    simp only [hf, reachableComponent_vertexSet, mem_ofPred_eq]
    exact ⟨fun h ↦ ⟨h.1, hz.2.trans h.2⟩, fun h ↦ ⟨h.1, hz.2.symm.trans h.2⟩⟩
  set V := L.vertexSet_finite.toFinset
  set S₁ := hT₁.toFinset
  set S₂ := hT₂.toFinset
  have h₁ : ∀ x ∈ S₁, f x ∈ V.image f := fun x hx ↦
    Finset.mem_image_of_mem f (by rw [Set.Finite.mem_toFinset] at hx ⊢; exact hx.1.1)
  have h₂ : ∀ x ∈ S₂, f x ∈ V.image f := fun x hx ↦
    Finset.mem_image_of_mem f (by rw [Set.Finite.mem_toFinset] at hx ⊢; exact hx.1)
  rw [ncard_eq_toFinset_card _ hT₁, ncard_eq_toFinset_card _ hT₂,
    Finset.card_eq_sum_card_fiberwise h₁, Finset.card_eq_sum_card_fiberwise h₂]
  refine Finset.sum_le_sum fun b hb ↦ ?_
  obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hb
  rw [Set.Finite.mem_toFinset] at hx₀
  have hl : ((S₁.filter fun x ↦ f x = f x₀) : Set α) ⊆ terminals K ∩ f x₀ := by
    intro z hz
    rw [Finset.coe_filter, mem_ofPred_eq, Set.Finite.mem_toFinset] at hz
    refine ⟨hz.1, ?_⟩
    rw [← hz.2]
    exact self_mem_reachableComponent hz.1.1.1
  have hr : terminals L ∩ f x₀ ⊆ ((S₂.filter fun x ↦ f x = f x₀) : Set α) := by
    intro z hz
    rw [Finset.coe_filter, mem_ofPred_eq, Set.Finite.mem_toFinset]
    exact ⟨hz.1, hsame hz.2⟩
  rw [← ncard_coe_finset, ← ncard_coe_finset]
  exact (ncard_le_ncard hl (hT₁.subset inter_subset_left)).trans
    ((hfiber x₀ hx₀).trans (ncard_le_ncard hr (Finset.finite_toSet _)))

/-- `L \ W` has at most as many terminals as `L`: "it is a $p$-linkage since each component of $L$
includes at most one component of $L \cap G'$", in the proof of (7.3). The claim is
`reachable_deleteVertices_of_closed`, with `M = (L ∩ C) \ B`: every tail is joined in `M` to a
terminal of `L`, and whatever `M` reaches from a tail is a tail. The count is
`ncard_terminals_deleteVertices_le_of_reachable`. -/
theorem ncard_terminals_deleteVertices_tailSet_le (hsep : G.IsSeparation A C)
    (hL : IsLinkage G L) :
    (terminals (L.deleteVertices (tailSet L C (A.vertexSet ∩ C.vertexSet)))).ncard ≤
      (terminals L).ncard := by
  set B := A.vertexSet ∩ C.vertexSet
  set M := (L ∩ C).deleteVertices B
  have hML : M ≤ L := (GM10.deleteVertices_le _ B).trans (GM10.inter_le_left hL.1 hsep.right_le)
  refine ncard_terminals_deleteVertices_le_of_reachable hL fun x y hxL hxW hyW hxy ↦ ?_
  refine reachable_deleteVertices_of_closed hL hML (fun w hw ↦ ?_) (fun w hw u hwu ↦ ?_)
    hxL hxW hyW hxy
  · obtain ⟨-, t, ht, -, hr⟩ := hw
    exact ⟨t, ht, hr.symm⟩
  · obtain ⟨hwC, t, ht, htC, hr⟩ := hw
    by_cases huw : u = w
    · exact huw ▸ ⟨hwC, t, ht, htC, hr⟩
    have huM : u ∈ M.vertexSet := by
      obtain ⟨p⟩ := hwu.symm
      cases p with
      | nil => exact (huw rfl).elim
      | cons h _ =>
        obtain ⟨_, e, heu, _⟩ := h
        exact M.vertex_mem_of_inc heu
    exact ⟨⟨huM.1.2, huM.2⟩, t, ht, htC, hr.trans hwu⟩

end tails

/-! ## Jumps and isolated vertices

The jumps of a graph with respect to a set `B`, and a fact used to count the components of
`L ∩ C` in `GraphMinor/GM21/Section7JumpUnion.lean`. -/

/-- The paths `Q ≤ C'` with two distinct ends in `B` and no other vertex in `B`. With `C' = Γ'`
and `B = ιV(V(Γ) ∩ bd(Σ))` these are the `Σ`-jumps in `Γ'`. -/
def jumpSet (C' : Hypergraph α β) (B : Set α) : Set (Hypergraph α β) :=
  {Q | Q ≤ C' ∧ IsPathGraph Q ∧ ∃ a ∈ B, ∃ b ∈ B, a ≠ b ∧ terminals Q = {a, b} ∧
    ∀ x ∈ Q.vertexSet, x ∈ B → x = a ∨ x = b}

section counting

variable {G A C L : Hypergraph α β}

/-- The vertices of `B` with no edge of `K` are isolated, so deleting them does not change the
other terminals. -/
theorem terminals_deleteVertices_of_isolated {G K : Hypergraph α β} (hK : IsLinkage G K)
    {X : Set α} (hX : ∀ x ∈ X, incidentEdges K x = ∅) :
    terminals (K.deleteVertices X) = terminals K \ X := by
  have hloopK : ∀ e ∈ K.edgeSet, (K.ends e).ncard = 2 := fun e he => hK.ends_ncard_eq_two he
  have hDK : K.deleteVertices X ≤ K := GM10.deleteVertices_le K X
  have hloopD : ∀ e ∈ (K.deleteVertices X).edgeSet, ((K.deleteVertices X).ends e).ncard = 2 :=
    fun e he => by rw [← hDK.ends_eq e he]; exact hloopK e (hDK.edgeSet_subset he)
  have hinc : ∀ y, incidentEdges (K.deleteVertices X) y = incidentEdges K y := by
    intro y
    apply Subset.antisymm (incidentEdges_subset_of_le hDK y)
    rintro e ⟨he, hinc⟩
    have hnoX : ∀ x ∈ X, ¬ K.Inc e x := fun x hx hx' => by
      have : e ∈ incidentEdges K x := ⟨he, hx'⟩
      rw [hX x hx] at this
      exact this
    exact ⟨⟨he, hnoX⟩, hinc, hnoX⟩
  ext y
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_sdiff, vertexDegree_eq_ncard_incidentEdges
    hloopK, vertexDegree_eq_ncard_incidentEdges hloopD, hinc]
  simp only [deleteVertices, mem_sdiff]
  tauto

end counting

end GM21
end GraphMinor
