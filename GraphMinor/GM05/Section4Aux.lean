module

public import GraphMinor.GM05.Section4Bipartite
public import GraphMinor.GM05.VertexWeb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Minors V, Section 4 (Part 2): Auxiliary Lemmas for (4.4)–(4.6)

This file provides the auxiliary definitions and lemmas for the proof of (4.4)–(4.6) in Section 4 of
N. Robertson and P. D. Seymour, *Graph Minors. V. Excluding a planar graph*,
J. Combin. Theory Ser. B **41** (1986), 92–114 (pages 98–100):

- `Path.isLeafOf_first_of_ne`: the initial vertex of a nontrivial path has valency `1` in its
  subgraph.
- `IsDirectBPath` and `webAuxGraph`: the auxiliary simple graph `L` on `Fin m` from the proof of
  (4.4).
- `exists_walk_webAuxGraph_of_path`: any path in `webSubgraph A B` from `A_{i₁}` to `A_{i₂}` induces
  a walk in `L` from `i₁` to `i₂` whose vertices correspond to `A_r` met by the path.
- `numComponents_biSup_path_le`: the subgraph `D_k = ⨆ r ∈ Y_k, A_r` has at most `|Y_k|`
  components.
- `theorem_4_4_arith_left` and `theorem_4_4_arith_right`: the arithmetic bounds that exclude both
  alternatives of (4.3) in Case 1 of (4.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set GM01

universe u

variable {V : Type u}

/-! ### Leaves of paths and unions of subgraphs -/

/-- In any walk `w : (⊤ : SimpleGraph V).Walk u v` with `u ∉ w.support` (Wait: for `Walk.cons hadj rest`
with `u ∉ rest.support`), `u` is not in `rest.toSubgraph.verts`. -/
lemma Path.isLeafOf_first_of_ne (P : GM01.Path V) (hne : P.first ≠ P.last) :
    IsLeafOf P.toSubgraph P.first := by
  refine ⟨P.first_mem_verts, ?_⟩
  rcases P with ⟨u, v, w, hw⟩
  dsimp [GM01.Path.toSubgraph] at hne ⊢
  cases w with
  | nil => exact absurd rfl hne
  | @cons u x v hadj rest =>
    rw [Walk.cons_isPath_iff] at hw
    have hnb_eq : (Walk.cons hadj rest).toSubgraph.neighborSet u = {x} := by
      ext z
      simp only [Subgraph.mem_neighborSet, Walk.toSubgraph, Subgraph.sup_adj,
        subgraphOfAdj_adj, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk,
        Set.mem_singleton_iff]
      constructor
      · rintro ((⟨_, rfl⟩ | ⟨_, rfl⟩) | hadj_rest)
        · rfl
        · exact absurd rfl hadj.ne
        · have hu_rest : u ∈ rest.support :=
             rest.mem_verts_toSubgraph.1 (rest.toSubgraph.edge_vert hadj_rest)
          exact absurd hu_rest hw.2
      · rintro rfl
        exact Or.inl (Or.inl ⟨trivial, rfl⟩)
    rw [hnb_eq, Set.ncard_singleton]

lemma neighborSet_sup_of_notMem_right {H₁ H₂ : (⊤ : SimpleGraph V).Subgraph} {v : V}
    (hv : v ∉ H₂.verts) :
    (H₁ ⊔ H₂).neighborSet v = H₁.neighborSet v := by
  ext w
  simp only [Subgraph.mem_neighborSet, Subgraph.sup_adj]
  exact ⟨fun h ↦ h.resolve_right (fun h₂ ↦ hv (H₂.edge_vert h₂)), Or.inl⟩

lemma isLeafOf_sup_of_notMem_right {H₁ H₂ : (⊤ : SimpleGraph V).Subgraph} {v : V}
    (hleaf : IsLeafOf H₁ v) (hv : v ∉ H₂.verts) :
    IsLeafOf (H₁ ⊔ H₂) v := by
  refine ⟨Or.inl hleaf.1, ?_⟩
  rw [neighborSet_sup_of_notMem_right hv]
  exact hleaf.2

/-! ### Direct subpaths of `B_j` and the auxiliary graph `L` -/

/-- `P` is a subpath of `B_j` with initial vertex in `A_i`, terminal vertex in `A_{i'}`, and no
internal vertex in any of `A₁, …, Aₘ` (Graph Minors V, proof of (4.4), page 98). -/
@[expose]
def IsDirectBPath {m n : ℕ} (A : Fin m → GM01.Path V) (B : Fin n → GM01.Path V)
    (j : Fin n) (i i' : Fin m) (P : GM01.Path V) : Prop :=
  P.toSubgraph ≤ (B j).toSubgraph ∧ P.first ∈ (A i).verts ∧ P.last ∈ (A i').verts ∧
    Disjoint P.internalVerts (⋃ s, (A s).verts)

lemma IsDirectBPath.reverse {m n : ℕ} {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V}
    {j : Fin n} {i i' : Fin m} {P : GM01.Path V} (h : IsDirectBPath A B j i i' P) :
    IsDirectBPath A B j i' i P.reverse := by
  refine ⟨by simpa using h.1, by simpa using h.2.2.1, by simpa using h.2.1, ?_⟩
  have hint : P.reverse.internalVerts = P.internalVerts := by
    simp [GM01.Path.internalVerts, GM01.Path.ends, Set.pair_comm]
  rw [hint]
  exact h.2.2.2

lemma IsDirectBPath.first_ne_last {m n : ℕ} {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V}
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    {j : Fin n} {i i' : Fin m} {P : GM01.Path V} (hne : i ≠ i')
    (h : IsDirectBPath A B j i i' P) : P.first ≠ P.last := by
  intro heq
  exact Set.disjoint_left.1 (hA_disj hne) h.2.1 (heq ▸ h.2.2.1)

lemma IsDirectBPath.verts_inter_left {m n : ℕ} {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V}
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    {j : Fin n} {i i' : Fin m} {P : GM01.Path V} (hne : i ≠ i')
    (h : IsDirectBPath A B j i i' P) :
    P.verts ∩ (A i).verts = {P.first} := by
  ext v
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨hvP, hvA⟩ ↦ ?_, fun hvf ↦ hvf ▸ ⟨P.first_mem_verts, h.2.1⟩⟩
  by_cases hve : v ∈ P.ends
  · rcases hve with rfl | rfl
    · rfl
    · exfalso
      exact Set.disjoint_left.1 (hA_disj hne) hvA h.2.2.1
  · exfalso
    have hv_int : v ∈ P.internalVerts := ⟨hvP, hve⟩
    exact Set.disjoint_left.1 h.2.2.2 hv_int (Set.mem_iUnion.2 ⟨i, hvA⟩)

lemma IsDirectBPath.disjoint_other {m n : ℕ} {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V}
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    {j : Fin n} {i i' s : Fin m} {P : GM01.Path V} (hsi : s ≠ i) (hsi' : s ≠ i')
    (h : IsDirectBPath A B j i i' P) :
    Disjoint P.verts (A s).verts := by
  rw [Set.disjoint_left]
  intro v hvP hvA
  by_cases hve : v ∈ P.ends
  · rcases hve with rfl | rfl
    · exact Set.disjoint_left.1 (hA_disj hsi) hvA h.2.1
    · exact Set.disjoint_left.1 (hA_disj hsi') hvA h.2.2.1
  · exact Set.disjoint_left.1 h.2.2.2 ⟨hvP, hve⟩ (Set.mem_iUnion.2 ⟨s, hvA⟩)

/-- The auxiliary simple graph `L` on `Fin m` in the proof of Graph Minors V, (4.4) (page 98):
"Let $L$ be the simple graph with vertex set $\{1, \dots, m\}$, in which distinct $i, i'$ are
adjacent if there exists $j \in \{1, \dots, n\}$ such that a subpath of $B_j$ has initial
vertex in one of $A_i, A_{i'}$, terminal vertex in the other, and no interior vertex in any
of $A_1, \dots, A_m$." -/
@[expose]
def webAuxGraph {m n : ℕ} (A : Fin m → GM01.Path V) (B : Fin n → GM01.Path V) :
    SimpleGraph (Fin m) where
  Adj i i' := i ≠ i' ∧ ∃ (j : Fin n) (P : GM01.Path V), IsDirectBPath A B j i i' P
  symm := ⟨fun _ _ ⟨hne, j, P, hP⟩ ↦ ⟨hne.symm, j, P.reverse, hP.reverse⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- The union of the subgraphs of `A₁, …, Aₘ` and `B₁, …, Bₙ`. -/
@[expose]
def webSubgraph {m n : ℕ} (A : Fin m → GM01.Path V) (B : Fin n → GM01.Path V) :
    (⊤ : SimpleGraph V).Subgraph :=
  (⨆ i, (A i).toSubgraph) ⊔ (⨆ j, (B j).toSubgraph)

lemma webSubgraph_le {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : VertexWeb G A B) :
    webSubgraph A B ≤ G :=
  sup_le (iSup_le fun i ↦ hweb.isIn_left i) (iSup_le fun j ↦ hweb.isIn_right j)

/-- Any path `P` in `webSubgraph A B` from `A_i` to `A_{i'}` (`i ≠ i'`) with no internal vertex in
`⋃ s, (A s).verts` lies in `(B j).toSubgraph` for some `j`, hence witnesses
`(webAuxGraph A B).Adj i i'`. -/
lemma webAuxGraph_adj_of_direct_path {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : VertexWeb G A B)
    {i i' : Fin m} (hne : i ≠ i') {P : GM01.Path V}
    (hP_le : P.toSubgraph ≤ webSubgraph A B)
    (hfirst : P.first ∈ (A i).verts) (hlast : P.last ∈ (A i').verts)
    (hint : Disjoint P.internalVerts (⋃ s, (A s).verts)) :
    (webAuxGraph A B).Adj i i' := by
  have hne_ends : P.first ≠ P.last := fun heq ↦
    Set.disjoint_left.1 (hweb.disjoint_left hne) hfirst (heq ▸ hlast)
  have hadj_in_B : ∀ {x y : V}, P.toSubgraph.Adj x y → (⨆ j, (B j).toSubgraph).Adj x y := by
    intro x y hxy
    have hxy_web := hP_le.2 hxy
    rw [webSubgraph, Subgraph.sup_adj, Subgraph.iSup_adj] at hxy_web
    rcases hxy_web with ⟨s, hxy_As⟩ | hxy_B
    · exfalso
      have hxP : x ∈ P.verts := P.toSubgraph.edge_vert hxy
      have hyP : y ∈ P.verts := P.toSubgraph.edge_vert hxy.symm
      have hxAs : x ∈ (A s).verts := (A s).toSubgraph.edge_vert hxy_As
      have hyAs : y ∈ (A s).verts := (A s).toSubgraph.edge_vert hxy_As.symm
      have hx_ends : x ∈ P.ends := by
        by_contra hx_not
        exact Set.disjoint_left.1 hint ⟨hxP, hx_not⟩ (Set.mem_iUnion.2 ⟨s, hxAs⟩)
      have hy_ends : y ∈ P.ends := by
        by_contra hy_not
        exact Set.disjoint_left.1 hint ⟨hyP, hy_not⟩ (Set.mem_iUnion.2 ⟨s, hyAs⟩)
      have hxy_ne : x ≠ y := hxy.ne
      have hsi : s = i := by
        by_contra hsi
        rcases hx_ends with rfl | rfl <;> rcases hy_ends with rfl | rfl
        · exact hxy_ne rfl
        · exact Set.disjoint_left.1 (hweb.disjoint_left hsi) hxAs hfirst
        · exact Set.disjoint_left.1 (hweb.disjoint_left hsi) hyAs hfirst
        · exact hxy_ne rfl
      have hsi' : s = i' := by
        by_contra hsi'
        rcases hx_ends with rfl | rfl <;> rcases hy_ends with rfl | rfl
        · exact hxy_ne rfl
        · exact Set.disjoint_left.1 (hweb.disjoint_left hsi') hyAs hlast
        · exact Set.disjoint_left.1 (hweb.disjoint_left hsi') hxAs hlast
        · exact hxy_ne rfl
      exact hne (hsi.symm.trans hsi')
    · exact hxy_B
  have hfirst_adj : ∃ w, P.toSubgraph.Adj P.first w := by
    rcases P with ⟨u, v, p, _⟩
    dsimp [GM01.Path.toSubgraph] at hne_ends ⊢
    cases p with
    | nil => exact absurd rfl hne_ends
    | @cons _ w _ _ _ =>
      exact ⟨w, Or.inl (by simp [subgraphOfAdj])⟩
  obtain ⟨w₀, hw₀⟩ := hfirst_adj
  have hw₀_B := hadj_in_B hw₀
  rw [Subgraph.iSup_adj] at hw₀_B
  obtain ⟨j₀, hw₀_j₀⟩ := hw₀_B
  have hfirst_Bj₀ : P.first ∈ (B j₀).verts := (B j₀).toSubgraph.edge_vert hw₀_j₀
  have hverts_Bj₀ : P.verts ⊆ (B j₀).verts := by
    intro z hz
    obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph P.toSubgraph).1
      P.connected_toSubgraph).2 P.first_mem_verts hz
    have haux : ∀ {a b : V} (q : (⊤ : SimpleGraph V).Walk a b),
        q.toSubgraph ≤ P.toSubgraph → a ∈ (B j₀).verts → b ∈ (B j₀).verts := by
      intro a b q hq ha
      induction q with
      | nil => exact ha
      | @cons a c b _ rest ih =>
        rw [Walk.toSubgraph, sup_le_iff] at hq
        have hadjP : P.toSubgraph.Adj a c := hq.1.2 (by simp)
        have hadjB := hadj_in_B hadjP
        rw [Subgraph.iSup_adj] at hadjB
        obtain ⟨j', hadj_j'⟩ := hadjB
        have ha_j' : a ∈ (B j').verts := (B j').toSubgraph.edge_vert hadj_j'
        have hj' : j' = j₀ := by
          by_contra hne_j
          exact Set.disjoint_left.1 (hweb.disjoint_right hne_j) ha_j' ha
        subst hj'
        exact ih hq.2 ((B j').toSubgraph.edge_vert hadj_j'.symm)
    exact haux p hp hfirst_Bj₀
  have hP_le_Bj₀ : P.toSubgraph ≤ (B j₀).toSubgraph := by
    refine ⟨hverts_Bj₀, fun x y hxy ↦ ?_⟩
    have hadjB := hadj_in_B hxy
    rw [Subgraph.iSup_adj] at hadjB
    obtain ⟨j', hadj_j'⟩ := hadjB
    have hx_j₀ : x ∈ (B j₀).verts := hverts_Bj₀ (P.toSubgraph.edge_vert hxy)
    have hx_j' : x ∈ (B j').verts := (B j').toSubgraph.edge_vert hadj_j'
    have hj' : j' = j₀ := by
      by_contra hne_j
      exact Set.disjoint_left.1 (hweb.disjoint_right hne_j) hx_j' hx_j₀
    subst hj'
    exact hadj_j'
  exact ⟨hne, j₀, P, hP_le_Bj₀, hfirst, hlast, hint⟩

/-- Every path `Q` in `webSubgraph A B` from `A_{i₁}` to `A_{i₂}` induces a walk in `webAuxGraph A B`
from `i₁` to `i₂` whose vertices `r` all satisfy `((A r).verts ∩ Q.verts).Nonempty`. -/
lemma exists_walk_webAuxGraph_of_path {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : VertexWeb G A B)
    {i₁ i₂ : Fin m} {Q : GM01.Path V} (hQ_le : Q.toSubgraph ≤ webSubgraph A B)
    (hfirst : Q.first ∈ (A i₁).verts) (hlast : Q.last ∈ (A i₂).verts) :
    ∃ w : (webAuxGraph A B).Walk i₁ i₂, ∀ r ∈ w.support, ((A r).verts ∩ Q.verts).Nonempty := by
  classical
  suffices h : ∀ (L_len : ℕ) {i₁ i₂ : Fin m} (Q : GM01.Path V),
      Q.walk.length ≤ L_len → Q.toSubgraph ≤ webSubgraph A B →
      Q.first ∈ (A i₁).verts → Q.last ∈ (A i₂).verts →
      ∃ w : (webAuxGraph A B).Walk i₁ i₂, ∀ r ∈ w.support, ((A r).verts ∩ Q.verts).Nonempty from
    h Q.walk.length Q le_rfl hQ_le hfirst hlast
  intro L_len
  induction L_len with
  | zero =>
    intro i₁ i₂ Q hlen _ hfirst hlast
    have hfeq : Q.first = Q.last := Walk.eq_of_length_eq_zero (Nat.le_zero.1 hlen)
    have hii : i₁ = i₂ := by
      by_contra hne
      exact Set.disjoint_left.1 (hweb.disjoint_left hne) hfirst (hfeq ▸ hlast)
    subst hii
    refine ⟨.nil, ?_⟩
    simp only [Walk.support_nil, List.mem_singleton, forall_eq]
    exact ⟨Q.first, hfirst, Q.first_mem_verts⟩
  | succ L_len ih =>
    intro i₁ i₂ Q hlen hQ_le hfirst hlast
    by_cases hii : i₁ = i₂
    · subst hii
      refine ⟨.nil, ?_⟩
      simp only [Walk.support_nil, List.mem_singleton, forall_eq]
      exact ⟨Q.first, hfirst, Q.first_mem_verts⟩
    · let S_other : Set V := ⋃ s ≠ i₁, (A s).verts
      have hQ_other : (Q.verts ∩ S_other).Nonempty :=
        ⟨Q.last, Q.last_mem_verts, Set.mem_biUnion (Ne.symm hii) hlast⟩
      obtain ⟨v, ⟨hvQ, hv_other⟩, hv_first⟩ := Q.exists_first_mem hQ_other
      obtain ⟨i', _, hi'_ne, hvAi'⟩ : ∃ i' ∈ Set.univ, i' ≠ i₁ ∧ v ∈ (A i').verts := by
        simpa [S_other] using hv_other
      let Q₁ := Q.takeUntil v hvQ
      have hQ₁_A₁ : (Q₁.verts ∩ (A i₁).verts).Nonempty :=
        ⟨Q.first, by rw [← Q.takeUntil_first hvQ]; exact Q₁.first_mem_verts, hfirst⟩
      obtain ⟨u, ⟨huQ₁, huAi₁⟩, hu_last⟩ := Q₁.exists_last_mem hQ₁_A₁
      let P := Q₁.dropUntil u huQ₁
      have hP_le : P.toSubgraph ≤ webSubgraph A B :=
        ((Q₁.dropUntil_toSubgraph_le huQ₁).trans (Q.takeUntil_toSubgraph_le hvQ)).trans hQ_le
      have hP_int : Disjoint P.internalVerts (⋃ s, (A s).verts) := by
        rw [Set.disjoint_left]
        rintro z ⟨hzP, hz_ends⟩ hz_union
        obtain ⟨s, hzAs⟩ := Set.mem_iUnion.1 hz_union
        have hzQ₁ : z ∈ Q₁.verts := Q₁.dropUntil_verts_subset huQ₁ hzP
        have hzQ : z ∈ Q.verts := Q.takeUntil_verts_subset hvQ hzQ₁
        have hzu : z ≠ u := fun h ↦ hz_ends (Or.inl h)
        have hzv : z ≠ v := fun h ↦ hz_ends (Or.inr h)
        by_cases hs : s = i₁
        · subst hs
          have hprec : Q₁.Precedes u z :=
            ((Q₁.mem_dropUntil_verts_iff huQ₁).1 hzP).2.resolve_right hzu
          rcases hu_last z ⟨hzQ₁, hzAs⟩ with rfl | hzu'
          · exact hzu rfl
          · exact hprec.asymm hzu'
        · have hprec : Q.Precedes z v :=
            ((Q.mem_takeUntil_verts_iff hvQ).1 hzQ₁).2.resolve_right hzv
          have hz_other : z ∈ Q.verts ∩ S_other := ⟨hzQ, Set.mem_biUnion hs hzAs⟩
          rcases hv_first z hz_other with rfl | hvz
          · exact hzv rfl
          · exact hprec.asymm hvz
      have hadj : (webAuxGraph A B).Adj i₁ i' :=
        webAuxGraph_adj_of_direct_path hweb hi'_ne.symm hP_le huAi₁ hvAi' hP_int
      let Q₂ := Q.dropUntil v hvQ
      have hv_ne_first : v ≠ Q.first := fun h ↦
        Set.disjoint_left.1 (hweb.disjoint_left hi'_ne) hvAi' (h ▸ hfirst)
      have hQ₂_len : Q₂.walk.length ≤ L_len := by
        have hsum : (Q.takeUntil v hvQ).walk.length + (Q.dropUntil v hvQ).walk.length =
            Q.walk.length := by
          have := congrArg Walk.length (Q.walk.take_spec (Q.mem_verts_iff.1 hvQ))
          rwa [Walk.length_append] at this
        have hpos : 0 < (Q.takeUntil v hvQ).walk.length := by
          by_contra! h0
          have heq := Walk.eq_of_length_eq_zero (Nat.le_zero.1 h0)
          exact hv_ne_first heq.symm
        change (Q.dropUntil v hvQ).walk.length ≤ L_len
        omega
      obtain ⟨w₂, hw₂⟩ := ih Q₂ hQ₂_len ((Q.dropUntil_toSubgraph_le hvQ).trans hQ_le) hvAi' hlast
      refine ⟨.cons hadj w₂, ?_⟩
      intro r hr
      rw [Walk.support_cons, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact ⟨Q.first, hfirst, Q.first_mem_verts⟩
      · obtain ⟨x, hxAr, hxQ₂⟩ := hw₂ r hr
        exact ⟨x, hxAr, Q.dropUntil_verts_subset hvQ hxQ₂⟩

/-- If `(A, B)` is an `(m, n)`-web in `G` with `0 < m` and `0 < n`, then `webAuxGraph A B` is
connected. -/
lemma webAuxGraph_connected {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → GM01.Path V} {B : Fin n → GM01.Path V} (hweb : VertexWeb G A B)
    (hm : 0 < m) (hn : 0 < n) : (webAuxGraph A B).Connected := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  refine ⟨fun i₁ i₂ ↦ ?_⟩
  let j₀ : Fin n := ⟨0, hn⟩
  obtain ⟨u, huA, huB⟩ := hweb.meets i₁ j₀
  obtain ⟨v, hvA, hvB⟩ := hweb.meets i₂ j₀
  have hB_le : (B j₀).toSubgraph ≤ webSubgraph A B :=
    le_sup_of_le_right (le_iSup (fun j ↦ (B j).toSubgraph) j₀)
  rcases (B j₀).precedes_or_eq_or_precedes huB hvB with hprec | heq | hprec
  · let Q := (B j₀).subpath u v huB hvB (Or.inl hprec)
    obtain ⟨w, _⟩ := exists_walk_webAuxGraph_of_path hweb
      (((B j₀).subpath_toSubgraph_le huB hvB (Or.inl hprec)).trans hB_le) huA hvA
    exact ⟨w⟩
  · subst heq
    let Q := (B j₀).subpath u u huB huB (Or.inr rfl)
    obtain ⟨w, _⟩ := exists_walk_webAuxGraph_of_path hweb
      (((B j₀).subpath_toSubgraph_le huB huB (Or.inr rfl)).trans hB_le) huA hvA
    exact ⟨w⟩
  · let Q := ((B j₀).subpath v u hvB huB (Or.inl hprec)).reverse
    have hQ_le : Q.toSubgraph ≤ webSubgraph A B := by
      rw [GM01.Path.reverse_toSubgraph]
      exact (((B j₀).subpath_toSubgraph_le hvB huB (Or.inl hprec)).trans hB_le)
    obtain ⟨w, _⟩ := exists_walk_webAuxGraph_of_path hweb hQ_le huA hvA
    exact ⟨w⟩

/-! ### Component count for unions of paths -/

/-- For any subset `Y ⊆ Fin m`, the subgraph `⨆ r ∈ Y, (A r).toSubgraph` has at most `Y.ncard`
connected components. -/
lemma numComponents_biSup_path_le {m : ℕ} (A : Fin m → GM01.Path V) (Y : Set (Fin m)) :
    numComponents (⨆ r ∈ Y, (A r).toSubgraph) ≤ Y.ncard := by
  classical
  let D : (⊤ : SimpleGraph V).Subgraph := ⨆ r ∈ Y, (A r).toSubgraph
  have hfirst_mem : ∀ r : ↥Y, (A r.1).first ∈ D.verts := by
    intro r
    simp only [D, Subgraph.verts_iSup, Set.mem_iUnion]
    exact ⟨r.1, r.2, (A r.1).first_mem_verts⟩
  let f : ↥Y → D.coe.ConnectedComponent := fun r ↦
    D.coe.connectedComponentMk ⟨(A r.1).first, hfirst_mem r⟩
  have hf_surj : Function.Surjective f := by
    intro c
    induction c using ConnectedComponent.ind with | h v =>
    have hv : v.1 ∈ D.verts := v.2
    simp only [D, Subgraph.verts_iSup, Set.mem_iUnion] at hv
    obtain ⟨r, hrY, hvAr⟩ := hv
    refine ⟨⟨r, hrY⟩, ?_⟩
    apply ConnectedComponent.eq.2
    have hle : (A r).toSubgraph ≤ D := le_biSup (fun i ↦ (A i).toSubgraph) hrY
    obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph (A r).toSubgraph).1
      (A r).connected_toSubgraph).2 (A r).first_mem_verts hvAr
    have hpD : p.toSubgraph ≤ D := hp.trans hle
    have haux : ∀ {a b : V} (q : (⊤ : SimpleGraph V).Walk a b) (hq : q.toSubgraph ≤ D)
        (ha : a ∈ D.verts) (hb : b ∈ D.verts),
        D.coe.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b q hq ha hb
      induction q with
      | nil => exact Reachable.refl _
      | @cons a x b _ rest ih =>
        rw [Walk.toSubgraph, sup_le_iff] at hq
        have hadjD : D.Adj a x := hq.1.2 (by simp)
        have hxD : x ∈ D.verts := D.edge_vert hadjD.symm
        exact (Adj.reachable hadjD).trans (ih hq.2 hxD hb)
    exact haux p hpD (hfirst_mem ⟨r, hrY⟩) v.2
  have hcard := Nat.card_le_card_of_surjective f hf_surj
  rwa [Nat.card_coe_set_eq] at hcard

/-! ### Arithmetic inequalities for Case 1 of (4.4) -/

private lemma two_mul_le_two_pow {k : ℕ} (hk : 3 ≤ k) : 2 * k ≤ 2 ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  clear hk
  induction d with
  | zero => decide
  | succ d ih =>
    have hpos : 2 ≤ 2 ^ (3 + d) := by
      have : 2 ^ 1 ≤ 2 ^ (3 + d) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using this
    calc
      2 * (3 + (d + 1)) = 2 * (3 + d) + 2 := by ring
      _ ≤ 2 ^ (3 + d) + 2 ^ (3 + d) := by omega
      _ = 2 ^ (3 + (d + 1)) := by ring

private lemma θ_pow_two_mul_θ_le {θ : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) :
    θ ^ (2 * θ) ≤ 2 ^ (θ ^ 2) := by
  obtain ⟨k, hk⟩ := heven
  have hθ_eq : θ = 2 * k := by omega
  have hk3 : 3 ≤ k := by omega
  have hle : θ ≤ 2 ^ k := by
    rw [hθ_eq]
    exact two_mul_le_two_pow hk3
  calc
    θ ^ (2 * θ) ≤ (2 ^ k) ^ (2 * θ) := Nat.pow_le_pow_left hle (2 * θ)
    _ = 2 ^ (k * (2 * θ)) := (Nat.pow_mul 2 k (2 * θ)).symm
    _ = 2 ^ (θ ^ 2) := by
      congr 1
      rw [hθ_eq]
      ring

private lemma four_mul_le_two_pow_half_sq {θ d : ℕ} (hθ : 6 ≤ θ) (hd : 1 ≤ d) :
    4 * d ≤ 2 ^ (d * θ ^ 2 / 2) := by
  have hlt : d < 2 ^ d := Nat.lt_two_pow_self
  have h4d : 4 * d ≤ 2 ^ (d + 2) := by
    have : 2 ^ (d + 2) = 4 * 2 ^ d := by ring
    omega
  have h36 : 36 ≤ θ ^ 2 := by
    have := Nat.mul_le_mul hθ hθ
    rw [sq]
    omega
  have hexp : d + 2 ≤ d * θ ^ 2 / 2 := by
    have : 36 * d ≤ d * θ ^ 2 := by
      rw [mul_comm 36 d]
      exact Nat.mul_le_mul_left d h36
    omega
  exact h4d.trans (Nat.pow_le_pow_right (by decide) hexp)

/-- First arithmetic bound in Case 1 of Graph Minors V, (4.4) (page 99):
for `n = p + q + p 2^{p θ²}`, `n < (p - 1) θ² / 2` is false. -/
lemma theorem_4_4_arith_left {θ p q : ℕ} (hp : 1 ≤ p) :
    ¬ (p + q + p * 2 ^ (p * θ ^ 2) < (p - 1) * θ ^ 2 / 2) := by
  have h1 : p * θ ^ 2 < 2 ^ (p * θ ^ 2) := Nat.lt_two_pow_self
  have h2 : (p - 1) * θ ^ 2 / 2 ≤ p * θ ^ 2 := by
    have : (p - 1) * θ ^ 2 ≤ p * θ ^ 2 := Nat.mul_le_mul_right (θ ^ 2) (by omega)
    omega
  have h3 : p * θ ^ 2 ≤ p * 2 ^ (p * θ ^ 2) := by
    calc
      p * θ ^ 2 ≤ 1 * (p * θ ^ 2) := by omega
      _ ≤ p * 2 ^ (p * θ ^ 2) := Nat.mul_le_mul hp (Nat.le_of_lt h1)
  omega

/-- Second arithmetic bound in Case 1 of Graph Minors V, (4.4) (page 99):
for `m' = 2^{p θ²}`, `m' < 2^{(p - 1) θ² / 2} (θ² + 2 (p - 1) θ^{2 θ})` is false. -/
lemma theorem_4_4_arith_right {θ p : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hp : 2 ≤ p) :
    ¬ (2 ^ (p * θ ^ 2) < 2 ^ ((p - 1) * θ ^ 2 / 2) * (θ ^ 2 + 2 * (p - 1) * θ ^ (2 * θ))) := by
  push Not
  set d := p - 1
  have hd : 1 ≤ d := by omega
  have hθ_sq_le : θ ^ 2 ≤ 2 * d * θ ^ (2 * θ) := by
    have hpow : θ ^ 2 ≤ θ ^ (2 * θ) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 * θ ^ 2 ≤ (2 * d) * θ ^ (2 * θ) := Nat.mul_le_mul (by omega) hpow
    simpa using h1
  have hsum_le : θ ^ 2 + 2 * d * θ ^ (2 * θ) ≤ 4 * d * θ ^ (2 * θ) :=
    calc
      θ ^ 2 + 2 * d * θ ^ (2 * θ) ≤ 2 * d * θ ^ (2 * θ) + 2 * d * θ ^ (2 * θ) :=
        Nat.add_le_add_right hθ_sq_le _
      _ = 4 * d * θ ^ (2 * θ) := by ring
  have h4d_le : 4 * d ≤ 2 ^ (d * θ ^ 2 / 2) := four_mul_le_two_pow_half_sq hθ hd
  have hθ_pow_le : θ ^ (2 * θ) ≤ 2 ^ (θ ^ 2) := θ_pow_two_mul_θ_le hθ heven
  have hprod_le :
      θ ^ 2 + 2 * d * θ ^ (2 * θ) ≤ 2 ^ (d * θ ^ 2 / 2) * 2 ^ (θ ^ 2) :=
    hsum_le.trans (Nat.mul_le_mul h4d_le hθ_pow_le)
  have hexp_le : (d * θ ^ 2 / 2) + ((d * θ ^ 2 / 2) + θ ^ 2) ≤ p * θ ^ 2 := by
    have hp_eq : p * θ ^ 2 = d * θ ^ 2 + θ ^ 2 := by
      have : p = d + 1 := by omega
      rw [this, Nat.add_one_mul]
    omega
  calc
    2 ^ (d * θ ^ 2 / 2) * (θ ^ 2 + 2 * d * θ ^ (2 * θ))
      ≤ 2 ^ (d * θ ^ 2 / 2) * (2 ^ (d * θ ^ 2 / 2) * 2 ^ (θ ^ 2)) :=
        Nat.mul_le_mul_left _ hprod_le
    _ = 2 ^ ((d * θ ^ 2 / 2) + ((d * θ ^ 2 / 2) + θ ^ 2)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
    _ ≤ 2 ^ (p * θ ^ 2) := Nat.pow_le_pow_right (by decide) hexp_le

end GraphMinor.GM05
