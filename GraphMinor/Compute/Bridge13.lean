module

public import GraphMinor.GM13.Section2
public import GraphMinor.GM13.Section6
public import GraphMinor.GM13.Section8
public import GraphMinor.Compute.FolioStatement
public import GraphMinor.Compute.Algorithm81Aux
public import GraphMinor.Compute.Algorithm64

/-!
# Bridge Between `GraphMinor.Compute` and `GraphMinor.GM13`

This file connects the Word RAM algorithmic representations in `GraphMinor.Compute` to the
mathematical definitions and theorems of Graph Minors IX and XIII (`GraphMinor.GM09`,
`GraphMinor.GM13`):

1. **Societies and Crosses (`Alg81Input.toSociety`, `hasCrossInSociety_iff_hasCross`):**
   - Converts a duplicate-free list `L : List α` into a `GM09.CyclicPerm α`
     (`cyclicPermOfNodupList`), and an `Alg81Input` `(G, omega)` into a society
     `x.toSociety : GM09.Society (Fin x.n) (Sym2 (Fin x.n))`.
   - Proves that `CrossesInOmega x.omega p₁ q₁ p₂ q₂` is equivalent to
     `x.toSociety.Ω.Crosses p₁ p₂ q₁ q₂`, that a valid `CrossWitness` yields a cross
     `x.toSociety.IsCross P Q`, and that `HasCrossInSociety x.G x.omega` is equivalent to
     `GM13.HasCross x.toSociety`.
2. **Graphs and Subgraphs (`SimpleGraph.toGMGraph`, `graphOfFinsetSimpleGraph`,
   `MultiDigraph.toGMGraph`):**
   - Converts `SimpleGraph (Fin n)`, induced subgraphs `(Z, C)`, and `MultiDigraph n` into
     `Graph (Fin n) (Sym2 (Fin n))`.
3. **Digraphs and Folios (`MultiDigraph.toGMDigraph`, `MultiDigraph.toEmbeddedGMDigraph`,
   `isDeltaFolioRep_iff_hasSameDeltaFolio`, `isIrrelevantVertex_iff_isDeltaFolioRep`):**
   - Converts `MultiDigraph n` (and vertex-embedded subdigraphs `emb : Fin n' → Fin n`) into
     `GM13.Digraph (Fin n) (Fin n × Fin n × ℕ)`.
   - Proves that `dp`'s `δ`-folio representation `IsDeltaFolioRep` (`FolioStatement.lean`) is
     equivalent to `GM13`'s `InDeltaFolio`, `HasSameDeltaFolio`, `HasSameDeltaFolioRel`, and
     `IsIrrelevantVertex`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM13

/-! ## Section 1: Graphs, Cyclic Permutations, Societies, and Crosses -/

/-- Turn a `SimpleGraph α` into a `Graph α (Sym2 α)`. -/
abbrev _root_.SimpleGraph.toGMGraph {α : Type*} (G : SimpleGraph α) : Graph α (Sym2 α) :=
  Graph.ofSimpleGraph G

/-- Turn a pair `(Z, C)` of a vertex finset `Z : Finset α` and a `SimpleGraph α` into the induced
`Graph α (Sym2 α)` with vertex set `Z`. -/
def graphOfFinsetSimpleGraph {α : Type*} (Z : Finset α) (C : SimpleGraph α) : Graph α (Sym2 α) :=
  (Graph.ofSimpleGraph C).induce (Z : Set α)

@[simp]
theorem vertexSet_graphOfFinsetSimpleGraph {α : Type*} (Z : Finset α) (C : SimpleGraph α) :
    V(graphOfFinsetSimpleGraph Z C) = (Z : Set α) := rfl

theorem graphOfFinsetSimpleGraph_isLink {α : Type*} (Z : Finset α) (C : SimpleGraph α)
    {e : Sym2 α} {u v : α} :
    (graphOfFinsetSimpleGraph Z C).IsLink e u v ↔
      (e = s(u, v) ∧ C.Adj u v) ∧ u ∈ Z ∧ v ∈ Z := by
  simp only [graphOfFinsetSimpleGraph, Graph.induce_isLink, Graph.ofSimpleGraph_isLink,
    Finset.mem_coe]
  constructor
  · rintro ⟨⟨rfl, he⟩, hu, hv⟩
    exact ⟨⟨rfl, C.mem_edgeSet.mp he⟩, hu, hv⟩
  · rintro ⟨⟨rfl, hadj⟩, hu, hv⟩
    exact ⟨⟨rfl, C.mem_edgeSet.mpr hadj⟩, hu, hv⟩

theorem graphOfFinsetSimpleGraph_adj {α : Type*} (Z : Finset α) (C : SimpleGraph α)
    {u v : α} :
    (graphOfFinsetSimpleGraph Z C).Adj u v ↔ C.Adj u v ∧ u ∈ Z ∧ v ∈ Z := by
  constructor
  · rintro ⟨e, hl⟩
    rw [graphOfFinsetSimpleGraph_isLink] at hl
    exact ⟨hl.1.2, hl.2.1, hl.2.2⟩
  · rintro ⟨hadj, hu, hv⟩
    exact ⟨s(u, v), (graphOfFinsetSimpleGraph_isLink Z C).mpr ⟨⟨rfl, hadj⟩, hu, hv⟩⟩

theorem isSimpleGraph_ofSimpleGraph {α : Type*} (C : SimpleGraph α) :
    IsSimpleGraph (Graph.ofSimpleGraph C) := by
  refine ⟨fun e _ v hl => ?_, fun e₁ _ e₂ _ u v hl₁ hl₂ => ?_⟩
  · rw [Graph.ofSimpleGraph_isLink] at hl
    rcases hl with ⟨rfl, he⟩
    exact C.loopless.irrefl v (C.mem_edgeSet.mp he)
  · rw [Graph.ofSimpleGraph_isLink] at hl₁ hl₂
    exact hl₁.1.trans hl₂.1.symm

theorem isSimpleGraph_graphOfFinsetSimpleGraph {α : Type*} (Z : Finset α) (C : SimpleGraph α) :
    IsSimpleGraph (graphOfFinsetSimpleGraph Z C) :=
  IsSimpleGraph.mono (isSimpleGraph_ofSimpleGraph C) ((Graph.ofSimpleGraph C).induce_le (subset_univ _))

/-- Turn a `MultiDigraph n` into its underlying undirected simple `Graph (Fin n) (Sym2 (Fin n))`. -/
def MultiDigraph.toGMGraph {n : ℕ} (G : MultiDigraph n) : Graph (Fin n) (Sym2 (Fin n)) :=
  Graph.ofSimpleGraph G.toSimpleGraph

/-- Lift a `SimpleGraph.Walk` on `G` to a `GraphWalk` on `Graph.ofSimpleGraph G`. -/
def _root_.SimpleGraph.Walk.toGraphWalk {α : Type*} {G : SimpleGraph α} {u v : α} :
    G.Walk u v → GraphWalk (Graph.ofSimpleGraph G) u v
  | .nil => .nil (Set.mem_univ u)
  | @SimpleGraph.Walk.cons _ _ u w _ h rest =>
      .cons (e := s(u, w)) ⟨rfl, G.mem_edgeSet.mpr h⟩ rest.toGraphWalk

@[simp]
theorem _root_.SimpleGraph.Walk.support_toGraphWalk {α : Type*} {G : SimpleGraph α} {u v : α}
    (W : G.Walk u v) : W.toGraphWalk.support = W.support := by
  induction W with
  | nil => rfl
  | cons _ _ ih =>
    change _ :: _ = _ :: _
    rw [ih]

theorem _root_.SimpleGraph.Walk.isSimple_toGraphWalk {α : Type*} {G : SimpleGraph α} {u v : α}
    {W : G.Walk u v} (hW : W.IsPath) : W.toGraphWalk.IsSimple := by
  unfold GraphWalk.IsSimple
  rw [W.support_toGraphWalk]
  exact hW.support_nodup

/-- Project a `GraphWalk` on `Graph.ofSimpleGraph G` to a `SimpleGraph.Walk` on `G`. -/
def _root_.GraphMinor.Surface.GraphWalk.toSimpleGraphWalk
    {α : Type*} {G : SimpleGraph α} {u v : α} :
    GraphWalk (Graph.ofSimpleGraph G) u v → G.Walk u v
  | .nil _ => .nil
  | .cons h rest => .cons (G.mem_edgeSet.mp (h.1 ▸ h.2)) rest.toSimpleGraphWalk

@[simp]
theorem _root_.GraphMinor.Surface.GraphWalk.support_toSimpleGraphWalk
    {α : Type*} {G : SimpleGraph α} {u v : α}
    (W : GraphWalk (Graph.ofSimpleGraph G) u v) :
    W.toSimpleGraphWalk.support = W.support := by
  induction W with
  | nil _ => rfl
  | cons _ _ ih =>
    change _ :: _ = _ :: _
    rw [ih]

theorem _root_.GraphMinor.Surface.GraphWalk.isPath_toSimpleGraphWalk
    {α : Type*} {G : SimpleGraph α} {u v : α}
    {W : GraphWalk (Graph.ofSimpleGraph G) u v} (hW : W.IsSimple) :
    W.toSimpleGraphWalk.IsPath := by
  rw [SimpleGraph.Walk.isPath_def, W.support_toSimpleGraphWalk]
  exact hW

/-- Build a `GM09.CyclicPerm α` from any duplicate-free list `L : List α`. -/
noncomputable def cyclicPermOfNodupList {α : Type*} (L : List α) (hnd : L.Nodup) :
    GM09.CyclicPerm α :=
  if hne : L = [] then
    { bar := ∅
      finite_bar := Set.finite_empty
      toFun := id
      bijOn := Set.bijOn_empty id
      single_orbit := fun _ hx => False.elim hx }
  else
    GM09.CyclicPerm.ofNodupList L hnd hne

@[simp]
theorem bar_cyclicPermOfNodupList {α : Type*} (L : List α) (hnd : L.Nodup) :
    (cyclicPermOfNodupList L hnd).bar = {x | x ∈ L} := by
  unfold cyclicPermOfNodupList
  split_ifs with hne
  · subst hne
    ext x
    simp
  · rfl

/-- Turn an `Alg81Input` `(G, omega)` into a `GM09.Society (Fin x.n) (Sym2 (Fin x.n))`. -/
noncomputable def Alg81Input.toSociety (x : Alg81Input) :
    GM09.Society (Fin x.n) (Sym2 (Fin x.n)) where
  G := Graph.ofSimpleGraph x.G
  Ω := cyclicPermOfNodupList x.omega x.nodup_omega
  bar_subset := fun _ _ => Set.mem_univ _
  finite_V := Set.toFinite _
  finite_E := Set.toFinite _

@[simp]
theorem Alg81Input.toSociety_G (x : Alg81Input) :
    x.toSociety.G = Graph.ofSimpleGraph x.G := rfl

@[simp]
theorem Alg81Input.toSociety_bar (x : Alg81Input) :
    x.toSociety.Ω.bar = {v : Fin x.n | v ∈ x.omega} :=
  bar_cyclicPermOfNodupList x.omega x.nodup_omega

theorem crosses_mem_and_ne {α : Type*} {Ω : GM09.CyclicPerm α} {p₁ p₂ q₁ q₂ : α}
    (hcr : Ω.Crosses p₁ p₂ q₁ q₂) :
    p₁ ∈ Ω.bar ∧ p₂ ∈ Ω.bar ∧ q₁ ∈ Ω.bar ∧ q₂ ∈ Ω.bar ∧ p₁ ≠ p₂ ∧ q₁ ≠ q₂ := by
  rcases hcr with h | h
  · obtain ⟨_, h13, _, _, h24, _, hv₁, hv₂, hv₃, hv₄, _⟩ := Ω.isClockwise4_iff.mp h
    exact ⟨hv₁, hv₃, hv₂, hv₄, h13, h24⟩
  · obtain ⟨_, h13, _, _, h24, _, hv₁, hv₂, hv₃, hv₄, _⟩ := Ω.isClockwise4_iff.mp h
    exact ⟨hv₄, hv₂, hv₃, hv₁, h24.symm, h13.symm⟩

/-- Equivalence between `CrossesInOmega` and `GM09.CyclicPerm.Crosses` on `cyclicPermOfNodupList`. -/
theorem crossesInOmega_iff_crosses {n : ℕ} (omega : List (Fin n)) (hnd : omega.Nodup)
    (p₁ q₁ p₂ q₂ : Fin n) :
    CrossesInOmega omega p₁ q₁ p₂ q₂ ↔
      (cyclicPermOfNodupList omega hnd).Crosses p₁ p₂ q₁ q₂ := by
  constructor
  · rintro ⟨i₁, i₂, i₃, i₄, h₁, h₂, h₃, h₄, hcases⟩
    have hi₁ : i₁ < omega.length := by omega
    have hi₂ : i₂ < omega.length := by omega
    have hi₃ : i₃ < omega.length := by omega
    have hne : omega ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hi₁)
    unfold cyclicPermOfNodupList
    simp only [hne, ↓reduceDIte]
    have h13 : i₁ < i₃ := by omega
    have h24 : i₂ < i₄ := by omega
    have hcr1 : (GM09.CyclicPerm.ofNodupList omega hnd hne).Crosses
        omega[i₁] omega[i₃] omega[i₂] omega[i₄] :=
      (GM09.CyclicPerm.ofNodupList_crosses_iff omega hnd hne h13 hi₃ h24 h₄).mpr
        (Or.inl ⟨h₁, h₂, h₃⟩)
    have hcr2 : (GM09.CyclicPerm.ofNodupList omega hnd hne).Crosses
        omega[i₂] omega[i₄] omega[i₁] omega[i₃] :=
      hcr1.symm
    rcases hcases with
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ |
      ⟨⟨rfl, rfl⟩ | ⟨rfl, rfl⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hcr1
    · exact hcr1.swap_right
    · exact hcr1.swap_left
    · exact hcr1.swap_left.swap_right
    · exact hcr2
    · exact hcr2.swap_left
    · exact hcr2.swap_right
    · exact hcr2.swap_left.swap_right
  · intro hcr
    have hmem_ne := crosses_mem_and_ne hcr
    rw [bar_cyclicPermOfNodupList] at hmem_ne
    rcases hmem_ne with ⟨hp₁, hp₂, hq₁, hq₂, hp_ne, hq_ne⟩
    rcases List.mem_iff_getElem.mp hp₁ with ⟨i₁, hi₁, rfl⟩
    rcases List.mem_iff_getElem.mp hp₂ with ⟨j₁, hj₁, rfl⟩
    rcases List.mem_iff_getElem.mp hq₁ with ⟨i₂, hi₂, rfl⟩
    rcases List.mem_iff_getElem.mp hq₂ with ⟨j₂, hj₂, rfl⟩
    have hne : omega ≠ [] := List.ne_nil_of_length_pos (Nat.zero_lt_of_lt hi₁)
    unfold cyclicPermOfNodupList at hcr
    simp only [hne, ↓reduceDIte] at hcr
    have hne1 : i₁ ≠ j₁ := fun h => hp_ne (by subst h; rfl)
    have hne2 : i₂ ≠ j₂ := fun h => hq_ne (by subst h; rfl)
    rcases Nat.lt_or_gt_of_ne hne1 with hlt1 | hgt1 <;>
      rcases Nat.lt_or_gt_of_ne hne2 with hlt2 | hgt2
    · rcases (GM09.CyclicPerm.ofNodupList_crosses_iff omega hnd hne hlt1 hj₁ hlt2 hj₂).mp
        hcr with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨i₁, i₂, j₁, j₂, h1, h2, h3, hj₂, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨i₂, i₁, j₂, j₁, h1, h2, h3, hj₁, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rcases (GM09.CyclicPerm.ofNodupList_crosses_iff omega hnd hne hlt1 hj₁ hgt2 hi₂).mp
        hcr.swap_right with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨i₁, j₂, j₁, i₂, h1, h2, h3, hi₂, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact ⟨j₂, i₁, i₂, j₁, h1, h2, h3, hj₁, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
    · rcases (GM09.CyclicPerm.ofNodupList_crosses_iff omega hnd hne hgt1 hi₁ hlt2 hj₂).mp
        hcr.swap_left with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨j₁, i₂, i₁, j₂, h1, h2, h3, hj₂, Or.inl ⟨Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩⟩
      · exact ⟨i₂, j₁, j₂, i₁, h1, h2, h3, hi₁, Or.inr ⟨Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
    · rcases (GM09.CyclicPerm.ofNodupList_crosses_iff omega hnd hne hgt1 hi₁ hgt2 hi₂).mp
        hcr.swap_left.swap_right with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · exact ⟨j₁, j₂, i₁, i₂, h1, h2, h3, hi₂, Or.inl ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩
      · exact ⟨j₂, j₁, i₂, i₁, h1, h2, h3, hi₁, Or.inr ⟨Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩⟩

/-- First path subgraph `P` of a `CrossWitness c` in `Graph.ofSimpleGraph G`. -/
noncomputable def CrossWitness.toGraphP {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (c : CrossWitness G omega) : Graph (Fin n) (Sym2 (Fin n)) :=
  GM09.walkSubgraph c.P.toGraphWalk

/-- Second path subgraph `Q` of a `CrossWitness c` in `Graph.ofSimpleGraph G`. -/
noncomputable def CrossWitness.toGraphQ {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (c : CrossWitness G omega) : Graph (Fin n) (Sym2 (Fin n)) :=
  GM09.walkSubgraph c.Q.toGraphWalk

/-- Every valid `CrossWitness` for `(x.G, x.omega)` yields a cross `(c.toGraphP, c.toGraphQ)`
in `x.toSociety`. -/
theorem CrossWitness.isCross_of_isValid (x : Alg81Input) {c : CrossWitness x.G x.omega}
    (hc : c.IsValid) :
    x.toSociety.IsCross c.toGraphP c.toGraphQ := by
  rcases hc with ⟨hP, hQ, hdisj, hcr⟩
  have hcr' : x.toSociety.Ω.Crosses c.p₁ c.p₂ c.q₁ c.q₂ :=
    (crossesInOmega_iff_crosses x.omega x.nodup_omega c.p₁ c.q₁ c.p₂ c.q₂).mp hcr
  obtain ⟨hp₁, hp₂, hq₁, hq₂, hp_ne, hq_ne⟩ := crosses_mem_and_ne hcr'
  refine ⟨?_, c.p₁, c.p₂, c.q₁, c.q₂, ?_, ?_, hcr'⟩
  · rw [Set.disjoint_left]
    intro v hv₁ hv₂
    rw [CrossWitness.toGraphP, GM09.vertexSet_walkSubgraph, mem_ofPred_eq,
      SimpleGraph.Walk.support_toGraphWalk] at hv₁
    rw [CrossWitness.toGraphQ, GM09.vertexSet_walkSubgraph, mem_ofPred_eq,
      SimpleGraph.Walk.support_toGraphWalk] at hv₂
    exact hdisj hv₁ hv₂
  · exact ⟨GM09.isGraphPathWithEnds_walkSubgraph (SimpleGraph.Walk.isSimple_toGraphWalk hP),
      hp_ne, hp₁, hp₂⟩
  · exact ⟨GM09.isGraphPathWithEnds_walkSubgraph (SimpleGraph.Walk.isSimple_toGraphWalk hQ),
      hq_ne, hq₁, hq₂⟩

/-- Equivalence between `Compute.HasCrossInSociety x.G x.omega` and `GM13.HasCross x.toSociety`. -/
theorem hasCrossInSociety_iff_hasCross (x : Alg81Input) :
    HasCrossInSociety x.G x.omega ↔ GM13.HasCross x.toSociety := by
  constructor
  · rintro ⟨p₁, p₂, q₁, q₂, P, Q, hcross⟩
    let c : CrossWitness x.G x.omega := ⟨p₁, p₂, q₁, q₂, P, Q⟩
    exact ⟨c.toGraphP, c.toGraphQ, c.isCross_of_isValid x hcross⟩
  · rintro ⟨P, Q, hdisj, p₁, p₂, q₁, q₂, ⟨hP, _, _, _⟩, ⟨hQ, _, _, _⟩, hcr⟩
    rcases hP with ⟨hP_le, W₁, hW₁_simple, hVP, _⟩
    rcases hQ with ⟨hQ_le, W₂, hW₂_simple, hVQ, _⟩
    rw [Alg81Input.toSociety_G] at hP_le hQ_le
    obtain ⟨W₁', hs₁, _⟩ := GM09.exists_walk_up_of_le hP_le W₁
    obtain ⟨W₂', hs₂, _⟩ := GM09.exists_walk_up_of_le hQ_le W₂
    have hW₁'_simple : W₁'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₁]; exact hW₁_simple
    have hW₂'_simple : W₂'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs₂]; exact hW₂_simple
    refine ⟨p₁, p₂, q₁, q₂, W₁'.toSimpleGraphWalk, W₂'.toSimpleGraphWalk,
      GraphWalk.isPath_toSimpleGraphWalk hW₁'_simple,
      GraphWalk.isPath_toSimpleGraphWalk hW₂'_simple, ?_,
      (crossesInOmega_iff_crosses x.omega x.nodup_omega p₁ q₁ p₂ q₂).mpr hcr⟩
    intro v hv₁ hv₂
    rw [GraphWalk.support_toSimpleGraphWalk, hs₁] at hv₁
    rw [GraphWalk.support_toSimpleGraphWalk, hs₂] at hv₂
    have hvP : v ∈ V(P) := by rw [hVP]; exact hv₁
    have hvQ : v ∈ V(Q) := by rw [hVQ]; exact hv₂
    exact Set.disjoint_left.mp hdisj hvP hvQ

/-! ## Section 2: Digraphs, Rooted Digraphs, and Folios -/

/-- Turn a `ComputeDigraph` into a `GM13.Digraph ℕ ℕ` on `{u | u < D.numVerts}` and
`{e | e < D.numEdges}`. -/
def ComputeDigraph.toGMDigraph (D : ComputeDigraph) : GM13.Digraph ℕ ℕ where
  vertexSet := {u : ℕ | u < D.numVerts}
  edgeSet := {e : ℕ | e < D.numEdges}
  head e := if h : e < D.numEdges then (D.head ⟨e, h⟩).1 else 0
  tail e := if h : e < D.numEdges then (D.tail ⟨e, h⟩).1 else 0
  head_mem e he := by
    simp only [mem_ofPred_eq] at he ⊢
    rw [dite_eq_left he]
    exact (D.head ⟨e, he⟩).2
  tail_mem e he := by
    simp only [mem_ofPred_eq] at he ⊢
    rw [dite_eq_left he]
    exact (D.tail ⟨e, he⟩).2

/-- Turn a `ComputeRootedDigraph q` into a `GM13.RootedDigraph ℕ ℕ q`. -/
def ComputeRootedDigraph.toGMRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    GM13.RootedDigraph ℕ ℕ q where
  digraph := H.digraph.toGMDigraph
  roots i := (H.roots i).1
  roots_mem i := (H.roots i).2

theorem ComputeDigraph.vertexSet_toGMDigraph_eq_coe_range (D : ComputeDigraph) :
    D.toGMDigraph.vertexSet = ↑(Finset.range D.numVerts) := by
  ext u
  simp [ComputeDigraph.toGMDigraph]

theorem ComputeDigraph.edgeSet_toGMDigraph_eq_coe_range (D : ComputeDigraph) :
    D.toGMDigraph.edgeSet = ↑(Finset.range D.numEdges) := by
  ext e
  simp [ComputeDigraph.toGMDigraph]

theorem ComputeDigraph.isFinite_toGMDigraph (D : ComputeDigraph) :
    D.toGMDigraph.IsFinite where
  finite_V := by
    rw [D.vertexSet_toGMDigraph_eq_coe_range]
    exact Finset.finite_toSet _
  finite_E := by
    rw [D.edgeSet_toGMDigraph_eq_coe_range]
    exact Finset.finite_toSet _

theorem ComputeRootedDigraph.isFinite_toGMRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    H.toGMRootedDigraph.digraph.IsFinite :=
  H.digraph.isFinite_toGMDigraph

theorem ComputeRootedDigraph.detail_toGMRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    H.toGMRootedDigraph.detail =
      max H.digraph.numEdges (Finset.univ \ H.rootFinset).card := by
  unfold GM13.RootedDigraph.detail
  have hE : H.toGMRootedDigraph.digraph.edgeSet.ncard = H.digraph.numEdges := by
    change H.digraph.toGMDigraph.edgeSet.ncard = H.digraph.numEdges
    rw [H.digraph.edgeSet_toGMDigraph_eq_coe_range, Set.ncard_coe_finset, Finset.card_range]
  have hV_eq : H.toGMRootedDigraph.digraph.vertexSet \ Set.range H.toGMRootedDigraph.roots =
      Fin.val '' ((Finset.univ \ H.rootFinset : Finset (Fin H.digraph.numVerts)) :
        Set (Fin H.digraph.numVerts)) := by
    ext u
    simp only [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
      ComputeRootedDigraph.rootFinset, mem_sdiff, mem_ofPred_eq, mem_range, not_exists,
      mem_image, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hu, hnot⟩
      refine ⟨⟨u, hu⟩, ?_, rfl⟩
      intro i hi
      exact hnot i (congrArg Fin.val hi)
    · rintro ⟨v, hnot, rfl⟩
      refine ⟨v.2, fun i hi => hnot i (Fin.ext hi)⟩
  have hV : (H.toGMRootedDigraph.digraph.vertexSet \ Set.range H.toGMRootedDigraph.roots).ncard =
      (Finset.univ \ H.rootFinset).card := by
    rw [hV_eq, Set.ncard_image_of_injective _ Fin.val_injective, Set.ncard_coe_finset]
  rw [hE, hV]

/-- Equivalence between `ComputeRootedDigraph.HasDetailLe δ` and
`GM13.RootedDigraph.detail ≤ δ`. -/
theorem ComputeRootedDigraph.hasDetailLe_iff_detail_le {q : ℕ} (δ : ℕ)
    (H : ComputeRootedDigraph q) :
    H.HasDetailLe δ ↔ H.toGMRootedDigraph.detail ≤ δ := by
  rw [ComputeRootedDigraph.HasDetailLe, H.detail_toGMRootedDigraph, Nat.max_le]

/-- Precomposing a `GM13.IsRootedDigraphModel` on the left with a rooted digraph isomorphism
`iso : GM13.RootedDigraph.Iso H₁ H₂`. -/
theorem isRootedDigraphModel_of_iso_left {α β α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {H₁ : GM13.RootedDigraph α₁ β₁ k} {H₂ : GM13.RootedDigraph α₂ β₂ k}
    {G : GM13.RootedDigraph α β k}
    {vMap : α₂ → GM13.Digraph α β} {eMap : β₂ → β}
    (iso : GM13.RootedDigraph.Iso H₁ H₂)
    (hM : GM13.IsRootedDigraphModel H₂ G vMap eMap) :
    GM13.IsRootedDigraphModel H₁ G (vMap ∘ iso.vMap) (eMap ∘ iso.eMap) where
  sub_of_mem _ hu := hM.sub_of_mem (iso.bijOn_v.mapsTo hu)
  connected_of_mem _ hu := hM.connected_of_mem (iso.bijOn_v.mapsTo hu)
  disjoint_of_ne _ _ hu hv hne :=
    hM.disjoint_of_ne (iso.bijOn_v.mapsTo hu) (iso.bijOn_v.mapsTo hv)
      (fun h => hne (iso.bijOn_v.injOn hu hv h))
  edge_mem _ he := hM.edge_mem (iso.bijOn_e.mapsTo he)
  head_tail_mem e he := by
    dsimp [Function.comp_def]
    rw [← iso.head_eq he, ← iso.tail_eq he]
    exact hM.head_tail_mem (iso.bijOn_e.mapsTo he)
  loop_not_mem e he hloop := by
    dsimp [Function.comp_def]
    rw [← iso.head_eq he]
    refine hM.loop_not_mem (iso.bijOn_e.mapsTo he) ?_
    rw [iso.head_eq he, iso.tail_eq he, hloop]
  eMap_injOn := hM.eMap_injOn.comp iso.bijOn_e.injOn iso.bijOn_e.mapsTo
  root_mem i := by
    dsimp [Function.comp_def]
    rw [iso.map_roots i]
    exact hM.root_mem i

theorem isRootedDigraphMinor_of_iso_left {α β α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {H₁ : GM13.RootedDigraph α₁ β₁ k} {H₂ : GM13.RootedDigraph α₂ β₂ k}
    {G : GM13.RootedDigraph α β k}
    (iso : GM13.RootedDigraph.Iso H₁ H₂)
    (h : GM13.IsRootedDigraphMinor H₂ G) :
    GM13.IsRootedDigraphMinor H₁ G := by
  rcases h with ⟨vMap, eMap, hM⟩
  exact ⟨vMap ∘ iso.vMap, eMap ∘ iso.eMap, isRootedDigraphModel_of_iso_left iso hM⟩

/-- Map a `GraphWalk` in `C.toGraph` along a digraph isomorphism `iso : GM13.Digraph.Iso G₁ G₂`
when `C.IsSubdigraph G₁`. -/
def mapWalkSubdigraphIso {α₁ β₁ α₂ β₂ : Type*}
    {G₁ C : GM13.Digraph α₁ β₁} {G₂ : GM13.Digraph α₂ β₂}
    (iso : GM13.Digraph.Iso G₁ G₂) (hC : C.IsSubdigraph G₁) :
    ∀ {u v : α₁}, GraphWalk C.toGraph u v →
      GraphWalk (G₂.subdigraphOf (iso.vMap '' C.vertexSet) (iso.eMap '' C.edgeSet)).toGraph
        (iso.vMap u) (iso.vMap v)
  | u, _, .nil hu =>
    .nil ⟨iso.bijOn_v.mapsTo (hC.vertexSet_subset hu), ⟨u, hu, rfl⟩⟩
  | u, _, @GraphWalk.cons _ _ _ _ z _ e hlink rest =>
    have heC : e ∈ C.edgeSet := hlink.1
    have heG₁ : e ∈ G₁.edgeSet := hC.edgeSet_subset heC
    have huC : u ∈ C.vertexSet := C.toGraph.left_mem_of_isLink hlink
    have hzC : z ∈ C.vertexSet := C.toGraph.left_mem_of_isLink hlink.symm
    have hlink' :
        (G₂.subdigraphOf (iso.vMap '' C.vertexSet) (iso.eMap '' C.edgeSet)).toGraph.IsLink
          (iso.eMap e) (iso.vMap u) (iso.vMap z) := by
      refine ⟨⟨⟨iso.bijOn_e.mapsTo heG₁, ⟨e, heC, rfl⟩⟩, ?_, ?_⟩, ?_⟩
      · rw [iso.head_eq heG₁, ← hC.head_eq heC]
        exact ⟨C.head e, C.head_mem heC, rfl⟩
      · rw [iso.tail_eq heG₁, ← hC.tail_eq heC]
        exact ⟨C.tail e, C.tail_mem heC, rfl⟩
      · change (G₂.head (iso.eMap e) = iso.vMap u ∧ G₂.tail (iso.eMap e) = iso.vMap z) ∨
          (G₂.head (iso.eMap e) = iso.vMap z ∧ G₂.tail (iso.eMap e) = iso.vMap u)
        rw [iso.head_eq heG₁, iso.tail_eq heG₁, ← hC.head_eq heC, ← hC.tail_eq heC]
        rcases hlink.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
    .cons hlink' (mapWalkSubdigraphIso iso hC rest)

/-- Postcomposing a `GM13.IsRootedDigraphModel` on the right with a rooted digraph isomorphism
`iso : GM13.RootedDigraph.Iso G₁ G₂`. -/
theorem isRootedDigraphMinor_of_iso_right {α₁ β₁ α₂ β₂ α' β' : Type*} {k : ℕ}
    {H : GM13.RootedDigraph α' β' k}
    {G₁ : GM13.RootedDigraph α₁ β₁ k} {G₂ : GM13.RootedDigraph α₂ β₂ k}
    (iso : GM13.RootedDigraph.Iso G₁ G₂)
    (h : GM13.IsRootedDigraphMinor H G₁) :
    GM13.IsRootedDigraphMinor H G₂ := by
  rcases h with ⟨vMap, eMap, hM⟩
  let vMap' (u : α') : GM13.Digraph α₂ β₂ :=
    G₂.digraph.subdigraphOf (iso.vMap '' (vMap u).vertexSet) (iso.eMap '' (vMap u).edgeSet)
  let eMap' (e : β') : β₂ := iso.eMap (eMap e)
  have hvMap'_V {u : α'} (hu : u ∈ H.digraph.vertexSet) :
      (vMap' u).vertexSet = iso.vMap '' (vMap u).vertexSet := by
    dsimp [vMap', GM13.Digraph.subdigraphOf]
    refine inter_eq_self_of_subset_right ?_
    rintro _ ⟨x, hx, rfl⟩
    exact iso.bijOn_v.mapsTo ((hM.sub_of_mem hu).vertexSet_subset hx)
  have hvMap'_E {u : α'} (hu : u ∈ H.digraph.vertexSet) :
      (vMap' u).edgeSet = iso.eMap '' (vMap u).edgeSet := by
    ext f
    simp only [vMap', GM13.Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
    constructor
    · exact fun hf => hf.1.2
    · rintro ⟨e, he, rfl⟩
      have hsub := hM.sub_of_mem hu
      have heG₁ : e ∈ G₁.digraph.edgeSet := hsub.edgeSet_subset he
      refine ⟨⟨iso.bijOn_e.mapsTo heG₁, ⟨e, he, rfl⟩⟩, ?_, ?_⟩
      · rw [iso.head_eq heG₁, ← hsub.head_eq he]
        exact ⟨(vMap u).head e, (vMap u).head_mem he, rfl⟩
      · rw [iso.tail_eq heG₁, ← hsub.tail_eq he]
        exact ⟨(vMap u).tail e, (vMap u).tail_mem he, rfl⟩
  refine ⟨vMap', eMap', {
    sub_of_mem := fun _ _ => G₂.digraph.subdigraphOf_isSubdigraph _ _
    connected_of_mem := fun u hu => by
      rcases hM.connected_of_mem hu with ⟨⟨x₀, hx₀⟩, hconn⟩
      refine ⟨⟨iso.vMap x₀, ?_⟩, fun x hx y hy => ?_⟩
      · rw [hvMap'_V hu]; exact ⟨x₀, hx₀, rfl⟩
      · rw [hvMap'_V hu] at hx hy
        rcases hx with ⟨x', hx', rfl⟩
        rcases hy with ⟨y', hy', rfl⟩
        rcases hconn x' hx' y' hy' with ⟨W⟩
        exact ⟨mapWalkSubdigraphIso iso.toIso (hM.sub_of_mem hu) W⟩
    disjoint_of_ne := fun u v hu hv hne => by
      rw [hvMap'_V hu, hvMap'_V hv, Set.disjoint_left]
      rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      have hxy : x = y :=
        iso.bijOn_v.injOn
          ((hM.sub_of_mem hu).vertexSet_subset hx)
          ((hM.sub_of_mem hv).vertexSet_subset hy) heq.symm
      subst hxy
      exact Set.disjoint_left.mp (hM.disjoint_of_ne hu hv hne) hx hy
    edge_mem := fun e he => iso.bijOn_e.mapsTo (hM.edge_mem he)
    head_tail_mem := fun e he => by
      have heG₁ := hM.edge_mem he
      have hht := hM.head_tail_mem he
      rw [hvMap'_V (H.digraph.head_mem he), hvMap'_V (H.digraph.tail_mem he)]
      dsimp [eMap']
      rw [iso.head_eq heG₁, iso.tail_eq heG₁]
      exact ⟨⟨_, hht.1, rfl⟩, ⟨_, hht.2, rfl⟩⟩
    loop_not_mem := fun e he hloop hmem => by
      rw [hvMap'_E (H.digraph.head_mem he)] at hmem
      rcases hmem with ⟨f, hf, heq⟩
      have hfG₁ : f ∈ G₁.digraph.edgeSet :=
        (hM.sub_of_mem (H.digraph.head_mem he)).edgeSet_subset hf
      have heG₁ : eMap e ∈ G₁.digraph.edgeSet := hM.edge_mem he
      have hfe : f = eMap e := iso.bijOn_e.injOn hfG₁ heG₁ heq
      subst hfe
      exact hM.loop_not_mem he hloop hf
    eMap_injOn := iso.bijOn_e.injOn.comp hM.eMap_injOn hM.edge_mem
    root_mem := fun i => by
      rw [hvMap'_V (H.roots_mem i), ← iso.map_roots i]
      exact ⟨G₁.roots i, hM.root_mem i, rfl⟩
  }⟩

/-- Turn a `DigraphSubgraph D` (`FolioTable.lean`) into a subdigraph of `D.toGMDigraph`. -/
def DigraphSubgraph.toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D) :
    GM13.Digraph ℕ ℕ :=
  D.toGMDigraph.subdigraphOf
    (Fin.val '' (S.verts : Set (Fin D.numVerts)))
    (Fin.val '' (S.edges : Set (Fin D.numEdges)))

theorem DigraphSubgraph.isSubdigraph_toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D) :
    S.toGMDigraph.IsSubdigraph D.toGMDigraph :=
  D.toGMDigraph.subdigraphOf_isSubdigraph _ _

@[simp]
theorem DigraphSubgraph.vertexSet_toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D) :
    S.toGMDigraph.vertexSet = Fin.val '' (S.verts : Set (Fin D.numVerts)) := by
  ext u
  simp only [DigraphSubgraph.toGMDigraph, GM13.Digraph.subdigraphOf, ComputeDigraph.toGMDigraph,
    mem_inter_iff, mem_ofPred_eq, mem_image, Finset.mem_coe]
  constructor
  · exact fun h => h.2
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.2, v, hv, rfl⟩

@[simp]
theorem DigraphSubgraph.edgeSet_toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D) :
    S.toGMDigraph.edgeSet = Fin.val '' (S.edges : Set (Fin D.numEdges)) := by
  ext e
  simp only [DigraphSubgraph.toGMDigraph, GM13.Digraph.subdigraphOf, ComputeDigraph.toGMDigraph,
    mem_inter_iff, mem_ofPred_eq, mem_image, Finset.mem_coe]
  constructor
  · exact fun h => h.1.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨⟨f.2, f, hf, rfl⟩, ?_, ?_⟩
    · rw [dite_eq_left f.2]
      exact ⟨D.head f, S.head_mem hf, rfl⟩
    · rw [dite_eq_left f.2]
      exact ⟨D.tail f, S.tail_mem hf, rfl⟩

theorem DigraphSubgraph.mem_vertexSet_toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D)
    (u : Fin D.numVerts) :
    u.1 ∈ S.toGMDigraph.vertexSet ↔ u ∈ S.verts := by
  rw [S.vertexSet_toGMDigraph, Fin.val_injective.mem_set_image]
  rfl

theorem DigraphSubgraph.mem_edgeSet_toGMDigraph {D : ComputeDigraph} (S : DigraphSubgraph D)
    (e : Fin D.numEdges) :
    e.1 ∈ S.toGMDigraph.edgeSet ↔ e ∈ S.edges := by
  rw [S.edgeSet_toGMDigraph, Fin.val_injective.mem_set_image]
  rfl

theorem DigraphSubgraph.nonempty_graphWalk_of_walk {D : ComputeDigraph} (S : DigraphSubgraph D) :
    ∀ {u v : Fin D.numVerts}, S.underlyingSimpleGraph.Walk u v → u ∈ S.verts →
      Nonempty (GraphWalk S.toGMDigraph.toGraph u.1 v.1)
  | u, _, .nil, hu =>
    ⟨.nil ((S.mem_vertexSet_toGMDigraph u).mpr hu)⟩
  | u, _, @SimpleGraph.Walk.cons _ _ _ w _ hadj rest, _ => by
    rcases hadj with ⟨_, e, he, hdir⟩
    have hw : w ∈ S.verts := by
      rcases hdir with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact S.tail_mem he
      · exact S.head_mem he
    rcases S.nonempty_graphWalk_of_walk rest hw with ⟨W'⟩
    have hlink : S.toGMDigraph.toGraph.IsLink e.1 u.1 w.1 := by
      refine ⟨(S.mem_edgeSet_toGMDigraph e).mpr he, ?_⟩
      change (D.toGMDigraph.head e.1 = u.1 ∧ D.toGMDigraph.tail e.1 = w.1) ∨
        (D.toGMDigraph.head e.1 = w.1 ∧ D.toGMDigraph.tail e.1 = u.1)
      simp only [ComputeDigraph.toGMDigraph, e.2, ↓reduceDIte]
      rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
    exact ⟨.cons hlink W'⟩

theorem DigraphSubgraph.isConnected_toGMDigraph {D : ComputeDigraph} {S : DigraphSubgraph D}
    (h : S.IsNonNullConnected) :
    S.toGMDigraph.IsConnected := by
  rcases h with ⟨⟨u₀, hu₀⟩, hreach⟩
  refine ⟨⟨u₀.1, (S.mem_vertexSet_toGMDigraph u₀).mpr hu₀⟩, fun x hx y hy => ?_⟩
  rw [S.vertexSet_toGMDigraph] at hx hy
  rcases hx with ⟨u, hu, rfl⟩
  rcases hy with ⟨v, hv, rfl⟩
  rcases hreach u hu v hv with ⟨W⟩
  exact S.nonempty_graphWalk_of_walk W hu

/-- Turn a subdigraph `K` of `D.toGMDigraph` into a `DigraphSubgraph D`. -/
noncomputable def toDigraphSubgraphOfSub {D : ComputeDigraph} {K : GM13.Digraph ℕ ℕ}
    (hsub : K.IsSubdigraph D.toGMDigraph) : DigraphSubgraph D where
  verts := Finset.univ.filter (fun u : Fin D.numVerts => u.1 ∈ K.vertexSet)
  edges := Finset.univ.filter (fun e : Fin D.numEdges => e.1 ∈ K.edgeSet)
  head_mem e he := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have hhead : D.toGMDigraph.head e.1 = (D.head e).1 := by
      simp [ComputeDigraph.toGMDigraph]
    rw [← hhead, ← hsub.head_eq he]
    exact K.head_mem he
  tail_mem e he := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    have htail : D.toGMDigraph.tail e.1 = (D.tail e).1 := by
      simp [ComputeDigraph.toGMDigraph]
    rw [← htail, ← hsub.tail_eq he]
    exact K.tail_mem he

theorem reachable_toDigraphSubgraphOfSub_of_graphWalk {D : ComputeDigraph} {K : GM13.Digraph ℕ ℕ}
    (hsub : K.IsSubdigraph D.toGMDigraph) :
    ∀ {x y : ℕ} (_W : GraphWalk K.toGraph x y) (hx : x < D.numVerts) (hy : y < D.numVerts),
      (toDigraphSubgraphOfSub hsub).underlyingSimpleGraph.Reachable ⟨x, hx⟩ ⟨y, hy⟩
  | _, _, .nil _, _, _ => SimpleGraph.Reachable.refl _
  | x, y, @GraphWalk.cons _ _ _ _ z _ e hlink rest, hx, hy => by
    have heK : e ∈ K.edgeSet := hlink.1
    have heD : e < D.numEdges := hsub.edgeSet_subset heK
    have hzK : z ∈ K.vertexSet := K.toGraph.left_mem_of_isLink hlink.symm
    have hz : z < D.numVerts := hsub.vertexSet_subset hzK
    have hstep : (toDigraphSubgraphOfSub hsub).underlyingSimpleGraph.Reachable ⟨x, hx⟩ ⟨z, hz⟩ := by
      by_cases hxz : (⟨x, hx⟩ : Fin D.numVerts) = ⟨z, hz⟩
      · rw [hxz]
      · refine SimpleGraph.Adj.reachable ⟨hxz, ⟨e, heD⟩, ?_, ?_⟩
        · simp [toDigraphSubgraphOfSub, heK]
        · have hh : (D.head ⟨e, heD⟩).1 = K.head e := by
            have := (hsub.head_eq heK).symm
            dsimp [ComputeDigraph.toGMDigraph] at this
            rwa [dite_eq_left heD] at this
          have ht : (D.tail ⟨e, heD⟩).1 = K.tail e := by
            have := (hsub.tail_eq heK).symm
            dsimp [ComputeDigraph.toGMDigraph] at this
            rwa [dite_eq_left heD] at this
          rcases hlink.2 with ⟨hx_eq, hz_eq⟩ | ⟨hz_eq, hx_eq⟩
          · exact Or.inl ⟨Fin.ext (hh.trans hx_eq), Fin.ext (ht.trans hz_eq)⟩
          · exact Or.inr ⟨Fin.ext (hh.trans hz_eq), Fin.ext (ht.trans hx_eq)⟩
    exact hstep.trans (reachable_toDigraphSubgraphOfSub_of_graphWalk hsub rest hz hy)

theorem isNonNullConnected_toDigraphSubgraphOfSub {D : ComputeDigraph} {K : GM13.Digraph ℕ ℕ}
    (hsub : K.IsSubdigraph D.toGMDigraph) (hconn : K.IsConnected) :
    (toDigraphSubgraphOfSub hsub).IsNonNullConnected := by
  rcases hconn with ⟨⟨x₀, hx₀⟩, hwalk⟩
  have hx₀D : x₀ < D.numVerts := hsub.vertexSet_subset hx₀
  refine ⟨⟨⟨x₀, hx₀D⟩, by simp [toDigraphSubgraphOfSub, hx₀]⟩, fun u hu v hv => ?_⟩
  simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  rcases hwalk u.1 hu v.1 hv with ⟨W⟩
  exact reachable_toDigraphSubgraphOfSub_of_graphWalk hsub W u.2 v.2

/-- Equivalence between `HasRootedDigraphModel H G` (`FolioTable.lean`) and
`GM13.IsRootedDigraphMinor H.toGMRootedDigraph G.toGMRootedDigraph`. -/
theorem hasRootedDigraphModel_iff_isRootedDigraphMinor {q : ℕ}
    (H G : ComputeRootedDigraph q) :
    HasRootedDigraphModel H G ↔
      GM13.IsRootedDigraphMinor H.toGMRootedDigraph G.toGMRootedDigraph := by
  constructor
  · rintro ⟨M⟩
    let vMap (u : ℕ) : GM13.Digraph ℕ ℕ :=
      if hu : u < H.digraph.numVerts then (M.vertMap ⟨u, hu⟩).toGMDigraph
      else G.digraph.toGMDigraph
    let eMap (e : ℕ) : ℕ :=
      if he : e < H.digraph.numEdges then (M.edgeMap ⟨e, he⟩).1 else 0
    refine ⟨vMap, eMap, {
      sub_of_mem := fun u hu => by
        change u < H.digraph.numVerts at hu
        dsimp [vMap]; rw [dite_eq_left hu]
        exact (M.vertMap ⟨u, hu⟩).isSubdigraph_toGMDigraph
      connected_of_mem := fun u hu => by
        change u < H.digraph.numVerts at hu
        dsimp [vMap]; rw [dite_eq_left hu]
        exact (M.vertMap ⟨u, hu⟩).isConnected_toGMDigraph (M.connected ⟨u, hu⟩)
      disjoint_of_ne := fun u v hu hv hne => by
        change u < H.digraph.numVerts at hu
        change v < H.digraph.numVerts at hv
        dsimp [vMap]; rw [dite_eq_left hu, dite_eq_left hv]
        rw [DigraphSubgraph.vertexSet_toGMDigraph, DigraphSubgraph.vertexSet_toGMDigraph,
          Set.disjoint_left]
        rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
        have hxy : x = y := Fin.ext heq.symm
        subst hxy
        exact Finset.disjoint_left.mp
          (M.vert_disjoint ⟨u, hu⟩ ⟨v, hv⟩ (fun h => hne (congrArg Fin.val h))) hx hy
      edge_mem := fun e he => by
        change e < H.digraph.numEdges at he
        dsimp [eMap]; rw [dite_eq_left he]
        exact (M.edgeMap ⟨e, he⟩).2
      head_tail_mem := fun e he => by
        change e < H.digraph.numEdges at he
        have hh_lt : (H.digraph.head ⟨e, he⟩).1 < H.digraph.numVerts :=
          (H.digraph.head ⟨e, he⟩).2
        have ht_lt : (H.digraph.tail ⟨e, he⟩).1 < H.digraph.numVerts :=
          (H.digraph.tail ⟨e, he⟩).2
        change G.digraph.toGMDigraph.head (eMap e) ∈
            (vMap (H.digraph.toGMDigraph.head e)).vertexSet ∧
          G.digraph.toGMDigraph.tail (eMap e) ∈
            (vMap (H.digraph.toGMDigraph.tail e)).vertexSet
        dsimp [ComputeDigraph.toGMDigraph, eMap, vMap]
        simp only [he, ↓reduceDIte, (M.edgeMap ⟨e, he⟩).2, hh_lt, ht_lt]
        exact ⟨((M.vertMap (H.digraph.head ⟨e, he⟩)).mem_vertexSet_toGMDigraph _).mpr
            (M.head_mem_vertMap ⟨e, he⟩),
          ((M.vertMap (H.digraph.tail ⟨e, he⟩)).mem_vertexSet_toGMDigraph _).mpr
            (M.tail_mem_vertMap ⟨e, he⟩)⟩
      loop_not_mem := fun e he _ hmem => by
        change e < H.digraph.numEdges at he
        have hh_lt : (H.digraph.head ⟨e, he⟩).1 < H.digraph.numVerts :=
          (H.digraph.head ⟨e, he⟩).2
        change eMap e ∈ (vMap (H.digraph.toGMDigraph.head e)).edgeSet at hmem
        dsimp [ComputeDigraph.toGMDigraph, eMap, vMap] at hmem
        simp only [he, ↓reduceDIte, hh_lt] at hmem
        rw [DigraphSubgraph.mem_edgeSet_toGMDigraph] at hmem
        exact M.edge_notMem_vert (H.digraph.head ⟨e, he⟩) ⟨e, he⟩ hmem
      eMap_injOn := by
        intro e₁ he₁ e₂ he₂ heq
        change e₁ < H.digraph.numEdges at he₁
        change e₂ < H.digraph.numEdges at he₂
        dsimp [eMap] at heq
        rw [dite_eq_left he₁, dite_eq_left he₂] at heq
        exact congrArg Fin.val (M.edge_injective (Fin.ext heq))
      root_mem := fun i => by
        have hr : (H.roots i).1 < H.digraph.numVerts := (H.roots i).2
        change (G.roots i).1 ∈ (vMap (H.roots i).1).vertexSet
        simp only [vMap, hr, ↓reduceDIte]
        exact ((M.vertMap (H.roots i)).mem_vertexSet_toGMDigraph _).mpr (M.root_mem_vertMap i)
    }⟩
  · rintro ⟨vMap, eMap, hM⟩
    refine ⟨{
      vertMap := fun u => toDigraphSubgraphOfSub (hM.sub_of_mem u.2)
      edgeMap := fun e => ⟨eMap e.1, hM.edge_mem e.2⟩
      connected := fun u =>
        isNonNullConnected_toDigraphSubgraphOfSub (hM.sub_of_mem u.2) (hM.connected_of_mem u.2)
      vert_disjoint := fun u v hne => by
        rw [Finset.disjoint_left]
        intro x hxu hxv
        simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and] at hxu hxv
        exact Set.disjoint_left.mp
          (hM.disjoint_of_ne u.2 v.2 (fun h => hne (Fin.ext h))) hxu hxv
      edge_injective := fun e₁ e₂ heq =>
        Fin.ext (hM.eMap_injOn e₁.2 e₂.2 (congrArg Fin.val heq))
      edge_notMem_vert := fun v e hmem => by
        simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
        exact hM.toIsDigraphModel.edge_not_mem_vMap e.2 v.2 hmem
      head_mem_vertMap := fun e => by
        simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and]
        have hht := (hM.head_tail_mem e.2).1
        have heG : eMap e.1 < G.digraph.numEdges := hM.edge_mem e.2
        change G.digraph.toGMDigraph.head (eMap e.1) ∈
          (vMap (H.digraph.toGMDigraph.head e.1)).vertexSet at hht
        simp only [ComputeDigraph.toGMDigraph, heG, e.2, ↓reduceDIte] at hht
        exact hht
      tail_mem_vertMap := fun e => by
        simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and]
        have hht := (hM.head_tail_mem e.2).2
        have heG : eMap e.1 < G.digraph.numEdges := hM.edge_mem e.2
        change G.digraph.toGMDigraph.tail (eMap e.1) ∈
          (vMap (H.digraph.toGMDigraph.tail e.1)).vertexSet at hht
        simp only [ComputeDigraph.toGMDigraph, heG, e.2, ↓reduceDIte] at hht
        exact hht
      root_mem_vertMap := fun i => by
        simp only [toDigraphSubgraphOfSub, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hM.root_mem i
    }⟩

/-- Canonical vertex equivalence `D.vertexSet ≃ Fin D.vertexSet.ncard` for a finite digraph `D`. -/
noncomputable def _root_.GraphMinor.GM13.Digraph.IsFinite.equivFinV {α β : Type*}
    {D : GM13.Digraph α β} (hfin : D.IsFinite) :
    D.vertexSet ≃ Fin D.vertexSet.ncard :=
  @Finite.equivFin D.vertexSet hfin.finite_V.to_subtype

/-- Canonical edge equivalence `D.edgeSet ≃ Fin D.edgeSet.ncard` for a finite digraph `D`. -/
noncomputable def _root_.GraphMinor.GM13.Digraph.IsFinite.equivFinE {α β : Type*}
    {D : GM13.Digraph α β} (hfin : D.IsFinite) :
    D.edgeSet ≃ Fin D.edgeSet.ncard :=
  @Finite.equivFin D.edgeSet hfin.finite_E.to_subtype

/-- Convert any finite `GM13.RootedDigraph ℕ ℕ q` into an isomorphic `ComputeRootedDigraph q`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.toComputeRootedDigraph {q : ℕ}
    (R : GM13.RootedDigraph ℕ ℕ q) (hfin : R.digraph.IsFinite) : ComputeRootedDigraph q :=
  let eV := hfin.equivFinV
  let eE := hfin.equivFinE
  { digraph :=
      { numVerts := R.digraph.vertexSet.ncard
        numEdges := R.digraph.edgeSet.ncard
        head := fun j => eV ⟨R.digraph.head (eE.symm j).1, R.digraph.head_mem (eE.symm j).2⟩
        tail := fun j => eV ⟨R.digraph.tail (eE.symm j).1, R.digraph.tail_mem (eE.symm j).2⟩ }
    roots := fun i => eV ⟨R.roots i, R.roots_mem i⟩ }

/-- Isomorphism from `R` to `(R.toComputeRootedDigraph hfin).toGMRootedDigraph`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.isoToComputeRootedDigraph {q : ℕ}
    (R : GM13.RootedDigraph ℕ ℕ q) (hfin : R.digraph.IsFinite) :
    GM13.RootedDigraph.Iso R (R.toComputeRootedDigraph hfin).toGMRootedDigraph :=
  let eV := hfin.equivFinV
  let eE := hfin.equivFinE
  { vMap := fun u => if hu : u ∈ R.digraph.vertexSet then (eV ⟨u, hu⟩).1 else 0
    eMap := fun e => if he : e ∈ R.digraph.edgeSet then (eE ⟨e, he⟩).1 else 0
    bijOn_v :=
      ⟨fun u hu => by
        simp only [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
          GM13.RootedDigraph.toComputeRootedDigraph, mem_ofPred_eq]
        rw [dite_eq_left hu]
        exact (eV ⟨u, hu⟩).2,
       fun u₁ hu₁ u₂ hu₂ heq => by
        dsimp only at heq
        rw [dite_eq_left hu₁, dite_eq_left hu₂] at heq
        exact congrArg Subtype.val (eV.injective (Fin.ext heq)),
       fun i hi => by
        simp only [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
          GM13.RootedDigraph.toComputeRootedDigraph, mem_ofPred_eq] at hi
        let u := eV.symm ⟨i, hi⟩
        refine ⟨u.1, u.2, ?_⟩
        dsimp only
        rw [dite_eq_left u.2]
        exact congrArg Fin.val (eV.apply_symm_apply ⟨i, hi⟩)⟩
    bijOn_e :=
      ⟨fun e he => by
        simp only [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
          GM13.RootedDigraph.toComputeRootedDigraph, mem_ofPred_eq]
        rw [dite_eq_left he]
        exact (eE ⟨e, he⟩).2,
       fun e₁ he₁ e₂ he₂ heq => by
        dsimp only at heq
        rw [dite_eq_left he₁, dite_eq_left he₂] at heq
        exact congrArg Subtype.val (eE.injective (Fin.ext heq)),
       fun j hj => by
        simp only [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
          GM13.RootedDigraph.toComputeRootedDigraph, mem_ofPred_eq] at hj
        let e := eE.symm ⟨j, hj⟩
        refine ⟨e.1, e.2, ?_⟩
        dsimp only
        rw [dite_eq_left e.2]
        exact congrArg Fin.val (eE.apply_symm_apply ⟨j, hj⟩)⟩
    head_eq := fun e he => by
      have hj : (eE ⟨e, he⟩).1 < R.digraph.edgeSet.ncard := (eE ⟨e, he⟩).2
      have hh : R.digraph.head e ∈ R.digraph.vertexSet := R.digraph.head_mem he
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
        GM13.RootedDigraph.toComputeRootedDigraph]
      simp only [he, ↓reduceDIte, hj, hh]
      refine congrArg (fun v : R.digraph.vertexSet => (eV v).1) (Subtype.ext ?_)
      exact congrArg (fun z : R.digraph.edgeSet => R.digraph.head z.1)
        (eE.symm_apply_apply ⟨e, he⟩)
    tail_eq := fun e he => by
      have hj : (eE ⟨e, he⟩).1 < R.digraph.edgeSet.ncard := (eE ⟨e, he⟩).2
      have ht : R.digraph.tail e ∈ R.digraph.vertexSet := R.digraph.tail_mem he
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
        GM13.RootedDigraph.toComputeRootedDigraph]
      simp only [he, ↓reduceDIte, hj, ht]
      refine congrArg (fun v : R.digraph.vertexSet => (eV v).1) (Subtype.ext ?_)
      exact congrArg (fun z : R.digraph.edgeSet => R.digraph.tail z.1)
        (eE.symm_apply_apply ⟨e, he⟩)
    map_roots := fun i => by
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, GM13.RootedDigraph.toComputeRootedDigraph]
      rw [dite_eq_left (R.roots_mem i)] }

/-- Isomorphism from `(R.toComputeRootedDigraph hfin).toGMRootedDigraph` to `R`. -/
noncomputable def _root_.GraphMinor.GM13.RootedDigraph.isoFromComputeRootedDigraph {q : ℕ}
    (R : GM13.RootedDigraph ℕ ℕ q) (hfin : R.digraph.IsFinite) :
    GM13.RootedDigraph.Iso (R.toComputeRootedDigraph hfin).toGMRootedDigraph R :=
  let eV := hfin.equivFinV
  let eE := hfin.equivFinE
  { vMap := fun i => if hi : i < R.digraph.vertexSet.ncard then (eV.symm ⟨i, hi⟩).1 else 0
    eMap := fun j => if hj : j < R.digraph.edgeSet.ncard then (eE.symm ⟨j, hj⟩).1 else 0
    bijOn_v :=
      ⟨fun i hi => by
        change i < R.digraph.vertexSet.ncard at hi
        dsimp only
        rw [dite_eq_left hi]
        exact (eV.symm ⟨i, hi⟩).2,
       fun i₁ hi₁ i₂ hi₂ heq => by
        change i₁ < R.digraph.vertexSet.ncard at hi₁
        change i₂ < R.digraph.vertexSet.ncard at hi₂
        dsimp only at heq
        rw [dite_eq_left hi₁, dite_eq_left hi₂] at heq
        exact congrArg Fin.val (eV.symm.injective (Subtype.ext heq)),
       fun u hu => by
        refine ⟨(eV ⟨u, hu⟩).1, (eV ⟨u, hu⟩).2, ?_⟩
        dsimp only
        rw [dite_eq_left (eV ⟨u, hu⟩).2]
        exact congrArg Subtype.val (eV.symm_apply_apply ⟨u, hu⟩)⟩
    bijOn_e :=
      ⟨fun j hj => by
        change j < R.digraph.edgeSet.ncard at hj
        dsimp only
        rw [dite_eq_left hj]
        exact (eE.symm ⟨j, hj⟩).2,
       fun j₁ hj₁ j₂ hj₂ heq => by
        change j₁ < R.digraph.edgeSet.ncard at hj₁
        change j₂ < R.digraph.edgeSet.ncard at hj₂
        dsimp only at heq
        rw [dite_eq_left hj₁, dite_eq_left hj₂] at heq
        exact congrArg Fin.val (eE.symm.injective (Subtype.ext heq)),
       fun e he => by
        refine ⟨(eE ⟨e, he⟩).1, (eE ⟨e, he⟩).2, ?_⟩
        dsimp only
        rw [dite_eq_left (eE ⟨e, he⟩).2]
        exact congrArg Subtype.val (eE.symm_apply_apply ⟨e, he⟩)⟩
    head_eq := fun j hj => by
      change j < R.digraph.edgeSet.ncard at hj
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
        GM13.RootedDigraph.toComputeRootedDigraph]
      simp only [hj, ↓reduceDIte, Fin.is_lt]
      have hsymm := eV.symm_apply_apply
        ⟨R.digraph.head (eE.symm ⟨j, hj⟩).1, R.digraph.head_mem (eE.symm ⟨j, hj⟩).2⟩
      exact (congrArg Subtype.val hsymm).symm
    tail_eq := fun j hj => by
      change j < R.digraph.edgeSet.ncard at hj
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
        GM13.RootedDigraph.toComputeRootedDigraph]
      simp only [hj, ↓reduceDIte, Fin.is_lt]
      have hsymm := eV.symm_apply_apply
        ⟨R.digraph.tail (eE.symm ⟨j, hj⟩).1, R.digraph.tail_mem (eE.symm ⟨j, hj⟩).2⟩
      exact (congrArg Subtype.val hsymm).symm
    map_roots := fun i => by
      dsimp [ComputeRootedDigraph.toGMRootedDigraph, GM13.RootedDigraph.toComputeRootedDigraph]
      simp only [Fin.is_lt, ↓reduceDIte]
      exact congrArg Subtype.val (eV.symm_apply_apply ⟨R.roots i, R.roots_mem i⟩) }

theorem _root_.GraphMinor.GM13.RootedDigraph.detail_eq_of_iso {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    {R₁ : GM13.RootedDigraph α₁ β₁ k} {R₂ : GM13.RootedDigraph α₂ β₂ k}
    (iso : GM13.RootedDigraph.Iso R₁ R₂) :
    R₂.detail = R₁.detail := by
  unfold GM13.RootedDigraph.detail
  have hE : R₂.digraph.edgeSet.ncard = R₁.digraph.edgeSet.ncard := by
    rw [← iso.bijOn_e.image_eq, iso.bijOn_e.injOn.ncard_image]
  have hbij_sdiff :
      Set.BijOn iso.vMap
        (R₁.digraph.vertexSet \ Set.range R₁.roots)
        (R₂.digraph.vertexSet \ Set.range R₂.roots) := by
    refine ⟨fun u ⟨hu, hnot⟩ => ⟨iso.bijOn_v.mapsTo hu, ?_⟩,
      iso.bijOn_v.injOn.mono sdiff_subset,
      fun v ⟨hv, hnot⟩ => ?_⟩
    · rintro ⟨i, hi⟩
      rw [← iso.map_roots i] at hi
      exact hnot ⟨i, iso.bijOn_v.injOn (R₁.roots_mem i) hu hi⟩
    · rcases iso.bijOn_v.surjOn hv with ⟨u, hu, rfl⟩
      refine ⟨u, ⟨hu, fun ⟨i, hi⟩ => hnot ⟨i, ?_⟩⟩, rfl⟩
      rw [← iso.map_roots i, hi]
  have hV : (R₂.digraph.vertexSet \ Set.range R₂.roots).ncard =
      (R₁.digraph.vertexSet \ Set.range R₁.roots).ncard := by
    rw [← hbij_sdiff.image_eq, hbij_sdiff.injOn.ncard_image]
  rw [hE, hV]

theorem _root_.GraphMinor.GM13.RootedDigraph.hasDetailLe_toComputeRootedDigraph_iff {q : ℕ}
    (δ : ℕ) (R : GM13.RootedDigraph ℕ ℕ q) (hfin : R.digraph.IsFinite) :
    (R.toComputeRootedDigraph hfin).HasDetailLe δ ↔ R.detail ≤ δ := by
  rw [(R.toComputeRootedDigraph hfin).hasDetailLe_iff_detail_le δ,
    GM13.RootedDigraph.detail_eq_of_iso (R.isoToComputeRootedDigraph hfin)]

theorem _root_.GraphMinor.GM13.RootedDigraph.inFolio_toComputeRootedDigraph_iff
    {α β : Type*} {q : ℕ} (G : GM13.RootedDigraph α β q)
    (R : GM13.RootedDigraph ℕ ℕ q) (hfin : R.digraph.IsFinite) :
    G.InFolio (R.toComputeRootedDigraph hfin).toGMRootedDigraph ↔ G.InFolio R := by
  unfold GM13.RootedDigraph.InFolio
  refine ⟨fun ⟨_, hmin⟩ =>
      ⟨hfin, isRootedDigraphMinor_of_iso_left (R.isoToComputeRootedDigraph hfin) hmin⟩,
    fun ⟨_, hmin⟩ =>
      ⟨(R.toComputeRootedDigraph hfin).isFinite_toGMRootedDigraph,
       isRootedDigraphMinor_of_iso_left (R.isoFromComputeRootedDigraph hfin) hmin⟩⟩

/-- Two `GM13.RootedDigraph`s `R₁` and `R₂` have the same `δ`-folio (`GM13.HasSameDeltaFolio`)
if and only if they agree on `H.toGMRootedDigraph` for every `H : ComputeRootedDigraph k` of
detail `≤ δ`. -/
theorem hasSameDeltaFolio_iff_forall_computeRootedDigraph
    {α₁ β₁ α₂ β₂ : Type*} {k : ℕ}
    (R₁ : GM13.RootedDigraph α₁ β₁ k) (R₂ : GM13.RootedDigraph α₂ β₂ k) (δ : ℕ) :
    GM13.HasSameDeltaFolio R₁ R₂ δ ↔
      ∀ H : ComputeRootedDigraph k, H.HasDetailLe δ →
        (R₁.InFolio H.toGMRootedDigraph ↔ R₂.InFolio H.toGMRootedDigraph) := by
  constructor
  · intro hsame H hdet
    have hmem : H.toGMRootedDigraph ∈ R₁.deltaFolio δ ↔ H.toGMRootedDigraph ∈ R₂.deltaFolio δ :=
      by rw [hsame]
    have hdet' : H.toGMRootedDigraph.detail ≤ δ := (H.hasDetailLe_iff_detail_le δ).mp hdet
    simpa [GM13.RootedDigraph.deltaFolio, GM13.RootedDigraph.InDeltaFolio, hdet'] using hmem
  · intro hall
    ext R
    simp only [GM13.RootedDigraph.deltaFolio, mem_ofPred_eq, GM13.RootedDigraph.InDeltaFolio]
    constructor
    · rintro ⟨hfin_in, hdet⟩
      have hfin : R.digraph.IsFinite := hfin_in.1
      have hdet_c : (R.toComputeRootedDigraph hfin).HasDetailLe δ :=
        (R.hasDetailLe_toComputeRootedDigraph_iff δ hfin).mpr hdet
      have hin₁ : R₁.InFolio (R.toComputeRootedDigraph hfin).toGMRootedDigraph :=
        (GM13.RootedDigraph.inFolio_toComputeRootedDigraph_iff R₁ R hfin).mpr hfin_in
      have hin₂ : R₂.InFolio (R.toComputeRootedDigraph hfin).toGMRootedDigraph :=
        (hall _ hdet_c).mp hin₁
      exact ⟨(GM13.RootedDigraph.inFolio_toComputeRootedDigraph_iff R₂ R hfin).mp hin₂, hdet⟩
    · rintro ⟨hfin_in, hdet⟩
      have hfin : R.digraph.IsFinite := hfin_in.1
      have hdet_c : (R.toComputeRootedDigraph hfin).HasDetailLe δ :=
        (R.hasDetailLe_toComputeRootedDigraph_iff δ hfin).mpr hdet
      have hin₂ : R₂.InFolio (R.toComputeRootedDigraph hfin).toGMRootedDigraph :=
        (GM13.RootedDigraph.inFolio_toComputeRootedDigraph_iff R₂ R hfin).mpr hfin_in
      have hin₁ : R₁.InFolio (R.toComputeRootedDigraph hfin).toGMRootedDigraph :=
        (hall _ hdet_c).mpr hin₂
      exact ⟨(GM13.RootedDigraph.inFolio_toComputeRootedDigraph_iff R₁ R hfin).mp hin₁, hdet⟩

/-- Embed a `Finset (Fin n)` into `Set ℕ` via `Fin.val`. -/
def _root_.Finset.toNatSet {n : ℕ} (Z : Finset (Fin n)) : Set ℕ :=
  Fin.val '' (Z : Set (Fin n))

@[simp]
theorem mem_toNatSet_iff {n : ℕ} (Z : Finset (Fin n)) (u : Fin n) :
    u.1 ∈ Z.toNatSet ↔ u ∈ Z := by
  unfold Finset.toNatSet
  rw [Fin.val_injective.mem_set_image, Finset.mem_coe]

theorem toNatSet_subset_lt {n : ℕ} (Z : Finset (Fin n)) :
    Z.toNatSet ⊆ {u : ℕ | u < n} := by
  rintro _ ⟨u, _, rfl⟩
  exact u.2

@[simp]
theorem ncard_toNatSet {n : ℕ} (Z : Finset (Fin n)) :
    Z.toNatSet.ncard = Z.card := by
  unfold Finset.toNatSet
  rw [Set.ncard_image_of_injective _ Fin.val_injective, Set.ncard_coe_finset]

theorem injective_rootsZ_val {n : ℕ} (Z : Finset (Fin n)) :
    Function.Injective (fun i : Fin Z.card => (rootsZ Z i).1) :=
  Fin.val_injective.comp (injective_rootsZ Z)

@[simp]
theorem range_rootsZ_val_eq_toNatSet {n : ℕ} (Z : Finset (Fin n)) :
    Set.range (fun i : Fin Z.card => (rootsZ Z i).1) = Z.toNatSet := by
  ext u
  simp only [mem_range, Finset.toNatSet, mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨rootsZ Z i, rootsZ_mem Z i, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    rcases exists_rootsZ_eq Z hv with ⟨i, rfl⟩
    exact ⟨i, rfl⟩

/-- `GM13.HasSameDeltaFolioRel` relative to `Z₀` is equivalent to `GM13.HasSameDeltaFolio`
with respect to any injective enumeration `v' : Fin k' → α` of `Z₀`. -/
theorem hasSameDeltaFolioRel_iff_hasSameDeltaFolio_of_injective
    {α β : Type*} {G₁ G₂ : GM13.Digraph α β} {δ k' : ℕ} {Z₀ : Set α}
    (hZ₁ : Z₀ ⊆ G₁.vertexSet) (hZ₂ : Z₀ ⊆ G₂.vertexSet)
    {v' : Fin k' → α} (hinj : Function.Injective v') (hrange : Set.range v' = Z₀) :
    GM13.HasSameDeltaFolioRel G₁ G₂ δ Z₀ ↔
      GM13.HasSameDeltaFolio
        ⟨G₁, v', fun j => hZ₁ (hrange ▸ Set.mem_range_self j)⟩
        ⟨G₂, v', fun j => hZ₂ (hrange ▸ Set.mem_range_self j)⟩ δ := by
  have hv'Z : ∀ j, v' j ∈ Z₀ := fun j => hrange ▸ Set.mem_range_self j
  constructor
  · intro hrel
    exact hrel.2.2 k' v' (fun j => hZ₁ (hv'Z j)) (fun j => hZ₂ (hv'Z j)) hinj hrange.subset
  · intro hsame
    refine ⟨hZ₁, hZ₂, fun k v hv₁ hv₂ _ hv_sub => ?_⟩
    have hex : ∀ i : Fin k, ∃ j : Fin k', v' j = v i := by
      intro i
      rw [← Set.mem_range, hrange]
      exact hv_sub (Set.mem_range_self i)
    let f (i : Fin k) : Fin k' := (hex i).choose
    have hf : ∀ i, v i = v' (f i) := fun i => (hex i).choose_spec.symm
    ext H
    rw [GM13.inDeltaFolio_iff_exists_isRootedExtension (hv' := fun j => hZ₁ (hv'Z j)) hinj hf δ H,
      GM13.inDeltaFolio_iff_exists_isRootedExtension (hv' := fun j => hZ₂ (hv'Z j)) hinj hf δ H,
      hsame]

/-- Turn a `MultiDigraph n` (`Basic.lean`) into a `GM13.Digraph ℕ (ℕ × ℕ × ℕ)`.
Vertices are `{u : ℕ | u < n}` and directed edges are triples `(u, v, k)` with `u < n`, `v < n`,
and `k < G.edgeMult ⟨u, hu⟩ ⟨v, hv⟩`, where `tail (u, v, k) = u` and `head (u, v, k) = v`. -/
def MultiDigraph.toGMDigraph {n : ℕ} (G : MultiDigraph n) :
    GM13.Digraph ℕ (ℕ × ℕ × ℕ) where
  vertexSet := {u : ℕ | u < n}
  edgeSet := {e : ℕ × ℕ × ℕ | ∃ (hu : e.1 < n) (hv : e.2.1 < n),
    e.2.2 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩}
  head e := e.2.1
  tail e := e.1
  head_mem _ he := he.choose_spec.choose
  tail_mem _ he := he.choose

/-- Rooted `GM13.RootedDigraph` built from `G : MultiDigraph n` and `Z : Finset (Fin n)`,
using the sorted root enumeration `rootsZ Z : Fin Z.card → Fin n`. -/
def MultiDigraph.toGMRootedDigraph {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) : GM13.RootedDigraph ℕ (ℕ × ℕ × ℕ) Z.card where
  digraph := G.toGMDigraph
  roots i := (rootsZ Z i).1
  roots_mem i := (rootsZ Z i).2

/-- The list of directed edge triples `(u.1, v.1, k)` of `G : MultiDigraph n`, in exact 1-to-1
correspondence with `G.directedEdgesList`. -/
def MultiDigraph.directedEdgeTriples {n : ℕ} (G : MultiDigraph n) : List (ℕ × ℕ × ℕ) :=
  (List.finRange n).flatMap (fun u =>
    (List.finRange n).flatMap (fun v =>
      (List.range (G.edgeMult u v)).map (fun k => (u.1, v.1, k))))

theorem MultiDigraph.map_directedEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.directedEdgeTriples.map (fun e => (e.1, e.2.1)) =
      G.directedEdgesList.map (fun p => (p.1.1, p.2.1)) := by
  unfold MultiDigraph.directedEdgeTriples MultiDigraph.directedEdgesList
  simp [List.map_flatMap, Function.comp_def]

@[simp]
theorem MultiDigraph.length_directedEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.directedEdgeTriples.length = G.directedEdgesList.length := by
  have h := congrArg List.length G.map_directedEdgeTriples
  simpa using h

theorem MultiDigraph.getElem_directedEdgeTriples_fst_snd {n : ℕ} (G : MultiDigraph n)
    (i : ℕ) (hi : i < G.directedEdgesList.length) :
    let hi' : i < G.directedEdgeTriples.length := by
      rw [G.length_directedEdgeTriples]; exact hi
    ((G.directedEdgeTriples[i]'hi').1, (G.directedEdgeTriples[i]'hi').2.1) =
      ((G.directedEdgesList[i]'hi).1.1, (G.directedEdgesList[i]'hi).2.1) := by
  intro hi'
  have h := congrArg (fun L : List (ℕ × ℕ) => L[i]?) G.map_directedEdgeTriples
  rw [List.getElem?_map, List.getElem?_map,
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

@[simp]
theorem MultiDigraph.mem_directedEdgeTriples_iff {n : ℕ} (G : MultiDigraph n)
    (e : ℕ × ℕ × ℕ) :
    e ∈ G.directedEdgeTriples ↔ e ∈ G.toGMDigraph.edgeSet := by
  rcases e with ⟨u, v, k⟩
  simp only [MultiDigraph.directedEdgeTriples, MultiDigraph.toGMDigraph, List.mem_flatMap,
    List.mem_finRange, true_and, List.mem_map, List.mem_range, Prod.mk.injEq, mem_ofPred_eq]
  constructor
  · rintro ⟨u', v', k', hk', rfl, rfl, rfl⟩
    exact ⟨u'.2, v'.2, hk'⟩
  · rintro ⟨hu, hv, hk⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, k, hk, rfl, rfl, rfl⟩

theorem MultiDigraph.nodup_directedEdgeTriples {n : ℕ} (G : MultiDigraph n) :
    G.directedEdgeTriples.Nodup := by
  unfold MultiDigraph.directedEdgeTriples
  refine List.nodup_flatMap.2 ⟨fun u _ => ?_, (List.nodup_finRange n).imp fun hne x hx₁ hx₂ => ?_⟩
  · refine List.nodup_flatMap.2 ⟨fun v _ => ?_, (List.nodup_finRange n).imp fun hne x hx₁ hx₂ => ?_⟩
    · refine List.Nodup.map (fun k₁ k₂ h => ?_) List.nodup_range
      simpa using h
    · simp only [List.mem_map, List.mem_range] at hx₁ hx₂
      rcases hx₁ with ⟨_, _, rfl⟩
      rcases hx₂ with ⟨_, _, heq⟩
      exact hne (Fin.ext (Prod.mk.inj (Prod.mk.inj heq).2).1.symm)
  · simp only [List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, List.mem_range] at hx₁ hx₂
    rcases hx₁ with ⟨_, _, _, rfl⟩
    rcases hx₂ with ⟨_, _, _, heq⟩
    exact hne (Fin.ext (Prod.mk.inj heq).1.symm)

theorem MultiDigraph.edgeSet_toGMDigraph_eq_coe_toFinset {n : ℕ} (G : MultiDigraph n) :
    G.toGMDigraph.edgeSet = ↑G.directedEdgeTriples.toFinset := by
  ext e
  simp [MultiDigraph.mem_directedEdgeTriples_iff]

theorem MultiDigraph.isFinite_toGMDigraph {n : ℕ} (G : MultiDigraph n) :
    G.toGMDigraph.IsFinite where
  finite_V := by
    change {u : ℕ | u < n}.Finite
    have heq : {u : ℕ | u < n} = ↑(Finset.range n) := by ext; simp
    rw [heq]
    exact Finset.finite_toSet _
  finite_E := by
    rw [G.edgeSet_toGMDigraph_eq_coe_toFinset]
    exact Finset.finite_toSet _

@[simp]
theorem MultiDigraph.ncard_vertexSet_toGMDigraph {n : ℕ} (G : MultiDigraph n) :
    G.toGMDigraph.vertexSet.ncard = n := by
  change {u : ℕ | u < n}.ncard = n
  have heq : {u : ℕ | u < n} = ↑(Finset.range n) := by ext; simp
  rw [heq, Set.ncard_coe_finset, Finset.card_range]

@[simp]
theorem MultiDigraph.ncard_edgeSet_toGMDigraph {n : ℕ} (G : MultiDigraph n) :
    G.toGMDigraph.edgeSet.ncard = G.numEdges := by
  rw [G.edgeSet_toGMDigraph_eq_coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup G.nodup_directedEdgeTriples,
    G.length_directedEdgeTriples, G.length_directedEdgesList]

/-- Map an edge index `i : Fin G.directedEdgesList.length` to the corresponding edge triple in
`G.toGMDigraph.edgeSet`. -/
def MultiDigraph.edgeToGMTriple {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.directedEdgesList.length) : G.toGMDigraph.edgeSet :=
  ⟨G.directedEdgeTriples[i.1]'(by rw [G.length_directedEdgeTriples]; exact i.2),
   (G.mem_directedEdgeTriples_iff _).mp (List.getElem_mem _)⟩

theorem MultiDigraph.bijective_edgeToGMTriple {n : ℕ} (G : MultiDigraph n) :
    Function.Bijective G.edgeToGMTriple := by
  constructor
  · intro i j heq
    have hval := congrArg Subtype.val heq
    dsimp [MultiDigraph.edgeToGMTriple] at hval
    have hinj := (G.nodup_directedEdgeTriples.getElem_inj_iff
      (i := i.1) (j := j.1)
      (hi := by rw [G.length_directedEdgeTriples]; exact i.2)
      (hj := by rw [G.length_directedEdgeTriples]; exact j.2)).mp hval
    exact Fin.ext hinj
  · rintro ⟨e, he⟩
    have hmem : e ∈ G.directedEdgeTriples := (G.mem_directedEdgeTriples_iff e).mpr he
    rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, heq⟩
    refine ⟨⟨idx, by rw [← G.length_directedEdgeTriples]; exact hidx⟩, Subtype.ext heq⟩

/-- Canonical bijection between `Fin G.directedEdgesList.length` and `G.toGMDigraph.edgeSet`. -/
noncomputable def MultiDigraph.edgeEquiv {n : ℕ} (G : MultiDigraph n) :
    Fin G.directedEdgesList.length ≃ G.toGMDigraph.edgeSet :=
  Equiv.ofBijective G.edgeToGMTriple G.bijective_edgeToGMTriple

@[simp]
theorem MultiDigraph.edgeEquiv_apply {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.directedEdgesList.length) :
    G.edgeEquiv i = G.edgeToGMTriple i :=
  rfl

/-- Isomorphism from `(rootedDigraphOfZ G Z).toGMRootedDigraph` to `G.toGMRootedDigraph Z`. -/
noncomputable def MultiDigraph.isoToGMRootedDigraph {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    GM13.RootedDigraph.Iso (rootedDigraphOfZ G Z).toGMRootedDigraph (G.toGMRootedDigraph Z) where
  vMap := id
  eMap i := if hi : i < G.directedEdgesList.length then (G.edgeEquiv ⟨i, hi⟩).1 else (0, 0, 0)
  bijOn_v := ⟨fun _ h => h, Set.injOn_id _, fun x hx => ⟨x, hx, rfl⟩⟩
  bijOn_e :=
    ⟨fun i hi => by
      change i < G.directedEdgesList.length at hi
      dsimp only
      rw [dite_eq_left hi]
      exact (G.edgeEquiv ⟨i, hi⟩).2,
     fun i₁ hi₁ i₂ hi₂ heq => by
      change i₁ < G.directedEdgesList.length at hi₁
      change i₂ < G.directedEdgesList.length at hi₂
      dsimp only at heq
      rw [dite_eq_left hi₁, dite_eq_left hi₂] at heq
      exact congrArg Fin.val (G.edgeEquiv.injective (Subtype.ext heq)),
     fun e he => by
      let i := G.edgeEquiv.symm ⟨e, he⟩
      refine ⟨i.1, i.2, ?_⟩
      dsimp only
      rw [dite_eq_left i.2]
      exact congrArg Subtype.val (G.edgeEquiv.apply_symm_apply ⟨e, he⟩)⟩
  head_eq i hi := by
    change i < G.directedEdgesList.length at hi
    change (if hi' : i < G.directedEdgesList.length then (G.edgeEquiv ⟨i, hi'⟩).1 else (0, 0, 0)).2.1 =
      if hi' : i < G.directedEdgesList.length then ((G.directedEdgesList[i]'hi').2).1 else 0
    rw [dite_eq_left hi, dite_eq_left hi, MultiDigraph.edgeEquiv_apply, MultiDigraph.edgeToGMTriple]
    simpa using congrArg Prod.snd (G.getElem_directedEdgeTriples_fst_snd i hi)
  tail_eq i hi := by
    change i < G.directedEdgesList.length at hi
    change (if hi' : i < G.directedEdgesList.length then (G.edgeEquiv ⟨i, hi'⟩).1 else (0, 0, 0)).1 =
      if hi' : i < G.directedEdgesList.length then ((G.directedEdgesList[i]'hi').1).1 else 0
    rw [dite_eq_left hi, dite_eq_left hi, MultiDigraph.edgeEquiv_apply, MultiDigraph.edgeToGMTriple]
    simpa using congrArg Prod.fst (G.getElem_directedEdgeTriples_fst_snd i hi)
  map_roots _ := rfl

/-- Isomorphism from `G.toGMRootedDigraph Z` to `(rootedDigraphOfZ G Z).toGMRootedDigraph`. -/
noncomputable def MultiDigraph.isoFromGMRootedDigraph {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    GM13.RootedDigraph.Iso (G.toGMRootedDigraph Z) (rootedDigraphOfZ G Z).toGMRootedDigraph where
  vMap := id
  eMap e := if he : e ∈ G.toGMDigraph.edgeSet then (G.edgeEquiv.symm ⟨e, he⟩).1 else 0
  bijOn_v := ⟨fun _ h => h, Set.injOn_id _, fun x hx => ⟨x, hx, rfl⟩⟩
  bijOn_e :=
    ⟨fun e he => by
      change e ∈ G.toGMDigraph.edgeSet at he
      dsimp only
      rw [dite_eq_left he]
      exact (G.edgeEquiv.symm ⟨e, he⟩).2,
     fun e₁ he₁ e₂ he₂ heq => by
      change e₁ ∈ G.toGMDigraph.edgeSet at he₁
      change e₂ ∈ G.toGMDigraph.edgeSet at he₂
      dsimp only at heq
      rw [dite_eq_left he₁, dite_eq_left he₂] at heq
      exact congrArg Subtype.val (G.edgeEquiv.symm.injective (Fin.ext heq)),
     fun i hi => by
      change i < G.directedEdgesList.length at hi
      let e := G.edgeEquiv ⟨i, hi⟩
      refine ⟨e.1, e.2, ?_⟩
      dsimp only
      rw [dite_eq_left e.2]
      exact congrArg Fin.val (G.edgeEquiv.symm_apply_apply ⟨i, hi⟩)⟩
  head_eq e he := by
    change e ∈ G.toGMDigraph.edgeSet at he
    have hi : (G.edgeEquiv.symm ⟨e, he⟩).1 < G.directedEdgesList.length :=
      (G.edgeEquiv.symm ⟨e, he⟩).2
    change (rootedDigraphOfZ G Z).toGMRootedDigraph.digraph.head
        (if he' : e ∈ G.toGMDigraph.edgeSet then (G.edgeEquiv.symm ⟨e, he'⟩).1 else 0) =
      e.2.1
    rw [dite_eq_left he]
    dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
      rootedDigraphOfZ, MultiDigraph.toComputeDigraph]
    rw [dite_eq_left hi]
    have hfst : ((G.directedEdgesList[(G.edgeEquiv.symm ⟨e, he⟩).1]'hi).2).1 =
        (G.edgeToGMTriple (G.edgeEquiv.symm ⟨e, he⟩)).1.2.1 := by
      dsimp [MultiDigraph.edgeToGMTriple]
      exact (congrArg Prod.snd (G.getElem_directedEdgeTriples_fst_snd _ hi)).symm
    rw [hfst, ← MultiDigraph.edgeEquiv_apply]
    have hsymm : (G.edgeEquiv (G.edgeEquiv.symm ⟨e, he⟩)).1 = e :=
      congrArg Subtype.val (G.edgeEquiv.apply_symm_apply ⟨e, he⟩)
    exact congrArg (fun x : ℕ × ℕ × ℕ => x.2.1) hsymm
  tail_eq e he := by
    change e ∈ G.toGMDigraph.edgeSet at he
    have hi : (G.edgeEquiv.symm ⟨e, he⟩).1 < G.directedEdgesList.length :=
      (G.edgeEquiv.symm ⟨e, he⟩).2
    change (rootedDigraphOfZ G Z).toGMRootedDigraph.digraph.tail
        (if he' : e ∈ G.toGMDigraph.edgeSet then (G.edgeEquiv.symm ⟨e, he'⟩).1 else 0) =
      e.1
    rw [dite_eq_left he]
    dsimp [ComputeRootedDigraph.toGMRootedDigraph, ComputeDigraph.toGMDigraph,
      rootedDigraphOfZ, MultiDigraph.toComputeDigraph]
    rw [dite_eq_left hi]
    have hfst : ((G.directedEdgesList[(G.edgeEquiv.symm ⟨e, he⟩).1]'hi).1).1 =
        (G.edgeToGMTriple (G.edgeEquiv.symm ⟨e, he⟩)).1.1 := by
      dsimp [MultiDigraph.edgeToGMTriple]
      exact (congrArg Prod.fst (G.getElem_directedEdgeTriples_fst_snd _ hi)).symm
    rw [hfst, ← MultiDigraph.edgeEquiv_apply]
    have hsymm : (G.edgeEquiv (G.edgeEquiv.symm ⟨e, he⟩)).1 = e :=
      congrArg Subtype.val (G.edgeEquiv.apply_symm_apply ⟨e, he⟩)
    exact congrArg (fun x : ℕ × ℕ × ℕ => x.1) hsymm
  map_roots _ := rfl

/-- Equivalence between `HasRootedDigraphModel H (rootedDigraphOfZ G Z)` and
`GM13.IsRootedDigraphMinor H.toGMRootedDigraph (G.toGMRootedDigraph Z)`. -/
theorem hasRootedDigraphModel_iff_isRootedDigraphMinor_toGMRootedDigraph
    {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (H : ComputeRootedDigraph Z.card) :
    HasRootedDigraphModel H (rootedDigraphOfZ G Z) ↔
      GM13.IsRootedDigraphMinor H.toGMRootedDigraph (G.toGMRootedDigraph Z) := by
  rw [hasRootedDigraphModel_iff_isRootedDigraphMinor]
  exact ⟨isRootedDigraphMinor_of_iso_right (G.isoToGMRootedDigraph Z),
    isRootedDigraphMinor_of_iso_right (G.isoFromGMRootedDigraph Z)⟩

/-- Equivalence between `HasRootedDigraphModel H (rootedDigraphOfZ G Z)` and
`(G.toGMRootedDigraph Z).InFolio H.toGMRootedDigraph`. -/
theorem hasRootedDigraphModel_iff_inFolio
    {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) (H : ComputeRootedDigraph Z.card) :
    HasRootedDigraphModel H (rootedDigraphOfZ G Z) ↔
      (G.toGMRootedDigraph Z).InFolio H.toGMRootedDigraph := by
  unfold GM13.RootedDigraph.InFolio
  rw [hasRootedDigraphModel_iff_isRootedDigraphMinor_toGMRootedDigraph]
  exact ⟨fun h => ⟨H.isFinite_toGMRootedDigraph, h⟩, fun h => h.2⟩

/-- Equivalence between `(G.toGMRootedDigraph Z).InDeltaFolio δ H.toGMRootedDigraph` and
`H.HasDetailLe δ ∧ HasRootedDigraphModel H (rootedDigraphOfZ G Z)`. -/
theorem inDeltaFolio_iff_hasDetailLe_and_hasRootedDigraphModel
    {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n))
    (H : ComputeRootedDigraph Z.card) :
    (G.toGMRootedDigraph Z).InDeltaFolio δ H.toGMRootedDigraph ↔
      H.HasDetailLe δ ∧ HasRootedDigraphModel H (rootedDigraphOfZ G Z) := by
  unfold GM13.RootedDigraph.InDeltaFolio
  rw [← hasRootedDigraphModel_iff_inFolio, ← H.hasDetailLe_iff_detail_le, and_comm]

/-- Canonical `FolioSetRep Z.card δ` representing the `δ`-folio of `G` relative to `Z`. -/
noncomputable def deltaFolioRepOfZ {n : ℕ} (δ : ℕ) (G : MultiDigraph n)
    (Z : Finset (Fin n)) : FolioSetRep Z.card δ :=
  @buildFolioSetRep Z.card δ
    (fun H => HasRootedDigraphModel H (rootedDigraphOfZ G Z))
    (Classical.decPred _)

theorem isDeltaFolioRep_deltaFolioRepOfZ {n : ℕ} (δ : ℕ) (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    IsDeltaFolioRep δ G Z (deltaFolioRepOfZ δ G Z) := by
  intro H hdet
  exact @memIso_buildFolioSetRep_iff Z.card δ
    (fun H' => HasRootedDigraphModel H' (rootedDigraphOfZ G Z))
    (Classical.decPred _)
    (fun _ _ hiso => HasRootedDigraphModel.iff_of_iso hiso)
    H hdet

/-- Cast a `FolioSetRep q₁ δ` along an equality `q₁ = q₂`. -/
def FolioSetRep.castCard {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (F : FolioSetRep q₁ δ) :
    FolioSetRep q₂ δ :=
  h ▸ F

/-- Equivalence between `GM13.HasSameDeltaFolio (G₁.toGMRootedDigraph Z) (G₂.toGMRootedDigraph Z) δ`
and `dp`'s `IsDeltaFolioRep` condition. -/
theorem hasSameDeltaFolio_iff_forall_isDeltaFolioRep {n : ℕ} (δ : ℕ)
    (G₁ G₂ : MultiDigraph n) (Z : Finset (Fin n)) :
    GM13.HasSameDeltaFolio (G₁.toGMRootedDigraph Z) (G₂.toGMRootedDigraph Z) δ ↔
      ∀ F : FolioSetRep Z.card δ, IsDeltaFolioRep δ G₁ Z F ↔ IsDeltaFolioRep δ G₂ Z F := by
  rw [hasSameDeltaFolio_iff_forall_computeRootedDigraph]
  constructor
  · intro hsame F
    refine ⟨fun hF H hdet => ?_, fun hF H hdet => ?_⟩
    · rw [hF H hdet, hasRootedDigraphModel_iff_inFolio, hsame H hdet,
        ← hasRootedDigraphModel_iff_inFolio]
    · rw [hF H hdet, hasRootedDigraphModel_iff_inFolio, ← hsame H hdet,
        ← hasRootedDigraphModel_iff_inFolio]
  · intro hall H hdet
    have hF₁ := isDeltaFolioRep_deltaFolioRepOfZ δ G₁ Z
    have hF₂ := (hall (deltaFolioRepOfZ δ G₁ Z)).mp hF₁
    rw [← hasRootedDigraphModel_iff_inFolio, ← hF₁ H hdet, hF₂ H hdet,
      hasRootedDigraphModel_iff_inFolio]

/-- Equivalence between `GM13.HasSameDeltaFolioRel G₁.toGMDigraph G₂.toGMDigraph δ Z.toNatSet`
and `dp`'s `IsDeltaFolioRep` condition. -/
theorem hasSameDeltaFolioRel_iff_forall_isDeltaFolioRep {n : ℕ} (δ : ℕ)
    (G₁ G₂ : MultiDigraph n) (Z : Finset (Fin n)) :
    GM13.HasSameDeltaFolioRel G₁.toGMDigraph G₂.toGMDigraph δ Z.toNatSet ↔
      ∀ F : FolioSetRep Z.card δ, IsDeltaFolioRep δ G₁ Z F ↔ IsDeltaFolioRep δ G₂ Z F := by
  rw [hasSameDeltaFolioRel_iff_hasSameDeltaFolio_of_injective
    (toNatSet_subset_lt Z) (toNatSet_subset_lt Z)
    (injective_rootsZ_val Z) (range_rootsZ_val_eq_toNatSet Z)]
  exact hasSameDeltaFolio_iff_forall_isDeltaFolioRep δ G₁ G₂ Z

/-- Embed `G' : MultiDigraph n'` along `emb : Fin n' → Fin n` as a `GM13.Digraph ℕ (ℕ × ℕ × ℕ)`. -/
def MultiDigraph.toEmbeddedGMDigraph {n n' : ℕ} (G' : MultiDigraph n')
    (emb : Fin n' → Fin n) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) where
  vertexSet := {u : ℕ | ∃ x : Fin n', (emb x).1 = u}
  edgeSet := {e : ℕ × ℕ × ℕ | ∃ x y : Fin n',
    (emb x).1 = e.1 ∧ (emb y).1 = e.2.1 ∧ e.2.2 < G'.edgeMult x y}
  head e := e.2.1
  tail e := e.1
  head_mem _ := by rintro ⟨x, y, _, hy, _⟩; exact ⟨y, hy⟩
  tail_mem _ := by rintro ⟨x, y, hx, _, _⟩; exact ⟨x, hx⟩

theorem MultiDigraph.isSubdigraph_toEmbeddedGMDigraph {n n' : ℕ}
    {G : MultiDigraph n} {G' : MultiDigraph n'} {emb : Fin n' → Fin n}
    (hle : ∀ u v : Fin n', G'.edgeMult u v ≤ G.edgeMult (emb u) (emb v)) :
    (G'.toEmbeddedGMDigraph emb).IsSubdigraph G.toGMDigraph where
  vertexSet_subset := by
    rintro _ ⟨x, rfl⟩
    exact (emb x).2
  edgeSet_subset := by
    rintro ⟨u, v, k⟩ ⟨x, y, hx, hy, hk⟩
    dsimp only at hx hy hk
    subst hx hy
    exact ⟨(emb x).2, (emb y).2, lt_of_lt_of_le hk (hle x y)⟩
  head_eq _ _ := rfl
  tail_eq _ _ := rfl

theorem MultiDigraph.toNatSet_subset_toEmbeddedGMDigraph {n n' : ℕ}
    {Z : Finset (Fin n)} {Z' : Finset (Fin n')} (G' : MultiDigraph n')
    {emb : Fin n' → Fin n} (hZ : Z'.image emb = Z) :
    Z.toNatSet ⊆ (G'.toEmbeddedGMDigraph emb).vertexSet := by
  rintro _ ⟨u, huZ, rfl⟩
  rw [Finset.mem_coe, ← hZ, Finset.mem_image] at huZ
  rcases huZ with ⟨x, _, rfl⟩
  exact ⟨x, rfl⟩

theorem sortedFinsetList_map_of_strictMono {n n' : ℕ} {Z' : Finset (Fin n')} {Z : Finset (Fin n)}
    {emb : Fin n' → Fin n} (hemb : StrictMono emb) (hZ : Z'.image emb = Z) :
    (sortedFinsetList Z').map emb = sortedFinsetList Z := by
  have hp₁ : ((sortedFinsetList Z').map emb).Pairwise (· < ·) :=
    List.pairwise_map.mpr ((pairwise_lt_sortedFinsetList Z').imp (fun h => hemb h))
  have hp₂ : (sortedFinsetList Z).Pairwise (· < ·) := pairwise_lt_sortedFinsetList Z
  have hnd₁ : ((sortedFinsetList Z').map emb).Nodup :=
    (nodup_sortedFinsetList Z').map hemb.injective
  have hnd₂ : (sortedFinsetList Z).Nodup := nodup_sortedFinsetList Z
  have hperm : List.Perm ((sortedFinsetList Z').map emb) (sortedFinsetList Z) := by
    rw [List.perm_ext_iff_of_nodup hnd₁ hnd₂]
    intro u
    simp [← hZ]
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => False.elim (lt_asymm h1 h2)) hp₁ hp₂

theorem rootsZ_of_strictMono {n n' : ℕ} {Z' : Finset (Fin n')} {Z : Finset (Fin n)}
    {emb : Fin n' → Fin n} (hemb : StrictMono emb) (hZ : Z'.image emb = Z)
    (hcard : Z'.card = Z.card) (i : Fin Z.card) :
    emb (rootsZ Z' (i.cast hcard.symm)) = rootsZ Z i := by
  unfold rootsZ
  have hmap := sortedFinsetList_map_of_strictMono hemb hZ
  have hget := congrArg (fun L : List (Fin n) => L[i.1]?) hmap
  have hi' : i.1 < (sortedFinsetList Z').length := by
    rw [length_sortedFinsetList, hcard]; exact i.2
  have hi : i.1 < (sortedFinsetList Z).length := by
    rw [length_sortedFinsetList]; exact i.2
  rw [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hget
  exact Option.some.inj hget

/-- Digraph isomorphism from `G'.toGMDigraph` to `G'.toEmbeddedGMDigraph emb` for an injective
embedding `emb : Fin n' → Fin n`. -/
noncomputable def MultiDigraph.isoToEmbeddedGMDigraph {n n' : ℕ} (G' : MultiDigraph n')
    {emb : Fin n' → Fin n} (hemb : Function.Injective emb) :
    GM13.Digraph.Iso G'.toGMDigraph (G'.toEmbeddedGMDigraph emb) where
  vMap u := if hu : u < n' then (emb ⟨u, hu⟩).1 else 0
  eMap e :=
    if h : e.1 < n' ∧ e.2.1 < n' then
      ((emb ⟨e.1, h.1⟩).1, (emb ⟨e.2.1, h.2⟩).1, e.2.2)
    else (0, 0, 0)
  bijOn_v :=
    ⟨fun u hu => by
      change u < n' at hu
      dsimp only [MultiDigraph.toEmbeddedGMDigraph, mem_ofPred_eq]
      rw [dite_eq_left hu]
      exact ⟨⟨u, hu⟩, rfl⟩,
     fun u₁ hu₁ u₂ hu₂ heq => by
      change u₁ < n' at hu₁
      change u₂ < n' at hu₂
      dsimp only at heq
      rw [dite_eq_left hu₁, dite_eq_left hu₂] at heq
      exact congrArg Fin.val (hemb (Fin.ext heq)),
     fun v ⟨x, hx⟩ => by
      refine ⟨x.1, x.2, ?_⟩
      dsimp only
      rw [dite_eq_left x.2]
      exact hx⟩
  bijOn_e :=
    ⟨fun e ⟨hu, hv, hk⟩ => by
      have h : e.1 < n' ∧ e.2.1 < n' := ⟨hu, hv⟩
      dsimp only [MultiDigraph.toEmbeddedGMDigraph, mem_ofPred_eq]
      rw [dite_eq_left h]
      exact ⟨⟨e.1, hu⟩, ⟨e.2.1, hv⟩, rfl, rfl, hk⟩,
     fun e₁ ⟨hu₁, hv₁, _⟩ e₂ ⟨hu₂, hv₂, _⟩ heq => by
      have h₁ : e₁.1 < n' ∧ e₁.2.1 < n' := ⟨hu₁, hv₁⟩
      have h₂ : e₂.1 < n' ∧ e₂.2.1 < n' := ⟨hu₂, hv₂⟩
      dsimp only at heq
      rw [dite_eq_left h₁, dite_eq_left h₂] at heq
      rcases e₁ with ⟨u₁, v₁, k₁⟩
      rcases e₂ with ⟨u₂, v₂, k₂⟩
      simp only [Prod.mk.injEq] at heq
      have hxu : u₁ = u₂ := congrArg Fin.val (hemb (Fin.ext heq.1))
      have hxv : v₁ = v₂ := congrArg Fin.val (hemb (Fin.ext heq.2.1))
      rw [hxu, hxv, heq.2.2],
     fun e ⟨x, y, hx, hy, hk⟩ => by
      refine ⟨(x.1, y.1, e.2.2), ⟨x.2, y.2, hk⟩, ?_⟩
      have h : x.1 < n' ∧ y.1 < n' := ⟨x.2, y.2⟩
      dsimp only
      rw [dite_eq_left h]
      rcases e with ⟨u, v, k⟩
      dsimp only at hx hy
      rw [hx, hy]⟩
  head_eq := fun e ⟨hu, hv, _⟩ => by
    have h : e.1 < n' ∧ e.2.1 < n' := ⟨hu, hv⟩
    change (if h' : e.1 < n' ∧ e.2.1 < n' then
        ((emb ⟨e.1, h'.1⟩).1, (emb ⟨e.2.1, h'.2⟩).1, e.2.2) else (0, 0, 0)).2.1 =
      if hu' : e.2.1 < n' then (emb ⟨e.2.1, hu'⟩).1 else 0
    rw [dite_eq_left h, dite_eq_left hv]
  tail_eq := fun e ⟨hu, hv, _⟩ => by
    have h : e.1 < n' ∧ e.2.1 < n' := ⟨hu, hv⟩
    change (if h' : e.1 < n' ∧ e.2.1 < n' then
        ((emb ⟨e.1, h'.1⟩).1, (emb ⟨e.2.1, h'.2⟩).1, e.2.2) else (0, 0, 0)).1 =
      if hu' : e.1 < n' then (emb ⟨e.1, hu'⟩).1 else 0
    rw [dite_eq_left h, dite_eq_left hu]

/-- Digraph isomorphism from `G'.toEmbeddedGMDigraph emb` to `G'.toGMDigraph` for an injective
embedding `emb : Fin n' → Fin n`. -/
noncomputable def MultiDigraph.isoFromEmbeddedGMDigraph {n n' : ℕ} (G' : MultiDigraph n')
    {emb : Fin n' → Fin n} (hemb : Function.Injective emb) :
    GM13.Digraph.Iso (G'.toEmbeddedGMDigraph emb) G'.toGMDigraph where
  vMap v :=
    if hv : ∃ x : Fin n', (emb x).1 = v then (hv.choose).1 else 0
  eMap e :=
    if he : (∃ x : Fin n', (emb x).1 = e.1) ∧ (∃ y : Fin n', (emb y).1 = e.2.1) then
      ((he.1.choose).1, (he.2.choose).1, e.2.2)
    else (0, 0, 0)
  bijOn_v :=
    ⟨fun v hv => by
      change ∃ x : Fin n', (emb x).1 = v at hv
      dsimp only [MultiDigraph.toGMDigraph, mem_ofPred_eq]
      rw [dite_eq_left hv]
      exact (hv.choose).2,
     fun v₁ hv₁ v₂ hv₂ heq => by
      change ∃ x : Fin n', (emb x).1 = v₁ at hv₁
      change ∃ x : Fin n', (emb x).1 = v₂ at hv₂
      dsimp only at heq
      rw [dite_eq_left hv₁, dite_eq_left hv₂] at heq
      have hx : hv₁.choose = hv₂.choose := Fin.ext heq
      rw [← hv₁.choose_spec, ← hv₂.choose_spec, hx],
     fun u hu => by
      change u < n' at hu
      have hv : ∃ x : Fin n', (emb x).1 = (emb ⟨u, hu⟩).1 := ⟨⟨u, hu⟩, rfl⟩
      refine ⟨(emb ⟨u, hu⟩).1, hv, ?_⟩
      dsimp only
      rw [dite_eq_left hv]
      exact congrArg Fin.val (hemb (Fin.ext hv.choose_spec))⟩
  bijOn_e :=
    ⟨fun e ⟨x, y, hx, hy, hk⟩ => by
      have he : (∃ x' : Fin n', (emb x').1 = e.1) ∧ (∃ y' : Fin n', (emb y').1 = e.2.1) :=
        ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      dsimp only [MultiDigraph.toGMDigraph, mem_ofPred_eq]
      rw [dite_eq_left he]
      have hx_eq : he.1.choose = x := hemb (Fin.ext (he.1.choose_spec.trans hx.symm))
      have hy_eq : he.2.choose = y := hemb (Fin.ext (he.2.choose_spec.trans hy.symm))
      refine ⟨(he.1.choose).2, (he.2.choose).2, ?_⟩
      simpa [hx_eq, hy_eq] using hk,
     fun e₁ ⟨x₁, y₁, hx₁, hy₁, _⟩ e₂ ⟨x₂, y₂, hx₂, hy₂, _⟩ heq => by
      have he₁ : (∃ x' : Fin n', (emb x').1 = e₁.1) ∧ (∃ y' : Fin n', (emb y').1 = e₁.2.1) :=
        ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩
      have he₂ : (∃ x' : Fin n', (emb x').1 = e₂.1) ∧ (∃ y' : Fin n', (emb y').1 = e₂.2.1) :=
        ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩
      dsimp only at heq
      rw [dite_eq_left he₁, dite_eq_left he₂] at heq
      simp only [Prod.mk.injEq] at heq
      have hxu : he₁.1.choose = he₂.1.choose := Fin.ext heq.1
      have hxv : he₁.2.choose = he₂.2.choose := Fin.ext heq.2.1
      have hu : e₁.1 = e₂.1 := by
        rw [← he₁.1.choose_spec, ← he₂.1.choose_spec, hxu]
      have hv : e₁.2.1 = e₂.2.1 := by
        rw [← he₁.2.choose_spec, ← he₂.2.choose_spec, hxv]
      exact Prod.ext hu (Prod.ext hv heq.2.2),
     fun e ⟨hu, hv, hk⟩ => by
      let x : Fin n' := ⟨e.1, hu⟩
      let y : Fin n' := ⟨e.2.1, hv⟩
      refine ⟨((emb x).1, (emb y).1, e.2.2), ⟨x, y, rfl, rfl, hk⟩, ?_⟩
      have he : (∃ x' : Fin n', (emb x').1 = (emb x).1) ∧
          (∃ y' : Fin n', (emb y').1 = (emb y).1) :=
        ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
      dsimp only
      rw [dite_eq_left he]
      have hx_eq : he.1.choose = x := hemb (Fin.ext he.1.choose_spec)
      have hy_eq : he.2.choose = y := hemb (Fin.ext he.2.choose_spec)
      rcases e with ⟨u, v, k⟩
      simp [hx_eq, hy_eq, x, y]⟩
  head_eq := fun e ⟨x, y, hx, hy, _⟩ => by
    have he : (∃ x' : Fin n', (emb x').1 = e.1) ∧ (∃ y' : Fin n', (emb y').1 = e.2.1) :=
      ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    change G'.toGMDigraph.head
        (if he' : (∃ x' : Fin n', (emb x').1 = e.1) ∧ (∃ y' : Fin n', (emb y').1 = e.2.1) then
          ((he'.1.choose).1, (he'.2.choose).1, e.2.2) else (0, 0, 0)) =
      if hv : ∃ x' : Fin n', (emb x').1 = e.2.1 then (hv.choose).1 else 0
    rw [dite_eq_left he, dite_eq_left he.2]
    rfl
  tail_eq := fun e ⟨x, y, hx, hy, _⟩ => by
    have he : (∃ x' : Fin n', (emb x').1 = e.1) ∧ (∃ y' : Fin n', (emb y').1 = e.2.1) :=
      ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    change G'.toGMDigraph.tail
        (if he' : (∃ x' : Fin n', (emb x').1 = e.1) ∧ (∃ y' : Fin n', (emb y').1 = e.2.1) then
          ((he'.1.choose).1, (he'.2.choose).1, e.2.2) else (0, 0, 0)) =
      if hv : ∃ x' : Fin n', (emb x').1 = e.1 then (hv.choose).1 else 0
    rw [dite_eq_left he, dite_eq_left he.1]
    rfl

@[simp]
theorem MultiDigraph.ncard_vertexSet_toEmbeddedGMDigraph {n n' : ℕ} (G' : MultiDigraph n')
    {emb : Fin n' → Fin n} (hemb : Function.Injective emb) :
    (G'.toEmbeddedGMDigraph emb).vertexSet.ncard = n' := by
  have iso := G'.isoToEmbeddedGMDigraph hemb
  rw [← iso.bijOn_v.image_eq, iso.bijOn_v.injOn.ncard_image, G'.ncard_vertexSet_toGMDigraph]

@[simp]
theorem MultiDigraph.ncard_edgeSet_toEmbeddedGMDigraph {n n' : ℕ} (G' : MultiDigraph n')
    {emb : Fin n' → Fin n} (hemb : Function.Injective emb) :
    (G'.toEmbeddedGMDigraph emb).edgeSet.ncard = G'.numEdges := by
  have iso := G'.isoToEmbeddedGMDigraph hemb
  rw [← iso.bijOn_e.image_eq, iso.bijOn_e.injOn.ncard_image, G'.ncard_edgeSet_toGMDigraph]

/-- Rooted `GM13.RootedDigraph` built from `G'.toEmbeddedGMDigraph emb` and `Z = Z'.image emb`. -/
def MultiDigraph.toEmbeddedGMRootedDigraph {n n' : ℕ} (G' : MultiDigraph n')
    {Z : Finset (Fin n)} {Z' : Finset (Fin n')}
    {emb : Fin n' → Fin n} (hZ : Z'.image emb = Z) :
    GM13.RootedDigraph ℕ (ℕ × ℕ × ℕ) Z.card where
  digraph := G'.toEmbeddedGMDigraph emb
  roots i := (rootsZ Z i).1
  roots_mem i :=
    G'.toNatSet_subset_toEmbeddedGMDigraph hZ ⟨rootsZ Z i, rootsZ_mem Z i, rfl⟩

/-- Reindex the roots of a `GM13.RootedDigraph` along an equality `k₁ = k₂`. -/
def _root_.GraphMinor.GM13.RootedDigraph.castRoots {α β : Type*} {k₁ k₂ : ℕ}
    (h : k₁ = k₂) (R : GM13.RootedDigraph α β k₁) : GM13.RootedDigraph α β k₂ where
  digraph := R.digraph
  roots i := R.roots (i.cast h.symm)
  roots_mem i := R.roots_mem (i.cast h.symm)

theorem isRootedDigraphMinor_castRoots {α β : Type*} {q₁ q₂ : ℕ} (h : q₁ = q₂)
    (H : ComputeRootedDigraph q₁) (G : GM13.RootedDigraph α β q₂) :
    GM13.IsRootedDigraphMinor H.toGMRootedDigraph (G.castRoots h.symm) ↔
      GM13.IsRootedDigraphMinor (h ▸ H).toGMRootedDigraph G := by
  subst h
  rfl

theorem isDeltaFolioRep_castCard_iff {n q δ : ℕ} {G : MultiDigraph n} {Z : Finset (Fin n)}
    (h : q = Z.card) (F : FolioSetRep q δ) :
    IsDeltaFolioRep δ G Z (F.castCard h) ↔
      ∀ H : ComputeRootedDigraph q, H.HasDetailLe δ →
        (F.MemIso H ↔ HasRootedDigraphModel (h ▸ H) (rootedDigraphOfZ G Z)) := by
  subst h
  rfl

/-- Equivalence between `HasRootedDigraphModel (hcard.symm ▸ H) (rootedDigraphOfZ G' Z')`
and `(G'.toEmbeddedGMRootedDigraph hZ).InFolio H.toGMRootedDigraph` when `StrictMono emb`. -/
theorem hasRootedDigraphModel_iff_inFolio_toEmbeddedGMRootedDigraph
    {n n' : ℕ} (G' : MultiDigraph n') {Z : Finset (Fin n)} {Z' : Finset (Fin n')}
    {emb : Fin n' → Fin n} (hemb : StrictMono emb) (hZ : Z'.image emb = Z)
    (hcard : Z'.card = Z.card) (H : ComputeRootedDigraph Z.card) :
    HasRootedDigraphModel (hcard.symm ▸ H) (rootedDigraphOfZ G' Z') ↔
      (G'.toEmbeddedGMRootedDigraph hZ).InFolio H.toGMRootedDigraph := by
  rw [hasRootedDigraphModel_iff_isRootedDigraphMinor_toGMRootedDigraph,
    ← isRootedDigraphMinor_castRoots hcard.symm H (G'.toGMRootedDigraph Z')]
  unfold GM13.RootedDigraph.InFolio
  have isoTo : GM13.RootedDigraph.Iso
      ((G'.toGMRootedDigraph Z').castRoots hcard)
      (G'.toEmbeddedGMRootedDigraph hZ) :=
    { toIso := G'.isoToEmbeddedGMDigraph hemb.injective
      map_roots := fun i => by
        have hlt : (rootsZ Z' (i.cast hcard.symm)).1 < n' := (rootsZ Z' (i.cast hcard.symm)).2
        change (if hu : (rootsZ Z' (i.cast hcard.symm)).1 < n' then
            (emb ⟨(rootsZ Z' (i.cast hcard.symm)).1, hu⟩).1 else 0) =
          (rootsZ Z i).1
        rw [dite_eq_left hlt]
        exact congrArg Fin.val (rootsZ_of_strictMono hemb hZ hcard i) }
  have isoFrom : GM13.RootedDigraph.Iso
      (G'.toEmbeddedGMRootedDigraph hZ)
      ((G'.toGMRootedDigraph Z').castRoots hcard) :=
    { toIso := G'.isoFromEmbeddedGMDigraph hemb.injective
      map_roots := fun i => by
        dsimp [GM13.RootedDigraph.castRoots, MultiDigraph.toGMRootedDigraph,
          MultiDigraph.toEmbeddedGMRootedDigraph, MultiDigraph.isoFromEmbeddedGMDigraph]
        have hroot := rootsZ_of_strictMono hemb hZ hcard i
        have hv : ∃ x : Fin n', (emb x).1 = (rootsZ Z i).1 :=
          ⟨rootsZ Z' (i.cast hcard.symm), congrArg Fin.val hroot⟩
        rw [dite_eq_left hv]
        exact congrArg Fin.val (hemb.injective (Fin.ext (hv.choose_spec.trans
          (congrArg Fin.val hroot.symm)))) }
  exact ⟨fun h => ⟨H.isFinite_toGMRootedDigraph, isRootedDigraphMinor_of_iso_right isoTo h⟩,
    fun ⟨_, h⟩ => isRootedDigraphMinor_of_iso_right isoFrom h⟩

/-- Equivalence between
`GM13.HasSameDeltaFolioRel G.toGMDigraph (G'.toEmbeddedGMDigraph emb) δ Z.toNatSet`
and `dp`'s `IsDeltaFolioRep` condition when `StrictMono emb` and `Z'.image emb = Z`. -/
theorem hasSameDeltaFolioRel_toEmbeddedGMDigraph_iff_forall_isDeltaFolioRep
    {n n' : ℕ} (δ : ℕ) (G : MultiDigraph n) (G' : MultiDigraph n')
    {Z : Finset (Fin n)} {Z' : Finset (Fin n')}
    {emb : Fin n' → Fin n} (hemb : StrictMono emb) (hZ : Z'.image emb = Z)
    (hcard : Z'.card = Z.card) :
    GM13.HasSameDeltaFolioRel G.toGMDigraph (G'.toEmbeddedGMDigraph emb) δ Z.toNatSet ↔
      ∀ F : FolioSetRep Z.card δ,
        IsDeltaFolioRep δ G Z F ↔ IsDeltaFolioRep δ G' Z' (F.castCard hcard.symm) := by
  rw [hasSameDeltaFolioRel_iff_hasSameDeltaFolio_of_injective
    (toNatSet_subset_lt Z) (G'.toNatSet_subset_toEmbeddedGMDigraph hZ)
    (injective_rootsZ_val Z) (range_rootsZ_val_eq_toNatSet Z)]
  change GM13.HasSameDeltaFolio (G.toGMRootedDigraph Z) (G'.toEmbeddedGMRootedDigraph hZ) δ ↔ _
  rw [hasSameDeltaFolio_iff_forall_computeRootedDigraph]
  constructor
  · intro hsame F
    rw [isDeltaFolioRep_castCard_iff hcard.symm F]
    refine ⟨fun hF H hdet => ?_, fun hF H hdet => ?_⟩
    · rw [hF H hdet, hasRootedDigraphModel_iff_inFolio, hsame H hdet,
        ← hasRootedDigraphModel_iff_inFolio_toEmbeddedGMRootedDigraph G' hemb hZ hcard H]
    · rw [hF H hdet,
        hasRootedDigraphModel_iff_inFolio_toEmbeddedGMRootedDigraph G' hemb hZ hcard H,
        ← hsame H hdet, ← hasRootedDigraphModel_iff_inFolio]
  · intro hall H hdet
    have hF₁ := isDeltaFolioRep_deltaFolioRepOfZ δ G Z
    have hF₂ := (isDeltaFolioRep_castCard_iff hcard.symm (deltaFolioRepOfZ δ G Z)).mp
      ((hall (deltaFolioRepOfZ δ G Z)).mp hF₁)
    rw [← hasRootedDigraphModel_iff_inFolio, ← hF₁ H hdet]
    exact (hF₂ H hdet).trans
      (hasRootedDigraphModel_iff_inFolio_toEmbeddedGMRootedDigraph G' hemb hZ hcard H)

/-- Delete vertex `v : Fin (n + 1)` from `G : MultiDigraph (n + 1)` via `v.succAbove`. -/
def MultiDigraph.eraseVertex {n : ℕ} (G : MultiDigraph (n + 1)) (v : Fin (n + 1)) :
    MultiDigraph n where
  edgeMult x y := G.edgeMult (v.succAbove x) (v.succAbove y)

/-- Preimage of `Z : Finset (Fin (n + 1))` under `v.succAbove : Fin n → Fin (n + 1)`. -/
def eraseVertexFinset {n : ℕ} (Z : Finset (Fin (n + 1))) (v : Fin (n + 1)) :
    Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => v.succAbove x ∈ Z)

theorem image_eraseVertexFinset {n : ℕ} {Z : Finset (Fin (n + 1))} {v : Fin (n + 1)}
    (hv : v ∉ Z) :
    (eraseVertexFinset Z v).image v.succAbove = Z := by
  ext u
  simp only [eraseVertexFinset, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro hu
    have hne : u ≠ v := fun h => hv (h ▸ hu)
    rcases Fin.exists_succAbove_eq hne with ⟨x, rfl⟩
    exact ⟨x, hu, rfl⟩

theorem card_eraseVertexFinset {n : ℕ} {Z : Finset (Fin (n + 1))} {v : Fin (n + 1)}
    (hv : v ∉ Z) :
    (eraseVertexFinset Z v).card = Z.card := by
  conv_rhs => rw [← image_eraseVertexFinset hv]
  rw [Finset.card_image_of_injective _ (Fin.strictMono_succAbove v).injective]

theorem _root_.GraphMinor.GM13.Digraph.ext_of_eq {α β : Type*} {D₁ D₂ : GM13.Digraph α β}
    (hV : D₁.vertexSet = D₂.vertexSet) (hE : D₁.edgeSet = D₂.edgeSet)
    (hh : D₁.head = D₂.head) (ht : D₁.tail = D₂.tail) :
    D₁ = D₂ := by
  cases D₁; cases D₂
  dsimp only at hV hE hh ht
  subst hV hE hh ht
  rfl

theorem MultiDigraph.toEmbeddedGMDigraph_eraseVertex_eq_deleteVertex {n : ℕ}
    (G : MultiDigraph (n + 1)) (v : Fin (n + 1)) :
    (G.eraseVertex v).toEmbeddedGMDigraph v.succAbove = G.toGMDigraph.deleteVertex v.1 := by
  refine GM13.Digraph.ext_of_eq ?_ ?_ rfl rfl
  · ext u
    simp only [MultiDigraph.toEmbeddedGMDigraph, GM13.Digraph.deleteVertex,
      GM13.Digraph.deleteVertices, GM13.Digraph.induce, MultiDigraph.toGMDigraph,
      mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(v.succAbove x).2, (v.succAbove x).2, fun h => Fin.succAbove_ne v x (Fin.ext h)⟩
    · rintro ⟨hu, _, hne⟩
      have hne' : (⟨u, hu⟩ : Fin (n + 1)) ≠ v := fun h => hne (congrArg Fin.val h)
      rcases Fin.exists_succAbove_eq hne' with ⟨x, hx⟩
      exact ⟨x, congrArg Fin.val hx⟩
  · ext ⟨u, w, k⟩
    simp only [MultiDigraph.toEmbeddedGMDigraph, MultiDigraph.eraseVertex,
      GM13.Digraph.deleteVertex, GM13.Digraph.deleteVertices, GM13.Digraph.induce,
      MultiDigraph.toGMDigraph, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨x, y, hx, hy, hk⟩
      subst hx hy
      exact ⟨⟨(v.succAbove x).2, (v.succAbove y).2, hk⟩,
        ⟨(v.succAbove y).2, fun h => Fin.succAbove_ne v y (Fin.ext h)⟩,
        ⟨(v.succAbove x).2, fun h => Fin.succAbove_ne v x (Fin.ext h)⟩⟩
    · rintro ⟨⟨hu, hw, hk⟩, ⟨_, hnew⟩, ⟨_, hneu⟩⟩
      have hneu' : (⟨u, hu⟩ : Fin (n + 1)) ≠ v := fun h => hneu (congrArg Fin.val h)
      have hnew' : (⟨w, hw⟩ : Fin (n + 1)) ≠ v := fun h => hnew (congrArg Fin.val h)
      rcases Fin.exists_succAbove_eq hneu' with ⟨x, hx⟩
      rcases Fin.exists_succAbove_eq hnew' with ⟨y, hy⟩
      refine ⟨x, y, congrArg Fin.val hx, congrArg Fin.val hy, ?_⟩
      simpa [hx, hy] using hk

/-- Equivalence between `GM13.IsIrrelevantVertex G.toGMDigraph δ Z.toNatSet v.1` and `dp`'s
`IsDeltaFolioRep` condition on `G.eraseVertex v` and `eraseVertexFinset Z v`. -/
theorem isIrrelevantVertex_iff_forall_isDeltaFolioRep {n : ℕ} (δ : ℕ)
    (G : MultiDigraph (n + 1)) (Z : Finset (Fin (n + 1))) (v : Fin (n + 1)) (hv : v ∉ Z) :
    GM13.IsIrrelevantVertex G.toGMDigraph δ Z.toNatSet v.1 ↔
      ∀ F : FolioSetRep Z.card δ,
        IsDeltaFolioRep δ G Z F ↔
          IsDeltaFolioRep δ (G.eraseVertex v) (eraseVertexFinset Z v)
            (F.castCard (card_eraseVertexFinset hv).symm) := by
  unfold GM13.IsIrrelevantVertex
  have hv₁ : v.1 ∈ G.toGMDigraph.vertexSet := v.2
  have hv₂ : v.1 ∉ Z.toNatSet := fun h => hv ((mem_toNatSet_iff Z v).mp h)
  have hsymm : GM13.HasSameDeltaFolioRel (G.toGMDigraph.deleteVertex v.1) G.toGMDigraph δ Z.toNatSet ↔
      GM13.HasSameDeltaFolioRel G.toGMDigraph (G.toGMDigraph.deleteVertex v.1) δ Z.toNatSet :=
    ⟨fun h => h.symm, fun h => h.symm⟩
  rw [and_iff_right hv₁, and_iff_right hv₂, hsymm, ← G.toEmbeddedGMDigraph_eraseVertex_eq_deleteVertex v]
  exact hasSameDeltaFolioRel_toEmbeddedGMDigraph_iff_forall_isDeltaFolioRep δ G
    (G.eraseVertex v) (Fin.strictMono_succAbove v) (image_eraseVertexFinset hv)
    (card_eraseVertexFinset hv)

/-- Order-preserving vertex embedding `Fin (n - 1) → Fin n` skipping `v : Fin n`. -/
def eraseVertexEmb : {n : ℕ} → Fin n → Fin (n - 1) → Fin n
  | 0, v, _ => v.elim0
  | _ + 1, v, x => v.succAbove x

@[simp]
theorem eraseVertexEmb_succ {n : ℕ} (v : Fin (n + 1)) :
    eraseVertexEmb v = v.succAbove := rfl

theorem strictMono_eraseVertexEmb {n : ℕ} (v : Fin n) :
    StrictMono (eraseVertexEmb v) := by
  cases n with
  | zero => exact v.elim0
  | succ n' =>
    rw [eraseVertexEmb_succ]
    exact Fin.strictMono_succAbove v

/-- Delete vertex `v : Fin n` from `G : MultiDigraph n` for arbitrary `n : ℕ`. -/
noncomputable def MultiDigraph.deleteVertexAt {n : ℕ} (G : MultiDigraph n) (v : Fin n) :
    MultiDigraph (n - 1) where
  edgeMult x y := G.edgeMult (eraseVertexEmb v x) (eraseVertexEmb v y)

/-- Preimage of `Z : Finset (Fin n)` under `eraseVertexEmb v : Fin (n - 1) → Fin n`. -/
noncomputable def deleteVertexAtFinset {n : ℕ} (Z : Finset (Fin n)) (v : Fin n) :
    Finset (Fin (n - 1)) :=
  Finset.univ.filter (fun x : Fin (n - 1) => eraseVertexEmb v x ∈ Z)

theorem image_deleteVertexAtFinset {n : ℕ} {Z : Finset (Fin n)} {v : Fin n} (hv : v ∉ Z) :
    (deleteVertexAtFinset Z v).image (eraseVertexEmb v) = Z := by
  cases n with
  | zero => exact v.elim0
  | succ n' =>
    change (Finset.univ.filter (fun x : Fin n' => eraseVertexEmb v x ∈ Z)).image
      (eraseVertexEmb v) = Z
    rw [eraseVertexEmb_succ]
    exact image_eraseVertexFinset hv

theorem card_deleteVertexAtFinset {n : ℕ} {Z : Finset (Fin n)} {v : Fin n} (hv : v ∉ Z) :
    (deleteVertexAtFinset Z v).card = Z.card := by
  cases n with
  | zero => exact v.elim0
  | succ n' =>
    change (Finset.univ.filter (fun x : Fin n' => eraseVertexEmb v x ∈ Z)).card = Z.card
    rw [eraseVertexEmb_succ]
    exact card_eraseVertexFinset hv

theorem MultiDigraph.toEmbeddedGMDigraph_deleteVertexAt_eq_deleteVertex {n : ℕ}
    (G : MultiDigraph n) (v : Fin n) :
    (G.deleteVertexAt v).toEmbeddedGMDigraph (eraseVertexEmb v) =
      G.toGMDigraph.deleteVertex v.1 := by
  cases n with
  | zero => exact v.elim0
  | succ n' =>
    have hG : G.deleteVertexAt v = G.eraseVertex v := by
      ext x y
      simp [MultiDigraph.deleteVertexAt, MultiDigraph.eraseVertex, eraseVertexEmb_succ]
    change (G.deleteVertexAt v).toEmbeddedGMDigraph (eraseVertexEmb v) =
      G.toGMDigraph.deleteVertex v.1
    rw [hG, eraseVertexEmb_succ]
    exact G.toEmbeddedGMDigraph_eraseVertex_eq_deleteVertex v

/-- Equivalence between `GM13.IsIrrelevantVertex G.toGMDigraph δ Z.toNatSet v.1` and `dp`'s
`IsDeltaFolioRep` condition on `G.deleteVertexAt v` and `deleteVertexAtFinset Z v` for arbitrary
`n : ℕ`. -/
theorem isIrrelevantVertex_iff_forall_isDeltaFolioRep_at {n : ℕ} (δ : ℕ)
    (G : MultiDigraph n) (Z : Finset (Fin n)) (v : Fin n) (hv : v ∉ Z) :
    GM13.IsIrrelevantVertex G.toGMDigraph δ Z.toNatSet v.1 ↔
      ∀ F : FolioSetRep Z.card δ,
        IsDeltaFolioRep δ G Z F ↔
          IsDeltaFolioRep δ (G.deleteVertexAt v) (deleteVertexAtFinset Z v)
            (F.castCard (card_deleteVertexAtFinset hv).symm) := by
  unfold GM13.IsIrrelevantVertex
  have hv₁ : v.1 ∈ G.toGMDigraph.vertexSet := v.2
  have hv₂ : v.1 ∉ Z.toNatSet := fun h => hv ((mem_toNatSet_iff Z v).mp h)
  have hsymm : GM13.HasSameDeltaFolioRel (G.toGMDigraph.deleteVertex v.1) G.toGMDigraph δ Z.toNatSet ↔
      GM13.HasSameDeltaFolioRel G.toGMDigraph (G.toGMDigraph.deleteVertex v.1) δ Z.toNatSet :=
    ⟨fun h => h.symm, fun h => h.symm⟩
  rw [and_iff_right hv₁, and_iff_right hv₂, hsymm,
    ← G.toEmbeddedGMDigraph_deleteVertexAt_eq_deleteVertex v]
  exact hasSameDeltaFolioRel_toEmbeddedGMDigraph_iff_forall_isDeltaFolioRep δ G
    (G.deleteVertexAt v) (strictMono_eraseVertexEmb v) (image_deleteVertexAtFinset hv)
    (card_deleteVertexAtFinset hv)

/-- Decrement the edge multiplicity of `(u₀, v₀)` in `G : MultiDigraph n` by `1`. -/
noncomputable def MultiDigraph.decEdge {n : ℕ} (G : MultiDigraph n) (u₀ v₀ : Fin n) :
    MultiDigraph n where
  edgeMult u v := if u = u₀ ∧ v = v₀ then G.edgeMult u₀ v₀ - 1 else G.edgeMult u v

theorem MultiDigraph.ncard_edgeFiber_toGMDigraph {n : ℕ} (G : MultiDigraph n) (u₀ v₀ : Fin n) :
    ({e ∈ G.toGMDigraph.edgeSet |
      G.toGMDigraph.head e = v₀.1 ∧ G.toGMDigraph.tail e = u₀.1}).ncard =
      G.edgeMult u₀ v₀ := by
  have heq :
      {e ∈ G.toGMDigraph.edgeSet |
        G.toGMDigraph.head e = v₀.1 ∧ G.toGMDigraph.tail e = u₀.1} =
        (fun k : ℕ => (u₀.1, v₀.1, k)) '' (Finset.range (G.edgeMult u₀ v₀) : Set ℕ) := by
    ext ⟨u, v, k⟩
    simp only [MultiDigraph.toGMDigraph, mem_ofPred_eq, mem_image,
      Finset.mem_coe, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hu, hv, hk⟩, rfl, rfl⟩
      exact ⟨k, hk, rfl, rfl, rfl⟩
    · rintro ⟨k', hk', rfl, rfl, rfl⟩
      exact ⟨⟨u₀.2, v₀.2, hk'⟩, rfl, rfl⟩
  have hinj : Function.Injective (fun k : ℕ => (u₀.1, v₀.1, k)) := by
    intro k₁ k₂ h
    simpa using h
  rw [heq, Set.ncard_image_of_injective _ hinj, Set.ncard_coe_finset, Finset.card_range]

theorem MultiDigraph.toGMDigraph_decEdge_eq_subdigraphOf {n : ℕ} (G : MultiDigraph n)
    (u₀ v₀ : Fin n) (hpos : 0 < G.edgeMult u₀ v₀) :
    (G.decEdge u₀ v₀).toGMDigraph =
      G.toGMDigraph.subdigraphOf G.toGMDigraph.vertexSet
        (G.toGMDigraph.edgeSet \ {(u₀.1, v₀.1, G.edgeMult u₀ v₀ - 1)}) := by
  refine GM13.Digraph.ext_of_eq (Set.inter_self _).symm ?_ rfl rfl
  ext ⟨u, v, k⟩
  simp only [MultiDigraph.toGMDigraph, MultiDigraph.decEdge, GM13.Digraph.subdigraphOf,
    mem_inter_iff, mem_sdiff, mem_singleton_iff, Prod.mk.injEq, mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hv, hk⟩
    split_ifs at hk with h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨⟨⟨hu, hv, by omega⟩, ⟨hu, hv, by omega⟩, by omega⟩, hv, hu⟩
    · refine ⟨⟨⟨hu, hv, hk⟩, ⟨hu, hv, hk⟩, ?_⟩, hv, hu⟩
      rintro ⟨rfl, rfl, _⟩
      exact h ⟨rfl, rfl⟩
  · rintro ⟨⟨⟨hu, hv, hk⟩, _, hne⟩, _, _⟩
    refine ⟨hu, hv, ?_⟩
    split_ifs with h
    · rcases h with ⟨hu_eq, hv_eq⟩
      have hu' : u = u₀.1 := congrArg Fin.val hu_eq
      have hv' : v = v₀.1 := congrArg Fin.val hv_eq
      subst hu' hv'
      simp only [Fin.eta] at hk
      have hk_ne : k ≠ G.edgeMult u₀ v₀ - 1 := fun hk_eq => hne ⟨rfl, rfl, hk_eq⟩
      omega
    · exact hk

theorem MultiDigraph.cap_decEdge_of_lt {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u₀ v₀ : Fin n)
    (hlt : (if u₀ = v₀ then δ else δ + 1) < G.edgeMult u₀ v₀) :
    (G.decEdge u₀ v₀).cap δ = G.cap δ := by
  ext u v
  by_cases h : u = u₀ ∧ v = v₀
  · rcases h with ⟨rfl, rfl⟩
    simp only [MultiDigraph.cap_edgeMult, MultiDigraph.decEdge, and_self, ↓reduceIte, Nat.min_def]
    split_ifs at hlt ⊢ <;> omega
  · simp [MultiDigraph.cap_edgeMult, MultiDigraph.decEdge, h]

/-- Step (1) of GM XIII Algorithm (6.5) (page 87): `G` and `G.cap δ` have the same `δ`-folio
relative to `Z`. -/
theorem hasSameDeltaFolioRel_cap {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n)) :
    GM13.HasSameDeltaFolioRel G.toGMDigraph (G.cap δ).toGMDigraph δ Z.toNatSet := by
  suffices h : ∀ (m : ℕ) (G : MultiDigraph n),
      G.toGMDigraph.edgeSet.ncard ≤ m →
      GM13.HasSameDeltaFolioRel G.toGMDigraph (G.cap δ).toGMDigraph δ Z.toNatSet from
    h G.toGMDigraph.edgeSet.ncard G le_rfl
  intro m
  induction m with
  | zero =>
    intro G hle
    have hcap : G.cap δ = G := by
      ext u v
      have h0 : G.edgeMult u v = 0 := by
        rw [← G.ncard_edgeFiber_toGMDigraph u v]
        have hsub : {e ∈ G.toGMDigraph.edgeSet |
            G.toGMDigraph.head e = v.1 ∧ G.toGMDigraph.tail e = u.1} ⊆
            G.toGMDigraph.edgeSet := sep_subset _ _
        have hle' := Set.ncard_le_ncard hsub G.isFinite_toGMDigraph.finite_E
        omega
      simp [MultiDigraph.cap, h0]
    rw [hcap]
    exact GM13.HasSameDeltaFolioRel.refl _ δ (toNatSet_subset_lt Z)
  | succ m ih =>
    intro G hle
    by_cases hcap : G.cap δ = G
    · rw [hcap]
      exact GM13.HasSameDeltaFolioRel.refl _ δ (toNatSet_subset_lt Z)
    · have hex : ∃ u₀ v₀ : Fin n,
          (if u₀ = v₀ then δ else δ + 1) < G.edgeMult u₀ v₀ := by
        by_contra hall
        push Not at hall
        apply hcap
        ext u v
        rw [MultiDigraph.cap_edgeMult]
        exact Nat.min_eq_left (hall u v)
      rcases hex with ⟨u₀, v₀, hlt⟩
      have hpos : 0 < G.edgeMult u₀ v₀ := by split_ifs at hlt <;> omega
      let e₀ : ℕ × ℕ × ℕ := (u₀.1, v₀.1, G.edgeMult u₀ v₀ - 1)
      have he₀ : e₀ ∈ G.toGMDigraph.edgeSet :=
        ⟨u₀.2, v₀.2, Nat.sub_lt hpos Nat.zero_lt_one⟩
      have hsame_step :
          GM13.HasSameDeltaFolioRel G.toGMDigraph (G.decEdge u₀ v₀).toGMDigraph δ Z.toNatSet := by
        rw [G.toGMDigraph_decEdge_eq_subdigraphOf u₀ v₀ hpos]
        by_cases huv : u₀ = v₀
        · subst huv
          simp only [↓reduceIte] at hlt
          rw [← G.ncard_edgeFiber_toGMDigraph u₀ u₀] at hlt
          exact GM13.hasSameDeltaFolioRel_delete_redundant_loop
            G.isFinite_toGMDigraph (toNatSet_subset_lt Z) he₀ ⟨rfl, rfl⟩ hlt
        · simp only [huv, ↓reduceIte] at hlt
          rw [← G.ncard_edgeFiber_toGMDigraph u₀ v₀] at hlt
          have hne_val : v₀.1 ≠ u₀.1 := Fin.val_ne_of_ne (Ne.symm huv)
          exact GM13.hasSameDeltaFolioRel_delete_redundant_parallel
            G.isFinite_toGMDigraph (toNatSet_subset_lt Z) he₀ ⟨rfl, rfl⟩ hne_val hlt
      have hE_eq :
          (G.decEdge u₀ v₀).toGMDigraph.edgeSet = G.toGMDigraph.edgeSet \ {e₀} := by
        rw [G.toGMDigraph_decEdge_eq_subdigraphOf u₀ v₀ hpos]
        ext e
        simp only [GM13.Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff,
          mem_ofPred_eq]
        exact ⟨fun h => h.1.2,
          fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.toGMDigraph.head_mem he, G.toGMDigraph.tail_mem he⟩⟩
      have hncard_le : (G.decEdge u₀ v₀).toGMDigraph.edgeSet.ncard ≤ m := by
        rw [hE_eq, Set.ncard_sdiff_singleton_of_mem he₀]
        have hpos_E : 0 < G.toGMDigraph.edgeSet.ncard :=
          (Set.ncard_pos G.isFinite_toGMDigraph.finite_E).mpr ⟨e₀, he₀⟩
        omega
      have hih := ih (G.decEdge u₀ v₀) hncard_le
      rw [G.cap_decEdge_of_lt δ u₀ v₀ hlt] at hih
      exact hsame_step.trans hih

theorem forall_isDeltaFolioRep_cap {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n)) :
    ∀ F : FolioSetRep Z.card δ,
      IsDeltaFolioRep δ G Z F ↔ IsDeltaFolioRep δ (G.cap δ) Z F :=
  (hasSameDeltaFolioRel_iff_forall_isDeltaFolioRep δ G (G.cap δ) Z).mp
    (hasSameDeltaFolioRel_cap δ G Z)

end GraphMinor.Compute
