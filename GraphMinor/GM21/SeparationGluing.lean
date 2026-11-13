module

public import GraphMinor.GM21.LinkageLemmas
public import GraphMinor.GM17.Section2

/-!
# Separation Gluing, Vertex Deletion, and Vertex Splitting for Linkages

Proves the structural lemmas needed for Graph Minors XXI, `(2.1)`, `(2.2)`, `(2.3)`, and `(2.4)`:
- `no_parallel_edges_of_exists_deg_one`: any loop-free hypergraph whose edge-nonempty
  subhypergraphs always have a degree-1 vertex has no parallel edges.
- `linkagePattern_eq_of_subset_of_terminals_eq`: if `M` and `L` are linkages with
  `terminals M = terminals L` and `linkagePattern M ⊆ linkagePattern L`, then
  `linkagePattern M = linkagePattern L`.
- Complete gluing theory across a separation `(A, B)` of `G` (`prunedLeft`, `theorem_2_3`).
- Complete vertex-deletion theory (`theorem_2_1`) reduced to `(2.2)` and `(2.3)`.
- Complete vertex-splitting theory (`theorem_2_4`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.GM10 GraphMinor.GM17

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. General criteria for `IsGraph`, `IsLinkage`, and `linkagePattern` equality -/

/-- Any loop-free hypergraph in which every edge-nonempty subhypergraph has a vertex of degree `1`
has no parallel edges. -/
lemma no_parallel_edges_of_exists_deg_one {M : Hypergraph α β}
    (hdeg1 : ∀ H : Hypergraph α β, H ≤ M → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1) :
    ∀ e₁ ∈ M.edgeSet, ∀ e₂ ∈ M.edgeSet, M.ends e₁ = M.ends e₂ → e₁ = e₂ := by
  intro e₁ he₁ e₂ he₂ hends
  by_contra hne
  let H : Hypergraph α β :=
    { vertexSet := M.vertexSet
      edgeSet := {e₁, e₂}
      Inc := fun e v => (e = e₁ ∨ e = e₂) ∧ M.Inc e v
      vertex_mem_of_inc := fun _ _ h => M.vertex_mem_of_inc h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := M.vertexSet_finite
      edgeSet_finite := (finite_singleton e₂).insert e₁ }
  have hHM : H ≤ M :=
    { vertexSet_subset := Subset.rfl
      edgeSet_subset := by
        rintro e (rfl | rfl)
        · exact he₁
        · exact he₂
      ends_eq := fun e he => by
        ext v
        simp only [Hypergraph.ends, mem_ofPred_eq, H]
        exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hH_ne : H.edgeSet.Nonempty := ⟨e₁, Or.inl rfl⟩
  obtain ⟨x, _, hx1⟩ := hdeg1 H hHM hH_ne
  obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1
  have he₀_mem : e₀ ∈ incidentEdges H x := by rw [he₀]; exact rfl
  have hx_ends₁ : x ∈ M.ends e₁ := by
    rcases he₀_mem.1 with rfl | rfl
    · exact he₀_mem.2.2
    · rw [hends]; exact he₀_mem.2.2
  have hx_ends₂ : x ∈ M.ends e₂ := by rw [← hends]; exact hx_ends₁
  have hinc_eq : incidentEdges H x = {e₁, e₂} := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, H, mem_insert_iff, mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl)
      · exact ⟨Or.inl rfl, Or.inl rfl, hx_ends₁⟩
      · exact ⟨Or.inr rfl, Or.inr rfl, hx_ends₂⟩
  rw [hinc_eq, ncard_pair hne] at hx1
  omega

/-- Criterion for `IsLinkage G M`: if `M ≤ G`, every edge of `M` has `2` ends, every vertex of `M`
has at most `2` incident edges, and every edge-nonempty subhypergraph `H ≤ M` has a vertex of
degree `1`, then `M` is a linkage in `G`. -/
lemma isLinkage_of_deg_le_two_of_exists_deg_one {G M : Hypergraph α β}
    (hMG : M ≤ G)
    (hloop : ∀ e ∈ M.edgeSet, (M.ends e).ncard = 2)
    (hdeg2 : ∀ v ∈ M.vertexSet, (incidentEdges M v).ncard ≤ 2)
    (hdeg1 : ∀ H : Hypergraph α β, H ≤ M → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1) :
    IsLinkage G M := by
  have hM_graph : M.IsGraph := fun e he =>
    ⟨nonempty_of_ncard_ne_zero (by rw [hloop e he]; omega),
     by rw [hloop e he]⟩
  have hM_nopar := no_parallel_edges_of_exists_deg_one hdeg1
  refine ⟨hMG, hM_graph, ?_⟩
  intro C hC
  have hCM : C ≤ M := hC.1
  have hC_graph : C.IsGraph := isGraph_of_le hCM hM_graph
  refine ⟨hC_graph, hC.2.1, hC.2.2.1, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [← hCM.ends_eq e he]
    exact hloop e (hCM.edgeSet_subset he)
  · intro e₁ he₁ e₂ he₂ hends
    apply hM_nopar e₁ (hCM.edgeSet_subset he₁) e₂ (hCM.edgeSet_subset he₂)
    rw [hCM.ends_eq e₁ he₁, hCM.ends_eq e₂ he₂, hends]
  · intro v hvC
    exact le_trans (ncard_le_ncard (incidentEdges_subset_of_le hCM v)
      (M.edgeSet_finite.subset fun _ h => h.1)) (hdeg2 v (hCM.vertexSet_subset hvC))
  · intro H hHC hH_ne
    exact hdeg1 H (le_trans hHC hCM) hH_ne

/-- If `M` and `L` are linkages with `terminals L ⊆ ⋃₀ linkagePattern M` and
`linkagePattern M ⊆ linkagePattern L`, then `linkagePattern M = linkagePattern L`. -/
lemma linkagePattern_eq_of_subset {G₁ M G₂ L : Hypergraph α β}
    (hM : IsLinkage G₁ M) (hL : IsLinkage G₂ L)
    (hterm : terminals L ⊆ terminals M)
    (hsub : linkagePattern M ⊆ linkagePattern L) :
    linkagePattern M = linkagePattern L := by
  apply Subset.antisymm hsub
  intro P hPL
  have hP_ne : P.Nonempty := by
    rcases hL.mem_linkagePattern_structure hPL with ⟨u, -, rfl, -⟩ | ⟨u, -, w, -, -, rfl, -⟩
    · exact singleton_nonempty u
    · exact insert_nonempty u {w}
  obtain ⟨x, hxP⟩ := hP_ne
  have hx_termL : x ∈ terminals L := by
    rw [hL.terminals_eq_sUnion_linkagePattern]
    exact ⟨P, hPL, hxP⟩
  have hx_termM : x ∈ terminals M := hterm hx_termL
  rw [hM.terminals_eq_sUnion_linkagePattern] at hx_termM
  obtain ⟨Q, hQM, hxQ⟩ := hx_termM
  have hQL : Q ∈ linkagePattern L := hsub hQM
  have hQP : Q = P := by
    by_contra hne
    exact Set.disjoint_left.mp (hL.disjoint_of_mem_linkagePattern hQL hPL hne) hxQ hxP
  rwa [← hQP]

/-! ## 2. Disjoint-edge unions of subhypergraphs -/

/-- For any two hypergraphs `A, B`, `incidentEdges (A ∪ B) v = incidentEdges A v ∪ incidentEdges B v`. -/
lemma incidentEdges_union_eq (A B : Hypergraph α β) (v : α) :
    incidentEdges (A ∪ B) v = incidentEdges A v ∪ incidentEdges B v := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq, union_edgeSet, mem_union]
  change (e ∈ A.edgeSet ∨ e ∈ B.edgeSet) ∧ (A.Inc e v ∨ B.Inc e v) ↔
    (e ∈ A.edgeSet ∧ A.Inc e v) ∨ (e ∈ B.edgeSet ∧ B.Inc e v)
  constructor
  · rintro ⟨_, hinc | hinc⟩
    · exact Or.inl ⟨A.edge_mem_of_inc hinc, hinc⟩
    · exact Or.inr ⟨B.edge_mem_of_inc hinc, hinc⟩
  · rintro (⟨heA, hincA⟩ | ⟨heB, hincB⟩)
    · exact ⟨Or.inl heA, Or.inl hincA⟩
    · exact ⟨Or.inr heB, Or.inr hincB⟩

/-- If `Disjoint A.edgeSet B.edgeSet`, then `(incidentEdges (A ∪ B) v).ncard =
(incidentEdges A v).ncard + (incidentEdges B v).ncard`. -/
lemma ncard_incidentEdges_union_of_disjoint {A B : Hypergraph α β}
    (hdisj : Disjoint A.edgeSet B.edgeSet) (v : α) :
    (incidentEdges (A ∪ B) v).ncard =
      (incidentEdges A v).ncard + (incidentEdges B v).ncard := by
  rw [incidentEdges_union_eq]
  apply ncard_union_eq
  · exact hdisj.mono (fun _ h => h.1) (fun _ h => h.1)
  · exact A.edgeSet_finite.subset fun _ h => h.1
  · exact B.edgeSet_finite.subset fun _ h => h.1

/-- If `Disjoint A.edgeSet B.edgeSet` and every edge of `A` and `B` has `2` ends, then every edge
of `A ∪ B` has `2` ends. -/
lemma ends_ncard_union_of_disjoint {A B : Hypergraph α β}
    (hdisj : Disjoint A.edgeSet B.edgeSet)
    (hA : ∀ e ∈ A.edgeSet, (A.ends e).ncard = 2)
    (hB : ∀ e ∈ B.edgeSet, (B.ends e).ncard = 2) :
    ∀ e ∈ (A ∪ B).edgeSet, ((A ∪ B).ends e).ncard = 2 := by
  rintro e (heA | heB)
  · have hnotB : e ∉ B.edgeSet := Set.disjoint_left.mp hdisj heA
    have hends : (A ∪ B).ends e = A.ends e := by
      ext u
      change A.Inc e u ∨ B.Inc e u ↔ A.Inc e u
      exact ⟨fun h => h.resolve_right (fun hB_inc => hnotB (B.edge_mem_of_inc hB_inc)), Or.inl⟩
    rw [hends]
    exact hA e heA
  · have hnotA : e ∉ A.edgeSet := Set.disjoint_right.mp hdisj heB
    have hends : (A ∪ B).ends e = B.ends e := by
      ext u
      change A.Inc e u ∨ B.Inc e u ↔ B.Inc e u
      exact ⟨fun h => h.resolve_left (fun hA_inc => hnotA (A.edge_mem_of_inc hA_inc)), Or.inr⟩
    rw [hends]
    exact hB e heB

/-! ## 3. Separation Gluing for (2.3) -/

/-- The pruned left part of `L` across a separation `(A, B)`: obtained from `L ∩ A` by removing
those vertices of `L ∩ B` that are internal vertices (not terminals) of `L ∩ B`. Since internal
vertices of `L ∩ B` have degree `2` in `L ∩ B` and therefore degree `0` in `L ∩ A`, this removes
no edges of `L ∩ A`. -/
def prunedLeft (L A B : Hypergraph α β) : Hypergraph α β :=
  (L ∩ A).deleteVertices ((L ∩ B).vertexSet \ terminals (L ∩ B))

/-- If `L` is a linkage in `G` and `(A, B)` is a separation of `G`, then every internal vertex
`v ∈ (L ∩ B).vertexSet \ terminals (L ∩ B)` has `incidentEdges (L ∩ B) v = incidentEdges L v` and
`incidentEdges (L ∩ A) v = ∅`. -/
lemma incidentEdges_inter_left_eq_empty_of_internal_right {G L A B : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B) {v : α}
    (hv : v ∈ (L ∩ B).vertexSet \ terminals (L ∩ B)) :
    incidentEdges (L ∩ A) v = ∅ := by
  have hLB : IsLinkage B (L ∩ B) :=
    isLinkage_of_le hL (inter_le_left hL.1 hsep.right_le) (inter_le_right hL.1 hsep.right_le)
  have hdeg2 : (incidentEdges (L ∩ B) v).ncard = 2 :=
    (hLB.notMem_terminals_iff hv.1).mp hv.2
  have hsub : incidentEdges (L ∩ B) v ⊆ incidentEdges L v :=
    incidentEdges_subset_of_le (inter_le_left hL.1 hsep.right_le) v
  have hle2 : (incidentEdges L v).ncard ≤ 2 := hL.ncard_incidentEdges_le_two v
  have heq : incidentEdges (L ∩ B) v = incidentEdges L v :=
    eq_of_subset_of_ncard_le hsub (by omega) (L.edgeSet_finite.subset fun _ h => h.1)
  ext e
  simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro heLA hincLA
  have he_in_L : e ∈ incidentEdges L v := ⟨heLA.1, hincLA.1⟩
  rw [← heq] at he_in_L
  exact hsep.notMem_edgeSet_right heLA.2 he_in_L.1.2

/-- Basic structural properties of `prunedLeft L A B`. -/
lemma prunedLeft_props {G L A B : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B) :
    prunedLeft L A B ≤ L ∩ A ∧
    prunedLeft L A B ≤ A ∧
    prunedLeft L A B ≤ L ∧
    (prunedLeft L A B).edgeSet = (L ∩ A).edgeSet ∧
    (∀ v : α, incidentEdges (prunedLeft L A B) v = incidentEdges (L ∩ A) v) ∧
    (prunedLeft L A B).vertexSet ∩ B.vertexSet = A.vertexSet ∩ terminals (L ∩ B) ∧
    prunedLeft L A B ∪ (L ∩ B) = L := by
  have hle_LA : prunedLeft L A B ≤ L ∩ A := deleteVertices_le (L ∩ A) _
  have hle_A : prunedLeft L A B ≤ A := le_trans hle_LA (inter_le_right hL.1 hsep.left_le)
  have hle_L : prunedLeft L A B ≤ L := le_trans hle_LA (inter_le_left hL.1 hsep.left_le)
  have hedge : (prunedLeft L A B).edgeSet = (L ∩ A).edgeSet := by
    ext e
    simp only [prunedLeft, deleteVertices, mem_ofPred_eq]
    refine ⟨fun h => h.1, fun he => ⟨he, fun w hw hinc => ?_⟩⟩
    have hemp := incidentEdges_inter_left_eq_empty_of_internal_right hL hsep hw
    have : e ∈ incidentEdges (L ∩ A) w := ⟨he, hinc⟩
    rw [hemp] at this
    exact this
  have hinc_eq : ∀ v : α, incidentEdges (prunedLeft L A B) v = incidentEdges (L ∩ A) v := by
    intro v
    rw [incidentEdges_eq_inter_edgeSet_of_le hle_LA, hedge,
      inter_eq_self_of_subset_left fun _ h => h.1]
  have hv_inter : (prunedLeft L A B).vertexSet ∩ B.vertexSet =
      A.vertexSet ∩ terminals (L ∩ B) := by
    ext v
    simp only [prunedLeft, deleteVertices, inter_vertexSet, mem_inter_iff, mem_sdiff, not_and,
      not_not]
    constructor
    · rintro ⟨⟨⟨hvL, hvA⟩, hterm⟩, hvB⟩
      exact ⟨hvA, hterm ⟨hvL, hvB⟩⟩
    · rintro ⟨hvA, hv_term⟩
      have hvLB : v ∈ (L ∩ B).vertexSet := hv_term.1
      exact ⟨⟨⟨hvLB.1, hvA⟩, fun _ => hv_term⟩, hvLB.2⟩
  have hunion : prunedLeft L A B ∪ (L ∩ B) = L := by
    have hLB_le : L ∩ B ≤ L := inter_le_left hL.1 hsep.right_le
    apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq (union_le hle_L hLB_le) (le_refl L)
    · ext v
      simp only [union_vertexSet, prunedLeft, deleteVertices, inter_vertexSet, mem_union,
        mem_sdiff, mem_inter_iff]
      constructor
      · rintro (⟨⟨hvL, _⟩, _⟩ | ⟨hvL, _⟩) <;> exact hvL
      · intro hvL
        by_cases hvB : v ∈ B.vertexSet
        · exact Or.inr ⟨hvL, hvB⟩
        · left
          have hvG : v ∈ G.vertexSet := hL.1.vertexSet_subset hvL
          have hvAB : v ∈ A.vertexSet ∪ B.vertexSet := by rwa [hsep.vertexSet_union]
          have hvA : v ∈ A.vertexSet := hvAB.resolve_right hvB
          exact ⟨⟨hvL, hvA⟩, fun h => hvB h.1.2⟩
    · ext e
      simp only [union_edgeSet, hedge, inter_edgeSet, mem_union, mem_inter_iff]
      constructor
      · rintro (⟨heL, _⟩ | ⟨heL, _⟩) <;> exact heL
      · intro heL
        have heG : e ∈ G.edgeSet := hL.1.edgeSet_subset heL
        have heAB : e ∈ A.edgeSet ∪ B.edgeSet := by rwa [hsep.edgeSet_union]
        rcases heAB with heA | heB
        · exact Or.inl ⟨heL, heA⟩
        · exact Or.inr ⟨heL, heB⟩
  exact ⟨hle_LA, hle_A, hle_L, hedge, hinc_eq, hv_inter, hunion⟩

/-- Active terminal pairs of `L'` for a subhypergraph `H ≤ prunedLeft L A B ∪ L'`:
pairs `P ∈ linkagePattern L'` of size `2` such that both vertices of `P` have degree `1` in
`H ∩ L'`. -/
def activePairs (L' H : Hypergraph α β) : Set (Set α) :=
  {P ∈ linkagePattern L' | P.ncard = 2 ∧ ∀ z ∈ P, (incidentEdges (H ∩ L') z).ncard = 1}

/-- The union of components of `LB` whose terminal sets belong to `S`. -/
def patternSubgraph (LB : Hypergraph α β) (S : Set (Set α)) : Hypergraph α β where
  vertexSet := {v ∈ LB.vertexSet | ∃ P ∈ S, ∃ u ∈ P, LB.skeleton.Reachable u v}
  edgeSet := {e ∈ LB.edgeSet | ∃ P ∈ S, ∃ u ∈ P, ∃ w, LB.Inc e w ∧ LB.skeleton.Reachable u w}
  Inc e v := LB.Inc e v ∧ ∃ P ∈ S, ∃ u ∈ P, ∃ w, LB.Inc e w ∧ LB.skeleton.Reachable u w
  vertex_mem_of_inc := by
    rintro e v ⟨hinc_v, P, hPS, u, huP, w, hinc_w, hr⟩
    refine ⟨LB.vertex_mem_of_inc hinc_v, P, hPS, u, huP, ?_⟩
    by_cases hwv : w = v
    · subst hwv; exact hr
    · exact hr.trans (SimpleGraph.Adj.reachable ⟨hwv, e, hinc_w, hinc_v⟩)
  edge_mem_of_inc := fun _ _ h => ⟨LB.edge_mem_of_inc h.1, h.2⟩
  vertexSet_finite := LB.vertexSet_finite.subset fun _ h => h.1
  edgeSet_finite := LB.edgeSet_finite.subset fun _ h => h.1

/-- `patternSubgraph LB S` is a subhypergraph of `LB`. -/
lemma patternSubgraph_le (LB : Hypergraph α β) (S : Set (Set α)) :
    patternSubgraph LB S ≤ LB where
  vertexSet_subset := fun _ h => h.1
  edgeSet_subset := fun _ h => h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, patternSubgraph]
    exact ⟨fun h => ⟨h, he.2⟩, fun h => h.1⟩

/-- For any `S ⊆ linkagePattern LB` such that every `P ∈ S` has `P.ncard = 2`, the incident edges
of `patternSubgraph LB S` at `z` equal `incidentEdges LB z` if `z ∈ ⋃₀ (rel_component S)` and `∅`
otherwise; in particular, at `z ∈ terminals LB`, `(incidentEdges (patternSubgraph LB S) z).ncard`
is `1` if `∃ P ∈ S, z ∈ P` and `0` otherwise, while at `z ∉ terminals LB`,
`(incidentEdges (patternSubgraph LB S) z).ncard` is `0` or `2` (never `1`). -/
lemma patternSubgraph_incidentEdges_props {B LB : Hypergraph α β} {S : Set (Set α)}
    (hLB : IsLinkage B LB) (hS_sub : S ⊆ linkagePattern LB)
    (hS_two : ∀ P ∈ S, P.ncard = 2) :
    (∀ z ∈ terminals LB,
      ((∃ P ∈ S, z ∈ P) → (incidentEdges (patternSubgraph LB S) z).ncard = 1) ∧
      ((¬ ∃ P ∈ S, z ∈ P) → (incidentEdges (patternSubgraph LB S) z).ncard = 0)) ∧
    (∀ z : α, z ∉ terminals LB → (incidentEdges (patternSubgraph LB S) z).ncard ≠ 1) ∧
    (S.Nonempty → (patternSubgraph LB S).edgeSet.Nonempty) := by
  have hinc_iff : ∀ z : α,
      (∃ P ∈ S, ∃ u ∈ P, LB.skeleton.Reachable u z) →
      incidentEdges (patternSubgraph LB S) z = incidentEdges LB z := by
    rintro z ⟨P, hPS, u, huP, hruz⟩
    ext e
    simp only [incidentEdges, mem_ofPred_eq, patternSubgraph]
    constructor
    · exact fun h => ⟨h.1.1, h.2.1⟩
    · rintro ⟨he, hinc⟩
      exact ⟨⟨he, P, hPS, u, huP, z, hinc, hruz⟩, hinc, P, hPS, u, huP, z, hinc, hruz⟩
  have hinc_emp : ∀ z : α,
      (¬ ∃ P ∈ S, ∃ u ∈ P, LB.skeleton.Reachable u z) →
      incidentEdges (patternSubgraph LB S) z = ∅ := by
    intro z hnot
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro he hinc
    have hv_mem : z ∈ (patternSubgraph LB S).vertexSet :=
      (patternSubgraph LB S).vertex_mem_of_inc hinc
    exact hnot hv_mem.2
  have hterm_reach : ∀ z ∈ terminals LB,
      (∃ P ∈ S, ∃ u ∈ P, LB.skeleton.Reachable u z) ↔ (∃ P ∈ S, z ∈ P) := by
    intro z hz
    constructor
    · rintro ⟨P, hPS, u, huP, hruz⟩
      have hPLB : P ∈ linkagePattern LB := hS_sub hPS
      obtain ⟨C, hC, rfl⟩ := hPLB
      have huC : u ∈ C.vertexSet := huP.2
      have hC_eq : C = reachableComponent LB u :=
        eq_reachableComponent_of_isComponentOf hLB.2.1 hC huC
      have hzC : z ∈ C.vertexSet := by
        rw [hC_eq]
        exact ⟨hz.1, hruz⟩
      exact ⟨terminals LB ∩ C.vertexSet, hPS, hz, hzC⟩
    · rintro ⟨P, hPS, hzP⟩
      exact ⟨P, hPS, z, hzP, SimpleGraph.Reachable.refl z⟩
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [ ← hterm_reach z hz ]
    constructor
    · intro hreach
      rw [hinc_iff z hreach]
      rw [hterm_reach z hz] at hreach
      obtain ⟨P, hPS, hzP⟩ := hreach
      have hP2 : P.ncard = 2 := hS_two P hPS
      have hPLB : P ∈ linkagePattern LB := hS_sub hPS
      rcases hLB.mem_linkagePattern_structure hPLB with
        ⟨u, _, rfl, _⟩ | ⟨u, w, _, _, huw, rfl, h1, h2⟩
      · rw [ncard_singleton] at hP2; omega
      · rcases hzP with rfl | rfl
        · exact h1
        · exact h2
    · intro hnot
      rw [hinc_emp z hnot, ncard_empty]
  · intro z hz_not hcard1
    by_cases hreach : ∃ P ∈ S, ∃ u ∈ P, LB.skeleton.Reachable u z
    · rw [hinc_iff z hreach] at hcard1
      rcases hreach with ⟨P, _, u, _, hruz⟩
      have hzV : z ∈ LB.vertexSet := by
        have : (incidentEdges LB z).Nonempty := (ncard_pos (LB.edgeSet_finite.subset fun _ h => h.1)).mp (by omega)
        obtain ⟨e, he⟩ := this
        exact LB.vertex_mem_of_inc he.2
      have h2 : (incidentEdges LB z).ncard = 2 := (hLB.notMem_terminals_iff hzV).mp hz_not
      omega
    · rw [hinc_emp z hreach, ncard_empty] at hcard1
      omega
  · rintro ⟨P, hPS⟩
    have hP2 : P.ncard = 2 := hS_two P hPS
    have hPLB : P ∈ linkagePattern LB := hS_sub hPS
    rcases hLB.mem_linkagePattern_structure hPLB with
      ⟨u, _, hPu, _⟩ | ⟨u, w, huLB, _, huw, hPuw, h1, _⟩
    · rw [hPu, ncard_singleton] at hP2; omega
    · obtain ⟨e, he⟩ := ncard_eq_one.mp h1
      have he_mem : e ∈ incidentEdges LB u := by rw [he]; exact rfl
      have huP : u ∈ P := by rw [hPuw]; exact Or.inl rfl
      refine ⟨e, he_mem.1, P, hPS, u, huP, u, he_mem.2, SimpleGraph.Reachable.refl u⟩

/-- For any `H, L' : Hypergraph α β` and `u : α`,
`H ∩ L' ∩ reachableComponent L' u = H ∩ reachableComponent L' u`. -/
lemma inter_inter_reachableComponent_eq (H L' : Hypergraph α β) (u : α) :
    H ∩ L' ∩ reachableComponent L' u = H ∩ reachableComponent L' u := by
  refine Hypergraph.ext ?_ ?_ (funext fun e => funext fun v => propext ?_)
  · ext v
    simp only [inter_vertexSet, reachableComponent, mem_inter_iff, mem_ofPred_eq]
    tauto
  · ext e
    simp only [inter_edgeSet, reachableComponent, mem_inter_iff, mem_ofPred_eq]
    tauto
  · change (H.Inc e v ∧ L'.Inc e v) ∧ (L'.Inc e v ∧ _) ↔ H.Inc e v ∧ (L'.Inc e v ∧ _)
    tauto

/-- Main subgraph replacement lemma for `(2.3)`: if `H ≤ prunedLeft L A B ∪ L'` satisfies that
every component `C'` of `L'` meeting `H.edgeSet` has all degree-1 vertices of `H ∩ C'` inside
`terminals L'`, then setting `H_L := (H ∩ prunedLeft L A B) ∪ patternSubgraph (L ∩ B) (activePairs L' H)`
gives `H_L ≤ L`, `H_L.edgeSet.Nonempty ↔ H.edgeSet.Nonempty`, and for all `z : α`,
`(incidentEdges H_L z).ncard = 1 ↔ (incidentEdges H z).ncard = 1`. -/
lemma subgraph_replacement_props {G L A B L' H : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B)
    (hL' : IsLinkage B L') (hpat : linkagePattern L' = linkagePattern (L ∩ B))
    (hHM : H ≤ prunedLeft L A B ∪ L')
    (hcase2 : ∀ u ∈ L'.vertexSet, (H ∩ reachableComponent L' u).edgeSet.Nonempty →
      ∀ x ∈ (H ∩ reachableComponent L' u).vertexSet,
        (incidentEdges (H ∩ reachableComponent L' u) x).ncard = 1 → x ∈ terminals L') :
    let LA := prunedLeft L A B
    let LB := L ∩ B
    let S := activePairs L' H
    let H_L := (H ∩ LA) ∪ patternSubgraph LB S
    H_L ≤ L ∧
    (H.edgeSet.Nonempty → H_L.edgeSet.Nonempty) ∧
    (∀ z : α, (incidentEdges H_L z).ncard = 1 ↔ (incidentEdges H z).ncard = 1) := by
  intro LA LB S H_L
  obtain ⟨hle_LA, hle_A, hle_L, hedge_LA, hinc_LA, hv_inter_B, hunion_L⟩ :=
    prunedLeft_props hL hsep
  have hLB : IsLinkage B LB :=
    isLinkage_of_le hL (inter_le_left hL.1 hsep.right_le) (inter_le_right hL.1 hsep.right_le)
  have hterm_eq : terminals L' = terminals LB :=
    terminals_eq_of_linkagePattern_eq hL' hLB hpat
  have hle_G : LA ≤ G := le_trans hle_A hsep.left_le
  have hL'_G : L' ≤ G := le_trans hL'.1 hsep.right_le
  have hHLA_le_LA : H ∩ LA ≤ LA :=
    inter_le_right hHM (le_union_left hle_G hL'_G)
  have hHL'_le_L' : H ∩ L' ≤ L' :=
    inter_le_right hHM (le_union_right hle_G hL'_G)
  have hHB_le_LB : patternSubgraph LB S ≤ LB := patternSubgraph_le LB S
  have hHL_le_L : H_L ≤ L :=
    union_le (le_trans hHLA_le_LA hle_L) (le_trans hHB_le_LB (inter_le_left hL.1 hsep.right_le))
  have hdisj_AB : Disjoint A.edgeSet B.edgeSet :=
    Set.disjoint_left.mpr fun _ heA heB => hsep.notMem_edgeSet_right heA heB
  have hS_sub : S ⊆ linkagePattern LB := by
    rw [← hpat]; exact fun _ h => h.1
  have hS_two : ∀ P ∈ S, P.ncard = 2 := fun _ h => h.2.1
  obtain ⟨hPB_term, hPB_not_term, hPB_ne⟩ :=
    patternSubgraph_incidentEdges_props hLB hS_sub hS_two
  -- Characterize activePairs L' H at z ∈ terminals L'
  have hactive_iff : ∀ z ∈ terminals L',
      (∃ P ∈ S, z ∈ P) ↔ (incidentEdges (H ∩ L') z).ncard = 1 := by
    intro z hz
    constructor
    · rintro ⟨P, hPS, hzP⟩
      exact hPS.2.2 z hzP
    · intro hcard1
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hcard1
      have he₀_mem : e₀ ∈ incidentEdges (H ∩ L') z := by rw [he₀]; exact rfl
      have hzL' : z ∈ L'.vertexSet := hz.1
      let C' := reachableComponent L' z
      have hC'_comp : IsComponentOf L' C' := isComponentOf_reachableComponent hL'.2.1 hzL'
      have hC'_path : IsPathGraph C' := hL'.2.2 C' hC'_comp
      have hHC'_le : H ∩ C' ≤ C' := inter_le_right hHM (le_trans (reachableComponent_le L' z)
        (le_union_right hle_G hL'_G))
      have he₀_HC' : e₀ ∈ (H ∩ C').edgeSet :=
        ⟨he₀_mem.1.1, he₀_mem.1.2, z, he₀_mem.2.2, SimpleGraph.Reachable.refl z⟩
      have hHC'_ne : (H ∩ C').edgeSet.Nonempty := ⟨e₀, he₀_HC'⟩
      obtain ⟨x₁, hx₁V, x₂, hx₂V, hx_ne, hx₁1, hx₂1⟩ :=
        exists_two_deg_one_of_edgeSet_nonempty hC'_path.2.2.2.1 hC'_path.2.2.2.2.2.2
          (H ∩ C') hHC'_le hHC'_ne
      have hx₁_term : x₁ ∈ terminals L' := hcase2 z hzL' hHC'_ne x₁ hx₁V hx₁1
      have hx₂_term : x₂ ∈ terminals L' := hcase2 z hzL' hHC'_ne x₂ hx₂V hx₂1
      have hx₁_termC' : x₁ ∈ terminals C' := by
        rw [← hL'.terminals_inter_component_eq hC'_comp]
        exact ⟨hx₁_term, hx₁V.2⟩
      have hx₂_termC' : x₂ ∈ terminals C' := by
        rw [← hL'.terminals_inter_component_eq hC'_comp]
        exact ⟨hx₂_term, hx₂V.2⟩
      have hC'_ne : C'.edgeSet.Nonempty := ⟨e₀, he₀_HC'.2⟩
      obtain ⟨a, _, b, _, hab, htermC', _, _, _⟩ := isPathGraph_of_edgeSet_nonempty hC'_path hC'_ne
      have hP_eq : terminals C' = {x₁, x₂} := by
        rw [htermC'] at hx₁_termC' hx₂_termC' ⊢
        rcases hx₁_termC' with rfl | rfl <;> rcases hx₂_termC' with rfl | rfl
        · exact (hx_ne rfl).elim
        · rfl
        · exact pair_comm x₂ x₁
        · exact (hx_ne rfl).elim
      have hP_mem_pat : terminals C' ∈ linkagePattern L' :=
        ⟨C', hC'_comp, (hL'.terminals_inter_component_eq hC'_comp).symm⟩
      have hP_card2 : (terminals C').ncard = 2 := by rw [hP_eq, ncard_pair hx_ne]
      have hP_deg1 : ∀ w ∈ terminals C', (incidentEdges (H ∩ L') w).ncard = 1 := by
        rw [hP_eq]
        rintro w (rfl | rfl)
        · rw [← incidentEdges_inter_reachableComponent_eq hHL'_le_L' ⟨⟨hx₁V.1, hx₁V.2.1⟩, hx₁V.2⟩,
            inter_inter_reachableComponent_eq]
          exact hx₁1
        · rw [← incidentEdges_inter_reachableComponent_eq hHL'_le_L' ⟨⟨hx₂V.1, hx₂V.2.1⟩, hx₂V.2⟩,
            inter_inter_reachableComponent_eq]
          exact hx₂1
      have hz_termC' : z ∈ terminals C' := by
        rw [← hL'.terminals_inter_component_eq hC'_comp]
        exact ⟨hz, self_mem_reachableComponent hzL'⟩
      exact ⟨terminals C', ⟨hP_mem_pat, hP_card2, hP_deg1⟩, hz_termC'⟩
  -- For any z, H = (H ∩ LA) ∪ (H ∩ L') on edges
  have hH_inc_split : ∀ z : α,
      (incidentEdges H z).ncard =
        (incidentEdges (H ∩ LA) z).ncard + (incidentEdges (H ∩ L') z).ncard := by
    intro z
    have heq : incidentEdges H z = incidentEdges (H ∩ LA) z ∪ incidentEdges (H ∩ L') z := by
      ext e
      simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet, mem_union]
      change e ∈ H.edgeSet ∧ H.Inc e z ↔
        ((e ∈ H.edgeSet ∧ e ∈ LA.edgeSet) ∧ H.Inc e z ∧ LA.Inc e z) ∨
        ((e ∈ H.edgeSet ∧ e ∈ L'.edgeSet) ∧ H.Inc e z ∧ L'.Inc e z)
      constructor
      · rintro ⟨heH, hincH⟩
        have heM : e ∈ (LA ∪ L').edgeSet := hHM.edgeSet_subset heH
        have hincM : (LA ∪ L').Inc e z := inc_of_le hHM hincH
        rcases heM with heLA | heL'
        · have hnotL' : e ∉ L'.edgeSet :=
            Set.disjoint_left.mp (hdisj_AB.mono hle_A.edgeSet_subset hL'.1.edgeSet_subset) heLA
          have hincLA : LA.Inc e z :=
            hincM.resolve_right (fun h => hnotL' (L'.edge_mem_of_inc h))
          exact Or.inl ⟨⟨heH, heLA⟩, hincH, hincLA⟩
        · have hnotLA : e ∉ LA.edgeSet :=
            Set.disjoint_right.mp (hdisj_AB.mono hle_A.edgeSet_subset hL'.1.edgeSet_subset) heL'
          have hincL' : L'.Inc e z :=
            hincM.resolve_left (fun h => hnotLA (LA.edge_mem_of_inc h))
          exact Or.inr ⟨⟨heH, heL'⟩, hincH, hincL'⟩
      · rintro (⟨⟨heH, _⟩, hincH, _⟩ | ⟨⟨heH, _⟩, hincH, _⟩) <;> exact ⟨heH, hincH⟩
    rw [heq]
    apply ncard_union_eq
    · exact (hdisj_AB.mono hle_A.edgeSet_subset hL'.1.edgeSet_subset).mono
        (fun _ h => h.1.2) (fun _ h => h.1.2)
    · exact H.edgeSet_finite.subset fun _ h => h.1.1
    · exact H.edgeSet_finite.subset fun _ h => h.1.1
  refine ⟨hHL_le_L, ?_, ?_⟩
  · rintro ⟨e, heH⟩
    rcases hHM.edgeSet_subset heH with heLA | heL'
    · exact ⟨e, Or.inl ⟨heH, heLA⟩⟩
    · obtain ⟨u, hu⟩ := (hL'.2.1 e heL').1
      have huL' : u ∈ L'.vertexSet := L'.vertex_mem_of_inc hu
      have he_HC' : e ∈ (H ∩ reachableComponent L' u).edgeSet :=
        ⟨heH, heL', u, hu, SimpleGraph.Reachable.refl u⟩
      have hC'_comp : IsComponentOf L' (reachableComponent L' u) :=
        isComponentOf_reachableComponent hL'.2.1 huL'
      have hC'_path : IsPathGraph (reachableComponent L' u) := hL'.2.2 _ hC'_comp
      have hHC'_le : H ∩ reachableComponent L' u ≤ reachableComponent L' u :=
        inter_le_right hHM (le_trans (reachableComponent_le L' u)
          (le_union_right hle_G hL'_G))
      obtain ⟨x₁, hx₁V, _, _, _, hx₁1, _⟩ :=
        exists_two_deg_one_of_edgeSet_nonempty hC'_path.2.2.2.1 hC'_path.2.2.2.2.2.2
          (H ∩ reachableComponent L' u) hHC'_le ⟨e, he_HC'⟩
      have hx₁_term : x₁ ∈ terminals L' := hcase2 u huL' ⟨e, he_HC'⟩ x₁ hx₁V hx₁1
      have hx₁_HL' : (incidentEdges (H ∩ L') x₁).ncard = 1 := by
        rw [← incidentEdges_inter_reachableComponent_eq hHL'_le_L' ⟨⟨hx₁V.1, hx₁V.2.1⟩, hx₁V.2⟩,
          inter_inter_reachableComponent_eq]
        exact hx₁1
      obtain ⟨P, hPS, _⟩ := (hactive_iff x₁ hx₁_term).mpr hx₁_HL'
      obtain ⟨e', he'⟩ := hPB_ne ⟨P, hPS⟩
      exact ⟨e', Or.inr he'⟩
  · intro z
    have hHL_split : (incidentEdges H_L z).ncard =
        (incidentEdges (H ∩ LA) z).ncard + (incidentEdges (patternSubgraph LB S) z).ncard :=
      ncard_incidentEdges_union_of_disjoint
        (hdisj_AB.mono (le_trans hHLA_le_LA hle_A).edgeSet_subset
          (le_trans hHB_le_LB (inter_le_right hL.1 hsep.right_le)).edgeSet_subset) z
    by_cases hz_term : z ∈ terminals LB
    · have hz_termL' : z ∈ terminals L' := by rwa [hterm_eq]
      have hcard_eq : (incidentEdges (patternSubgraph LB S) z).ncard =
          (incidentEdges (H ∩ L') z).ncard := by
        by_cases hact : ∃ P ∈ S, z ∈ P
        · rw [(hPB_term z hz_term).1 hact, (hactive_iff z hz_termL').mp hact]
        · rw [(hPB_term z hz_term).2 hact]
          have hnot1 : (incidentEdges (H ∩ L') z).ncard ≠ 1 :=
            fun h1 => hact ((hactive_iff z hz_termL').mpr h1)
          have hle1 : (incidentEdges (H ∩ L') z).ncard ≤ 1 := by
            have hsub := incidentEdges_subset_of_le hHL'_le_L' z
            have hle := ncard_le_ncard hsub (L'.edgeSet_finite.subset fun _ h => h.1)
            have hnot2 : (incidentEdges L' z).ncard ≠ 2 :=
              fun h2 => (hL'.notMem_terminals_iff hz_termL'.1).mpr h2 hz_termL'
            have hle2 : (incidentEdges L' z).ncard ≤ 2 := hL'.ncard_incidentEdges_le_two z
            omega
          omega
      rw [hHL_split, hH_inc_split, hcard_eq]
    · by_cases hzLA : z ∈ LA.vertexSet
      · have hz_not_B : z ∉ B.vertexSet := by
          intro hzB
          have : z ∈ LA.vertexSet ∩ B.vertexSet := ⟨hzLA, hzB⟩
          rw [hv_inter_B] at this
          exact hz_term this.2
        have hPB0 : incidentEdges (patternSubgraph LB S) z = ∅ := by
          ext e
          simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro _ hinc
          exact hz_not_B (LB.vertex_mem_of_inc hinc.1).2
        have hHL'0 : incidentEdges (H ∩ L') z = ∅ := by
          ext e
          simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro _ hinc
          exact hz_not_B (hL'.1.vertexSet_subset (L'.vertex_mem_of_inc hinc.2))
        rw [hHL_split, hH_inc_split, hPB0, hHL'0, ncard_empty, add_zero]
      · have hHLA0 : incidentEdges (H ∩ LA) z = ∅ := by
          ext e
          simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          intro _ hinc
          exact hzLA (LA.vertex_mem_of_inc hinc.2)
        have hnot_HL : (incidentEdges H_L z).ncard ≠ 1 := by
          rw [hHL_split, hHLA0, ncard_empty, zero_add]
          exact hPB_not_term z hz_term
        have hnot_H : (incidentEdges H z).ncard ≠ 1 := by
          rw [hH_inc_split, hHLA0, ncard_empty, zero_add]
          intro h1
          obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp h1
          have he₀_mem : e₀ ∈ incidentEdges (H ∩ L') z := by rw [he₀]; exact rfl
          have hzL' : z ∈ L'.vertexSet := L'.vertex_mem_of_inc he₀_mem.2.2
          have hz_HC' : z ∈ (H ∩ reachableComponent L' z).vertexSet :=
            ⟨H.vertex_mem_of_inc he₀_mem.2.1, self_mem_reachableComponent hzL'⟩
          have h1_HC' : (incidentEdges (H ∩ reachableComponent L' z) z).ncard = 1 := by
            rw [← inter_inter_reachableComponent_eq,
              incidentEdges_inter_reachableComponent_eq hHL'_le_L' ⟨⟨hz_HC'.1, hzL'⟩, hz_HC'.2⟩]
            exact h1
          have hz_termL' : z ∈ terminals L' :=
            hcase2 z hzL' ⟨e₀, he₀_mem.1.1, he₀_mem.1.2, z, he₀_mem.2.2,
              SimpleGraph.Reachable.refl z⟩ z hz_HC' h1_HC'
          rw [hterm_eq] at hz_termL'
          exact hz_term hz_termL'
        exact iff_of_false hnot_HL hnot_H

/-- Gluing theorem for `(2.3)`: if `L` is a linkage in `G`, `(A, B)` is a separation of `G`, and
`L'` is a linkage in `B` with `linkagePattern L' = linkagePattern (L ∩ B)`, then
`prunedLeft L A B ∪ L'` is a linkage in `G` with the same pattern and terminals as `L`. -/
theorem prunedLeft_union_isLinkage_and_pattern {G L A B L' : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B)
    (hL' : IsLinkage B L') (hpat : linkagePattern L' = linkagePattern (L ∩ B)) :
    IsLinkage G (prunedLeft L A B ∪ L') ∧
    terminals (prunedLeft L A B ∪ L') = terminals L ∧
    linkagePattern (prunedLeft L A B ∪ L') = linkagePattern L := by
  let LA := prunedLeft L A B
  let LB := L ∩ B
  let M := LA ∪ L'
  obtain ⟨hle_LA, hle_A, hle_L, hedge_LA, hinc_LA, hv_inter_B, hunion_L⟩ :=
    prunedLeft_props hL hsep
  have hLB : IsLinkage B LB :=
    isLinkage_of_le hL (inter_le_left hL.1 hsep.right_le) (inter_le_right hL.1 hsep.right_le)
  have hterm_eq : terminals L' = terminals LB :=
    terminals_eq_of_linkagePattern_eq hL' hLB hpat
  have hle_G : LA ≤ G := le_trans hle_A hsep.left_le
  have hL'_G : L' ≤ G := le_trans hL'.1 hsep.right_le
  have hMG : M ≤ G := union_le hle_G hL'_G
  have hdisj_AB : Disjoint A.edgeSet B.edgeSet :=
    Set.disjoint_left.mpr fun _ heA heB => hsep.notMem_edgeSet_right heA heB
  have hdisj_LAL' : Disjoint LA.edgeSet L'.edgeSet :=
    hdisj_AB.mono hle_A.edgeSet_subset hL'.1.edgeSet_subset
  have hdisj_LALB : Disjoint LA.edgeSet LB.edgeSet :=
    hdisj_AB.mono hle_A.edgeSet_subset (inter_le_right hL.1 hsep.right_le).edgeSet_subset
  have hloop_M : ∀ e ∈ M.edgeSet, (M.ends e).ncard = 2 :=
    ends_ncard_union_of_disjoint hdisj_LAL'
      (fun e he => by rw [← hle_L.ends_eq e he]; exact hL.ends_ncard_eq_two (hle_L.edgeSet_subset he))
      (fun e he => hL'.ends_ncard_eq_two he)
  -- Degree identity on T_U = LA.vertexSet ∪ terminals LB
  have hdeg_TU : ∀ v : α, v ∈ LA.vertexSet ∪ terminals LB →
      (incidentEdges M v).ncard = (incidentEdges L v).ncard := by
    intro v hv
    have hM_split := ncard_incidentEdges_union_of_disjoint hdisj_LAL' v
    have hL_split := ncard_incidentEdges_union_of_disjoint hdisj_LALB v
    rw [hunion_L] at hL_split
    rw [hM_split, hL_split]
    congr 1
    by_cases hv_term : v ∈ terminals LB
    · exact ncard_incidentEdges_eq_of_linkagePattern_eq hL' hLB hpat (hterm_eq.symm ▸ hv_term)
    · have hvLA : v ∈ LA.vertexSet := hv.resolve_right hv_term
      have hv_not_B : v ∉ B.vertexSet := by
        intro hvB
        have : v ∈ LA.vertexSet ∩ B.vertexSet := ⟨hvLA, hvB⟩
        rw [hv_inter_B] at this
        exact hv_term this.2
      have hL'0 : incidentEdges L' v = ∅ := by
        ext e
        simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ hinc
        exact hv_not_B (hL'.1.vertexSet_subset (L'.vertex_mem_of_inc hinc))
      have hLB0 : incidentEdges LB v = ∅ := by
        ext e
        simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ hinc
        exact hv_not_B (LB.vertex_mem_of_inc hinc).2
      rw [hL'0, hLB0]
  have hdeg_not_TU : ∀ v ∈ M.vertexSet, v ∉ LA.vertexSet ∪ terminals LB →
      (incidentEdges M v).ncard = 2 := by
    intro v hvM hv_not
    have hv_not_LA : v ∉ LA.vertexSet := fun h => hv_not (Or.inl h)
    have hv_not_term : v ∉ terminals L' := by rw [hterm_eq]; exact fun h => hv_not (Or.inr h)
    have hvL' : v ∈ L'.vertexSet := hvM.resolve_left hv_not_LA
    have hLA0 : incidentEdges LA v = ∅ := by
      ext e
      simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ hinc
      exact hv_not_LA (LA.vertex_mem_of_inc hinc)
    rw [ncard_incidentEdges_union_of_disjoint hdisj_LAL' v, hLA0, ncard_empty, zero_add]
    exact (hL'.notMem_terminals_iff hvL').mp hv_not_term
  have hdeg2_M : ∀ v ∈ M.vertexSet, (incidentEdges M v).ncard ≤ 2 := by
    intro v hvM
    by_cases hv : v ∈ LA.vertexSet ∪ terminals LB
    · rw [hdeg_TU v hv]
      exact hL.ncard_incidentEdges_le_two v
    · rw [hdeg_not_TU v hvM hv]
  have hdeg1_M : ∀ H : Hypergraph α β, H ≤ M → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1 := by
    intro H hHM hH_ne
    by_cases hcase1 : ∃ u ∈ L'.vertexSet, (H ∩ reachableComponent L' u).edgeSet.Nonempty ∧
        ∃ x ∈ (H ∩ reachableComponent L' u).vertexSet,
          (incidentEdges (H ∩ reachableComponent L' u) x).ncard = 1 ∧ x ∉ terminals L'
    · obtain ⟨u, _, _, x, hxV, hx1, hx_not_term⟩ := hcase1
      refine ⟨x, hxV.1, ?_⟩
      have hx_not_LA : x ∉ LA.vertexSet := by
        intro hxLA
        have hxB : x ∈ B.vertexSet := hL'.1.vertexSet_subset hxV.2.1
        have : x ∈ LA.vertexSet ∩ B.vertexSet := ⟨hxLA, hxB⟩
        rw [hv_inter_B, ← hterm_eq] at this
        exact hx_not_term this.2
      have hHLA0 : incidentEdges (H ∩ LA) x = ∅ := by
        ext e
        simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro _ hinc
        exact hx_not_LA (LA.vertex_mem_of_inc hinc.2)
      have hHL'_le : H ∩ L' ≤ L' :=
        inter_le_right hHM (le_union_right hle_G hL'_G)
      have hinc_eq : incidentEdges H x = incidentEdges (H ∩ L') x := by
        ext e
        simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet]
        change e ∈ H.edgeSet ∧ H.Inc e x ↔
          (e ∈ H.edgeSet ∧ e ∈ L'.edgeSet) ∧ H.Inc e x ∧ L'.Inc e x
        refine ⟨fun ⟨heH, hincH⟩ => ?_, fun ⟨⟨heH, _⟩, hincH, _⟩ => ⟨heH, hincH⟩⟩
        have heM := hHM.edgeSet_subset heH
        have hincM := inc_of_le hHM hincH
        have hnotLA : e ∉ LA.edgeSet := fun heLA => by
          have : e ∈ incidentEdges (H ∩ LA) x :=
            ⟨⟨heH, heLA⟩, hincH, hincM.resolve_right (fun h =>
              Set.disjoint_left.mp hdisj_LAL' heLA (L'.edge_mem_of_inc h))⟩
          rw [hHLA0] at this; exact this
        have heL' : e ∈ L'.edgeSet := heM.resolve_left hnotLA
        have hincL' : L'.Inc e x :=
          hincM.resolve_left (fun h => hnotLA (LA.edge_mem_of_inc h))
        exact ⟨⟨heH, heL'⟩, hincH, hincL'⟩
      rw [hinc_eq, ← incidentEdges_inter_reachableComponent_eq hHL'_le ⟨⟨hxV.1, hxV.2.1⟩, hxV.2⟩,
        inter_inter_reachableComponent_eq]
      exact hx1
    · push Not at hcase1
      obtain ⟨hHL_le, hHL_ne, hHL_iff⟩ :=
        subgraph_replacement_props hL hsep hL' hpat hHM hcase1
      obtain ⟨x, _, hx1⟩ := hL.exists_deg_one_of_le hHL_le (hHL_ne hH_ne)
      have hx1_H : (incidentEdges H x).ncard = 1 := (hHL_iff x).mp hx1
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1_H
      have he₀_mem : e₀ ∈ incidentEdges H x := by rw [he₀]; exact rfl
      exact ⟨x, H.vertex_mem_of_inc he₀_mem.2, hx1_H⟩
  have hM_link : IsLinkage G M :=
    isLinkage_of_deg_le_two_of_exists_deg_one hMG hloop_M hdeg2_M hdeg1_M
  have hterm_M_eq : terminals M = terminals L := by
    ext v
    constructor
    · intro hvM
      have hv_in_TU : v ∈ LA.vertexSet ∪ terminals LB := by
        by_contra hnot
        have h2 := hdeg_not_TU v hvM.1 hnot
        exact (hM_link.notMem_terminals_iff hvM.1).mpr h2 hvM
      have hvL : v ∈ L.vertexSet := by
        rcases hv_in_TU with hvLA | hv_termLB
        · exact hle_L.vertexSet_subset hvLA
        · exact hv_termLB.1.1
      have hnot2 : (incidentEdges L v).ncard ≠ 2 := by
        rw [← hdeg_TU v hv_in_TU]
        exact fun h2 => (hM_link.notMem_terminals_iff hvM.1).mpr h2 hvM
      by_contra hv_not_termL
      exact hnot2 ((hL.notMem_terminals_iff hvL).mp hv_not_termL)
    · intro hvL
      have hv_in_TU : v ∈ LA.vertexSet ∪ terminals LB := by
        have hvL_mem : v ∈ (LA ∪ LB).vertexSet := by rw [hunion_L]; exact hvL.1
        rcases hvL_mem with hvLA | hvLB
        · exact Or.inl hvLA
        · by_cases hv_term : v ∈ terminals LB
          · exact Or.inr hv_term
          · exfalso
            have h2_LB : (incidentEdges LB v).ncard = 2 :=
              (hLB.notMem_terminals_iff hvLB).mp hv_term
            have hle : (incidentEdges LB v).ncard ≤ (incidentEdges L v).ncard :=
              ncard_le_ncard (incidentEdges_subset_of_le (inter_le_left hL.1 hsep.right_le) v)
                (L.edgeSet_finite.subset fun _ h => h.1)
            have hle2 : (incidentEdges L v).ncard ≤ 2 := hL.ncard_incidentEdges_le_two v
            have h2_L : (incidentEdges L v).ncard = 2 := by omega
            exact (hL.notMem_terminals_iff hvL.1).mpr h2_L hvL
      have hvM : v ∈ M.vertexSet := by
        rcases hv_in_TU with hvLA | hv_termLB
        · exact Or.inl hvLA
        · rw [← hterm_eq] at hv_termLB
          exact Or.inr hv_termLB.1
      have hnot2 : (incidentEdges M v).ncard ≠ 2 := by
        rw [hdeg_TU v hv_in_TU]
        exact fun h2 => (hL.notMem_terminals_iff hvL.1).mpr h2 hvL
      by_contra hv_not_termM
      exact hnot2 ((hM_link.notMem_terminals_iff hvM).mp hv_not_termM)
  have hpat_sub : linkagePattern M ⊆ linkagePattern L := by
    intro P hPM
    rcases hM_link.mem_linkagePattern_structure hPM with
      ⟨u, hu_termM, rfl, hu0⟩ | ⟨u, hu_termM, w, hw_termM, huw, rfl, _⟩
    · have hu_termL : u ∈ terminals L := by rwa [← hterm_M_eq]
      have hu_TU : u ∈ LA.vertexSet ∪ terminals LB := by
        rcases hu_termM.1 with huLA | huL'
        · exact Or.inl huLA
        · right
          rw [← hterm_eq]
          have h0_L' : (incidentEdges L' u).ncard = 0 := by
            have hsplit := ncard_incidentEdges_union_of_disjoint hdisj_LAL' u
            change (incidentEdges M u).ncard = _ at hsplit
            omega
          by_contra hu_not_term
          have h2 := (hL'.notMem_terminals_iff huL').mp hu_not_term
          omega
      have hu0_L : (incidentEdges L u).ncard = 0 := by
        rw [← hdeg_TU u hu_TU, hu0]
      exact (hL.ncard_incidentEdges_eq_zero_iff hu_termL.1).mp hu0_L
    · obtain ⟨C_M, hC_M, hP_eq⟩ := hPM
      have hCM_le_M : C_M ≤ M := hC_M.1
      have hcase2_CM : ∀ v ∈ L'.vertexSet, (C_M ∩ reachableComponent L' v).edgeSet.Nonempty →
          ∀ x ∈ (C_M ∩ reachableComponent L' v).vertexSet,
            (incidentEdges (C_M ∩ reachableComponent L' v) x).ncard = 1 → x ∈ terminals L' := by
        intro v hvL' ⟨e, he_in⟩ x hxV hx1
        obtain ⟨z, hz⟩ := (hL'.2.1 e he_in.2.1).1
        have hz_CM : z ∈ C_M.vertexSet :=
          C_M.vertex_mem_of_inc ((inc_iff_of_le hCM_le_M he_in.1).2 (Or.inr hz))
        have hC_M_eq : C_M = reachableComponent M z :=
          eq_reachableComponent_of_isComponentOf hM_link.2.1 hC_M hz_CM
        have hrz_v : L'.skeleton.Reachable v z := by
          obtain ⟨w, hw_inc, hrvw⟩ := he_in.2.2
          by_cases hwz : w = z
          · subst hwz; exact hrvw
          · exact hrvw.trans (SimpleGraph.Adj.reachable ⟨hwz, e, hw_inc, hz⟩)
        have hsub_CM : reachableComponent L' v ≤ C_M := by
          rw [hC_M_eq]
          refine ⟨fun y hy => ⟨Or.inr hy.1, ?_⟩, fun e' he' => ⟨Or.inr he'.1, ?_⟩, fun e' he' => ?_⟩
          · exact reachable_of_le (le_union_right hle_G hL'_G)
              (hrz_v.symm.trans hy.2)
          · obtain ⟨w, hw_inc, hrvw⟩ := he'.2
            exact ⟨w, Or.inr hw_inc,
              reachable_of_le (le_union_right hle_G hL'_G)
                (hrz_v.symm.trans hrvw)⟩
          · ext y
            simp only [Hypergraph.ends, mem_ofPred_eq, reachableComponent]
            constructor
            · rintro ⟨hLA_inc | hL'_inc, _⟩
              · exfalso
                exact Set.disjoint_left.mp hdisj_LAL' (LA.edge_mem_of_inc hLA_inc) he'.1
              · exact ⟨hL'_inc, he'.2⟩
            · rintro ⟨hL'_inc, w, hw_inc, hrvw⟩
              exact ⟨Or.inr hL'_inc, w, Or.inr hw_inc,
                reachable_of_le (le_union_right hle_G hL'_G)
                  (hrz_v.symm.trans hrvw)⟩
        have h_inter_eq : C_M ∩ reachableComponent L' v = reachableComponent L' v :=
          eq_of_le_of_vertexSet_eq_of_edgeSet_eq
            (inter_le_right hCM_le_M (le_trans (reachableComponent_le L' v)
              (le_union_right hle_G hL'_G)))
            (le_refl _)
            (inter_eq_self_of_subset_right hsub_CM.vertexSet_subset)
            (inter_eq_self_of_subset_right hsub_CM.edgeSet_subset)
        rw [h_inter_eq] at hx1 hxV
        have hcomp_v : IsComponentOf L' (reachableComponent L' v) :=
          isComponentOf_reachableComponent hL'.2.1 hvL'
        rw [incidentEdges_component_eq hL'.2.1 hcomp_v hxV] at hx1
        have hx_termL' : x ∈ terminals L' := by
          by_contra hx_not_termL'
          have h2 := (hL'.notMem_terminals_iff hxV.1).mp hx_not_termL'
          omega
        exact hx_termL'
      obtain ⟨hHL_le, _, hHL_iff⟩ :=
        subgraph_replacement_props hL hsep hL' hpat hCM_le_M hcase2_CM
      have hCM_path : IsPathGraph C_M := hM_link.2.2 C_M hC_M
      have hterm_CM : terminals M ∩ C_M.vertexSet = terminals C_M :=
        hM_link.terminals_inter_component_eq hC_M
      have hCM_ne : C_M.edgeSet.Nonempty := by
        by_contra hemp
        rw [not_nonempty_iff_eq_empty] at hemp
        obtain ⟨u', _, _, hterm_u', _⟩ := isPathGraph_of_edgeSet_empty hCM_path hemp
        have : ({u, w} : Set α).ncard = ({u'} : Set α).ncard := by
          rw [hP_eq, hterm_CM, hterm_u']
        rw [ncard_pair huw, ncard_singleton] at this
        omega
      obtain ⟨a, haV, b, hbV, hab, hterm_ab, ha1, hb1, hother⟩ :=
        isPathGraph_of_edgeSet_nonempty hCM_path hCM_ne
      have hab_eq : ({a, b} : Set α) = {u, w} := by rw [← hterm_ab, ← hterm_CM, ← hP_eq]
      have hu1_CM : (incidentEdges C_M u).ncard = 1 := by
        have hu_ab : u ∈ ({a, b} : Set α) := by rw [hab_eq]; exact Or.inl rfl
        rcases hu_ab with rfl | rfl
        · exact ha1
        · exact hb1
      have hw1_CM : (incidentEdges C_M w).ncard = 1 := by
        have hw_ab : w ∈ ({a, b} : Set α) := by rw [hab_eq]; exact Or.inr rfl
        rcases hw_ab with rfl | rfl
        · exact ha1
        · exact hb1
      let HL_CM := (C_M ∩ LA) ∪ patternSubgraph LB (activePairs L' C_M)
      have hu1_HL : (incidentEdges HL_CM u).ncard = 1 := (hHL_iff u).mpr hu1_CM
      have hw1_HL : (incidentEdges HL_CM w).ncard = 1 := (hHL_iff w).mpr hw1_CM
      have hu_HL : u ∈ HL_CM.vertexSet := by
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hu1_HL
        have : e₀ ∈ incidentEdges HL_CM u := by rw [he₀]; exact rfl
        exact HL_CM.vertex_mem_of_inc this.2
      have hw_HL : w ∈ HL_CM.vertexSet := by
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hw1_HL
        have : e₀ ∈ incidentEdges HL_CM w := by rw [he₀]; exact rfl
        exact HL_CM.vertex_mem_of_inc this.2
      have honly_HL : ∀ z ∈ HL_CM.vertexSet,
          (incidentEdges HL_CM z).ncard = 1 → z = u ∨ z = w := by
        intro z _ hz1
        have hz1_CM : (incidentEdges C_M z).ncard = 1 := (hHL_iff z).mp hz1
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hz1_CM
        have he₀_mem : e₀ ∈ incidentEdges C_M z := by rw [he₀]; exact rfl
        have hz_CM : z ∈ C_M.vertexSet := C_M.vertex_mem_of_inc he₀_mem.2
        have hz_ab : z ∈ ({a, b} : Set α) := by
          by_contra hnot
          simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
          have h2 := hother z hz_CM hnot.1 hnot.2
          omega
        rwa [hab_eq] at hz_ab
      have hreach_L : L.skeleton.Reachable u w :=
        same_component_of_deg_one_two_subgraph hL hHL_le hu_HL hw_HL huw hu1_HL honly_HL
      have hu_termL : u ∈ terminals L := by rwa [← hterm_M_eq]
      have hw_termL : w ∈ terminals L := by rwa [← hterm_M_eq]
      exact (hL.pair_mem_linkagePattern_iff hu_termL hw_termL huw).mpr hreach_L
  exact ⟨hM_link, hterm_M_eq,
    linkagePattern_eq_of_subset hM_link hL (ge_of_eq hterm_M_eq) hpat_sub⟩

/-- If `prunedLeft L A B ∪ L' = L`, then `L' = L ∩ B`. -/
lemma eq_inter_right_of_prunedLeft_union_eq {G L A B L' : Hypergraph α β}
    (hL : IsLinkage G L) (hsep : G.IsSeparation A B)
    (hL' : IsLinkage B L') (hpat : linkagePattern L' = linkagePattern (L ∩ B))
    (hU : prunedLeft L A B ∪ L' = L) :
    L' = L ∩ B := by
  have hLB_le : L ∩ B ≤ B := inter_le_right hL.1 hsep.right_le
  have hLB : IsLinkage B (L ∩ B) :=
    isLinkage_of_le hL (inter_le_left hL.1 hsep.right_le) hLB_le
  have hterm_eq : terminals L' = terminals (L ∩ B) :=
    terminals_eq_of_linkagePattern_eq hL' hLB hpat
  obtain ⟨_, hle_A, _, _, _, _, _⟩ := prunedLeft_props hL hsep
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hL'.1 hLB_le
  · ext v
    constructor
    · intro hvL'
      have hvL : v ∈ L.vertexSet := by rw [← hU]; exact Or.inr hvL'
      exact ⟨hvL, hL'.1.vertexSet_subset hvL'⟩
    · intro hvLB
      by_cases hv_term : v ∈ terminals (L ∩ B)
      · rw [← hterm_eq] at hv_term
        exact hv_term.1
      · have hv_not_LA : v ∉ (prunedLeft L A B).vertexSet :=
          fun h => h.2 ⟨hvLB, hv_term⟩
        have hvU : v ∈ (prunedLeft L A B ∪ L').vertexSet := by
          rw [hU]; exact hvLB.1
        exact hvU.resolve_left hv_not_LA
  · ext e
    constructor
    · intro heL'
      have heL : e ∈ L.edgeSet := by rw [← hU]; exact Or.inr heL'
      exact ⟨heL, hL'.1.edgeSet_subset heL'⟩
    · rintro ⟨heL, heB⟩
      have heU : e ∈ (prunedLeft L A B ∪ L').edgeSet := by rwa [hU]
      rcases heU with heLA | heL'
      · exfalso
        exact hsep.notMem_edgeSet_right (hle_A.edgeSet_subset heLA) heB
      · exact heL'

/-- Second part of Graph Minors XXI, `(2.3)`: if `L` is a vital linkage in `G` and `(A, B)` is a
separation of `G`, then `L ∩ B` is a vital linkage in `B`. -/
theorem isVitalLinkage_inter_right_of_isSeparation {G L A B : Hypergraph α β}
    (hL : IsVitalLinkage G L) (hsep : G.IsSeparation A B) :
    IsVitalLinkage B (L ∩ B) := by
  have hLB : IsLinkage B (L ∩ B) :=
    isLinkage_of_le hL.1 (inter_le_left hL.1.1 hsep.right_le) (inter_le_right hL.1.1 hsep.right_le)
  refine ⟨hLB, ?_, ?_⟩
  · calc
      (L ∩ B).vertexSet = L.vertexSet ∩ B.vertexSet := rfl
      _ = G.vertexSet ∩ B.vertexSet := by rw [hL.2.1]
      _ = B.vertexSet := inter_eq_self_of_subset_right hsep.right_le.vertexSet_subset
  · intro L' hL' hpat
    obtain ⟨hM_link, _, hM_pat⟩ := prunedLeft_union_isLinkage_and_pattern hL.1 hsep hL' hpat
    have hU : prunedLeft L A B ∪ L' = L := hL.2.2 _ hM_link hM_pat
    exact eq_inter_right_of_prunedLeft_union_eq hL.1 hsep hL' hpat hU

/-! ## 4. Vertex Deletion for (2.1) -/

/-- For any `G : Hypergraph α β` and `X : Set α`, the complement of `G.deleteVertices X` with
vertex set `G.vertexSet` forms a separation `(deleteVerticesComplement G X, G.deleteVertices X)`
of `G`. -/
def deleteVerticesComplement (G : Hypergraph α β) (X : Set α) : Hypergraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet \ (G.deleteVertices X).edgeSet
  Inc e v := e ∈ G.edgeSet \ (G.deleteVertices X).edgeSet ∧ G.Inc e v
  vertex_mem_of_inc := fun _ _ h => G.vertex_mem_of_inc h.2
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.subset sdiff_subset

/-- `(deleteVerticesComplement G X, G.deleteVertices X)` is a separation of `G`. -/
lemma isSeparation_deleteVertices (G : Hypergraph α β) (X : Set α) :
    G.IsSeparation (deleteVerticesComplement G X) (G.deleteVertices X) := by
  have hleft : deleteVerticesComplement G X ≤ G :=
    { vertexSet_subset := Subset.rfl
      edgeSet_subset := sdiff_subset
      ends_eq := fun e he => by
        ext v
        simp only [Hypergraph.ends, mem_ofPred_eq, deleteVerticesComplement]
        exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  have hright : G.deleteVertices X ≤ G := deleteVertices_le G X
  rw [isSeparation_iff_of_le hleft hright]
  refine ⟨union_eq_self_of_subset_right hright.vertexSet_subset,
    sdiff_union_of_subset hright.edgeSet_subset, ?_⟩
  ext e
  simp only [deleteVerticesComplement, mem_inter_iff, mem_sdiff, mem_empty_iff_false, iff_false,
    not_and]
  exact fun h1 h2 => h1.2 h2

/-- If `L ≤ G`, then `L ∩ G.deleteVertices X = L.deleteVertices X`. -/
lemma inter_deleteVertices_eq {G L : Hypergraph α β} (hLG : L ≤ G) (X : Set α) :
    L ∩ G.deleteVertices X = L.deleteVertices X := by
  have h1 : L ∩ G.deleteVertices X ≤ L := inter_le_left hLG (deleteVertices_le G X)
  have h2 : L.deleteVertices X ≤ L := deleteVertices_le L X
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq h1 h2
  · ext v
    simp only [inter_vertexSet, deleteVertices, mem_inter_iff, mem_sdiff]
    exact ⟨fun ⟨hvL, _, hvX⟩ => ⟨hvL, hvX⟩,
      fun ⟨hvL, hvX⟩ => ⟨hvL, hLG.vertexSet_subset hvL, hvX⟩⟩
  · ext e
    simp only [inter_edgeSet, deleteVertices, mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun ⟨heL, _, hnot⟩ => ⟨heL, fun w hwX hincL =>
      hnot w hwX ((inc_iff_of_le hLG heL).1 hincL)⟩,
      fun ⟨heL, hnot⟩ => ⟨heL, hLG.edgeSet_subset heL, fun w hwX hincG =>
        hnot w hwX ((inc_iff_of_le hLG heL).2 hincG)⟩⟩

/-- Terminal bound for `(2.1)`: if `L` is a `p`-linkage in `G` and `X ⊆ G.vertexSet`, then
`(terminals (L.deleteVertices X)).ncard ≤ p + 2 * X.ncard`. -/
lemma terminals_deleteVertices_ncard_le {G L : Hypergraph α β} {p : ℕ} {X : Set α}
    (hL : IsPLinkage G L p) (hX : X ⊆ G.vertexSet) :
    (terminals (L.deleteVertices X)).ncard ≤ p + 2 * X.ncard := by
  have hX_fin : X.Finite := G.vertexSet_finite.subset hX
  let N : α → Set α := fun x => ⋃ e ∈ incidentEdges L x, (L.ends e \ {x})
  have hN_fin : ∀ x : α, (N x).Finite := fun x =>
    L.vertexSet_finite.subset (iUnion₂_subset fun e _ =>
      Subset.trans sdiff_subset (fun _ h => L.vertex_mem_of_inc h))
  have hN_card : ∀ x : α, (N x).ncard ≤ 2 := by
    intro x
    have hinc_fin : (incidentEdges L x).Finite := L.edgeSet_finite.subset fun _ h => h.1
    have h1 : ∀ e ∈ incidentEdges L x, (L.ends e \ {x}).ncard ≤ 1 := by
      intro e he
      have h2 : (L.ends e).ncard = 2 := hL.1.ends_ncard_eq_two he.1
      have hx_in : x ∈ L.ends e := he.2
      rw [ncard_sdiff (singleton_subset_iff.mpr hx_in) (finite_singleton x), ncard_singleton, h2]
    have hle_two : (incidentEdges L x).ncard ≤ 2 := hL.1.ncard_incidentEdges_le_two x
    rcases ( le_iff_lt_or_eq.mp hle_two ) with hlt2 | heq2
    · rcases ( Nat.lt_succ_iff.mp hlt2 ) |> le_iff_lt_or_eq.mp with hlt1 | heq1
      · have hemp : incidentEdges L x = ∅ :=
          (ncard_eq_zero hinc_fin).mp (Nat.lt_one_iff.mp hlt1)
        have hN_emp : N x = ∅ := by simp [N, hemp]
        rw [hN_emp, ncard_empty]; omega
      · obtain ⟨e₁, he₁⟩ := ncard_eq_one.mp heq1
        have hN_eq : N x = L.ends e₁ \ {x} := by simp [N, he₁]
        rw [hN_eq]
        have he₁_in : e₁ ∈ incidentEdges L x := by rw [he₁]; exact rfl
        exact le_trans (h1 e₁ he₁_in) (by omega)
    · obtain ⟨e₁, e₂, hne, heq⟩ := ncard_eq_two.mp heq2
      have hN_eq : N x = (L.ends e₁ \ {x}) ∪ (L.ends e₂ \ {x}) := by
        ext u
        simp only [N, heq, mem_insert_iff, mem_singleton_iff, mem_iUnion, mem_union]
        constructor
        · rintro ⟨i, rfl | rfl, hu⟩
          · exact Or.inl hu
          · exact Or.inr hu
        · rintro (hu | hu)
          · exact ⟨e₁, Or.inl rfl, hu⟩
          · exact ⟨e₂, Or.inr rfl, hu⟩
      have he₁_in : e₁ ∈ incidentEdges L x := by rw [heq]; exact Or.inl rfl
      have he₂_in : e₂ ∈ incidentEdges L x := by rw [heq]; exact Or.inr rfl
      rw [hN_eq]
      exact le_trans (ncard_union_le _ _) (by
        have := h1 e₁ he₁_in
        have := h1 e₂ he₂_in
        omega)
  have hbiUnion_le : ∀ Y : Set α, Y.Finite → (⋃ x ∈ Y, N x).ncard ≤ 2 * Y.ncard := by
    intro Y hY
    induction Y, hY using Set.Finite.induction_on with
    | empty => simp
    | @insert a s has hs ih =>
      rw [biUnion_insert, ncard_insert_of_notMem has hs]
      have hle := ncard_union_le (N a) (⋃ x ∈ s, N x)
      have hNa := hN_card a
      omega
  have hsub_term : terminals (L.deleteVertices X) ⊆
      terminals L ∪ (⋃ x ∈ X, N x) := by
    intro v hv
    have hvL : v ∈ L.vertexSet := hv.1.1
    have hLD_link : IsLinkage (G.deleteVertices X) (L.deleteVertices X) := by
      rw [← inter_deleteVertices_eq hL.1.1 X]
      exact isLinkage_of_le hL.1 (inter_le_left hL.1.1 (deleteVertices_le G X))
        (inter_le_right hL.1.1 (deleteVertices_le G X))
    by_cases hinc_eq : incidentEdges (L.deleteVertices X) v = incidentEdges L v
    · left
      have hnot2_LD : (incidentEdges (L.deleteVertices X) v).ncard ≠ 2 :=
        fun h2 => (hLD_link.notMem_terminals_iff hv.1).mpr h2 hv
      rw [hinc_eq] at hnot2_LD
      by_contra hv_not_termL
      exact hnot2_LD ((hL.1.notMem_terminals_iff hvL).mp hv_not_termL)
    · right
      have hsub_inc : incidentEdges (L.deleteVertices X) v ⊆ incidentEdges L v :=
        incidentEdges_subset_of_le (deleteVertices_le L X) v
      have hne_diff : (incidentEdges L v \ incidentEdges (L.deleteVertices X) v).Nonempty :=
        nonempty_iff_ne_empty.mpr fun hemp => hinc_eq (Subset.antisymm hsub_inc
          (sdiff_eq_empty.mp hemp))
      obtain ⟨e, heL, he_not_LD⟩ := hne_diff
      have hex_x : ∃ x ∈ X, L.Inc e x := by
        by_contra hnot
        push Not at hnot
        exact he_not_LD ⟨⟨heL.1, hnot⟩, heL.2, hnot⟩
      obtain ⟨x, hxX, hinc_x⟩ := hex_x
      have hvx : v ≠ x := fun h => hv.1.2 (h ▸ hxX)
      exact mem_biUnion hxX (mem_biUnion ⟨heL.1, hinc_x⟩ ⟨heL.2, hvx⟩)
  have hfin_rhs : (terminals L ∪ (⋃ x ∈ X, N x)).Finite :=
    (L.vertexSet_finite.subset fun _ h => h.1).union (hX_fin.biUnion fun x _ => hN_fin x)
  calc
    (terminals (L.deleteVertices X)).ncard
      ≤ (terminals L ∪ (⋃ x ∈ X, N x)).ncard := ncard_le_ncard hsub_term hfin_rhs
    _ ≤ (terminals L).ncard + (⋃ x ∈ X, N x).ncard := ncard_union_le _ _
    _ ≤ p + 2 * X.ncard := Nat.add_le_add hL.2 (hbiUnion_le X hX_fin)

end GM21
end GraphMinor
