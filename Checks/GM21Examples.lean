module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.LinkageLemmas
public import GraphMinor.GM21.Final

/-!
# Checks of the definitions of Graph Minors XXI

This file checks on small graphs that the definitions in `GraphMinor/GM21/Defs.lean` are neither
empty nor trivial:
1. A graph with a vital linkage (`oneVertex_vitalLinkage`),
2. A graph with a linkage that is not vital (`twoVertex_spanning_not_vitalLinkage`),
3. A linkage that is unique among those of its pattern, but fails `V(L) = V(G)`
   (`twoVertexEdgeless_uniquePattern_not_vital`).
-/

@[expose] public section

namespace GraphMinor.GM21.Checks

open Set Graph GraphMinor GraphMinor.Hypergraph GraphMinor.GM10 GraphMinor.GM21

/-! ## Example 1: One-vertex edgeless graph has a vital 1-linkage -/

/-- The graph with one vertex `0 : Fin 1` and no edges. -/
def oneVertexGraph : Hypergraph (Fin 1) Empty where
  vertexSet := {0}
  edgeSet := ∅
  Inc e _ := e.elim
  vertex_mem_of_inc e _ := e.elim
  edge_mem_of_inc e _ := e.elim
  vertexSet_finite := finite_singleton 0
  edgeSet_finite := finite_empty

theorem oneVertex_isLinkage : IsLinkage oneVertexGraph oneVertexGraph := by
  refine ⟨le_rfl, fun e he => he.elim, ?_⟩
  intro C ⟨hC_le, hC_ne, hC_conn, _⟩
  refine ⟨fun e he => (hC_le.edgeSet_subset he).elim, hC_ne, hC_conn,
    fun e he => (hC_le.edgeSet_subset he).elim,
    fun e₁ he₁ => (hC_le.edgeSet_subset he₁).elim, ?_,
    fun H hH ⟨e, he⟩ => (hC_le.edgeSet_subset (hH.edgeSet_subset he)).elim⟩
  intro x _
  have h_emp : incidentEdges C x = ∅ := by
    ext e; exact ⟨fun h => (hC_le.edgeSet_subset h.1).elim, False.elim⟩
  rw [h_emp, ncard_empty]
  exact Nat.zero_le 2

theorem oneVertex_isComponentOf : IsComponentOf oneVertexGraph oneVertexGraph := by
  refine ⟨le_rfl, ⟨0, rfl⟩, ?_, ?_⟩
  · intro x hx y hy
    rw [show x = 0 from hx, show y = 0 from hy]
  · intro C' hC' _ _ hle
    exact le_antisymm hC' hle

theorem oneVertex_terminals : terminals oneVertexGraph = {0} := by
  ext x
  simp only [terminals, IsTerminal, mem_singleton_iff]
  change (x ∈ ({0} : Set (Fin 1)) ∧ vertexDegree oneVertexGraph x ≤ 1) ↔ x = 0
  refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
  have h_emp : incidentEdges oneVertexGraph x = ∅ := by
    ext e; exact ⟨fun h => h.1.elim, False.elim⟩
  unfold vertexDegree
  rw [h_emp, sep_empty, ncard_empty]
  exact Nat.zero_le 1

theorem oneVertex_vitalLinkage :
    IsVitalLinkage oneVertexGraph oneVertexGraph ∧
    IsPLinkage oneVertexGraph oneVertexGraph 1 := by
  have hL := oneVertex_isLinkage
  refine ⟨⟨hL, rfl, ?_⟩, ⟨hL, ?_⟩⟩
  · intro L' hL' hpat
    have hE : L'.edgeSet = ∅ := subset_empty_iff.mp hL'.1.edgeSet_subset
    have hB : ({0} : Set (Fin 1)) ∈ linkagePattern oneVertexGraph := by
      refine ⟨oneVertexGraph, oneVertex_isComponentOf, ?_⟩
      rw [oneVertex_terminals]
      ext z; simp [oneVertexGraph]
    rw [← hpat] at hB
    rcases hB with ⟨C', hC', hB_eq⟩
    have h0 : (0 : Fin 1) ∈ L'.vertexSet := by
      have : (0 : Fin 1) ∈ terminals L' ∩ C'.vertexSet := by rw [← hB_eq]; exact rfl
      exact this.1.1
    have hV : L'.vertexSet = oneVertexGraph.vertexSet :=
      Subset.antisymm hL'.1.vertexSet_subset (singleton_subset_iff.mpr h0)
    have hle : oneVertexGraph ≤ L' :=
      { vertexSet_subset := hV.symm.subset
        edgeSet_subset := empty_subset _
        ends_eq := fun e he => he.elim }
    exact le_antisymm hL'.1 hle
  · rw [oneVertex_terminals, ncard_singleton]

/-! ## Example 2: A linkage that is unique for its pattern, but fails `V(L) = V(G)` (hence not vital) -/

/-- A two-vertex edgeless graph on `Fin 2`. -/
def twoVertexEdgelessGraph : Hypergraph (Fin 2) Empty where
  vertexSet := univ
  edgeSet := ∅
  Inc e _ := e.elim
  vertex_mem_of_inc e _ := e.elim
  edge_mem_of_inc e _ := e.elim
  vertexSet_finite := finite_univ
  edgeSet_finite := finite_empty

/-- The linkage consisting only of vertex `0` in `twoVertexEdgelessGraph`. -/
def vertexZeroLinkage : Hypergraph (Fin 2) Empty where
  vertexSet := {0}
  edgeSet := ∅
  Inc e _ := e.elim
  vertex_mem_of_inc e _ := e.elim
  edge_mem_of_inc e _ := e.elim
  vertexSet_finite := finite_singleton 0
  edgeSet_finite := finite_empty

theorem twoVertexEdgeless_isLinkage :
    IsLinkage twoVertexEdgelessGraph vertexZeroLinkage := by
  refine ⟨{ vertexSet_subset := subset_univ _
            edgeSet_subset := empty_subset _
            ends_eq := fun e he => he.elim }, fun e he => he.elim, ?_⟩
  intro C ⟨hC_le, hC_ne, hC_conn, _⟩
  refine ⟨fun e he => (hC_le.edgeSet_subset he).elim, hC_ne, hC_conn,
    fun e he => (hC_le.edgeSet_subset he).elim,
    fun e₁ he₁ => (hC_le.edgeSet_subset he₁).elim, ?_,
    fun H hH ⟨e, he⟩ => (hC_le.edgeSet_subset (hH.edgeSet_subset he)).elim⟩
  intro x _
  have h_emp : incidentEdges C x = ∅ := by
    ext e; exact ⟨fun h => (hC_le.edgeSet_subset h.1).elim, False.elim⟩
  rw [h_emp, ncard_empty]
  exact Nat.zero_le 2

/-- `vertexZeroLinkage` is the unique linkage in `twoVertexEdgelessGraph` with its pattern,
yet `V(L) ≠ V(G)`, so it is not vital. -/
theorem twoVertexEdgeless_uniquePattern_not_vital :
    IsLinkage twoVertexEdgelessGraph vertexZeroLinkage ∧
    (∀ L' : Hypergraph (Fin 2) Empty,
      IsLinkage twoVertexEdgelessGraph L' →
      linkagePattern L' = linkagePattern vertexZeroLinkage →
      L' = vertexZeroLinkage) ∧
    vertexZeroLinkage.vertexSet ≠ twoVertexEdgelessGraph.vertexSet ∧
    ¬ IsVitalLinkage twoVertexEdgelessGraph vertexZeroLinkage := by
  have hL := twoVertexEdgeless_isLinkage
  have h_term : terminals vertexZeroLinkage = {0} := by
    ext x
    change (x ∈ ({0} : Set (Fin 2)) ∧ vertexDegree vertexZeroLinkage x ≤ 1) ↔ x ∈ ({0} : Set (Fin 2))
    refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
    have h_emp : incidentEdges vertexZeroLinkage x = ∅ := by
      ext e; exact ⟨fun h => h.1.elim, False.elim⟩
    unfold vertexDegree
    rw [h_emp, sep_empty, ncard_empty]
    exact Nat.zero_le 1
  have h_uniq : ∀ L' : Hypergraph (Fin 2) Empty,
      IsLinkage twoVertexEdgelessGraph L' →
      linkagePattern L' = linkagePattern vertexZeroLinkage →
      L' = vertexZeroLinkage := by
    intro L' hL' hpat
    have hE : L'.edgeSet = ∅ := subset_empty_iff.mp hL'.1.edgeSet_subset
    have hC0 : IsComponentOf vertexZeroLinkage vertexZeroLinkage := by
      refine ⟨le_rfl, ⟨0, rfl⟩, ?_, ?_⟩
      · intro u hu v hv
        rw [show u = 0 from hu, show v = 0 from hv]
      · intro H hH _ _ hle
        exact le_antisymm hH hle
    have hB0 : ({0} : Set (Fin 2)) ∈ linkagePattern vertexZeroLinkage := by
      refine ⟨vertexZeroLinkage, hC0, ?_⟩
      rw [h_term]; ext z; simp [vertexZeroLinkage]
    rw [← hpat] at hB0
    rcases hB0 with ⟨C', _, hB_eq⟩
    have h0_in : (0 : Fin 2) ∈ L'.vertexSet := by
      have : (0 : Fin 2) ∈ terminals L' ∩ C'.vertexSet := by rw [← hB_eq]; exact rfl
      exact this.1.1
    have h1_not_in : (1 : Fin 2) ∉ L'.vertexSet := by
      intro h1
      let C1 : Hypergraph (Fin 2) Empty :=
        { vertexSet := {1}
          edgeSet := ∅
          Inc := fun e _ => e.elim
          vertex_mem_of_inc := fun e _ => e.elim
          edge_mem_of_inc := fun e _ => e.elim
          vertexSet_finite := finite_singleton 1
          edgeSet_finite := finite_empty }
      have hC1 : IsComponentOf L' C1 := by
        refine ⟨{ vertexSet_subset := singleton_subset_iff.mpr h1
                  edgeSet_subset := empty_subset _
                  ends_eq := fun e he => he.elim }, ⟨1, rfl⟩, ?_, ?_⟩
        · intro u hu v hv
          rw [show u = 1 from hu, show v = 1 from hv]
        · intro H hH _ hH_conn hSub
          refine le_antisymm ?_ hSub
          refine { vertexSet_subset := ?_
                   edgeSet_subset := fun e he => (hL'.1.edgeSet_subset (hH.edgeSet_subset he)).elim
                   ends_eq := fun e he => (hL'.1.edgeSet_subset (hH.edgeSet_subset he)).elim }
          intro u hu
          have h1H : (1 : Fin 2) ∈ H.vertexSet := hSub.vertexSet_subset rfl
          have hreach := hH_conn u hu 1 h1H
          rcases hreach with ⟨p⟩
          cases p with
          | nil => rfl
          | @cons _ b _ hadj _ =>
            rcases hadj with ⟨_, e, he, _⟩
            exact (hL'.1.edgeSet_subset (hH.edgeSet_subset (H.edge_mem_of_inc he))).elim
      have h1_term : (1 : Fin 2) ∈ terminals L' := by
        refine ⟨h1, ?_⟩
        have h_emp : incidentEdges L' 1 = ∅ := by
          ext e; exact ⟨fun h => (hL'.1.edgeSet_subset h.1).elim, False.elim⟩
        unfold vertexDegree
        rw [h_emp, sep_empty, ncard_empty]
        exact Nat.zero_le 1
      have hB1 : terminals L' ∩ C1.vertexSet ∈ linkagePattern L' := ⟨C1, hC1, rfl⟩
      rw [hpat] at hB1
      rcases hB1 with ⟨C'', _, hB1_eq⟩
      have h1_in_0 : (1 : Fin 2) ∈ terminals vertexZeroLinkage ∩ C''.vertexSet := by
        rw [← hB1_eq]
        exact ⟨h1_term, rfl⟩
      rw [h_term] at h1_in_0
      have : (1 : Fin 2) = 0 := h1_in_0.1
      revert this; decide
    have hV : L'.vertexSet = {0} := by
      ext x
      fin_cases x
      · exact ⟨fun _ => rfl, fun _ => h0_in⟩
      · exact ⟨fun hx => (h1_not_in hx).elim, fun hx => by cases hx⟩
    exact Hypergraph.ext hV hE (funext fun e => e.elim)
  have h_ne : vertexZeroLinkage.vertexSet ≠ twoVertexEdgelessGraph.vertexSet := by
    intro h_eq
    have h1_mem : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := by
      change (1 : Fin 2) ∈ vertexZeroLinkage.vertexSet
      rw [h_eq]; exact mem_univ 1
    have h1_eq : (1 : Fin 2) = 0 := h1_mem
    revert h1_eq; decide
  exact ⟨hL, h_uniq, h_ne, fun h_vit => h_ne h_vit.2.1⟩

/-! ## Example 3: 4-cycle counterexample to the first claim of (2.3) as printed

This is the counterexample of the correction to (2.3) in `corrections/GM21.md`. Let `G` be the
4-cycle `a, v, b, x` (`0, 1, 2, 3 : Fin 4`), let `L` be the 2-edge path `a, v, b` (`0 - 1 - 2`),
let `A` be the edgeless graph on `{a, v, b}`, let `B = G`, and let `L'` be the 2-edge path
`a, x, b` (`0 - 3 - 2`).
Then `(A, B)` is a separation of `G`, `L` is a linkage in `G`, `L'` is a linkage in `B` with the
same pattern `{{a, b}}` as `L ∩ B = L`, yet the literal union `(L ∩ A) ∪ L'` has `{v}` as an
isolated-vertex component and therefore does not have the same pattern as `L`. -/

/-- Incidence relation of the 4-cycle `0 - 1 - 2 - 3 - 0` on `Fin 4` (`a = 0, v = 1, b = 2, x = 3`). -/
def c4Inc (e u : Fin 4) : Prop :=
  (e = 0 ∧ (u = 0 ∨ u = 1)) ∨
  (e = 1 ∧ (u = 1 ∨ u = 2)) ∨
  (e = 2 ∧ (u = 2 ∨ u = 3)) ∨
  (e = 3 ∧ (u = 3 ∨ u = 0))

/-- The 4-cycle `G` on `a = 0, v = 1, b = 2, x = 3`. -/
def fourCycleGraph : Hypergraph (Fin 4) (Fin 4) where
  vertexSet := univ
  edgeSet := univ
  Inc := c4Inc
  vertex_mem_of_inc _ _ _ := mem_univ _
  edge_mem_of_inc _ _ _ := mem_univ _
  vertexSet_finite := finite_univ
  edgeSet_finite := finite_univ

/-- The 2-edge path `L = a, v, b` (`0 - 1 - 2`, edges `0` and `1`) in `fourCycleGraph`. -/
def pathAVB : Hypergraph (Fin 4) (Fin 4) where
  vertexSet := {0, 1, 2}
  edgeSet := {0, 1}
  Inc e u := (e = 0 ∧ (u = 0 ∨ u = 1)) ∨ (e = 1 ∧ (u = 1 ∨ u = 2))
  vertex_mem_of_inc := by
    rintro e u (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> simp
  edge_mem_of_inc := by
    rintro e u (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> simp
  vertexSet_finite := toFinite _
  edgeSet_finite := toFinite _

/-- The edgeless subgraph `A` on `{a, v, b} = {0, 1, 2}`. -/
def edgelessAVB : Hypergraph (Fin 4) (Fin 4) where
  vertexSet := {0, 1, 2}
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := toFinite _
  edgeSet_finite := finite_empty

/-- The 2-edge path `L' = a, x, b` (`0 - 3 - 2`, edges `2` and `3`) in `fourCycleGraph`. -/
def pathAXB : Hypergraph (Fin 4) (Fin 4) where
  vertexSet := {0, 3, 2}
  edgeSet := {2, 3}
  Inc e u := (e = 2 ∧ (u = 2 ∨ u = 3)) ∨ (e = 3 ∧ (u = 3 ∨ u = 0))
  vertex_mem_of_inc := by
    rintro e u (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;> simp
  edge_mem_of_inc := by
    rintro e u (⟨rfl, _⟩ | ⟨rfl, _⟩) <;> simp
  vertexSet_finite := toFinite _
  edgeSet_finite := toFinite _

/-- General characterization of a 2-edge path `0 - m - 2` inside `fourCycleGraph`: if `P ≤ fourCycleGraph`
has vertex set `{0, m, 2}` (`m ≠ 0, 2`) and edge set `{e₁, e₂}` (`e₁ ≠ e₂`) with ends `{0, m}` and
`{m, 2}`, then `P` is a linkage in `fourCycleGraph` with pattern `{{0, 2}}`. -/
lemma isLinkage_and_pattern_of_twoEdgePath {P : Hypergraph (Fin 4) (Fin 4)} {m e₁ e₂ : Fin 4}
    (hP_le : P ≤ fourCycleGraph)
    (hm0 : m ≠ 0) (hm2 : m ≠ 2) (he : e₁ ≠ e₂)
    (hV : P.vertexSet = {0, m, 2})
    (hE : P.edgeSet = {e₁, e₂})
    (hends₁ : P.ends e₁ = {0, m})
    (hends₂ : P.ends e₂ = {m, 2}) :
    IsLinkage fourCycleGraph P ∧ linkagePattern P = {{0, 2}} := by
  have he₁P : e₁ ∈ P.edgeSet := by rw [hE]; exact Or.inl rfl
  have he₂P : e₂ ∈ P.edgeSet := by rw [hE]; exact Or.inr rfl
  have h0_e₁ : P.Inc e₁ 0 := by change (0 : Fin 4) ∈ P.ends e₁; rw [hends₁]; exact Or.inl rfl
  have hm_e₁ : P.Inc e₁ m := by change m ∈ P.ends e₁; rw [hends₁]; exact Or.inr rfl
  have hm_e₂ : P.Inc e₂ m := by change m ∈ P.ends e₂; rw [hends₂]; exact Or.inl rfl
  have h2_e₂ : P.Inc e₂ 2 := by change (2 : Fin 4) ∈ P.ends e₂; rw [hends₂]; exact Or.inr rfl
  have hnot_0_e₂ : ¬ P.Inc e₂ 0 := by
    change (0 : Fin 4) ∉ P.ends e₂
    rw [hends₂]
    rintro (h | h)
    · exact hm0 h.symm
    · revert h; decide
  have hnot_2_e₁ : ¬ P.Inc e₁ 2 := by
    change (2 : Fin 4) ∉ P.ends e₁
    rw [hends₁]
    rintro (h | h)
    · revert h; decide
    · exact hm2 h.symm
  have hinc_0 : incidentEdges P 0 = {e₁} := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun ⟨heP, hinc⟩ => ?_, fun h => h ▸ ⟨he₁P, h0_e₁⟩⟩
    rw [hE] at heP
    rcases heP with rfl | rfl
    · rfl
    · exact (hnot_0_e₂ hinc).elim
  have hinc_2 : incidentEdges P 2 = {e₂} := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun ⟨heP, hinc⟩ => ?_, fun h => h ▸ ⟨he₂P, h2_e₂⟩⟩
    rw [hE] at heP
    rcases heP with rfl | rfl
    · exact (hnot_2_e₁ hinc).elim
    · rfl
  have hinc_m : incidentEdges P m = {e₁, e₂} := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    refine ⟨fun ⟨heP, _⟩ => by rwa [hE] at heP, ?_⟩
    rintro (rfl | rfl)
    · exact ⟨he₁P, hm_e₁⟩
    · exact ⟨he₂P, hm_e₂⟩
  have h2_ends : ∀ e ∈ P.edgeSet, (P.ends e).ncard = 2 := by
    intro e heP
    rw [hE] at heP
    rcases heP with rfl | rfl
    · rw [hends₁, ncard_pair hm0.symm]
    · rw [hends₂, ncard_pair hm2]
  have hP_gr : P.IsGraph := by
    intro e heP
    rw [hE] at heP
    rcases heP with rfl | rfl
    · exact ⟨⟨0, h0_e₁⟩, by rw [hends₁, ncard_pair hm0.symm]⟩
    · exact ⟨⟨m, hm_e₂⟩, by rw [hends₂, ncard_pair hm2]⟩
  have hadj_0m : P.skeleton.Adj 0 m := ⟨hm0.symm, e₁, h0_e₁, hm_e₁⟩
  have hadj_m2 : P.skeleton.Adj m 2 := ⟨hm2, e₂, hm_e₂, h2_e₂⟩
  have hreach_m : ∀ x ∈ P.vertexSet, P.skeleton.Reachable m x := by
    intro x hx
    rw [hV] at hx
    rcases hx with rfl | rfl | rfl
    · exact hadj_0m.symm.reachable
    · exact SimpleGraph.Reachable.refl _
    · exact hadj_m2.reachable
  have hconn : ∀ x ∈ P.vertexSet, ∀ y ∈ P.vertexSet, P.skeleton.Reachable x y :=
    fun x hx y hy => (hreach_m x hx).symm.trans (hreach_m y hy)
  have hP_ne : P.vertexSet.Nonempty := ⟨0, by rw [hV]; exact Or.inl rfl⟩
  have hP_path : IsPathGraph P := by
    refine ⟨hP_gr, hP_ne, hconn, h2_ends, ?_, ?_, ?_⟩
    · intro a ha b hb hends_eq
      rw [hE] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exfalso
        have h0_in : (0 : Fin 4) ∈ P.ends a := by rw [hends₁]; exact Or.inl rfl
        rw [hends_eq] at h0_in
        exact hnot_0_e₂ h0_in
      · exfalso
        have h0_in : (0 : Fin 4) ∈ P.ends b := by rw [hends₁]; exact Or.inl rfl
        rw [← hends_eq] at h0_in
        exact hnot_0_e₂ h0_in
      · rfl
    · intro x hx
      rw [hV] at hx
      rcases hx with rfl | rfl | rfl
      · rw [hinc_0, ncard_singleton]; omega
      · rw [hinc_m, ncard_pair he]
      · rw [hinc_2, ncard_singleton]; omega
    · intro H hHP ⟨e₀, he₀H⟩
      by_cases he₁H : e₁ ∈ H.edgeSet
      · have h0_incH : H.Inc e₁ 0 := (inc_iff_of_le hHP he₁H).2 h0_e₁
        refine ⟨0, H.vertex_mem_of_inc h0_incH, ?_⟩
        have hincH_0 : incidentEdges H 0 = {e₁} := by
          refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨he₁H, h0_incH⟩)
          rw [← hinc_0]
          exact fun e he => ⟨hHP.edgeSet_subset he.1, inc_of_le hHP he.2⟩
        rw [hincH_0, ncard_singleton]
      · have he₀P : e₀ ∈ P.edgeSet := hHP.edgeSet_subset he₀H
        rw [hE] at he₀P
        have he₂H : e₂ ∈ H.edgeSet := (he₀P.resolve_left fun h => he₁H (h ▸ he₀H)) ▸ he₀H
        have h2_incH : H.Inc e₂ 2 := (inc_iff_of_le hHP he₂H).2 h2_e₂
        refine ⟨2, H.vertex_mem_of_inc h2_incH, ?_⟩
        have hincH_2 : incidentEdges H 2 = {e₂} := by
          refine Subset.antisymm ?_ (singleton_subset_iff.mpr ⟨he₂H, h2_incH⟩)
          rw [← hinc_2]
          exact fun e he => ⟨hHP.edgeSet_subset he.1, inc_of_le hHP he.2⟩
        rw [hincH_2, ncard_singleton]
  have hcomp_iff : ∀ C : Hypergraph (Fin 4) (Fin 4), IsComponentOf P C ↔ C = P := by
    intro C
    refine ⟨fun hC => (hC.2.2.2 P le_rfl hP_ne hconn hC.1).symm, ?_⟩
    rintro rfl
    exact ⟨le_rfl, hP_ne, hconn, fun C' hC' _ _ hPC' => le_antisymm hC' hPC'⟩
  have hL : IsLinkage fourCycleGraph P :=
    ⟨hP_le, hP_gr, fun C hC => (hcomp_iff C).mp hC ▸ hP_path⟩
  have hdeg_eq : ∀ x : Fin 4, vertexDegree P x = (incidentEdges P x).ncard :=
    fun x => hL.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl x
  have hterm : terminals P = {0, 2} := by
    ext x
    simp only [terminals, IsTerminal, mem_ofPred_eq, hdeg_eq, hV, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨rfl | rfl | rfl, hle⟩
      · exact Or.inl rfl
      · rw [hinc_m, ncard_pair he] at hle; omega
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · refine ⟨Or.inl rfl, ?_⟩; rw [hinc_0, ncard_singleton]
      · refine ⟨Or.inr (Or.inr rfl), ?_⟩; rw [hinc_2, ncard_singleton]
  refine ⟨hL, ?_⟩
  ext B
  simp only [linkagePattern, mem_ofPred_eq, hcomp_iff, exists_eq_left, mem_singleton_iff]
  have hinter : terminals P ∩ P.vertexSet = {0, 2} := by
    rw [hterm, hV]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    tauto
  rw [hinter]

/-- **The first claim of Graph Minors XXI, (2.3), as printed, is false** (see the correction to
(2.3) in `corrections/GM21.md`). For the 4-cycle `G = fourCycleGraph`, path `L = pathAVB`, edgeless
`A = edgelessAVB`, `B = fourCycleGraph`, and `L' = pathAXB`, all hypotheses of `(2.3)` hold, yet the
literal union `(L ∩ A) ∪ L'` does not have the pattern of `L`. -/
theorem theorem_2_3_literal_union_counterexample :
    IsLinkage fourCycleGraph pathAVB ∧
    fourCycleGraph.IsSeparation edgelessAVB fourCycleGraph ∧
    IsLinkage fourCycleGraph pathAXB ∧
    linkagePattern pathAXB = linkagePattern (pathAVB ∩ fourCycleGraph) ∧
    linkagePattern ((pathAVB ∩ edgelessAVB) ∪ pathAXB) ≠ linkagePattern pathAVB := by
  have hL_le : pathAVB ≤ fourCycleGraph := by
    refine ⟨subset_univ _, subset_univ _, fun e he => ?_⟩
    ext u
    rcases he with rfl | rfl <;> simp [Hypergraph.ends, pathAVB, fourCycleGraph, c4Inc]
  have hL'_le : pathAXB ≤ fourCycleGraph := by
    refine ⟨subset_univ _, subset_univ _, fun e he => ?_⟩
    ext u
    rcases he with rfl | rfl <;> simp [Hypergraph.ends, pathAXB, fourCycleGraph, c4Inc]
  have hL_props : IsLinkage fourCycleGraph pathAVB ∧ linkagePattern pathAVB = {{0, 2}} := by
    refine isLinkage_and_pattern_of_twoEdgePath (m := 1) (e₁ := 0) (e₂ := 1)
      hL_le (by decide) (by decide) (by decide) rfl rfl ?_ ?_
    · ext u; simp [Hypergraph.ends, pathAVB]
    · ext u; simp [Hypergraph.ends, pathAVB]
  have hL'_props : IsLinkage fourCycleGraph pathAXB ∧ linkagePattern pathAXB = {{0, 2}} := by
    refine isLinkage_and_pattern_of_twoEdgePath (m := 3) (e₁ := 3) (e₂ := 2)
      hL'_le (by decide) (by decide) (by decide) rfl ?_ ?_ ?_
    · ext e; simp [pathAXB, or_comm]
    · ext u; simp [Hypergraph.ends, pathAXB, or_comm]
    · ext u; simp [Hypergraph.ends, pathAXB, or_comm]
  have hsep : fourCycleGraph.IsSeparation edgelessAVB fourCycleGraph :=
    { left_le :=
        { vertexSet_subset := subset_univ _
          edgeSet_subset := empty_subset _
          ends_eq := fun _ he => he.elim }
      right_le := le_rfl
      union_eq := Hypergraph.ext
        (by ext x; simp [fourCycleGraph])
        (by ext e; simp [fourCycleGraph, edgelessAVB])
        (funext fun e => funext fun u => propext ⟨fun h => h.resolve_left id, Or.inr⟩)
      edgeSet_inter_eq := empty_inter _ }
  have hLB_eq : pathAVB ∩ fourCycleGraph = pathAVB :=
    eq_of_le_of_vertexSet_eq_of_edgeSet_eq (inter_le_left hL_le le_rfl) le_rfl
      (by ext x; simp [fourCycleGraph]) (by ext e; simp [fourCycleGraph])
  refine ⟨hL_props.1, hsep, hL'_props.1, by rw [hLB_eq, hL'_props.2, hL_props.2], ?_⟩
  intro hpat_eq
  let U := (pathAVB ∩ edgelessAVB) ∪ pathAXB
  have h1_U : (1 : Fin 4) ∈ U.vertexSet :=
    Or.inl ⟨by simp [pathAVB], by simp [edgelessAVB]⟩
  have hnot_inc_1 : ∀ e : Fin 4, ¬ U.Inc e 1 := by
    rintro e (⟨_, hA⟩ | hL')
    · exact hA
    · rcases hL' with ⟨_, h | h⟩ | ⟨_, h | h⟩ <;> revert h <;> decide
  have hinc_U_1 : incidentEdges U 1 = ∅ := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun _ => hnot_inc_1 e
  have h1_termU : (1 : Fin 4) ∈ terminals U := by
    refine ⟨h1_U, ?_⟩
    unfold vertexDegree
    rw [hinc_U_1, sep_empty, ncard_empty]
    exact Nat.zero_le 1
  let C₁ : Hypergraph (Fin 4) (Fin 4) :=
    { vertexSet := {1}
      edgeSet := ∅
      Inc := fun _ _ => False
      vertex_mem_of_inc := fun _ _ h => h.elim
      edge_mem_of_inc := fun _ _ h => h.elim
      vertexSet_finite := finite_singleton 1
      edgeSet_finite := finite_empty }
  have hC₁_comp : IsComponentOf U C₁ := by
    refine ⟨{ vertexSet_subset := singleton_subset_iff.mpr h1_U
              edgeSet_subset := empty_subset _
              ends_eq := fun _ he => he.elim }, ⟨1, rfl⟩, ?_, ?_⟩
    · intro x hx y hy
      rw [show x = 1 from hx, show y = 1 from hy]
    · intro H hHU _ hH_conn hC₁H
      have h1H : (1 : Fin 4) ∈ H.vertexSet := hC₁H.vertexSet_subset rfl
      have hV_H : H.vertexSet ⊆ {1} := by
        intro u hu
        obtain ⟨W⟩ := hH_conn 1 h1H u hu
        cases W with
        | nil => rfl
        | @cons _ b _ hadj _ =>
          rcases hadj with ⟨_, e, hinc1, _⟩
          exact (hnot_inc_1 e (inc_of_le hHU hinc1)).elim
      have hE_H : H.edgeSet = ∅ := by
        ext e
        simp only [mem_empty_iff_false, iff_false]
        intro heH
        have heU : e ∈ U.edgeSet := hHU.edgeSet_subset heH
        rcases heU with ⟨_, heA⟩ | heL'
        · exact heA
        · have heG : e ∈ fourCycleGraph.edgeSet := hL'_le.edgeSet_subset heL'
          have h2_ends : e = 2 ∨ e = 3 := heL'
          rcases h2_ends with rfl | rfl
          · have h2_inc : U.Inc 2 2 := Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
            have h2_H : (2 : Fin 4) ∈ H.vertexSet :=
              H.vertex_mem_of_inc ((inc_iff_of_le hHU heH).2 h2_inc)
            have h2_eq : (2 : Fin 4) = 1 := hV_H h2_H
            revert h2_eq; decide
          · have h3_inc : U.Inc 3 3 := Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)
            have h3_H : (3 : Fin 4) ∈ H.vertexSet :=
              H.vertex_mem_of_inc ((inc_iff_of_le hHU heH).2 h3_inc)
            have h3_eq : (3 : Fin 4) = 1 := hV_H h3_H
            revert h3_eq; decide
      refine le_antisymm ?_ hC₁H
      exact { vertexSet_subset := hV_H
              edgeSet_subset := hE_H.subset
              ends_eq := fun _ he => (hE_H ▸ he).elim }
  have h1_block : ({1} : Set (Fin 4)) ∈ linkagePattern U := by
    refine ⟨C₁, hC₁_comp, ?_⟩
    ext x
    simp only [C₁, mem_singleton_iff, mem_inter_iff, iff_and_self]
    rintro rfl
    exact h1_termU
  rw [hpat_eq, hL_props.2, mem_singleton_iff] at h1_block
  have h1_in_02 : (1 : Fin 4) ∈ ({0, 2} : Set (Fin 4)) := by
    rw [← h1_block]; exact rfl
  rcases h1_in_02 with h | h <;> revert h <;> decide

/-! ## Example 4: A drawing with no edges is not a presentation of a graph with an edge -/

universe u v w

/-- A drawing `Γ` with no edges (`Γ.E = ∅`) cannot be a presentation when the drawn subgraph
`Γ_sub` has an edge. -/
theorem edgeless_drawing_not_isPresentation_of_subgraph_edge
    {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G Γ_sub : Hypergraph α β} {Γ : Surface.Drawing S}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hE_empty : Γ.E = ∅) (hne : Γ_sub.edgeSet.Nonempty) :
    ¬ IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q := by
  intro hp
  rcases hne with ⟨e, he⟩
  rw [← hp.drawing_iso.ιE_image, hE_empty, image_empty] at he
  exact he

/-- On any surface `S` with empty boundary (`bd S = ∅`), a drawing `Γ` with no edges (`Γ.E = ∅`)
is not a presentation of any graph `G` with an edge (`G.edgeSet.Nonempty`), for any choice of
`Γ_sub, ιV, ιE, r, F_star, H, μ, q`. -/
theorem edgeless_drawing_not_isPresentation_of_bd_empty
    {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G Γ_sub : Hypergraph α β} {Γ : Surface.Drawing S}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {H : Fin r → Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hE_empty : Γ.E = ∅) (hbd : Surface.bd S = ∅) (hne : G.edgeSet.Nonempty) :
    ¬ IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q := by
  intro hp
  rcases hne with ⟨e, heG⟩
  rw [hp.v1_union_E] at heG
  rcases heG with he_H | he_sub
  · rw [mem_iUnion] at he_H
    rcases he_H with ⟨j, _⟩
    rcases hp.supports_isSupport j with ⟨_, _, ⟨_, hv, _⟩ | ⟨_, _, hv, _⟩⟩
    · have h := hv.2; rw [hbd] at h; exact h
    · have h := hv.2; rw [hbd] at h; exact h
  · rw [← hp.drawing_iso.ιE_image, hE_empty, image_empty] at he_sub
    exact he_sub

/-! ## Example 5: Type check of `theorem_1_1_proof` (`GM21Theorem11Statement`) -/

example :
    ∀ p : ℕ, ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β),
      V(G).Finite → E(G).Finite → Final.IsVitalPLinkage G L p → TreeWidthLE G w :=
  @theorem_1_1_proof.{u, v}

end GraphMinor.GM21.Checks
