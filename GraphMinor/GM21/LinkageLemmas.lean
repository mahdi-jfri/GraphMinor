module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI: Basic lemmas on components, paths, and linkages

This file establishes the structural properties of connected components (`reachableComponent`,
`IsComponentOf`), path graphs (`IsPathGraph`), linkages (`IsLinkage`), terminals (`terminals`),
and linkage patterns (`linkagePattern`) used in Section 2 and throughout Graph Minors XXI.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Subhypergraphs of graphs and skeletons -/

/-- Any subhypergraph of a graph is a graph. -/
lemma isGraph_of_le {H G : Hypergraph α β} (hle : H ≤ G) (hG : G.IsGraph) : H.IsGraph := by
  intro e he
  rw [← hle.ends_eq e he]
  exact hG e (hle.edgeSet_subset he)

/-- If `H ≤ G`, then `H.skeleton ≤ G.skeleton`. -/
lemma skeleton_le_of_le {H G : Hypergraph α β} (hle : H ≤ G) : H.skeleton ≤ G.skeleton := by
  intro x y ⟨hne, e, hx, hy⟩
  exact ⟨hne, e, inc_of_le hle hx, inc_of_le hle hy⟩

/-- Reachability in `H.skeleton` implies reachability in `G.skeleton` when `H ≤ G`. -/
lemma reachable_of_le {H G : Hypergraph α β} (hle : H ≤ G) {x y : α}
    (hr : H.skeleton.Reachable x y) : G.skeleton.Reachable x y :=
  hr.mono (skeleton_le_of_le hle)

/-- For `H ≤ G` and `v : α`, `incidentEdges H v ⊆ incidentEdges G v`. -/
lemma incidentEdges_subset_of_le {H G : Hypergraph α β} (hle : H ≤ G) (v : α) :
    incidentEdges H v ⊆ incidentEdges G v := by
  rintro e ⟨he, hinc⟩
  exact ⟨hle.edgeSet_subset he, inc_of_le hle hinc⟩

/-- For `H ≤ G` and `v : α`, `incidentEdges H v = incidentEdges G v ∩ H.edgeSet`. -/
lemma incidentEdges_eq_inter_edgeSet_of_le {H G : Hypergraph α β} (hle : H ≤ G) (v : α) :
    incidentEdges H v = incidentEdges G v ∩ H.edgeSet := by
  ext e
  simp only [incidentEdges, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨he, hinc⟩
    exact ⟨⟨hle.edgeSet_subset he, inc_of_le hle hinc⟩, he⟩
  · rintro ⟨⟨_, hincG⟩, he⟩
    exact ⟨he, (inc_iff_of_le hle he).2 hincG⟩

/-- If `H` is loop-free (every edge has 2 ends), then `vertexDegree H v = (incidentEdges H v).ncard`. -/
lemma vertexDegree_eq_ncard_incidentEdges {H : Hypergraph α β}
    (hloop : ∀ e ∈ H.edgeSet, (H.ends e).ncard = 2) (v : α) :
    vertexDegree H v = (incidentEdges H v).ncard := by
  unfold vertexDegree
  have hemp : {e ∈ incidentEdges H v | (H.ends e).Subsingleton} = ∅ := by
    ext e
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro he hsub
    have h2 : (H.ends e).ncard = 2 := hloop e he.1
    rcases hsub.eq_empty_or_singleton with h | ⟨x, h⟩
    · rw [h, ncard_empty] at h2; omega
    · rw [h, ncard_singleton] at h2; omega
  rw [hemp, ncard_empty, add_zero]

/-! ## 2. Connected components (`reachableComponent` and `IsComponentOf`) -/

/-- The connected component of `H` containing `v`: the subhypergraph of `H` with vertex set
`{u ∈ H.vertexSet | H.skeleton.Reachable v u}` and all edges of `H` incident with a vertex
reachable from `v` in `H.skeleton`. -/
def reachableComponent (H : Hypergraph α β) (v : α) : Hypergraph α β where
  vertexSet := {u ∈ H.vertexSet | H.skeleton.Reachable v u}
  edgeSet := {e ∈ H.edgeSet | ∃ u, H.Inc e u ∧ H.skeleton.Reachable v u}
  Inc e u := H.Inc e u ∧ ∃ w, H.Inc e w ∧ H.skeleton.Reachable v w
  vertex_mem_of_inc := by
    rintro e u ⟨hinc, w, hw, hr⟩
    refine ⟨H.vertex_mem_of_inc hinc, ?_⟩
    by_cases huw : u = w
    · subst huw; exact hr
    · exact hr.trans (SimpleGraph.Adj.reachable ⟨Ne.symm huw, e, hw, hinc⟩)
  edge_mem_of_inc := fun _ _ ⟨hinc, hex⟩ => ⟨H.edge_mem_of_inc hinc, hex⟩
  vertexSet_finite := H.vertexSet_finite.subset fun _ hu => hu.1
  edgeSet_finite := H.edgeSet_finite.subset fun _ he => he.1

@[simp]
lemma reachableComponent_vertexSet (H : Hypergraph α β) (v : α) :
    (reachableComponent H v).vertexSet = {u ∈ H.vertexSet | H.skeleton.Reachable v u} := rfl

@[simp]
lemma reachableComponent_edgeSet (H : Hypergraph α β) (v : α) :
    (reachableComponent H v).edgeSet =
      {e ∈ H.edgeSet | ∃ u, H.Inc e u ∧ H.skeleton.Reachable v u} := rfl

@[simp]
lemma reachableComponent_inc (H : Hypergraph α β) (v : α) (e : β) (u : α) :
    (reachableComponent H v).Inc e u ↔
      H.Inc e u ∧ ∃ w, H.Inc e w ∧ H.skeleton.Reachable v w := Iff.rfl

/-- `reachableComponent H v` is always a subhypergraph of `H`. -/
lemma reachableComponent_le (H : Hypergraph α β) (v : α) : reachableComponent H v ≤ H where
  vertexSet_subset _ hu := hu.1
  edgeSet_subset _ he := he.1
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, reachableComponent_inc]
    exact ⟨fun h => ⟨h, he.2⟩, fun h => h.1⟩

/-- If `v ∈ H.vertexSet`, then `v ∈ (reachableComponent H v).vertexSet`. -/
lemma self_mem_reachableComponent {H : Hypergraph α β} {v : α} (hv : v ∈ H.vertexSet) :
    v ∈ (reachableComponent H v).vertexSet :=
  ⟨hv, SimpleGraph.Reachable.refl v⟩

/-- Any walk in `H.skeleton` starting at a vertex in `reachableComponent H v` lifts to a walk in
`(reachableComponent H v).skeleton`. -/
lemma walk_lift_reachableComponent {H : Hypergraph α β} {v x y : α}
    (hx : H.skeleton.Reachable v x) (W : H.skeleton.Walk x y) :
    (reachableComponent H v).skeleton.Reachable x y := by
  induction W with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons a b c hadj W' ih =>
    have hab_reach : H.skeleton.Reachable v b := hx.trans hadj.reachable
    have hadj_rc : (reachableComponent H v).skeleton.Adj a b := by
      rcases hadj with ⟨hne, e, ha, hb⟩
      exact ⟨hne, e, ⟨ha, a, ha, hx⟩, ⟨hb, a, ha, hx⟩⟩
    exact hadj_rc.reachable.trans (ih hab_reach)

/-- Two vertices `x, y ∈ (reachableComponent H v).vertexSet` are reachable in
`(reachableComponent H v).skeleton` if and only if they are reachable in `H.skeleton`. -/
lemma reachable_reachableComponent_iff {H : Hypergraph α β} {v x y : α}
    (hx : x ∈ (reachableComponent H v).vertexSet) :
    (reachableComponent H v).skeleton.Reachable x y ↔ H.skeleton.Reachable x y := by
  refine ⟨reachable_of_le (reachableComponent_le H v), fun ⟨W⟩ => ?_⟩
  exact walk_lift_reachableComponent hx.2 W

/-- Every vertex in `reachableComponent H v` is reachable from every other vertex in
`reachableComponent H v` inside `(reachableComponent H v).skeleton`. -/
lemma reachableComponent_connected (H : Hypergraph α β) (v : α)
    {x y : α} (hx : x ∈ (reachableComponent H v).vertexSet)
    (hy : y ∈ (reachableComponent H v).vertexSet) :
    (reachableComponent H v).skeleton.Reachable x y := by
  rw [reachable_reachableComponent_iff hx]
  exact hx.2.symm.trans hy.2

/-- If `H.IsGraph` and `v ∈ H.vertexSet`, then `reachableComponent H v` is a connected component
of `H` (`IsComponentOf H (reachableComponent H v)`). -/
lemma isComponentOf_reachableComponent {H : Hypergraph α β} (hH : H.IsGraph)
    {v : α} (hv : v ∈ H.vertexSet) :
    IsComponentOf H (reachableComponent H v) := by
  refine ⟨reachableComponent_le H v, ⟨v, self_mem_reachableComponent hv⟩,
    fun x hx y hy => reachableComponent_connected H v hx hy, ?_⟩
  intro C' hC'H _ hC'_conn hle
  apply eq_of_le_of_vertexSet_eq_of_edgeSet_eq hC'H (reachableComponent_le H v)
  · refine Subset.antisymm ?_ hle.vertexSet_subset
    intro u hu
    have hvC' : v ∈ C'.vertexSet := hle.vertexSet_subset (self_mem_reachableComponent hv)
    exact ⟨hC'H.vertexSet_subset hu, reachable_of_le hC'H (hC'_conn v hvC' u hu)⟩
  · refine Subset.antisymm ?_ hle.edgeSet_subset
    intro e he
    have heH : e ∈ H.edgeSet := hC'H.edgeSet_subset he
    obtain ⟨u, hu⟩ := (hH e heH).1
    have huC' : C'.Inc e u := (inc_iff_of_le hC'H he).2 hu
    have hu_mem : u ∈ C'.vertexSet := C'.vertex_mem_of_inc huC'
    have hvC' : v ∈ C'.vertexSet := hle.vertexSet_subset (self_mem_reachableComponent hv)
    exact ⟨heH, u, hu, reachable_of_le hC'H (hC'_conn v hvC' u hu_mem)⟩

/-- If `H.IsGraph`, `IsComponentOf H C`, and `v ∈ C.vertexSet`, then `C = reachableComponent H v`. -/
lemma eq_reachableComponent_of_isComponentOf {H C : Hypergraph α β} (hH : H.IsGraph)
    (hC : IsComponentOf H C) {v : α} (hv : v ∈ C.vertexSet) :
    C = reachableComponent H v := by
  have hvH : v ∈ H.vertexSet := hC.1.vertexSet_subset hv
  have hrc : IsComponentOf H (reachableComponent H v) := isComponentOf_reachableComponent hH hvH
  have hle : C ≤ reachableComponent H v := by
    rw [le_iff_of_le hC.1 (reachableComponent_le H v)]
    refine ⟨?_, ?_⟩
    · intro u hu
      exact ⟨hC.1.vertexSet_subset hu, reachable_of_le hC.1 (hC.2.2.1 v hv u hu)⟩
    · intro e he
      have heH : e ∈ H.edgeSet := hC.1.edgeSet_subset he
      obtain ⟨u, hu⟩ := (hH e heH).1
      have huC : C.Inc e u := (inc_iff_of_le hC.1 he).2 hu
      have hu_mem : u ∈ C.vertexSet := C.vertex_mem_of_inc huC
      exact ⟨heH, u, hu, reachable_of_le hC.1 (hC.2.2.1 v hv u hu_mem)⟩
  exact (hC.2.2.2 (reachableComponent H v) hrc.1 hrc.2.1 hrc.2.2.1 hle).symm

/-- For `x ∈ (reachableComponent H v).vertexSet`, the incident edges of `x` in
`reachableComponent H v` are the same as in `H`. -/
lemma incidentEdges_reachableComponent_eq {H : Hypergraph α β} {v x : α}
    (hx : x ∈ (reachableComponent H v).vertexSet) :
    incidentEdges (reachableComponent H v) x = incidentEdges H x := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq, reachableComponent_edgeSet, reachableComponent_inc]
  exact ⟨fun ⟨he, hinc, _⟩ => ⟨he.1, hinc⟩, fun ⟨he, hinc⟩ => ⟨⟨he, x, hinc, hx.2⟩, hinc, x, hinc, hx.2⟩⟩

/-- For any component `C` of a graph `H` and `x ∈ C.vertexSet`,
`incidentEdges C x = incidentEdges H x`. -/
lemma incidentEdges_component_eq {H C : Hypergraph α β} (hH : H.IsGraph)
    (hC : IsComponentOf H C) {x : α} (hx : x ∈ C.vertexSet) :
    incidentEdges C x = incidentEdges H x := by
  rw [eq_reachableComponent_of_isComponentOf hH hC hx]
  exact incidentEdges_reachableComponent_eq (self_mem_reachableComponent (hC.1.vertexSet_subset hx))

/-- For any component `C` of a graph `H` and `x ∈ C.vertexSet`,
`vertexDegree C x = vertexDegree H x`. -/
lemma vertexDegree_component_eq {H C : Hypergraph α β} (hH : H.IsGraph)
    (hC : IsComponentOf H C) {x : α} (hx : x ∈ C.vertexSet) :
    vertexDegree C x = vertexDegree H x := by
  have hinc := incidentEdges_component_eq hH hC hx
  unfold vertexDegree
  rw [hinc]
  congr 2
  ext e
  simp only [mem_ofPred_eq]
  refine and_congr_right fun he => ?_
  have heC : e ∈ C.edgeSet := by
    have : e ∈ incidentEdges C x := by rwa [hinc]
    exact this.1
  rw [hC.1.ends_eq e heC]

/-- For any subhypergraph `H' ≤ H` and any `v, x : α` with `x ∈ (H' ∩ reachableComponent H v).vertexSet`,
`incidentEdges (H' ∩ reachableComponent H v) x = incidentEdges H' x`. -/
lemma incidentEdges_inter_reachableComponent_eq {H H' : Hypergraph α β} (hH' : H' ≤ H)
    {v x : α} (hx : x ∈ (H' ∩ reachableComponent H v).vertexSet) :
    incidentEdges (H' ∩ reachableComponent H v) x = incidentEdges H' x := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq, inter_edgeSet, inter_inc,
    reachableComponent_edgeSet, reachableComponent_inc]
  constructor
  · rintro ⟨⟨he, _⟩, hinc, _⟩
    exact ⟨he, hinc⟩
  · rintro ⟨he, hinc⟩
    have hincH : H.Inc e x := inc_of_le hH' hinc
    exact ⟨⟨he, hH'.edgeSet_subset he, x, hincH, hx.2.2⟩, hinc, hincH, x, hincH, hx.2.2⟩

/-- Distinct components of a graph `H` have disjoint vertex sets and disjoint edge sets. -/
lemma disjoint_of_isComponentOf_ne {H C₁ C₂ : Hypergraph α β} (hH : H.IsGraph)
    (h₁ : IsComponentOf H C₁) (h₂ : IsComponentOf H C₂) (hne : C₁ ≠ C₂) :
    Disjoint C₁.vertexSet C₂.vertexSet ∧ Disjoint C₁.edgeSet C₂.edgeSet := by
  have hV : Disjoint C₁.vertexSet C₂.vertexSet := by
    rw [disjoint_left]
    intro x hx₁ hx₂
    apply hne
    rw [eq_reachableComponent_of_isComponentOf hH h₁ hx₁,
        eq_reachableComponent_of_isComponentOf hH h₂ hx₂]
  refine ⟨hV, disjoint_left.2 fun e he₁ he₂ => ?_⟩
  have heH : e ∈ H.edgeSet := h₁.1.edgeSet_subset he₁
  obtain ⟨u, hu⟩ := (hH e heH).1
  have hu₁ : u ∈ C₁.vertexSet := C₁.vertex_mem_of_inc ((inc_iff_of_le h₁.1 he₁).2 hu)
  have hu₂ : u ∈ C₂.vertexSet := C₂.vertex_mem_of_inc ((inc_iff_of_le h₂.1 he₂).2 hu)
  exact disjoint_left.1 hV hu₁ hu₂

/-! ## 3. Heredity of `IsPathGraph` and `IsLinkage` -/

/-- Any non-empty connected subhypergraph `C` of a path graph `P` is a path graph. -/
lemma isPathGraph_of_le {P C : Hypergraph α β} (hP : IsPathGraph P) (hCP : C ≤ P)
    (hne : C.vertexSet.Nonempty)
    (hconn : ∀ x ∈ C.vertexSet, ∀ y ∈ C.vertexSet, C.skeleton.Reachable x y) :
    IsPathGraph C := by
  rcases hP with ⟨hP_gr, _, _, hP_ends, hP_simp, hP_deg, hP_acyc⟩
  refine ⟨isGraph_of_le hCP hP_gr, hne, hconn, ?_, ?_, ?_, ?_⟩
  · intro e he
    rw [← hCP.ends_eq e he]
    exact hP_ends e (hCP.edgeSet_subset he)
  · intro e₁ he₁ e₂ he₂ hends
    apply hP_simp e₁ (hCP.edgeSet_subset he₁) e₂ (hCP.edgeSet_subset he₂)
    rw [hCP.ends_eq e₁ he₁, hCP.ends_eq e₂ he₂, hends]
  · intro x hx
    calc
      (incidentEdges C x).ncard ≤ (incidentEdges P x).ncard :=
        ncard_le_ncard (incidentEdges_subset_of_le hCP x)
          (P.edgeSet_finite.subset fun _ h => h.1)
      _ ≤ 2 := hP_deg x (hCP.vertexSet_subset hx)
  · intro H hHC hH_ne
    exact hP_acyc H (hHC.trans hCP) hH_ne

/-- If `L` is a linkage in `G` and `H ≤ L` with `H ≤ G'`, then `H` is a linkage in `G'`. -/
lemma isLinkage_of_le {G G' L H : Hypergraph α β} (hL : IsLinkage G L)
    (hHL : H ≤ L) (hHG' : H ≤ G') : IsLinkage G' H := by
  have hH_gr : H.IsGraph := isGraph_of_le hHL hL.2.1
  refine ⟨hHG', hH_gr, fun C hC => ?_⟩
  obtain ⟨v, hvC⟩ := hC.2.1
  have hvL : v ∈ L.vertexSet := hHL.vertexSet_subset (hC.1.vertexSet_subset hvC)
  let C₀ := reachableComponent L v
  have hC₀_comp : IsComponentOf L C₀ := isComponentOf_reachableComponent hL.2.1 hvL
  have hC₀_path : IsPathGraph C₀ := hL.2.2 C₀ hC₀_comp
  have hCC₀ : C ≤ C₀ := by
    rw [le_iff_of_le (hC.1.trans hHL) (reachableComponent_le L v)]
    refine ⟨?_, ?_⟩
    · intro u hu
      exact ⟨hHL.vertexSet_subset (hC.1.vertexSet_subset hu),
        reachable_of_le (hC.1.trans hHL) (hC.2.2.1 v hvC u hu)⟩
    · intro e he
      have heH : e ∈ H.edgeSet := hC.1.edgeSet_subset he
      obtain ⟨u, hu⟩ := (hH_gr e heH).1
      have huC : C.Inc e u := (inc_iff_of_le hC.1 he).2 hu
      have hu_mem : u ∈ C.vertexSet := C.vertex_mem_of_inc huC
      exact ⟨hHL.edgeSet_subset heH, u, inc_of_le hHL hu,
        reachable_of_le (hC.1.trans hHL) (hC.2.2.1 v hvC u hu_mem)⟩
  exact isPathGraph_of_le hC₀_path hCC₀ hC.2.1 hC.2.2.1

/-! ## 4. Basic edge and degree properties of linkages -/

/-- Every edge of a linkage `L` has two distinct ends (`(L.ends e).ncard = 2`). -/
lemma IsLinkage.ends_ncard_eq_two {G L : Hypergraph α β} (hL : IsLinkage G L)
    {e : β} (he : e ∈ L.edgeSet) : (L.ends e).ncard = 2 := by
  obtain ⟨v, hv⟩ := (hL.2.1 e he).1
  have hvL : v ∈ L.vertexSet := L.vertex_mem_of_inc hv
  have hcomp : IsComponentOf L (reachableComponent L v) :=
    isComponentOf_reachableComponent hL.2.1 hvL
  have hpath : IsPathGraph (reachableComponent L v) := hL.2.2 _ hcomp
  have he_rc : e ∈ (reachableComponent L v).edgeSet :=
    ⟨he, v, hv, SimpleGraph.Reachable.refl v⟩
  rw [(reachableComponent_le L v).ends_eq e he_rc]
  exact hpath.2.2.2.1 e he_rc

/-- Every vertex of a linkage `L` has at most `2` incident edges in `L`. -/
lemma IsLinkage.ncard_incidentEdges_le_two {G L : Hypergraph α β} (hL : IsLinkage G L)
    (x : α) : (incidentEdges L x).ncard ≤ 2 := by
  by_cases hx : x ∈ L.vertexSet
  · have hcomp : IsComponentOf L (reachableComponent L x) :=
      isComponentOf_reachableComponent hL.2.1 hx
    have hpath : IsPathGraph (reachableComponent L x) := hL.2.2 _ hcomp
    have hx_rc : x ∈ (reachableComponent L x).vertexSet := self_mem_reachableComponent hx
    rw [← incidentEdges_reachableComponent_eq hx_rc]
    exact hpath.2.2.2.2.2.1 x hx_rc
  · have hemp : incidentEdges L x = ∅ := by
      ext e
      simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ hinc
      exact hx (L.vertex_mem_of_inc hinc)
    rw [hemp, ncard_empty]
    exact Nat.zero_le 2

/-- For any subhypergraph `H ≤ L` of a linkage `L`, `vertexDegree H x = (incidentEdges H x).ncard`. -/
lemma IsLinkage.vertexDegree_eq_ncard_incidentEdges_of_le {G L H : Hypergraph α β}
    (hL : IsLinkage G L) (hHL : H ≤ L) (x : α) :
    vertexDegree H x = (incidentEdges H x).ncard := by
  apply vertexDegree_eq_ncard_incidentEdges
  intro e he
  rw [← hHL.ends_eq e he]
  exact hL.ends_ncard_eq_two (hHL.edgeSet_subset he)

/-- Every edge-nonempty subhypergraph `H ≤ L` of a linkage `L` has a vertex of degree `1` in `H`. -/
lemma IsLinkage.exists_deg_one_of_le {G L H : Hypergraph α β} (hL : IsLinkage G L)
    (hHL : H ≤ L) (hne : H.edgeSet.Nonempty) :
    ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1 := by
  rcases hne with ⟨e, he⟩
  have heL : e ∈ L.edgeSet := hHL.edgeSet_subset he
  obtain ⟨v, hv⟩ := (hL.2.1 e heL).1
  have hvL : v ∈ L.vertexSet := L.vertex_mem_of_inc hv
  let C := reachableComponent L v
  have hC_comp : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 hvL
  have hC_path : IsPathGraph C := hL.2.2 C hC_comp
  have hHC_le : H ∩ C ≤ C := inter_le_right hHL (reachableComponent_le L v)
  have he_HC : e ∈ (H ∩ C).edgeSet := ⟨he, heL, v, hv, SimpleGraph.Reachable.refl v⟩
  obtain ⟨x, hx_HC, hx_deg⟩ := hC_path.2.2.2.2.2.2 (H ∩ C) hHC_le ⟨e, he_HC⟩
  refine ⟨x, hx_HC.1, ?_⟩
  rwa [incidentEdges_inter_reachableComponent_eq hHL hx_HC] at hx_deg

/-! ## 5. Two-degree-1 lemma and `same_component_of_deg_one_two_subgraph` -/

/-- If `e` has `2` ends in `H` and `a ∈ H.ends e`, there exists `u ∈ H.vertexSet` with `u ≠ a` and
`H.ends e = {a, u}`. -/
lemma exists_other_end_of_ncard_eq_two {H : Hypergraph α β} {e : β} {a : α}
    (h2 : (H.ends e).ncard = 2) (ha : H.Inc e a) :
    ∃ u ∈ H.vertexSet, u ≠ a ∧ H.ends e = {a, u} := by
  obtain ⟨x, y, hxy, heq⟩ := ncard_eq_two.mp h2
  have ha_mem : a ∈ ({x, y} : Set α) := by rwa [← heq]
  rcases ha_mem with rfl | rfl
  · have hy : y ∈ H.ends e := by rw [heq]; exact Or.inr rfl
    exact ⟨y, H.vertex_mem_of_inc hy, hxy.symm, heq⟩
  · have hx : x ∈ H.ends e := by rw [heq]; exact Or.inl rfl
    refine ⟨x, H.vertex_mem_of_inc hx, hxy, ?_⟩
    rw [heq, pair_comm]

/-- Deleting `{a}` from `H` when `incidentEdges H a = {e₀}` and `H.ends e₀ = {a, u}` removes
only `e₀` from `H.edgeSet`, and leaves `incidentEdges (H.deleteVertices {a}) z = incidentEdges H z`
for all `z ≠ a, u`. -/
lemma deleteVertices_singleton_deg_one_props {H : Hypergraph α β} {a u : α} {e₀ : β}
    (hinc_a : incidentEdges H a = {e₀}) (hends : H.ends e₀ = {a, u}) :
    (H.deleteVertices {a}).edgeSet = H.edgeSet \ {e₀} ∧
    (∀ z : α, z ≠ a → z ≠ u →
      incidentEdges (H.deleteVertices {a}) z = incidentEdges H z) ∧
    incidentEdges (H.deleteVertices {a}) u = incidentEdges H u \ {e₀} := by
  have he₀_mem : e₀ ∈ H.edgeSet := by
    have : e₀ ∈ incidentEdges H a := by rw [hinc_a]; exact rfl
    exact this.1
  have ha_e₀ : H.Inc e₀ a := by
    have : e₀ ∈ incidentEdges H a := by rw [hinc_a]; exact rfl
    exact this.2
  have hE : (H.deleteVertices {a}).edgeSet = H.edgeSet \ {e₀} := by
    ext e
    simp only [deleteVertices, mem_ofPred_eq, mem_singleton_iff, forall_eq, mem_sdiff]
    refine ⟨fun ⟨he, hna⟩ => ⟨he, fun h => hna (h ▸ ha_e₀)⟩, fun ⟨he, hne⟩ => ⟨he, fun ha => hne ?_⟩⟩
    have : e ∈ ({e₀} : Set β) := by rw [← hinc_a]; exact ⟨he, ha⟩
    exact this
  refine ⟨hE, ?_, ?_⟩
  · intro z hza hzu
    ext e
    simp only [incidentEdges, mem_ofPred_eq, deleteVertices, mem_singleton_iff, forall_eq]
    refine ⟨fun ⟨⟨he, _⟩, hinc, _⟩ => ⟨he, hinc⟩, fun ⟨he, hinc⟩ => ?_⟩
    have hna : ¬ H.Inc e a := by
      intro ha
      have he_eq : e = e₀ := by
        have : e ∈ ({e₀} : Set β) := by rw [← hinc_a]; exact ⟨he, ha⟩
        exact this
      subst he_eq
      have hz_mem : z ∈ ({a, u} : Set α) := by rw [← hends]; exact hinc
      rcases hz_mem with rfl | rfl
      · exact hza rfl
      · exact hzu rfl
    exact ⟨⟨he, hna⟩, hinc, hna⟩
  · ext e
    simp only [incidentEdges, mem_ofPred_eq, deleteVertices, mem_singleton_iff, forall_eq, mem_sdiff]
    constructor
    · rintro ⟨⟨he, hna⟩, hinc, _⟩
      exact ⟨⟨he, hinc⟩, fun h => hna (h ▸ ha_e₀)⟩
    · rintro ⟨⟨he, hinc⟩, hne⟩
      have hna : ¬ H.Inc e a := by
        intro ha
        apply hne
        have : e ∈ ({e₀} : Set β) := by rw [← hinc_a]; exact ⟨he, ha⟩
        exact this
      exact ⟨⟨he, hna⟩, hinc, hna⟩

/-- **Two-degree-1 lemma:** In any hypergraph `P` where every edge has `2` ends and every
edge-nonempty subhypergraph `H ≤ P` has a vertex of degree `1`, every edge-nonempty `H ≤ P`
actually has *two* distinct vertices of degree `1`. -/
lemma exists_two_deg_one_of_edgeSet_nonempty {P : Hypergraph α β}
    (hends : ∀ e ∈ P.edgeSet, (P.ends e).ncard = 2)
    (hdeg1 : ∀ H : Hypergraph α β, H ≤ P → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1) :
    ∀ H : Hypergraph α β, H ≤ P → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, ∃ y ∈ H.vertexSet,
        x ≠ y ∧ (incidentEdges H x).ncard = 1 ∧ (incidentEdges H y).ncard = 1 := by
  intro H₀ hH₀P hH₀_ne
  suffices ∀ n : ℕ, ∀ H : Hypergraph α β, H ≤ P → H.edgeSet.ncard = n → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, ∃ y ∈ H.vertexSet,
        x ≠ y ∧ (incidentEdges H x).ncard = 1 ∧ (incidentEdges H y).ncard = 1 from
    this H₀.edgeSet.ncard H₀ hH₀P rfl hH₀_ne
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro H hHP hn hne
    obtain ⟨a, haV, ha1⟩ := hdeg1 H hHP hne
    obtain ⟨e₀, he₀_eq⟩ := ncard_eq_one.mp ha1
    have he₀_mem : e₀ ∈ incidentEdges H a := by rw [he₀_eq]; exact rfl
    have he₀H : e₀ ∈ H.edgeSet := he₀_mem.1
    have ha_inc : H.Inc e₀ a := he₀_mem.2
    have h2 : (H.ends e₀).ncard = 2 := by
      rw [← hHP.ends_eq e₀ he₀H]
      exact hends e₀ (hHP.edgeSet_subset he₀H)
    obtain ⟨u, huV, hua, hends_e₀⟩ := exists_other_end_of_ncard_eq_two h2 ha_inc
    have hu_inc : H.Inc e₀ u := by
      change u ∈ H.ends e₀
      rw [hends_e₀]; exact Or.inr rfl
    let H' := H.deleteVertices {a}
    have hH'H : H' ≤ H := GM10.deleteVertices_le H {a}
    have hH'P : H' ≤ P := hH'H.trans hHP
    obtain ⟨hE', hinc_other, hinc_u⟩ := deleteVertices_singleton_deg_one_props he₀_eq hends_e₀
    rcases eq_empty_or_nonempty H'.edgeSet with hemp | hne'
    · refine ⟨a, haV, u, huV, hua.symm, ha1, ?_⟩
      have hinc_u_emp : incidentEdges H' u = ∅ :=
        subset_empty_iff.mp (hemp ▸ fun _ h => h.1)
      have hsub : incidentEdges H u ⊆ {e₀} := by
        rw [← sdiff_eq_empty, ← hinc_u, hinc_u_emp]
      have hinc_u_eq : incidentEdges H u = {e₀} :=
        Subset.antisymm hsub (singleton_subset_iff.mpr ⟨he₀H, hu_inc⟩)
      rw [hinc_u_eq, ncard_singleton]
    · have hn' : H'.edgeSet.ncard < n := by
        rw [← hn, hE', ncard_sdiff (singleton_subset_iff.mpr he₀H) (finite_singleton e₀),
          ncard_singleton]
        have : 1 ≤ H.edgeSet.ncard := (ncard_pos H.edgeSet_finite).mpr hne
        omega
      obtain ⟨b₁, hb₁V, b₂, hb₂V, hb_ne, hb₁1, hb₂1⟩ :=
        ih H'.edgeSet.ncard hn' H' hH'P rfl hne'
      by_cases hb₁u : b₁ = u
      · have hb₂u : b₂ ≠ u := fun h => hb_ne (hb₁u.trans h.symm)
        have hb₂a : b₂ ≠ a := hb₂V.2
        refine ⟨a, haV, b₂, hb₂V.1, hb₂a.symm, ha1, ?_⟩
        rwa [← hinc_other b₂ hb₂a hb₂u]
      · have hb₁a : b₁ ≠ a := hb₁V.2
        refine ⟨a, haV, b₁, hb₁V.1, hb₁a.symm, ha1, ?_⟩
        rwa [← hinc_other b₁ hb₁a hb₁u]

/-- If `L` is a linkage, `H ≤ L`, and `u ≠ w` in `H.vertexSet` are the only vertices of `H` with
degree `1` in `H`, then `u` and `w` belong to the same component of `L` (`L.skeleton.Reachable u w`). -/
lemma same_component_of_deg_one_two_subgraph {G L H : Hypergraph α β}
    (hL : IsLinkage G L) (hHL : H ≤ L) {u w : α}
    (huH : u ∈ H.vertexSet) (hwH : w ∈ H.vertexSet) (huw : u ≠ w)
    (hu1 : (incidentEdges H u).ncard = 1)
    (honly : ∀ z ∈ H.vertexSet, (incidentEdges H z).ncard = 1 → z = u ∨ z = w) :
    L.skeleton.Reachable u w := by
  have huL : u ∈ L.vertexSet := hHL.vertexSet_subset huH
  let C := reachableComponent L u
  have hC_comp : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 huL
  have hC_path : IsPathGraph C := hL.2.2 C hC_comp
  have hHC_le : H ∩ C ≤ C := inter_le_right hHL (reachableComponent_le L u)
  have hu_HC : u ∈ (H ∩ C).vertexSet := ⟨huH, self_mem_reachableComponent huL⟩
  have hu_HC1 : (incidentEdges (H ∩ C) u).ncard = 1 := by
    rwa [incidentEdges_inter_reachableComponent_eq hHL hu_HC]
  have hHC_ne : (H ∩ C).edgeSet.Nonempty := by
    obtain ⟨e, he⟩ := ncard_eq_one.mp hu_HC1
    have : e ∈ incidentEdges (H ∩ C) u := by rw [he]; exact rfl
    exact ⟨e, this.1⟩
  obtain ⟨x₁, hx₁V, x₂, hx₂V, hx_ne, hx₁1, hx₂1⟩ :=
    exists_two_deg_one_of_edgeSet_nonempty hC_path.2.2.2.1 hC_path.2.2.2.2.2.2
      (H ∩ C) hHC_le hHC_ne
  rw [incidentEdges_inter_reachableComponent_eq hHL hx₁V] at hx₁1
  rw [incidentEdges_inter_reachableComponent_eq hHL hx₂V] at hx₂1
  have h1 := honly x₁ hx₁V.1 hx₁1
  have h2 := honly x₂ hx₂V.1 hx₂1
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · exact (hx_ne rfl).elim
  · exact hx₂V.2.2
  · exact hx₁V.2.2
  · exact (hx_ne rfl).elim

/-! ## 6. Terminal structure of path graphs and linkage patterns -/

/-- A vertex `a` with at most one neighbor `u` in `K` cannot be an internal vertex of a simple
walk (path) in `K`. -/
lemma not_mem_support_of_unique_neighbor {K : SimpleGraph α} {a u x y : α}
    (huniq : ∀ w, K.Adj a w → w = u) (W : K.Walk x y) (hnd : W.support.Nodup)
    (hax : a ≠ x) (hay : a ≠ y) : a ∉ W.support := by
  induction W with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    exact hax
  | @cons v₁ v₂ v₃ hadj₁ W₁ ih =>
    cases W₁ with
    | nil =>
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨hax, hay⟩
    | @cons _ c _ hadj₂ W₂ =>
      have hnd_tail : (SimpleGraph.Walk.cons hadj₂ W₂).support.Nodup :=
        (List.nodup_cons.mp hnd).2
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      have hv₁c : v₁ ≠ c := fun h => hnd.1 (by simp [h])
      have hav₂ : a ≠ v₂ := by
        rintro rfl
        have h1 : v₁ = u := huniq v₁ hadj₁.symm
        have h2 : c = u := huniq c hadj₂
        exact hv₁c (h1.trans h2.symm)
      have hrec := ih hnd_tail hav₂ hay
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hrec ⊢
      exact ⟨hax, hrec.1, hrec.2⟩

/-- In a graph `H`, if `e` is incident with distinct vertices `b` and `c`, then `e` is not incident
with any vertex `a` distinct from `b` and `c`. -/
lemma not_inc_of_inc_inc_ne {H : Hypergraph α β} (hH : H.IsGraph) {e : β} {a b c : α}
    (hb : H.Inc e b) (hc : H.Inc e c) (hbc : b ≠ c) (hab : a ≠ b) (hac : a ≠ c) :
    ¬ H.Inc e a := by
  intro ha
  have he : e ∈ H.edgeSet := H.edge_mem_of_inc hb
  have hle2 : (H.ends e).ncard ≤ 2 := (hH e he).2
  have hsub : ({a, b, c} : Set α) ⊆ H.ends e := by
    rintro z (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hc
  have h3 : ({a, b, c} : Set α).ncard = 3 := by
    rw [ncard_insert_of_notMem, ncard_pair hbc]
    simp [hab, hac]
  have hge3 : 3 ≤ (H.ends e).ncard := by
    rw [← h3]
    exact ncard_le_ncard hsub (H.vertexSet_finite.subset fun _ h => H.vertex_mem_of_inc h)
  omega

/-- Any walk in `H.skeleton` whose support avoids `a` lifts to `(H.deleteVertices {a}).skeleton`. -/
lemma reachable_deleteVertices_singleton_of_walk {H : Hypergraph α β} (hH : H.IsGraph)
    {a x y : α} (W : H.skeleton.Walk x y) (hna : a ∉ W.support) :
    (H.deleteVertices {a}).skeleton.Reachable x y := by
  induction W with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons b c d hadj W' ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hna
    have hab : a ≠ b := hna.1
    have hac : a ≠ c := fun h => hna.2 (h ▸ W'.start_mem_support)
    rcases hadj with ⟨hne, e, hb, hc⟩
    have hna_e : ¬ H.Inc e a := not_inc_of_inc_inc_ne hH hb hc hne hab hac
    have hadj' : (H.deleteVertices {a}).skeleton.Adj b c := by
      refine ⟨hne, e, ⟨hb, ?_⟩, ⟨hc, ?_⟩⟩ <;>
      · intro w hw
        rw [mem_singleton_iff] at hw
        exact hw ▸ hna_e
    exact hadj'.reachable.trans (ih hna.2)

/-- Deleting a degree-1 vertex `a` from a path graph `P` yields a path graph `P.deleteVertices {a}`. -/
lemma isPathGraph_deleteVertices_singleton_of_deg_one {P : Hypergraph α β}
    (hP : IsPathGraph P) {a u : α} {e₀ : β}
    (huV : u ∈ P.vertexSet) (hua : u ≠ a)
    (hinc_a : incidentEdges P a = {e₀}) (hends_e₀ : P.ends e₀ = {a, u}) :
    IsPathGraph (P.deleteVertices {a}) := by
  have hle : P.deleteVertices {a} ≤ P := GM10.deleteVertices_le P {a}
  have hne : (P.deleteVertices {a}).vertexSet.Nonempty := ⟨u, huV, hua⟩
  have huniq : ∀ w, P.skeleton.Adj a w → w = u := by
    rintro w ⟨hne_aw, e, ha_e, hw_e⟩
    have he_eq : e = e₀ := by
      have : e ∈ ({e₀} : Set β) := by
        rw [← hinc_a]
        exact ⟨P.edge_mem_of_inc ha_e, ha_e⟩
      exact this
    subst he_eq
    have hw_mem : w ∈ ({a, u} : Set α) := by rw [← hends_e₀]; exact hw_e
    rcases hw_mem with rfl | rfl
    · exact (hne_aw rfl).elim
    · rfl
  refine isPathGraph_of_le hP hle hne ?_
  intro x hx y hy
  classical
  obtain ⟨W⟩ := hP.2.2.1 x hx.1 y hy.1
  let Wp := W.toPath
  have hna : a ∉ Wp.1.support :=
    not_mem_support_of_unique_neighbor huniq Wp.1 Wp.2.support_nodup
      (Ne.symm hx.2) (Ne.symm hy.2)
  exact reachable_deleteVertices_singleton_of_walk hP.1 Wp.1 hna

/-- An edgeless path graph has a single vertex `a`, which is its unique terminal of degree `0`. -/
lemma isPathGraph_of_edgeSet_empty {P : Hypergraph α β} (hP : IsPathGraph P)
    (hemp : P.edgeSet = ∅) :
    ∃ a ∈ P.vertexSet, P.vertexSet = {a} ∧ terminals P = {a} ∧ (incidentEdges P a).ncard = 0 := by
  obtain ⟨a, ha⟩ := hP.2.1
  have hinc_emp : ∀ x, incidentEdges P x = ∅ := by
    intro x
    ext e
    simp only [incidentEdges, mem_ofPred_eq, hemp, mem_empty_iff_false, false_and]
  have hV : P.vertexSet = {a} := by
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr ha)
    intro x hx
    obtain ⟨W⟩ := hP.2.2.1 x hx a ha
    cases W with
    | nil => rfl
    | @cons _ b _ hadj _ =>
      rcases hadj with ⟨_, e, he, _⟩
      have : e ∈ (∅ : Set β) := hemp ▸ P.edge_mem_of_inc he
      exact this.elim
  have hterm : terminals P = {a} := by
    ext x
    simp only [terminals, IsTerminal, mem_ofPred_eq, hV, mem_singleton_iff,
      vertexDegree_eq_ncard_incidentEdges hP.2.2.2.1, hinc_emp x, ncard_empty]
    exact ⟨fun h => h.1, fun hx => ⟨hx, Nat.zero_le 1⟩⟩
  refine ⟨a, ha, hV, hterm, ?_⟩
  rw [hinc_emp a, ncard_empty]

/-- In a path graph `P` with `P.edgeSet.Nonempty`, every vertex `z ∈ P.vertexSet` has at least one
incident edge. -/
lemma isPathGraph_one_le_ncard_incidentEdges {P : Hypergraph α β} (hP : IsPathGraph P)
    (hne : P.edgeSet.Nonempty) {z : α} (hz : z ∈ P.vertexSet) :
    1 ≤ (incidentEdges P z).ncard := by
  rcases hne with ⟨e, he⟩
  obtain ⟨u, hu⟩ := (hP.1 e he).1
  have huV : u ∈ P.vertexSet := P.vertex_mem_of_inc hu
  have hinc_ne : (incidentEdges P z).Nonempty := by
    by_cases hzu : z = u
    · subst hzu
      exact ⟨e, he, hu⟩
    · obtain ⟨W⟩ := hP.2.2.1 z hz u huV
      cases W with
      | nil => exact (hzu rfl).elim
      | @cons _ b _ hadj _ =>
        rcases hadj with ⟨_, e', hz_e', _⟩
        exact ⟨e', P.edge_mem_of_inc hz_e', hz_e'⟩
  exact (ncard_pos (P.edgeSet_finite.subset fun _ h => h.1)).mpr hinc_ne

/-- **Structure of an edge-nonempty path graph:** `P` has exactly two distinct terminals `a ≠ b`,
each of degree `1`, and every other vertex of `P` has degree `2`. -/
lemma isPathGraph_of_edgeSet_nonempty {P : Hypergraph α β} (hP : IsPathGraph P)
    (hne : P.edgeSet.Nonempty) :
    ∃ a ∈ P.vertexSet, ∃ b ∈ P.vertexSet,
      a ≠ b ∧ terminals P = {a, b} ∧
      (incidentEdges P a).ncard = 1 ∧ (incidentEdges P b).ncard = 1 ∧
      ∀ z ∈ P.vertexSet, z ≠ a → z ≠ b → (incidentEdges P z).ncard = 2 := by
  suffices ∀ n : ℕ, ∀ Q : Hypergraph α β, IsPathGraph Q → Q.edgeSet.ncard = n → Q.edgeSet.Nonempty →
      ∃ a ∈ Q.vertexSet, ∃ b ∈ Q.vertexSet,
        a ≠ b ∧
        (incidentEdges Q a).ncard = 1 ∧ (incidentEdges Q b).ncard = 1 ∧
        ∀ z ∈ Q.vertexSet, z ≠ a → z ≠ b → (incidentEdges Q z).ncard = 2 by
    obtain ⟨a, ha, b, hb, hab, ha1, hb1, hother⟩ := this P.edgeSet.ncard P hP rfl hne
    refine ⟨a, ha, b, hb, hab, ?_, ha1, hb1, hother⟩
    ext z
    simp only [terminals, IsTerminal, mem_ofPred_eq,
      vertexDegree_eq_ncard_incidentEdges hP.2.2.2.1, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzV, hle1⟩
      by_contra! hne_ab
      have h2 := hother z hzV hne_ab.1 hne_ab.2
      omega
    · rintro (rfl | rfl)
      · exact ⟨ha, by omega⟩
      · exact ⟨hb, by omega⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Q hQ hn hQ_ne
    obtain ⟨a, haV, ha1⟩ := hQ.2.2.2.2.2.2 Q le_rfl hQ_ne
    obtain ⟨e₀, he₀_eq⟩ := ncard_eq_one.mp ha1
    have he₀_mem : e₀ ∈ incidentEdges Q a := by rw [he₀_eq]; exact rfl
    have he₀Q : e₀ ∈ Q.edgeSet := he₀_mem.1
    have ha_inc : Q.Inc e₀ a := he₀_mem.2
    obtain ⟨u, huV, hua, hends_e₀⟩ :=
      exists_other_end_of_ncard_eq_two (hQ.2.2.2.1 e₀ he₀Q) ha_inc
    have hu_inc : Q.Inc e₀ u := by
      change u ∈ Q.ends e₀
      rw [hends_e₀]; exact Or.inr rfl
    let Q' := Q.deleteVertices {a}
    have hQ'_path : IsPathGraph Q' :=
      isPathGraph_deleteVertices_singleton_of_deg_one hQ huV hua he₀_eq hends_e₀
    obtain ⟨hE', hinc_other, hinc_u⟩ := deleteVertices_singleton_deg_one_props he₀_eq hends_e₀
    have he₀_in_u : e₀ ∈ incidentEdges Q u := ⟨he₀Q, hu_inc⟩
    have hinc_u_fin : (incidentEdges Q u).Finite := Q.edgeSet_finite.subset fun _ h => h.1
    have hcard_u : (incidentEdges Q u).ncard = (incidentEdges Q' u).ncard + 1 := by
      rw [hinc_u, ncard_sdiff (singleton_subset_iff.mpr he₀_in_u) (finite_singleton e₀),
        ncard_singleton]
      have : 1 ≤ (incidentEdges Q u).ncard :=
        (ncard_pos hinc_u_fin).mpr ⟨e₀, he₀_in_u⟩
      omega
    rcases eq_empty_or_nonempty Q'.edgeSet with hemp | hne'
    · obtain ⟨u', _, hV', _, hu'0⟩ := isPathGraph_of_edgeSet_empty hQ'_path hemp
      have hu_in_Q' : u ∈ Q'.vertexSet := ⟨huV, hua⟩
      have hu_eq_u' : u = u' := by rwa [hV', mem_singleton_iff] at hu_in_Q'
      subst hu_eq_u'
      have hu1 : (incidentEdges Q u).ncard = 1 := by omega
      refine ⟨a, haV, u, huV, hua.symm, ha1, hu1, ?_⟩
      intro z hzV hza hzu
      have hz_Q' : z ∈ Q'.vertexSet := ⟨hzV, hza⟩
      rw [hV', mem_singleton_iff] at hz_Q'
      exact (hzu hz_Q').elim
    · have hn' : Q'.edgeSet.ncard < n := by
        rw [← hn, hE', ncard_sdiff (singleton_subset_iff.mpr he₀Q) (finite_singleton e₀),
          ncard_singleton]
        have : 1 ≤ Q.edgeSet.ncard := (ncard_pos Q.edgeSet_finite).mpr hQ_ne
        omega
      obtain ⟨b₁, hb₁V, b₂, hb₂V, hb_ne, hb₁1, hb₂1, hother'⟩ :=
        ih Q'.edgeSet.ncard hn' Q' hQ'_path rfl hne'
      have hu_in_Q' : u ∈ Q'.vertexSet := ⟨huV, hua⟩
      have hu_ge1 : 1 ≤ (incidentEdges Q' u).ncard :=
        isPathGraph_one_le_ncard_incidentEdges hQ'_path hne' hu_in_Q'
      have hu_le2 : (incidentEdges Q u).ncard ≤ 2 := hQ.2.2.2.2.2.1 u huV
      have hu_Q'1 : (incidentEdges Q' u).ncard = 1 := by omega
      have hu_Q2 : (incidentEdges Q u).ncard = 2 := by omega
      have hu_eq : u = b₁ ∨ u = b₂ := by
        by_contra! hne_u
        have h2 := hother' u hu_in_Q' hne_u.1 hne_u.2
        omega
      rcases hu_eq with rfl | rfl
      · have hb₂a : b₂ ≠ a := hb₂V.2
        have hb₂Q1 : (incidentEdges Q b₂).ncard = 1 := by
          rwa [← hinc_other b₂ hb₂a hb_ne.symm]
        refine ⟨a, haV, b₂, hb₂V.1, hb₂a.symm, ha1, hb₂Q1, ?_⟩
        intro z hzV hza hzb₂
        by_cases hzu : z = u
        · subst hzu; exact hu_Q2
        · rw [← hinc_other z hza hzu]
          exact hother' z ⟨hzV, hza⟩ hzu hzb₂
      · have hb₁a : b₁ ≠ a := hb₁V.2
        have hb₁Q1 : (incidentEdges Q b₁).ncard = 1 := by
          rwa [← hinc_other b₁ hb₁a hb_ne]
        refine ⟨a, haV, b₁, hb₁V.1, hb₁a.symm, ha1, hb₁Q1, ?_⟩
        intro z hzV hza hzb₁
        by_cases hzu : z = u
        · subst hzu; exact hu_Q2
        · rw [← hinc_other z hza hzu]
          exact hother' z ⟨hzV, hza⟩ hzb₁ hzu

/-- For any component `C` of a linkage `L`, `terminals L ∩ C.vertexSet = terminals C`. -/
lemma IsLinkage.terminals_inter_component_eq {G L C : Hypergraph α β}
    (hL : IsLinkage G L) (hC : IsComponentOf L C) :
    terminals L ∩ C.vertexSet = terminals C := by
  ext x
  simp only [terminals, IsTerminal, mem_inter_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨⟨_, hdeg⟩, hxC⟩
    refine ⟨hxC, ?_⟩
    rwa [vertexDegree_component_eq hL.2.1 hC hxC]
  · rintro ⟨hxC, hdeg⟩
    refine ⟨⟨hC.1.vertexSet_subset hxC, ?_⟩, hxC⟩
    rwa [← vertexDegree_component_eq hL.2.1 hC hxC]

/-- Every block `B ∈ linkagePattern L` of a linkage `L` is nonempty and has size `1` or `2`. -/
lemma IsLinkage.mem_linkagePattern_structure {G L : Hypergraph α β} (hL : IsLinkage G L)
    {B : Set α} (hB : B ∈ linkagePattern L) :
    (∃ a ∈ terminals L, B = {a} ∧ (incidentEdges L a).ncard = 0) ∨
    (∃ a ∈ terminals L, ∃ b ∈ terminals L, a ≠ b ∧ B = {a, b} ∧
      (incidentEdges L a).ncard = 1 ∧ (incidentEdges L b).ncard = 1) := by
  rcases hB with ⟨C, hC, rfl⟩
  have hC_path : IsPathGraph C := hL.2.2 C hC
  have hterm_eq : terminals L ∩ C.vertexSet = terminals C := hL.terminals_inter_component_eq hC
  rcases eq_empty_or_nonempty C.edgeSet with hemp | hne
  · obtain ⟨a, haC, _, htermC, ha0⟩ := isPathGraph_of_edgeSet_empty hC_path hemp
    left
    have ha_term : a ∈ terminals L := by
      have : a ∈ terminals L ∩ C.vertexSet := by rw [hterm_eq, htermC]; exact rfl
      exact this.1
    rw [incidentEdges_component_eq hL.2.1 hC haC] at ha0
    exact ⟨a, ha_term, hterm_eq.trans htermC, ha0⟩
  · obtain ⟨a, haC, b, hbC, hab, htermC, ha1, hb1, _⟩ :=
      isPathGraph_of_edgeSet_nonempty hC_path hne
    right
    have ha_term : a ∈ terminals L := by
      have : a ∈ terminals L ∩ C.vertexSet := by rw [hterm_eq, htermC]; exact Or.inl rfl
      exact this.1
    have hb_term : b ∈ terminals L := by
      have : b ∈ terminals L ∩ C.vertexSet := by rw [hterm_eq, htermC]; exact Or.inr rfl
      exact this.1
    rw [incidentEdges_component_eq hL.2.1 hC haC] at ha1
    rw [incidentEdges_component_eq hL.2.1 hC hbC] at hb1
    exact ⟨a, ha_term, b, hb_term, hab, hterm_eq.trans htermC, ha1, hb1⟩

/-- The set of terminals of a linkage `L` is the union of the blocks of `linkagePattern L`. -/
lemma IsLinkage.terminals_eq_sUnion_linkagePattern {G L : Hypergraph α β} (hL : IsLinkage G L) :
    terminals L = ⋃₀ linkagePattern L := by
  ext x
  simp only [mem_sUnion, linkagePattern, mem_ofPred_eq]
  constructor
  · intro hx
    have hxL : x ∈ L.vertexSet := hx.1
    let C := reachableComponent L x
    have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 hxL
    exact ⟨terminals L ∩ C.vertexSet, ⟨C, hC, rfl⟩, hx, self_mem_reachableComponent hxL⟩
  · rintro ⟨_, ⟨C, _, rfl⟩, hx, _⟩
    exact hx

/-- Two linkages with the same pattern have the same set of terminals. -/
lemma terminals_eq_of_linkagePattern_eq {G₁ L₁ G₂ L₂ : Hypergraph α β}
    (h₁ : IsLinkage G₁ L₁) (h₂ : IsLinkage G₂ L₂)
    (hpat : linkagePattern L₁ = linkagePattern L₂) :
    terminals L₁ = terminals L₂ := by
  rw [h₁.terminals_eq_sUnion_linkagePattern, h₂.terminals_eq_sUnion_linkagePattern, hpat]

/-- Distinct blocks of `linkagePattern L` are disjoint. -/
lemma IsLinkage.disjoint_of_mem_linkagePattern {G L : Hypergraph α β} (hL : IsLinkage G L)
    {B₁ B₂ : Set α} (h₁ : B₁ ∈ linkagePattern L) (h₂ : B₂ ∈ linkagePattern L) (hne : B₁ ≠ B₂) :
    Disjoint B₁ B₂ := by
  rcases h₁ with ⟨C₁, hC₁, rfl⟩
  rcases h₂ with ⟨C₂, hC₂, rfl⟩
  have hC_ne : C₁ ≠ C₂ := fun h => hne (h ▸ rfl)
  have hdisj := (disjoint_of_isComponentOf_ne hL.2.1 hC₁ hC₂ hC_ne).1
  exact Disjoint.mono inter_subset_right inter_subset_right hdisj

/-- For `x ∈ L.vertexSet`, `(incidentEdges L x).ncard = 0` if and only if `{x} ∈ linkagePattern L`.
-/
lemma IsLinkage.ncard_incidentEdges_eq_zero_iff {G L : Hypergraph α β} (hL : IsLinkage G L)
    {x : α} (hx : x ∈ L.vertexSet) :
    (incidentEdges L x).ncard = 0 ↔ {x} ∈ linkagePattern L := by
  let C := reachableComponent L x
  have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 hx
  have hC_path : IsPathGraph C := hL.2.2 C hC
  have hxC : x ∈ C.vertexSet := self_mem_reachableComponent hx
  constructor
  · intro h0
    have h0C : (incidentEdges C x).ncard = 0 := by
      rwa [incidentEdges_component_eq hL.2.1 hC hxC]
    have hemp : C.edgeSet = ∅ := by
      by_contra! hne
      have hge1 := isPathGraph_one_le_ncard_incidentEdges hC_path hne hxC
      omega
    obtain ⟨a, _, hVC, htermC, _⟩ := isPathGraph_of_edgeSet_empty hC_path hemp
    have hxa : x = a := by rwa [hVC, mem_singleton_iff] at hxC
    subst hxa
    refine ⟨C, hC, ?_⟩
    rw [hL.terminals_inter_component_eq hC, htermC]
  · intro hmem
    rcases hL.mem_linkagePattern_structure hmem with
      ⟨a, _, heq, ha0⟩ | ⟨a, _, b, _, hab, heq, _, _⟩
    · have hxa : x = a := by
        have : x ∈ ({a} : Set α) := by rw [← heq]; exact rfl
        exact this
      rwa [hxa]
    · exfalso
      have h1 : ({x} : Set α).ncard = 1 := ncard_singleton x
      have h2 : ({a, b} : Set α).ncard = 2 := ncard_pair hab
      rw [heq] at h1
      omega

/-- For `x ∈ terminals L`, `(incidentEdges L x).ncard = 1` if and only if `{x} ∉ linkagePattern L`.
-/
lemma IsLinkage.ncard_incidentEdges_eq_one_iff {G L : Hypergraph α β} (hL : IsLinkage G L)
    {x : α} (hx : x ∈ terminals L) :
    (incidentEdges L x).ncard = 1 ↔ {x} ∉ linkagePattern L := by
  have hxL : x ∈ L.vertexSet := hx.1
  have hle1 : (incidentEdges L x).ncard ≤ 1 := by
    have := hx.2
    rwa [hL.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl x] at this
  rw [← hL.ncard_incidentEdges_eq_zero_iff hxL]
  omega

/-- If `L₁` and `L₂` are linkages with `linkagePattern L₁ = linkagePattern L₂`, then every vertex
`x ∈ terminals L₁` has the same number of incident edges in `L₁` and `L₂`. -/
lemma ncard_incidentEdges_eq_of_linkagePattern_eq {G₁ L₁ G₂ L₂ : Hypergraph α β}
    (h₁ : IsLinkage G₁ L₁) (h₂ : IsLinkage G₂ L₂)
    (hpat : linkagePattern L₁ = linkagePattern L₂) {x : α} (hx : x ∈ terminals L₁) :
    (incidentEdges L₁ x).ncard = (incidentEdges L₂ x).ncard := by
  have hx₂ : x ∈ terminals L₂ := by rwa [← terminals_eq_of_linkagePattern_eq h₁ h₂ hpat]
  by_cases h0 : {x} ∈ linkagePattern L₁
  · have h0' : {x} ∈ linkagePattern L₂ := hpat ▸ h0
    rw [(h₁.ncard_incidentEdges_eq_zero_iff hx.1).mpr h0,
        (h₂.ncard_incidentEdges_eq_zero_iff hx₂.1).mpr h0']
  · have h0' : {x} ∉ linkagePattern L₂ := hpat ▸ h0
    rw [(h₁.ncard_incidentEdges_eq_one_iff hx).mpr h0,
        (h₂.ncard_incidentEdges_eq_one_iff hx₂).mpr h0']

/-- For `x ∈ L.vertexSet`, `x ∉ terminals L` if and only if `(incidentEdges L x).ncard = 2`. -/
lemma IsLinkage.notMem_terminals_iff {G L : Hypergraph α β} (hL : IsLinkage G L)
    {x : α} (hx : x ∈ L.vertexSet) :
    x ∉ terminals L ↔ (incidentEdges L x).ncard = 2 := by
  have hle2 : (incidentEdges L x).ncard ≤ 2 := hL.ncard_incidentEdges_le_two x
  simp only [terminals, IsTerminal, mem_ofPred_eq, hx, true_and,
    hL.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl x]
  omega

/-- Two distinct vertices `u ≠ w` in `terminals L` belong to the same component of `L`
(`L.skeleton.Reachable u w`) if and only if `{u, w} ∈ linkagePattern L`. -/
lemma IsLinkage.pair_mem_linkagePattern_iff {G L : Hypergraph α β} (hL : IsLinkage G L)
    {u w : α} (hu : u ∈ terminals L) (hw : w ∈ terminals L) (huw : u ≠ w) :
    {u, w} ∈ linkagePattern L ↔ L.skeleton.Reachable u w := by
  constructor
  · rintro ⟨C, hC, heq⟩
    have huC : u ∈ C.vertexSet := by
      have : u ∈ terminals L ∩ C.vertexSet := by rw [← heq]; exact Or.inl rfl
      exact this.2
    have hwC : w ∈ C.vertexSet := by
      have : w ∈ terminals L ∩ C.vertexSet := by rw [← heq]; exact Or.inr rfl
      exact this.2
    exact reachable_of_le hC.1 (hC.2.2.1 u huC w hwC)
  · intro hr
    let C := reachableComponent L u
    have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 hu.1
    have hC_path : IsPathGraph C := hL.2.2 C hC
    have huC : u ∈ C.vertexSet := self_mem_reachableComponent hu.1
    have hwC : w ∈ C.vertexSet := ⟨hw.1, hr⟩
    have hne : C.edgeSet.Nonempty := by
      by_contra! hemp
      obtain ⟨a, _, hVC, _, _⟩ := isPathGraph_of_edgeSet_empty hC_path hemp
      have h1 : u = a := by rwa [hVC, mem_singleton_iff] at huC
      have h2 : w = a := by rwa [hVC, mem_singleton_iff] at hwC
      exact huw (h1.trans h2.symm)
    obtain ⟨a, _, b, _, hab, htermC, _, _, _⟩ := isPathGraph_of_edgeSet_nonempty hC_path hne
    have hterm_eq : terminals L ∩ C.vertexSet = {a, b} :=
      (hL.terminals_inter_component_eq hC).trans htermC
    have hu_ab : u ∈ ({a, b} : Set α) := by rw [← hterm_eq]; exact ⟨hu, huC⟩
    have hw_ab : w ∈ ({a, b} : Set α) := by rw [← hterm_eq]; exact ⟨hw, hwC⟩
    have hpair_eq : ({u, w} : Set α) = {a, b} := by
      rcases hu_ab with h1 | h1 <;> rcases hw_ab with h2 | h2
      · exact (huw (h1.trans h2.symm)).elim
      · rw [h1, h2]
      · rw [h1, h2, pair_comm]
      · exact (huw (h1.trans h2.symm)).elim
    exact ⟨C, hC, hpair_eq.trans hterm_eq.symm⟩

end GM21
end GraphMinor
