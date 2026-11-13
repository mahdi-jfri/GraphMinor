module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ComponentSeparation
import GraphMinor.GM06.Section5NoReduction2
public import GraphMinor.GM06.Section3Induce

/-!
# Every retained component meets the linkage

An unused component can be discarded by Reduction 2. More precisely,
if a component contains no initial vertex, it contains no vertex of
any linkage path, since membership in a component is preserved along
a walk. The component separation then deletes it and keeps the
linkage. This is the connectivity consequence of Reduction 2 used in
the region argument for VI (5.1), page 129.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

private theorem walk_support_not_mem_component
    {α β : Type*} {G C : Graph α β} (hC : IsGraphComponent C G)
    {a b : α} (W : GraphWalk G a b) (ha : a ∉ Graph.vertexSet C) :
    ∀ x ∈ W.support, x ∉ Graph.vertexSet C := by
  induction W with
  | nil _ =>
    intro x hx
    exact (List.mem_singleton.mp hx) ▸ ha
  | cons hl R ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih (fun hb => ha ((hC.mem_iff_of_isLink hl).mpr hb)) x hx

/-- A subdrawing whose vertices lie in X is a subdrawing of the
full drawing induced on X. -/
theorem subdrawing_induce_of_vertices_subset
    {G P : Drawing ClosedCylinder} (hPG : P.IsSubdrawing G)
    {X : Set ClosedCylinder} (hX : X ⊆ G.V) (hPV : P.V ⊆ X) :
    P.IsSubdrawing (induceDrawing G X) := by
  constructor
  · rw [induceDrawing_V G hX]
    exact hPV
  · rw [induceDrawing_E]
    intro e he
    refine ⟨hPG.2 he, ?_⟩
    obtain ⟨a, b, hlP⟩ := P.toGraph.exists_isLink_of_mem_edgeSet he
    have hlG : G.toGraph.IsLink e a b := (hPG.isLink_iff he).mp hlP
    rw [hlG.2.2.2]
    rintro x (rfl | hx)
    · exact hPV hlP.left_mem
    · exact (mem_singleton_iff.mp hx) ▸ hPV hlP.right_mem

/-- Without Reduction 2, every component of G contains an initial
vertex of the linkage. This removes unused components in VI (5.1). -/
theorem component_contains_initial_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L)
    {K : Graph ClosedCylinder (Set ClosedCylinder)} (hK : IsGraphComponent K G.toGraph) :
    ∃ i : Fin k, cylinderM1Point k i ∈ Graph.vertexSet K := by
  by_contra hn
  have hmissing : ∀ i : Fin k, cylinderM1Point k i ∉ Graph.vertexSet K := by
    intro i hi
    exact hn ⟨i, hi⟩
  let X := G.V \ Graph.vertexSet K
  let G₁ := induceDrawing G X
  let G₂ := induceDrawing G (Graph.vertexSet K)
  have hV₁ : G₁.V = X := induceDrawing_V G sdiff_subset
  have hV₂ : G₂.V = Graph.vertexSet K := induceDrawing_V G hK.1.vertexSet_mono
  have hgraph₁ : G₁.toGraph = G.toGraph.induce X := induceDrawing_toGraph_eq_induce G sdiff_subset
  have hgraph₂ : G₂.toGraph = K := induceDrawing_toGraph_of_component G hK
  have hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph := by
    rw [hgraph₁, hgraph₂]
    exact isGraphSeparation_of_component hK
  have hpaths : ∀ i : Fin k, (L.pathDrawing i).IsSubdrawing G₁ := by
    intro i
    apply subdrawing_induce_of_vertices_subset (L.isSubdrawing i).1 sdiff_subset
    obtain ⟨W, _, hV, _⟩ := (L.isPath i).1
    have hle : (L.pathDrawing i).toGraph ≤ G.toGraph :=
      { vertexSet_mono := (L.isSubdrawing i).1.1
        isLink_mono := fun _ _ _ hl => ((L.isSubdrawing i).1.isLink_iff hl.1).mp hl }
    intro x hx
    refine ⟨(L.isSubdrawing i).1.1 hx, ?_⟩
    have hxW : x ∈ (W.mono hle).support := by
      rw [GraphWalk.support_mono]
      rw [hV] at hx
      exact hx
    exact walk_support_not_mem_component hK (W.mono hle) (hmissing i) x hxW
  obtain ⟨x, hx⟩ := hK.2.1.1
  have hne : G₁.toGraph ≠ G.toGraph := by
    intro heq
    have hveq : G₁.V = G.V := congrArg Graph.vertexSet heq
    have hx₁ : x ∈ G₁.V := hveq.symm ▸ hK.1.vertexSet_mono hx
    rw [hV₁] at hx₁
    exact hx₁.2 hx
  let i : Fin k := ⟨0, hG.1⟩
  have hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i} := by
    rw [hV₁, hV₂]
    rintro x ⟨hx₁, hx₂⟩
    exact False.elim (hx₁.2 hx₂)
  exact hno (reduction2_applies_of_linkage_separation L hG i hsep hoverlap hne hpaths)

end GraphMinor.GM06
