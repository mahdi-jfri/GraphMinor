module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section3Dual
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks

/-!
# Separation between distinct components on a cuff

The minimum interval argument of Graph Minors VI (4.2), claim (2), uses
that distinct components cannot have alternating vertices on a cuff.
Their point sets are compact, connected, and disjoint, so cuff crossing
excludes alternation. We also show that a path starting in a component
stays in its point set, for the crossing-curve argument.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

private theorem support_in_component
    {α : Type u} {β : Type v} {G C : Graph α β} (hC : IsGraphComponent C G)
    {a b : α} (W : GraphWalk G a b) (ha : a ∈ Graph.vertexSet C) :
    ∀ x ∈ W.support, x ∈ Graph.vertexSet C := by
  induction W with
  | nil _ =>
    intro x hx
    exact (List.mem_singleton.mp hx) ▸ ha
  | cons hl r ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih ((hC.mem_iff_of_isLink hl).mp ha) x hx

private theorem edges_in_component
    {α : Type u} {β : Type v} {G C : Graph α β} (hC : IsGraphComponent C G)
    {a b : α} (W : GraphWalk G a b) (ha : a ∈ Graph.vertexSet C) :
    ∀ e ∈ W.edges, e ∈ Graph.edgeSet C := by
  induction W with
  | nil _ => intro e he; exact False.elim (List.not_mem_nil he)
  | cons hl r ih =>
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact ((hC.isLink_iff_of_mem ha).mpr hl).edge_mem
    · exact ih ((hC.mem_iff_of_isLink hl).mp ha) e he

/-- A path in a drawing starting in a component stays in that component's
point set. -/
theorem path_U_subset_compPointSet_of_start
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {H P : Drawing S} {C : Graph S (Set S)} (hC : IsGraphComponent C H.toGraph)
    {a b : S} (hP : IsSubpathOf H P a b) (ha : a ∈ Graph.vertexSet C) :
    P.U ⊆ compPointSet C := by
  obtain ⟨W, _, hV, hE⟩ := hP.2.2.1
  have hle : P.toGraph ≤ H.toGraph :=
    { vertexSet_mono := hP.1.1
      isLink_mono := fun _ _ _ hl => (hP.1.isLink_iff hl.1).mp hl }
  have hPV : P.V ⊆ Graph.vertexSet C := by
    intro x hx
    have hxW : x ∈ W.support := by rw [hV] at hx; exact hx
    apply support_in_component hC (W.mono hle) ha x
    simpa only [GraphWalk.support_mono] using hxW
  have hPE : P.E ⊆ Graph.edgeSet C := by
    intro e he
    have heW : e ∈ W.edges := by rw [hE] at he; exact he
    apply edges_in_component hC (W.mono hle) ha e
    simpa only [GraphWalk.edges_mono] using heW
  rw [P.U_eq, compPointSet_eq_closure_union H hC]
  exact union_subset_union hPV (iUnion₂_subset fun e he =>
    subset_iUnion₂_of_subset e (hPE he) Subset.rfl)

/-- Distinct components cannot have alternating pairs of vertices on a
cuff. This is the noncrossing constraint used in the minimum-size step
of Graph Minors VI (4.2), claim (2), page 126. -/
theorem not_crossesOn_of_distinct_components
    {H : Drawing ClosedCylinder}
    {K L : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph) (hL : IsGraphComponent L H.toGraph) (hne : K ≠ L)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    {a b c d : ClosedCylinder}
    (ha : a ∈ Graph.vertexSet K) (hb : b ∈ Graph.vertexSet K)
    (hc : c ∈ Graph.vertexSet L) (hd : d ∈ Graph.vertexSet L) :
    ¬ CrossesOn C a b c d := by
  intro hcross
  obtain ⟨x, hxK, hxL⟩ := cuffCrossing_closedCylinder hC
    (isClosed_compPointSet H hK).isCompact (isClosed_compPointSet H hL).isCompact
    (isConnected_compPointSet H hK) (isConnected_compPointSet H hL)
    (Or.inl ha) (Or.inl hb) (Or.inl hc) (Or.inl hd) hcross
  exact disjoint_left.mp (disjoint_compPointSet_of_ne H hK hL hne) hxK hxL

/-- If a distinct component has one vertex on an open cuff arc between
two vertices of the first component, all its vertices on that cuff lie
in the same arc. Otherwise the two pairs alternate. -/
theorem component_cuff_vertices_subset_arc_of_mem
    {H : Drawing ClosedCylinder}
    {K L : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph) (hL : IsGraphComponent L H.toGraph) (hne : K ≠ L)
    {C A : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    {a b x : ClosedCylinder} (hab : a ≠ b)
    (ha : a ∈ Graph.vertexSet K ∩ C) (hb : b ∈ Graph.vertexSet K ∩ C)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (hx : x ∈ Graph.vertexSet L ∩ A) : Graph.vertexSet L ∩ C ⊆ A := by
  have hdisj := hK.disjoint_vertexSet_of_ne hL hne
  have hAsub : A ⊆ C \ {a, b} := by
    obtain ⟨o, _, rfl⟩ := hA
    exact connectedComponentIn_subset _ o
  have hccx : connectedComponentIn (C \ {a, b}) x = A := by
    obtain ⟨o, _, rfl⟩ := hA
    exact (connectedComponentIn_eq hx.2).symm
  intro y hy
  by_contra hyA
  have hax : a ≠ x := hdisj.ne_of_mem ha.1 hx.1
  have hbx : b ≠ x := hdisj.ne_of_mem hb.1 hx.1
  have hay : a ≠ y := hdisj.ne_of_mem ha.1 hy.1
  have hby : b ≠ y := hdisj.ne_of_mem hb.1 hy.1
  have hxy : x ≠ y := fun he => hyA (he ▸ hx.2)
  have hyF : y ∈ C \ {a, b} := by
    refine ⟨hy.2, ?_⟩
    rintro (he | he)
    · exact hay he.symm
    · exact hby he.symm
  have hccne : connectedComponentIn (C \ {a, b}) x ≠
      connectedComponentIn (C \ {a, b}) y := by
    intro he
    apply hyA
    rw [← hccx, he]
    exact mem_connectedComponentIn hyF
  exact not_crossesOn_of_distinct_components hK hL hne hC ha.1 hb.1 hx.1 hy.1
    ⟨ha.2, (hAsub hx.2).1, hb.2, hy.2, hab, hxy, hax, hay, hbx, hby, hccne⟩

end GraphMinor.GM06
