module

public import GraphMinor.GM05.SeriesParallelDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM05.ShadowMinor
import GraphMinor.GM05.ConnectedBags
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Subtrees of bags meeting connected subgraphs

Graph Minors V, proof of (8.8), page 111, assigns to a connected expansion
the tree vertices whose bags meet it. The running-intersection condition
makes this a nonempty connected vertex set. Disjoint such subtrees imply
disjoint subgraphs. The union of `r` bags of size at most `w+1` has size
at most `r*(w+1)`.
-/

public section

namespace GraphMinor.GM05

open Graph SimpleGraph Set

/-- The set `T(A)` in Graph Minors V, proof of (8.8), page 111: the tree
vertices whose bags meet the subgraph. -/
@[expose] def bagMeetingSet {α β ι : Type*} (χ : ι → Set α) (C : Graph α β) : Set ι :=
  {t | (χ t∩V(C)).Nonempty}

/-- The bags meeting a connected subgraph form a nonempty subtree. -/
theorem bagMeetingSet_connected {α β ι : Type*} [Fintype ι]
    {G C : Graph α β} {T : SimpleGraph ι} {χ : ι → Set α}
    (htd : IsTreeDecomposition (simpleShadow G) T χ) (hCG : C≤G)
    (hC : GraphConnected C) : (T.induce (bagMeetingSet χ C)).Connected := by
  have hcover : (⋃ t,χ t)=V(G) := htd.iUnion_eq
  obtain ⟨x,hx⟩ := hC.1
  have hxG := hCG.vertexSet_mono hx
  rw [←hcover] at hxG
  obtain ⟨t,ht⟩ := mem_iUnion.mp hxG
  let S := bagMeetingSet χ C
  let : Nonempty S := ⟨⟨t,x,ht,hx⟩⟩
  refine ⟨?_⟩
  intro a b
  obtain ⟨p,hp⟩ := htd.isTree.connected.exists_isPath a.1 b.1
  have hmem : ∀ c∈p.support,c∈S := by
    intro c hc
    exact htd.meets_connected_on_path (simpleShadow_mono hCG)
      ((graphConnected_iff_simpleShadow_connected C).mp hC)
      ((GM10.onTreePath_iff_of_isPath htd.isTree hp).mpr hc) a.2 b.2
  exact ⟨p.induce S hmem⟩

/-- Disjoint meeting subtrees imply disjoint vertex sets of subgraphs. -/
theorem disjoint_vertices_of_disjoint_bagMeetingSet {α β ι : Type*} [Fintype ι]
    {G C D : Graph α β} {T : SimpleGraph ι} {χ : ι → Set α}
    (htd : IsTreeDecomposition (simpleShadow G) T χ) (hCG : C≤G)
    (hCD : Disjoint (bagMeetingSet χ C) (bagMeetingSet χ D)) : Disjoint V(C) V(D) := by
  rw [Set.disjoint_left]
  intro x hxC hxD
  have hcover : (⋃ t,χ t)=V(G) := htd.iUnion_eq
  have hxG := hCG.vertexSet_mono hxC
  rw [←hcover] at hxG
  obtain ⟨t,ht⟩ := mem_iUnion.mp hxG
  exact Set.disjoint_left.mp hCD ⟨x,ht,hxC⟩ ⟨x,ht,hxD⟩

/-- A union of bags stays in the graph and has size bounded by the number
of chosen tree vertices times the maximum bag size. -/
theorem union_bags_bound {α β ι : Type*} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {χ : ι → Set α}
    (htd : IsTreeDecomposition (simpleShadow G) T χ) {w : ℕ}
    (hwidth : WidthLE χ w) (Y : Set ι) :
    (⋃ t∈Y,χ t)⊆V(G) ∧ (⋃ t∈Y,χ t).ncard≤Y.ncard*(w+1) := by
  classical
  have hcover : (⋃ t,χ t)=V(G) := htd.iUnion_eq
  constructor
  · intro x hx
    obtain ⟨t,htY,hxt⟩ := mem_iUnion₂.mp hx
    rw [←hcover]
    exact mem_iUnion.mpr ⟨t,hxt⟩
  · have he : (⋃ t∈Y,χ t)=⋃ t∈Y.toFinset,χ t := by ext x; simp
    rw [he]
    calc
      _≤∑ t∈Y.toFinset,(χ t).ncard := Finset.set_ncard_biUnion_le _ _
      _≤∑ t∈Y.toFinset,(w+1) := Finset.sum_le_sum (fun t _ ↦ hwidth t)
      _=Y.ncard*(w+1) := by
        simp only [Finset.sum_const,smul_eq_mul]
        rw [←ncard_eq_toFinset_card' Y]

end GraphMinor.GM05
