module

public import GraphMinor.GM01.RootedForkAssembly
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM13.Section7WallModel

/-!
# Constructing the fork root piece from two attachment paths

In Graph Minors I, (4.1), page 55, the root piece is an initial connected
part together with the bypass and a boundary attachment. Stop each path
before its final vertex in the corresponding arm support. Its remaining
prefix avoids that support and the other arm. The two prefixes meet the
initial piece, so their union with it is connected and contains the
ambient root. Their last edges supply the two joining edges of the fork.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

private theorem prefix_disjoint_of_intersection {α β : Type*} {P Q : Graph α β}
    {K : Set α} {b : α} (hQP : Q ≤ P) (hNot : b ∉ V(Q))
    (hMeet : V(P) ∩ K = {b}) : Disjoint V(Q) K := by
  apply Set.disjoint_left.mpr
  intro x hx hxK
  have heq : x = b := mem_singleton_iff.mp (hMeet ▸ ⟨hQP.vertexSet_mono hx, hxK⟩)
  exact hNot (heq ▸ hx)

/-- Construct the actual root piece and the two joining edges by removing
the last edge of each attachment path. This discharges the contraction
operation of GM01 (4.1) once its two arms and paths have been built. -/
noncomputable def rootedForkModelOfAttachmentPaths {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (G : RootedGraph α β)
    (C : Set α) (hCsub : C ⊆ V(G.graph)) (hCconn : GraphConnected (G.graph.induce C))
    (hroot : G.root.val ∈ C) {GP GB : RootedGraph α β}
    (hGP : GP.graph ≤ G.graph) (hGB : GB.graph ≤ G.graph)
    (MP : RootedMinorModel (rootedPathComb (γ - 1) (δ - 1) (by omega)) GP)
    (MB : RootedMinorModel (binaryRootedTree (γ - 1)) GB)
    (hCP : Disjoint C V(GP.graph)) (hCB : Disjoint C V(GB.graph))
    (hPB : Disjoint V(GP.graph) V(GB.graph))
    {P B : Graph α β} {a b : α} (ha : a ∈ C) (hb : b ∈ C)
    (hP : IsGraphPathWithEnds G.graph P a GP.root.val)
    (hB : IsGraphPathWithEnds G.graph B b GB.root.val)
    (hMeetP : V(P) ∩ V(GP.graph) = {GP.root.val})
    (hMeetB : V(B) ∩ V(GB.graph) = {GB.root.val})
    (hPavoidB : Disjoint V(P) V(GB.graph)) (hBavoidP : Disjoint V(B) V(GP.graph)) :
    RootedMinorModel (rootedForkGraph γ δ hγ hδ) G := by
  have haNe : a ≠ GP.root.val := by
    intro heq
    exact Set.disjoint_left.mp hCP ha (heq.symm ▸ GP.root.property)
  have hbNe : b ≠ GB.root.val := by
    intro heq
    exact Set.disjoint_left.mp hCB hb (heq.symm ▸ GB.root.property)
  have hexP := hP.exists_last_edge haNe
  have hexB := hB.exists_last_edge hbNe
  let ep := hexP.choose
  let qp := hexP.choose_spec.choose
  let Qp := hexP.choose_spec.choose_spec.choose
  have hpLink := hexP.choose_spec.choose_spec.choose_spec.1
  have hpSub := hexP.choose_spec.choose_spec.choose_spec.2.1
  have hpPath := hexP.choose_spec.choose_spec.choose_spec.2.2.1
  have hpNot := hexP.choose_spec.choose_spec.choose_spec.2.2.2.1
  let eb := hexB.choose
  let qb := hexB.choose_spec.choose
  let Qb := hexB.choose_spec.choose_spec.choose
  have hbLink := hexB.choose_spec.choose_spec.choose_spec.1
  have hbSub := hexB.choose_spec.choose_spec.choose_spec.2.1
  have hbPath := hexB.choose_spec.choose_spec.choose_spec.2.2.1
  have hbNot := hexB.choose_spec.choose_spec.choose_spec.2.2.2.1
  have hQpP : Disjoint V(Qp) V(GP.graph) := prefix_disjoint_of_intersection hpSub hpNot hMeetP
  have hQbB : Disjoint V(Qb) V(GB.graph) := prefix_disjoint_of_intersection hbSub hbNot hMeetB
  have hQpB : Disjoint V(Qp) V(GB.graph) := hPavoidB.mono_left hpSub.vertexSet_mono
  have hQbP : Disjoint V(Qb) V(GP.graph) := hBavoidP.mono_left hbSub.vertexSet_mono
  have hQpConn := graphConnected_induce_of_subgraph hpPath.le (graphConnected_of_isGraphPath hpPath)
  have hQbConn := graphConnected_induce_of_subgraph hbPath.le (graphConnected_of_isGraphPath hbPath)
  have hFirstConn := graphConnected_induce_union hCconn hQpConn ⟨a, ha, hpPath.left_mem⟩
  have hAllConn := graphConnected_induce_union hFirstConn hQbConn ⟨b, Or.inl hb, hbPath.left_mem⟩
  let C' := C ∪ V(Qp) ∪ V(Qb)
  have hC'sub : C' ⊆ V(G.graph) :=
    union_subset (union_subset hCsub hpPath.le.vertexSet_mono) hbPath.le.vertexSet_mono
  have hC'P : Disjoint C' V(GP.graph) := (hCP.union_left hQpP).union_left hQbP
  have hC'B : Disjoint C' V(GB.graph) := (hCB.union_left hQpB).union_left hQbB
  exact rootedForkModelOfArms hγ hδ G C' hC'sub hAllConn (Or.inl (Or.inl hroot))
    hGP hGB MP MB hC'P hC'B hPB
    ⟨ep, qp, Or.inl (Or.inr hpPath.right_mem), hpLink.mono hP.le⟩
    ⟨eb, qb, Or.inr hbPath.right_mem, hbLink.mono hB.le⟩

end GraphMinor.GM01
