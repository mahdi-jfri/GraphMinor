module

public import GraphMinor.Compute.Case3StepsSelectedCounts
public import GraphMinor.Compute.Case3StepsAttachmentBound
import GraphMinor.Compute.Case3StepsReadCoreEdgeProg

/-!
# The private contribution of a selected member

For the estimate in XIII (9.9), p. 106, a selected component member has a
private outside vertex. If its boundary has three vertices, it also has an
edge to that boundary. A selected core-edge member has an edge and boundary
size at most two. Together with the core boundary bound, these facts give
the paper's factor-four estimate for each member.
-/

public section

namespace GraphMinor.Compute

/-- A selected member containing a simple edge has at least one full
directed copy after routing. -/
theorem case3RoutedMember_numEdges_pos_of_adj (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (u v : Fin x.n) (hadj : (case3SelectedMember x Z i).graph.Adj u v) :
    0 < (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges := by
  classical
  have hbase := (case3SelectedMember x Z i).sub hadj
  have hbaseD := hbase
  rw [← hG, MultiDigraph.toSimpleGraph_adj] at hbaseD
  have hown := (case3PairOwner_adj_iff x Z u v hbase i).mp hadj
  have hown' := (case3PairOwner_adj_iff x Z v u hbase.symm i).mp hadj.symm
  rcases hbaseD.2 with hpos | hpos
  · have hp : 0 < (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult u v := by
      simpa only [case3RoutedMember, hown, ↓reduceIte] using hpos
    exact hp.trans_le (MultiDigraph.edgeMult_le_numEdges _ _ _)
  · have hp : 0 < (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).edgeMult v u := by
      simpa only [case3RoutedMember, hown', ↓reduceIte] using hpos
    exact hp.trans_le (MultiDigraph.edgeMult_le_numEdges _ _ _)

private theorem component_private_vertex (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (ha : case3GroupActive x Z (.inl u)) :
    0 < ((case3SelectedMember x Z ⟨.inl u, ha⟩).verts \ Z).card := by
  have hu := (case3GroupActive_inl_iff x Z u).mp ha
  apply Finset.card_pos.mpr
  refine ⟨u, Finset.mem_sdiff.mpr ⟨?_, hu.1⟩⟩
  exact (case3SelectedMember_mem_outside_iff x Z ⟨.inl u, ha⟩ u hu.1).mpr hu.2

private theorem component_edge_of_boundary_nonempty (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n)) (u : Fin x.n)
    (ha : case3GroupActive x Z (.inl u)) (hbd : (case3GroupBoundary x Z (.inl u)).Nonempty) :
    0 < (case3RoutedMember x D Z (case3RawIndexLabel x (.inl u))).numEdges := by
  classical
  have hu := (case3GroupActive_inl_iff x Z u).mp ha
  have hboundary : case3GroupBoundary x Z (.inl u) = attachOf x Z u :=
    case3AttachmentRowSet_eq_attachOf x Z u hu.1
  obtain ⟨z, hz⟩ := hbd
  rw [hboundary] at hz
  obtain ⟨_, w, hw, hwz⟩ := Finset.mem_filter.mp hz
  have hwout : w ∉ Z := by
    intro hwZ
    exact Finset.disjoint_left.mp (isComponentOutsideCore_compOutside x Z hu.1).disjoint_Z hw hwZ
  have hwA : w ∈ outsideOfBoundary x Z (case3GroupBoundary x Z (.inl u)) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwout⟩,
      (attachOf_eq_of_mem_compOutside hw).trans hboundary.symm⟩
  have hadj : (case3SelectedMember x Z ⟨.inl u, ha⟩).graph.Adj w z :=
    ⟨hwz, Or.inl (Or.inl hwA)⟩
  exact case3RoutedMember_numEdges_pos_of_adj x D hG Z ⟨.inl u, ha⟩ w z hadj

/-- Graph Minors XIII, (9.9), p. 106: each selected member's edge-and-vertex
size is at most four times its private outside vertices plus its edges. -/
theorem case3SelectedMember_size_le_four_private (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z) :
    (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges +
        (case3SelectedMember x d.core.Z i).verts.card + 1 ≤
      4 * (((case3SelectedMember x d.core.Z i).verts \ d.core.Z).card +
        (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges) := by
  classical
  have hcard := case3SelectedMember_card_eq_outside_add_boundary x d.core.Z i
  have hbd := case3GroupBoundary_card_le_three x d hd i.1
  rcases i with ⟨i, hi⟩
  dsimp only [Subtype.coe_mk] at hcard hbd ⊢
  cases i with
  | inl u =>
    have hout := component_private_vertex x d.core.Z u hi
    by_cases hb : (case3GroupBoundary x d.core.Z (.inl u)).card ≤ 2
    · omega
    · have hbpos : 0 < (case3GroupBoundary x d.core.Z (.inl u)).card := by omega
      have hedge := component_edge_of_boundary_nonempty x D hG d.core.Z u hi (Finset.card_pos.mp hbpos)
      omega
  | inr j =>
    let e := (case3InputEdges x)[j.1]
    have hecore := (case3GroupActive_inr_iff x d.core.Z j).mp hi
    have hadj := (case3InputEdges_get_spec x j).2
    have hpair : (case3GroupBoundary x d.core.Z (.inr j)).card ≤ 2 := by
      change ({e.1, e.2} : Finset (Fin x.n)).card ≤ 2
      have h := Finset.card_insert_le e.1 ({e.2} : Finset (Fin x.n))
      simpa only [Finset.card_singleton] using h
    have hmemedge : (case3SelectedMember x d.core.Z ⟨.inr j, hi⟩).graph.Adj e.1 e.2 :=
      (case3SelectedMember_adj_core_iff x d.core.Z ⟨.inr j, hi⟩ e.1 e.2 hecore.1.1 hecore.1.2 hadj).mpr rfl
    have hedge := case3RoutedMember_numEdges_pos_of_adj x D hG d.core.Z ⟨.inr j, hi⟩ e.1 e.2 hmemedge
    dsimp only [Subtype.coe_mk] at hedge
    omega

end GraphMinor.Compute
