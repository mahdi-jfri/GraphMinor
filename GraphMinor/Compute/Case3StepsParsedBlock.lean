module

public import GraphMinor.Compute.Case3StepsRecordListBounds
public import GraphMinor.Compute.Case3StepsRecordVertices
public import GraphMinor.Compute.Case3StepsScanCostBounds
import GraphMinor.Compute.Case3StepsMultigraphComponents

/-!
# The completed block passes the frozen parser

The full compass lists lie in the deleted graph. Every member record lies
in those lists and satisfies the tree checks. Distinct candidates give
distinct record vertex sets, and their directed-copy counts sum to at
most the compass count. These facts establish every finite check performed
by the case (iii) parser.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The computed lists and permitted member codes form a complete parsed
block. Only the finite format checks occur in this certificate. -/
theorem case3SelectedBlock_parses {N B : ℕ} (G : MultiDigraph N) (X : Finset (Fin N))
    (wallSec : ParsedWallSection (G.deleteVertices X) X)
    (x : Alg81Input) (D : MultiDigraph x.n) (hG : D.toSimpleGraph = x.G)
    (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (e : Fin x.n ↪ Fin N)
    (hbase : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ delGraph G X)
    (hcount : D.numEdges ≤ (G.deleteVertices X).numEdges)
    (hcorners : ∀ i : Fin 4, ∃ u : Fin x.n,
      (e u).1 = (wallSec.W.branchVert (elemWallCornerIdx wallSec.h2 i)).1)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hn : (entries.map Prod.fst).Nodup)
    (hcodes : ∀ p ∈ entries, IsValidBranchDecompCode B (case3CompactMember x D Z p.1) p.2 ∨
      p.2 = case3PlaceholderCode (case3CompactMember x D Z p.1).numEdges) :
    ∃ p : ParsedCase3Block (G.deleteVertices X) X,
      p.wallSec = wallSec ∧
      p.K_vList = List.ofFn (fun u : Fin x.n => (e u).1) ∧
      p.K_eList = D.multiEdgeTriples.map (origEdgeEmb e e.injective) ∧
      p.corners = List.ofFn (fun i : Fin 4 =>
        (wallSec.W.branchVert (elemWallCornerIdx wallSec.h2 i)).1) ∧
      p.members = case3SelectedRecordList x D Z e entries ∧
      parseCase3Block (G.deleteVertices X) X
        (encCase3Block wallSec.W p.K_vList p.K_eList p.corners p.members) = some p := by
  classical
  let Kv := List.ofFn (fun u : Fin x.n => (e u).1)
  let Ke := D.multiEdgeTriples.map (origEdgeEmb e e.injective)
  let corners := List.ofFn (fun i : Fin 4 =>
    (wallSec.W.branchVert (elemWallCornerIdx wallSec.h2 i)).1)
  let members := case3SelectedRecordList x D Z e entries
  have hnN : x.n ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hKvvalid : ∀ v ∈ Kv, isDelGraphVert N X v = true := by
    intro v hv
    obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hv
    apply isDelGraphVert_eq_true_iff.mpr
    apply hbase.vertexSet_mono
    exact ⟨u.1, u.2, origVertexEmb_apply_val e e.injective u⟩
  have hKeends : ∀ a ∈ Ke, a.1 ∈ Kv ∧ a.2.1 ∈ Kv := by
    have hend := case3BranchRecord_endpoints D e e.injective []
    dsimp only at hend
    rw [case3BranchRecord_orig_vList D e e.injective []] at hend
    exact hend
  have hKevalid : ∀ a ∈ Ke, isDelGraphEdge (G.deleteVertices X) a = true ∧
      a.1 ∈ Kv ∧ a.2.1 ∈ Kv := by
    intro a ha
    refine ⟨isDelGraphEdge_eq_true_iff.mpr (hbase.edgeSet_mono ?_), hKeends a ha⟩
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact ⟨b, (D.mem_multiEdgeTriples_iff b).mp hb, rfl⟩
  have hmemberslen : members.length ≤ N + (G.deleteVertices X).numEdges + 1 := by
    have hcand := hn.length_le_card
    rw [List.length_map] at hcand
    have hgroup := case3SelectedGroups_card_le x Z
    have hsimple := (case3InputEdges_length_le x D hG).trans D.numActivePairs_le_numEdges
    change (entries.map _).length ≤ _
    rw [List.length_map]
    omega
  let p : ParsedCase3Block (G.deleteVertices X) X := {
    wallSec := wallSec
    K_vList := Kv
    K_eList := Ke
    corners := corners
    members := members
    hK_v_len := by simpa only [Kv, List.length_ofFn] using hnN
    hK_v_nodup := List.nodup_ofFn.mpr (fun a b h => e.injective (Fin.ext h))
    hK_v_valid := hKvvalid
    hK_e_len := by simpa only [Ke, List.length_map, D.length_multiEdgeTriples] using hcount
    hK_e_nodup := D.nodup_multiEdgeTriples.map (origEdgeEmb e e.injective).injective
    hK_e_valid := hKevalid
    hcorners_eq := rfl
    hcorners_mem := by
      intro c hc
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
      exact List.mem_ofFn.mpr (hcorners i)
    hmembers_len := hmemberslen
    hmembers_edge_sum := (case3SelectedRecordList_edge_sum_le x D hG Z hdiv e entries hn).trans hcount
    hmembers_valid := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact case3IsValidMemberRecord_mono_edges Kv Ke _
        (case3SelectedRecord_isValid x D hG Z hdiv e q.1 q.2 (hcodes q hq)) hcount
    hmembers_distinct := case3SelectedRecordList_distinct x D Z e entries hn }
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, parseCase3Block_encCase3Block p⟩

end GraphMinor.Compute
