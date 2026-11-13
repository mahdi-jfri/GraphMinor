module

public import GraphMinor.Compute.Case3Block
public import GraphMinor.Compute.Bridge3
public import GraphMinor.Compute.Algorithm99TransportRural
import Mathlib.Data.List.GetD

/-!
# Turning a member branch code into a member record

The edge list expands each directed parallel class in its numbered order.
The leaf list keeps that order when the endpoints are renamed. The tree is
copied from the supplied code, with a one-vertex placeholder for the
at-most-one-edge convention. These are the record data required in XIII
(9.9), steps 6 and 7, pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The member record obtained from a branch code by renaming vertex and
edge labels. Parent and leaf lists retain the code's order. -/
def case3BranchRecord {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) : Case3MemberRecord where
  vList := (List.finRange n).map (fun v => f v.1)
  eList := G.multiEdgeTriples.map g
  t_len := max (bdNumTreeVerts code) 1
  parList := List.ofFn (fun z : Fin (max (bdNumTreeVerts code) 1) =>
    if z.1 < bdNumTreeVerts code then bdParent code z.1 else 0)
  tauList := List.ofFn (fun e : Fin G.numEdges => code.getD (2 + bdNumTreeVerts code + e.1) 0)

/-- The copied parent and leaf lists have precisely the record lengths. -/
theorem case3BranchRecord_lengths {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) :
    (case3BranchRecord G f g code).parList.length = (case3BranchRecord G f g code).t_len ∧
      (case3BranchRecord G f g code).tauList.length = (case3BranchRecord G f g code).eList.length := by
  simp only [case3BranchRecord, List.length_ofFn, List.length_map, G.length_multiEdgeTriples, and_self]

/-- Each expanded parallel copy appears once in the member record. -/
theorem case3BranchRecord_edges_nodup {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) :
    (case3BranchRecord G f g code).eList.Nodup :=
  G.nodup_multiEdgeTriples.map g.injective

/-- The original edge index is unchanged when the record renames its edge triple. -/
theorem case3BranchRecord_edge_idx {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) (e : Fin G.numEdges) :
    (case3BranchRecord G f g code).eList.idxOf (g (G.multiEdgeEquiv e).1) = e.1 := by
  have he : (case3BranchRecord G f g code).eList[e.1]'(by
      simp only [case3BranchRecord, List.length_map, G.length_multiEdgeTriples]; exact e.2) =
      g (G.multiEdgeEquiv e).1 := by
    simp only [case3BranchRecord, List.getElem_map, MultiDigraph.multiEdgeEquiv_apply,
      MultiDigraph.multiEdgeToGMTriple]
  rw [← he]
  exact (case3BranchRecord_edges_nodup G f g code).idxOf_getElem _ _

/-- A nontrivial code gives the same parent tree in the member record. -/
theorem case3BranchRecord_parent {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (ht : 0 < bdNumTreeVerts code) (z : ℕ) (hz : z < bdNumTreeVerts code) :
    (case3BranchRecord G f g code).parList.getD z 0 = bdParent code z := by
  have hmax : max (bdNumTreeVerts code) 1 = bdNumTreeVerts code := Nat.max_eq_left ht
  simp only [case3BranchRecord, hmax]
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_ofFn]; exact hz), List.getElem_ofFn]
  exact ite_eq_left hz

/-- Reading a copied leaf word at its expanded edge index recovers the code word. -/
theorem case3BranchRecord_tau_word {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) (e : Fin G.numEdges) :
    (case3BranchRecord G f g code).tauList.getD e.1 0 =
      code.getD (2 + bdNumTreeVerts code + e.1) 0 := by
  simp only [case3BranchRecord]
  rw [List.getD_eq_getElem _ 0 (by rw [List.length_ofFn]; exact e.2), List.getElem_ofFn]

/-- A missing edge name reads the zero default of the leaf list. -/
theorem case3BranchRecord_tau_missing {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ) (e : ℕ × ℕ × ℕ)
    (he : e ∉ G.toGMDigraph.edgeSet) :
    (case3BranchRecord G f g code).tauList.getD
      ((case3BranchRecord G f g code).eList.idxOf (g e)) 0 = 0 := by
  have hnot : g e ∉ (case3BranchRecord G f g code).eList := by
    intro h
    obtain ⟨a, ha, hae⟩ := List.mem_map.mp h
    exact he (g.injective hae ▸ (G.mem_multiEdgeTriples_iff a).mp ha)
  rw [List.idxOf_eq_length hnot, List.getD_eq_default _ _ (by
    rw [← (case3BranchRecord_lengths G f g code).2])]

private theorem record_decode (r : Case3MemberRecord) (t : ℕ) (ht : 0 < t)
    (hrt : r.t_len = t) :
    r.toBranchDecomp = ⟨t, parentTree t (fun z => r.parList.getD z 0),
      fun e => let u := r.tauList.getD (r.eList.idxOf e) 0
        if hu : u < t then ⟨u, hu⟩ else ⟨0, ht⟩⟩ := by
  have hm : max r.t_len 1 = t := by rw [hrt]; exact Nat.max_eq_left ht
  unfold Case3MemberRecord.toBranchDecomp
  generalize_proofs hp
  revert hp
  rw [hm]
  intro _
  rfl

/-- For a code with at least two graph edges, the record decodes to a
branch-decomposition of the renamed graph, with the same width bound. -/
theorem case3BranchRecord_branchDecomp {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hge : 2 ≤ G.numEdges) :
    let r := case3BranchRecord G f g code
    let bd := r.toBranchDecomp
    GM13.IsGraphBranchDecomposition (relabelGraph f g G.toGMDigraph.toGraph) bd.2.1 bd.2.2 ∧
      GM13.graphBranchDecompWidth (relabelGraph f g G.toGMDigraph.toGraph) bd.2.1 bd.2.2 ≤ B := by
  classical
  obtain ⟨ht, hbd, hwidth⟩ := hcode.isGraphBranchDecomposition_and_width_le hge
  have hmax : max (bdNumTreeVerts code) 1 = bdNumTreeVerts code := Nat.max_eq_left ht
  let r := case3BranchRecord G f g code
  let p (z : ℕ) := r.parList.getD z 0
  let tau (e : ℕ × ℕ × ℕ) : Fin (bdNumTreeVerts code) :=
    let u := r.tauList.getD (r.eList.idxOf e) 0
    if hu : u < bdNumTreeVerts code then ⟨u, hu⟩ else ⟨0, ht⟩
  have htree : parentTree (bdNumTreeVerts code) p = bdTree code := by
    ext u v
    change (u ≠ v ∧ ((0 < u.1 ∧ v.1 = p u.1) ∨ (0 < v.1 ∧ u.1 = p v.1))) ↔ _
    dsimp only [p, r]
    rw [case3BranchRecord_parent G f g code ht u.1 u.2,
      case3BranchRecord_parent G f g code ht v.1 v.2]
    rfl
  have htau : ∀ e, tau (g e) = bdTauGM G code ht e := by
    intro e
    by_cases he : e ∈ G.toGMDigraph.edgeSet
    · let j := G.multiEdgeEquiv.symm ⟨e, he⟩
      have hj : (G.multiEdgeEquiv j).1 = e := congrArg Subtype.val (G.multiEdgeEquiv.apply_symm_apply ⟨e, he⟩)
      rw [← hj]
      dsimp only [tau, r]
      rw [case3BranchRecord_edge_idx G f g code j, case3BranchRecord_tau_word G f g code j]
      exact (tauToGM_apply_equiv (D := G.toMultiComputeDigraph) G.multiEdgeEquiv ht (bdTau G code ht) j).symm
    · have hm := case3BranchRecord_tau_missing G f g code e he
      apply Fin.ext
      simp only [tau, r, hm, ht, ↓reduceDIte, bdTauGM, multiTauGM, tauToGM, he]
  have hb := (isGraphBranchDecomposition_relabelGraph_iff f g htau).mpr hbd
  have hw : GM13.graphBranchDecompWidth (relabelGraph f g G.toGMDigraph.toGraph) (bdTree code) tau ≤ B := by
    rw [graphBranchDecompWidth_relabelGraph f g htau]
    exact hwidth
  change let bd := r.toBranchDecomp; GM13.IsGraphBranchDecomposition _ bd.2.1 bd.2.2 ∧
    GM13.graphBranchDecompWidth _ bd.2.1 bd.2.2 ≤ B
  rw [record_decode r (bdNumTreeVerts code) ht hmax]
  change GM13.IsGraphBranchDecomposition _ (parentTree (bdNumTreeVerts code) p) tau ∧
    GM13.graphBranchDecompWidth _ (parentTree (bdNumTreeVerts code) p) tau ≤ B
  rw [htree]
  exact ⟨hb, hw⟩

/-- The record's vertex and edge lists decode exactly the renamed member
inside any ambient graph that contains it. -/
theorem case3BranchRecord_toSubgraph {n : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hsub : relabelGraph f g G.toGMDigraph.toGraph ≤ G₀) :
    (case3BranchRecord G f g code).toSubgraph G₀ = relabelGraph f g G.toGMDigraph.toGraph := by
  apply subgraphOfLists_eq_of_vertexSet_edgeSet hsub
  · ext v
    simp only [case3BranchRecord, Set.mem_ofPred_eq, List.mem_map, List.mem_finRange,
      true_and, vertexSet_relabelGraph, Set.mem_image]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u.1, u.2, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
  · ext e
    simp only [case3BranchRecord, Set.mem_ofPred_eq, List.mem_map,
      edgeSet_relabelGraph, Set.mem_image, G.mem_multiEdgeTriples_iff]
    rfl

/-- A valid branch code gives the decomposition claimed by the decoded
record whenever the member has at least two edges. -/
theorem case3BranchRecord_toSubgraph_branchDecomp {n B : ℕ} (G : MultiDigraph n) (f : ℕ ↪ ℕ)
    (g : (ℕ × ℕ × ℕ) ↪ (ℕ × ℕ × ℕ)) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hge : 2 ≤ G.numEdges)
    (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hsub : relabelGraph f g G.toGMDigraph.toGraph ≤ G₀) :
    let r := case3BranchRecord G f g code
    let bd := r.toBranchDecomp
    GM13.IsGraphBranchDecomposition (r.toSubgraph G₀) bd.2.1 bd.2.2 ∧
      GM13.graphBranchDecompWidth (r.toSubgraph G₀) bd.2.1 bd.2.2 ≤ B := by
  dsimp only
  rw [case3BranchRecord_toSubgraph G f g code G₀ hsub]
  exact case3BranchRecord_branchDecomp G f g code hcode hge

end GraphMinor.Compute
