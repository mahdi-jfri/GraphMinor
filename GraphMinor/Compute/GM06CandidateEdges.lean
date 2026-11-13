module

public import GraphMinor.Compute.GM06CandidateVertices
public import GraphMinor.Compute.GM06CutCSR

/-!
# Permanent edge labels of the Reduction 4 candidate graph

Section 12 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) retains only
ordinary face-incident edges whose endpoints survive the deletions.
Both orientations of each such edge are retained. The rotation rows
stay in their original order. This file identifies the resulting
cut-data search graph with the candidate graph and shows that its
increasing adjacency rows are the rows used by the pure BFS function.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Endpoint pairs read from permanent positive and negative dart slots. -/
def gm06CandidateEnds (m : ℕ) (origins : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn (fun e : Fin m => (origins[2 * e.val]?.getD 0, origins[2 * e.val + 1]?.getD 0))

/-- Every permanent edge slot has an endpoint pair. -/
theorem gm06CandidateEnds_length (m : ℕ) (origins : List ℕ) :
    (gm06CandidateEnds m origins).length = m := by
  simp only [gm06CandidateEnds, List.length_ofFn]

/-- Endpoint lookup agrees with the cut representation. -/
theorem gm06CandidateEnds_get {m e : ℕ} (origins : List ℕ) (he : e < m) :
    (gm06CandidateEnds m origins)[e]?.getD (0, 0) =
      (origins[2 * e]?.getD 0, origins[2 * e + 1]?.getD 0) := by
  simp only [gm06CandidateEnds, List.getElem?_ofFn, he, ↓reduceDIte, Option.getD_some]

/-- Both orientations of each candidate edge, in permanent dart order. -/
def gm06CandidateDarts (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) : List ℕ :=
  (List.range (2 * m)).filter (fun d => decide (d / 2 ∈
    gm06CandidateEdges (gm06CandidateEnds m origins) ordinary incV incE upper path j))

/-- Retained dart membership is exactly candidate-edge membership. -/
theorem gm06CandidateDarts_mem_iff (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j d : ℕ) :
    d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j ↔
      d < 2 * m ∧ d / 2 ∈
        gm06CandidateEdges (gm06CandidateEnds m origins) ordinary incV incE upper path j := by
  simp only [gm06CandidateDarts, List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- Complete pairs of retained ends are precisely the candidate edges. -/
theorem gm06CandidateDarts_edge_iff (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j e : ℕ) :
    (2 * e ∈ gm06CandidateDarts m origins ordinary incV incE upper path j ∧
      2 * e + 1 ∈ gm06CandidateDarts m origins ordinary incV incE upper path j) ↔
      e ∈ gm06CandidateEdges (gm06CandidateEnds m origins) ordinary incV incE upper path j := by
  rw [gm06CandidateDarts_mem_iff, gm06CandidateDarts_mem_iff]
  have hdiv₀ : 2 * e / 2 = e := by omega
  have hdiv₁ : (2 * e + 1) / 2 = e := by omega
  rw [hdiv₀, hdiv₁]
  constructor
  · exact fun h => h.1.2
  · intro he
    have hb := (gm06CandidateEdges_mem_iff _ ordinary incV incE upper path j e).mp he
    rw [gm06CandidateEnds_length] at hb
    exact ⟨⟨by omega, he⟩, by omega, he⟩

/-- Candidate darts are closed under reversal, including loop ends. -/
theorem gm06CandidateDarts_mate (m : ℕ) (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j d : ℕ)
    (hd : d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j) :
    gm06DartMate d ∈ gm06CandidateDarts m origins ordinary incV incE upper path j := by
  have hp := (gm06CandidateDarts_mem_iff m origins ordinary incV incE upper path j d).mp hd
  apply (gm06CandidateDarts_mem_iff m origins ordinary incV incE upper path j _).mpr
  refine ⟨gm06DartMate_lt hp.1, ?_⟩
  have hdiv : gm06DartMate d / 2 = d / 2 := by
    rcases gm06DartMate_end_cases d with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> omega
  simpa only [hdiv] using hp.2

/-- Candidate cut data keep the input rotations and permanent origins.
Excluded vertices have no retained incident edge. -/
def gm06CandidateData (n m : ℕ) (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) : GM06CutData where
  rotations := data.rotations
  origins := data.origins
  activeDarts := gm06CandidateDarts m data.origins ordinary incV incE upper path j
  vertices := List.range n

/-- The CSR search graph is exactly the finite graph A_(i,j). -/
theorem gm06CandidateData_graph (n m : ℕ) (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ) :
    gm06CutGraph n (gm06CandidateData n m data ordinary incV incE upper path j) =
      gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  have hedge : ∀ e, e ∈ gm06CutEdgeLabels
      (gm06CandidateData n m data ordinary incV incE upper path j) ↔
      e ∈ gm06CandidateEdges (gm06CandidateEnds m data.origins) ordinary incV incE upper path j := by
    intro e
    rw [gm06CutEdgeLabels_mem_iff]
    exact gm06CandidateDarts_edge_iff m data.origins ordinary incV incE upper path j e
  change (_ ∧ u.val ∈ List.range n ∧ v.val ∈ List.range n ∧ _) ↔ (_ ∧ _)
  simp only [List.mem_range, u.isLt, v.isLt, true_and]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨e, he, hends⟩
    have he' := (hedge e).mp he
    have hem : e < m := by
      simpa only [gm06CandidateEnds_length] using
        ((gm06CandidateEdges_mem_iff _ ordinary incV incE upper path j e).mp he').1
    exact ⟨e, he', by simpa only [gm06CandidateEnds_get data.origins hem,
      gm06CutEndpoints, gm06CandidateData] using hends⟩
  · rintro ⟨e, he, hends⟩
    have hem : e < m := by
      simpa only [gm06CandidateEnds_length] using
        ((gm06CandidateEdges_mem_iff _ ordinary incV incE upper path j e).mp he).1
    exact ⟨e, (hedge e).mpr he, by simpa only [gm06CandidateEnds_get data.origins hem,
      gm06CutEndpoints, gm06CandidateData] using hends⟩

/-- Consecutive CSR start offsets agree with the canonical BFS encoding. -/
theorem gm06CSRStarts_encodeLists {n : ℕ} (lists : Fin n → List ℕ) :
    gm06CSRStarts 0 (List.ofFn lists) = (encodeLists lists).1 := by
  apply List.ext_getElem
  · simp only [gm06CSRStarts_length, List.length_ofFn, encodeLists]
  · intro i hi hi'
    have hin : i < (List.ofFn lists).length := by
      simpa only [gm06CSRStarts_length] using hi
    simpa only [encodeLists, List.getElem_ofFn, Nat.zero_add] using
      gm06CSRStarts_getElem (List.ofFn lists) 0 i hin

/-- Consecutive CSR end offsets agree with the canonical BFS encoding. -/
theorem gm06CSREnds_encodeLists {n : ℕ} (lists : Fin n → List ℕ) :
    gm06CSREnds 0 (List.ofFn lists) = (encodeLists lists).2.1 := by
  apply List.ext_getElem
  · simp only [gm06CSREnds_length, List.length_ofFn, encodeLists]
  · intro i hi hi'
    have hin : i < (List.ofFn lists).length := by
      simpa only [gm06CSREnds_length] using hi
    simpa only [encodeLists, List.getElem_ofFn, Nat.zero_add] using
      gm06CSREnds_getElem (List.ofFn lists) 0 i hin

/-- Increasing adjacency lists respect equality of graphs even when
those graphs use separately synthesized decidable adjacency instances. -/
theorem gm06OrderedNeighbours_congr {n : ℕ} (G H : SimpleGraph (Fin n))
    [dG : DecidableRel G.Adj] [dH : DecidableRel H.Adj] (h : G = H) :
    gm06OrderedNeighbours G = gm06OrderedNeighbours H := by
  cases h
  have hd : dG = dH := Subsingleton.elim _ _
  cases hd
  rfl

private theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range]
  · intro i hi hi'
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    rfl

/-- Any correct row construction using the increasing permanent range
agrees with the increasing lists used by the pure BFS specification. -/
theorem gm06CutAdjacencyLists_eq_ordered {n : ℕ} (data : GM06CutData)
    (hproper : ∀ d ∈ data.activeDarts, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD []) (u : Fin n) :
    gm06CutAdjacencyLists n data u = gm06OrderedNeighbours (gm06CutGraph n data) u := by
  let keep := fun v => decide (v ∈ gm06CutNeighbourCandidates data.origins
    data.activeDarts data.vertices u.val (data.rotations[u.val]?.getD []))
  have hmap : gm06CutAdjacencyLists n data u =
      ((List.finRange n).filter (fun v => keep v.val)).map Fin.val := by
    change (List.range n).filter keep = _
    rw [← finRange_map_val n]
    exact List.filter_map
  rw [hmap, gm06OrderedNeighbours]
  congr 1
  apply List.filter_congr
  intro v _
  apply Bool.eq_iff_iff.mpr
  simp only [keep, decide_eq_true_eq]
  exact (gm06CutGraph_adj_iff_candidates data hproper u v).symm

end GraphMinor.Compute
