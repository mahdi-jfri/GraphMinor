module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.Compute.GM06Alg511PackedCall
import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Uniform sizes of the linkage rows in the feasibility loop

Each reference linkage in VI (5.11), page 134, consists of simple
paths in the original graph. A path has at most one occurrence of
each vertex, so its ordinary-dart row has fewer words than the
original vertex count. Its words are original directed edge labels.
These facts bound the complete successor input at every round by
the fixed drawing data and a polynomial path-table allowance.
The bounds follow from the actual walk interpretation of the rows.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set

private theorem support_length {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) : W.support.length = W.edges.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons h W ih => simpa only [GraphWalk.support_cons, GraphWalk.edges_cons, List.length_cons] using congrArg (fun n => n + 1) ih

private theorem simple_support_length_le {G : Drawing ClosedCylinder} {a b : ClosedCylinder}
    (W : GraphWalk G.toGraph a b) (hW : W.IsSimple) : W.support.length ≤ G.V.ncard := by
  classical
  have hs : (W.support.toFinset : Set ClosedCylinder) ⊆ G.V := by
    intro p hp
    exact W.mem_vertexSet_of_mem_support (List.mem_toFinset.mp hp)
  have hc := Set.ncard_le_ncard hs G.finite_V
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hW] at hc
  exact hc

/-- Every actual encoded linkage row has fewer words than the
original vertex count, and each of its words is an original
in-range directed edge end. These bounds also cover parallel edges. -/
theorem alg511_linkage_rows_bounds {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows) :
    rows.length = k ∧ ∀ row ∈ rows,
      row.length + 1 ≤ x.vertexCount ∧ ∀ d ∈ row, d < x.endpoints.length := by
  refine ⟨henc.1, ?_⟩
  intro row hr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
  have hjk : j < k := henc.1 ▸ hj
  obtain ⟨W, hW, hd, _⟩ := henc.path ⟨j, hjk⟩
  refine ⟨?_, ?_⟩
  · rw [hd.length_eq, ← support_length, rep.vertexCount_eq]
    exact simple_support_length_le W hW
  · intro d hm
    have hh := (hd.active_words d hm).1
    have hlen : x.endpoints.length = 2 * rep.initialTagged.length := by
      rw [rep.endpoints, gm06EndpointWords_length, GM06SuccessorGraphRep.initialTagged, List.length_map, List.length_map]
    rwa [hlen]

private theorem payload_length_le (rows : List (List ℕ)) (n : ℕ)
    (hrows : ∀ row ∈ rows, row.length ≤ n) :
    (gm06EncodeRowsPayload rows).length ≤ rows.length + rows.length * n := by
  induction rows with
  | nil => simp [gm06EncodeRowsPayload]
  | cons row rows ih =>
    have hh := ih (fun r hr => hrows r (by simp [hr]))
    have hr := hrows row (by simp)
    simp only [gm06EncodeRowsPayload, List.flatMap_cons, gm06EncodeNatList,
      List.length_append, List.length_cons] at hh ⊢
    nlinarith only [hh, hr]

private theorem encoded_words {w : ℕ} (rows : List (List ℕ))
    (hcount : rows.length < 2 ^ w)
    (hrows : ∀ row ∈ rows, row.length < 2 ^ w ∧ ∀ d ∈ row, d < 2 ^ w) :
    ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w := by
  intro d hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact hcount
  · obtain ⟨row, hr, hd⟩ := List.mem_flatMap.mp hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact (hrows row hr).1
    · exact (hrows row hr).2 d hd

/-- The current linkage table has at most the number of paths
times the original vertex allowance, including all row headers. -/
theorem alg511_linkage_code_length_le {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows) :
    (gm06EncodeRows rows).length ≤ 1 + k + k * x.vertexCount := by
  obtain ⟨hcount, hb⟩ := alg511_linkage_rows_bounds rep henc
  have hp := payload_length_le rows x.vertexCount (fun row hr => by have hh := (hb row hr).1; omega)
  simp only [gm06EncodeRows, List.length_cons]
  rw [hcount] at hp
  omega

/-- All words of any actual reference linkage fit whenever the
original vertex count, edge-end range and path count fit. No bound
on a selected row is assumed independently of its walk encoding. -/
theorem alg511_linkage_code_words {w k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows)
    (hk : k < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (he : x.endpoints.length < 2 ^ w) :
    ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w := by
  obtain ⟨hcount, hb⟩ := alg511_linkage_rows_bounds rep henc
  apply encoded_words rows (hcount ▸ hk)
  intro row hr
  exact ⟨(Nat.le_of_succ_le (hb row hr).1).trans_lt hn,
    fun d hd => ((hb row hr).2 d hd).trans he⟩

private theorem successor_words_of_path_words {w : ℕ} (x : GM06SuccessorInput)
    (rows : List (List ℕ))
    (hbase : ∀ d ∈ gm06EncodeSuccessorInput {x with linkage := []}, d < 2 ^ w)
    (hlen : (gm06EncodeRows rows).length < 2 ^ w)
    (hpaths : ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w) :
    ∀ d ∈ gm06EncodeSuccessorInput {x with linkage := rows}, d < 2 ^ w := by
  intro d hd
  rcases List.mem_cons.mp hd with hcount | hd
  · exact hbase d (List.mem_cons.mpr (Or.inl hcount))
  · obtain ⟨field, hfield, hd⟩ := List.mem_flatMap.mp hd
    change field ∈ [[x.vertexCount], x.endpoints, gm06EncodeRows x.rotations,
      x.innerCuff, x.outerCuff] ++ [gm06EncodeRows rows] at hfield
    rcases List.mem_append.mp hfield with hfield | hfield
    · have hf : field ∈ gm06SuccessorRows {x with linkage := []} :=
        List.mem_append_left [gm06EncodeRows []] hfield
      exact hbase d (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨field, hf, hd⟩))
    · have heq := List.mem_singleton.mp hfield
      subst field
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hlen
      · exact hpaths d hd

/-- The complete current input inherits all fixed drawing-word
bounds. Its changed path row words and length prefixes fit by the
actual walk encoding and one uniform path-table capacity bound. -/
theorem alg511_successor_input_words {w k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows)
    (hbase : ∀ d ∈ gm06EncodeSuccessorInput {x with linkage := []}, d < 2 ^ w)
    (hk : k < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (he : x.endpoints.length < 2 ^ w)
    (hcap : 1 + k + k * x.vertexCount < 2 ^ w) :
    ∀ d ∈ gm06EncodeSuccessorInput {x with linkage := rows}, d < 2 ^ w := by
  exact successor_words_of_path_words x rows hbase
    ((alg511_linkage_code_length_le rep henc).trans_lt hcap)
    (alg511_linkage_code_words rep henc hk hn he)

/-- Every round's full successor code is bounded by its fixed
drawing code with no paths, plus one uniform path-table allowance. -/
theorem alg511_successor_input_length_le {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows) :
    (gm06EncodeSuccessorInput {x with linkage := rows}).length ≤
      (gm06EncodeSuccessorInput {x with linkage := []}).length + k + k * x.vertexCount := by
  have hh := alg511_linkage_code_length_le rep henc
  have heq : (gm06EncodeSuccessorInput {x with linkage := rows}).length + 1 =
      (gm06EncodeSuccessorInput {x with linkage := []}).length + (gm06EncodeRows rows).length := by
    simp only [gm06EncodeSuccessorInput, gm06SuccessorRows, gm06EncodeRows,
      gm06EncodeRowsPayload, gm06EncodeNatList, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_append, List.length_nil]
    omega
  omega

/-- Substituting the uniformly bounded current code into the
proved call cost gives a bound independent of the particular
reference linkage chosen at any successful round. -/
theorem alg511_packed_call_time_le {k : ℕ} {x : GM06SuccessorInput}
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph)
    {L : CylinderLinkage k G} {rows : List (List ℕ)}
    (henc : GM06LinkageRowsEncoding L rep.initialTagged rep.vertexLabels rep.edgeLabels rows)
    (B : ℕ) :
    B + 137 + 68 * (gm06EncodeSuccessorInput {x with linkage := rows}).length ≤
      B + 137 + 68 * ((gm06EncodeSuccessorInput {x with linkage := []}).length + k + k * x.vertexCount) := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_left 68 (alg511_successor_input_length_le rep henc)) _

end GraphMinor.GM06
