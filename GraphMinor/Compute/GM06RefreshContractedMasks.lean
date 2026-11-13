module

public import GraphMinor.Compute.GM06InitLinkageMasks
public import GraphMinor.Compute.GM06ReplaceRotationRow
import GraphMinor.Compute.GM06ContractedMasks

/-!
# Recomputing linkage masks after a contraction

After the finite contraction update in VI (5.7), page 133, endpoint
labels at the retired neighbour have become the initial label and
one given path has lost its first directed edge. Recompute both
linkage masks from these changed ordinary fields. The construction
below gives the actual relabelled finite endpoint pairs and casts
the shortened path labels to their unchanged edge-label count.
No new mask is supplied as input.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Replace a retired vertex label by the retained initial label. -/
@[expose] def gm06ContractVertexLabel {n : ℕ} (a b v : Fin n) : Fin n :=
  if v = b then a else v

/-- Relabel both ends of each original edge, keeping every edge position. -/
@[expose] def gm06ContractEndpointPairs {n : ℕ} (es : List (Fin n × Fin n)) (a b : Fin n) :
    List (Fin n × Fin n) :=
  es.map (fun p => (gm06ContractVertexLabel a b p.1, gm06ContractVertexLabel a b p.2))

/-- Relabelling finite endpoint pairs gives exactly the numeric
substitution performed by the contraction's endpoint command. -/
theorem gm06ContractEndpointPairs_words {n : ℕ} (es : List (Fin n × Fin n)) (a b : Fin n) :
    gm06EndpointWords ((gm06ContractEndpointPairs es a b).map fun p => (p.1.val, p.2.val)) =
      (gm06EndpointWords (es.map fun p => (p.1.val, p.2.val))).map
        (fun v => if v = b.val then a.val else v) := by
  have hh : ∀ v : Fin n, (gm06ContractVertexLabel a b v).val =
      if v.val = b.val then a.val else v.val := by
    intro v
    by_cases h : v = b
    · simp [gm06ContractVertexLabel, h]
    · have h' : v.val ≠ b.val := fun h' => h (Fin.ext h')
      simp [gm06ContractVertexLabel, h, h']
  induction es with
  | nil => rfl
  | cons p es ih =>
    simpa only [gm06ContractEndpointPairs, List.map_cons, gm06EndpointWords,
      List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, hh, List.cons_append, List.nil_append] using
      congrArg (fun t =>
        (if p.1.val = b.val then a.val else p.1.val) ::
        (if p.2.val = b.val then a.val else p.2.val) :: t) ih

/-- The row encoding has one count word, one header per row and
one word per directed edge in the rows. -/
theorem gm06EncodeRows_length (rows : List (List ℕ)) :
    (gm06EncodeRows rows).length = 1 + rows.length + rows.flatten.length := by
  have hh : (gm06EncodeRowsPayload rows).length = rows.length + rows.flatten.length := by
    induction rows with
    | nil => rfl
    | cons row rows ih =>
      simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, List.flatten_cons] at *
      omega
  simp only [gm06EncodeRows, List.length_cons, hh]
  omega

private theorem map_rows_flatten_length {α β : Type} (f : α → β) (rows : List (List α)) :
    (rows.map (List.map f)).flatten.length = rows.flatten.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_map, ih]

/-- After the endpoint and path writes, the ordinary mask
initializer computes precisely the relabelled linkage's two masks.
The finite witnesses below are constructed by relabelling endpoints
and shortening the selected path, and their word labels are explicit. -/
theorem gm06RefreshContractedMasks_exec {w n : ℕ} (es : List (Fin n × Fin n))
    (rows : List (List (Fin (2 * es.length)))) (a b : Fin n) (i : ℕ) (hi : i < rows.length)
    (s : State) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * es.length < 2 ^ w)
    (hc : rows.length < 2 ^ w)
    (hcode : (gm06EncodeRows (rows.map (List.map Fin.val))).length < 2 ^ w)
    (h100 : s.regs 100 = n)
    (h3 : s.arrs 3 = (gm06EndpointWords (es.map fun p => (p.1.val, p.2.val))).map
      (fun v => if v = b.val then a.val else v))
    (h8 : s.arrs 8 = gm06EncodeRows ((rows.map (List.map Fin.val)).set i (rows[i].tail.map Fin.val))) :
    let es' := gm06ContractEndpointPairs es a b
    ∃ (rows' : List (List (Fin (2 * es'.length)))) (s' : State) (t : ℕ),
      rows'.map (List.map Fin.val) = (rows.map (List.map Fin.val)).set i (rows[i].tail.map Fin.val) ∧
      Exec w gm06InitLinkageMasksProg s s' t ∧
      t ≤ n + 36 * es.length + 22 * rows.length + 14 * rows.flatten.length + 22 ∧
      Keeps [40, 280, 281, 282, 283, 285] [17, 19] s s' ∧
      s'.arrs 19 = bitSetList rows'.flatten.toFinset ∧
      s'.arrs 17 = bitSetList (gm06UsedEndpointRows es' rows'.flatten.toFinset).flatten.toFinset := by
  let es' := gm06ContractEndpointPairs es a b
  have helen : es'.length = es.length := by simp only [es', gm06ContractEndpointPairs, List.length_map]
  let castDart : Fin (2 * es.length) → Fin (2 * es'.length) :=
    fun d => ⟨d.val, by rw [helen]; exact d.isLt⟩
  let shortened := rows.set i rows[i].tail
  let rows' := shortened.map (List.map castDart)
  have hnat : rows'.map (List.map Fin.val) =
      (rows.map (List.map Fin.val)).set i (rows[i].tail.map Fin.val) := by
    simp only [rows', shortened, List.map_map, Function.comp_def, castDart, List.map_set]
  have hcount : rows'.length = rows.length := by simp only [rows', shortened, List.length_map, List.length_set]
  have hnatlen := congrArg List.length hnat
  have hflatten : rows'.flatten.length ≤ rows.flatten.length := by
    have hcodeLen := gm06EncodeRows_set_length (rows.map (List.map Fin.val)) i
      (by simpa only [List.length_map] using hi) (rows[i].tail.map Fin.val)
    rw [gm06EncodeRows_length, gm06EncodeRows_length] at hcodeLen
    have hfl := map_rows_flatten_length Fin.val rows'
    have hflOld := map_rows_flatten_length Fin.val rows
    have hlenTail : rows[i].tail.length ≤ rows[i].length := by simp only [List.length_tail]; omega
    simp only [List.getElem_map, List.length_map, List.length_set] at hcodeLen
    rw [← hnat] at hcodeLen
    simp only [List.length_map] at hnatlen
    omega
  have hnewcode : (gm06EncodeRows (rows'.map (List.map Fin.val))).length < 2 ^ w := by
    rw [gm06EncodeRows_length, List.length_map, hcount, map_rows_flatten_length]
    rw [gm06EncodeRows_length, List.length_map, map_rows_flatten_length] at hcode
    omega
  obtain ⟨s', t, hex, ht, hk, hdarts, hverts⟩ := gm06InitLinkageMasksProg_exec es' rows'
    hw hn (by rw [helen]; exact hm) (by rw [hcount]; exact hc) hnewcode h100
    (by rw [gm06ContractEndpointPairs_words]; exact h3) (by rw [hnat]; exact h8)
  refine ⟨rows', s', t, hnat, hex, ?_, hk, hdarts, hverts⟩
  omega

/-- The endpoint substitution contains no occurrence of the
retired neighbour when its label differs from the retained label. -/
theorem gm06ContractEndpointPairs_ne_retired {n : ℕ} (es : List (Fin n × Fin n))
    (a b : Fin n) (hab : a ≠ b) :
    ∀ p ∈ gm06ContractEndpointPairs es a b, p.1 ≠ b ∧ p.2 ≠ b := by
  intro p hp
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  have hh : ∀ v, gm06ContractVertexLabel a b v ≠ b := by
    intro v
    by_cases h : v = b <;> simp [gm06ContractVertexLabel, h, hab]
  exact ⟨hh q.1, hh q.2⟩

/-- The finite edge table after a contraction keeps the original
indices, relabels both endpoints and clears the selected flag. -/
@[expose] def gm06ContractTaggedEdges {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ) :
    List ((Fin n × Fin n) × ℕ) :=
  tagged.mapIdx (fun j p =>
    ((gm06ContractVertexLabel a b p.1.1, gm06ContractVertexLabel a b p.1.2),
      if j = d then 0 else p.2))

/-- Contracting one edge preserves the original edge-label space. -/
theorem gm06ContractTaggedEdges_length {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ) :
    (gm06ContractTaggedEdges tagged a b d).length = tagged.length := by
  simp only [gm06ContractTaggedEdges, List.length_mapIdx]

/-- Each updated finite edge row has exactly the relabelled ends
and the activity word computed by the mask clearing. -/
theorem gm06ContractTaggedEdges_getElem {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ)
    {j : ℕ} (hj : j < tagged.length) :
    (gm06ContractTaggedEdges tagged a b d)[j]'(by rw [gm06ContractTaggedEdges_length]; exact hj) =
      ((gm06ContractVertexLabel a b tagged[j].1.1, gm06ContractVertexLabel a b tagged[j].1.2),
        if j = d then 0 else tagged[j].2) := by
  simp only [gm06ContractTaggedEdges, List.getElem_mapIdx]

/-- The activity words of the finite contracted table are exactly
the single-bit update of the old activity array. -/
theorem gm06ContractTaggedEdges_activity {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ) :
    (gm06ContractTaggedEdges tagged a b d).map Prod.snd = (tagged.map Prod.snd).set d 0 := by
  apply List.ext_getElem (by simp only [List.length_map, gm06ContractTaggedEdges_length, List.length_set])
  intro j hj hj'
  have hjT : j < tagged.length := by simpa only [List.length_map, gm06ContractTaggedEdges_length] using hj
  rw [List.getElem_map, gm06ContractTaggedEdges_getElem tagged a b d hjT, List.getElem_set]
  simp only [List.getElem_map]
  by_cases h : j = d
  · simp [h]
  · simp [h, Ne.symm h]

/-- The endpoint-pair projection is exactly the ordinary finite
endpoint substitution used to rebuild the linkage masks. -/
theorem gm06ContractTaggedEdges_endpoints {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ) :
    (gm06ContractTaggedEdges tagged a b d).map Prod.fst =
      gm06ContractEndpointPairs (tagged.map Prod.fst) a b := by
  apply List.ext_getElem (by simp only [List.length_map, gm06ContractTaggedEdges_length,
    gm06ContractEndpointPairs, List.length_map])
  intro j hj hj'
  have hjT : j < tagged.length := by simpa only [List.length_map, gm06ContractTaggedEdges_length] using hj
  simp only [List.getElem_map, gm06ContractTaggedEdges_getElem tagged a b d hjT,
    gm06ContractEndpointPairs]

/-- The finite updated table has exactly the endpoint word array
written by the contraction program. -/
theorem gm06ContractTaggedEdges_endpointWords {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ) :
    gm06EndpointWords ((gm06ContractTaggedEdges tagged a b d).map fun p => (p.1.1.val, p.1.2.val)) =
      (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val))).map
        (fun v => if v = b.val then a.val else v) := by
  have hh := gm06ContractEndpointPairs_words (tagged.map Prod.fst) a b
  rw [← gm06ContractTaggedEdges_endpoints tagged a b d] at hh
  simpa only [List.map_map, Function.comp_def] using hh

/-- Zero-one activity words remain zero-one after clearing the
contracted edge and relabelling its endpoints. -/
theorem gm06ContractTaggedEdges_flags_le_one {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (a b : Fin n) (d : ℕ)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1) :
    ∀ p ∈ gm06ContractTaggedEdges tagged a b d, p.2 ≤ 1 := by
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hp
  have hjT : j < tagged.length := by simpa only [gm06ContractTaggedEdges_length] using hj
  rw [gm06ContractTaggedEdges_getElem tagged a b d hjT]
  split
  · exact Nat.zero_le _
  · exact hbits tagged[j] (List.getElem_mem hjT)

/-- A live endpoint remains live under the neighbour-to-initial
substitution and is distinct from the retired label. -/
theorem gm06ContractVertexLabel_mem_erase {n : ℕ} (A : Finset (Fin n)) (a b v : Fin n)
    (ha : a ∈ A) (hv : v ∈ A) (hab : a ≠ b) : gm06ContractVertexLabel a b v ∈ A.erase b := by
  by_cases h : v = b
  · simp only [gm06ContractVertexLabel, h, ite_true]
    exact Finset.mem_erase.mpr ⟨hab, ha⟩
  · simp only [gm06ContractVertexLabel, h, ite_false]
    exact Finset.mem_erase.mpr ⟨h, hv⟩

end GraphMinor.Compute
