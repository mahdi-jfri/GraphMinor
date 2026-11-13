module

public import GraphMinor.Compute.GM06CutFaceInput
public import GraphMinor.Compute.GM06CutComponentRows
import GraphMinor.Compute.GM06CutOriginFacts

/-!
# Finite face-incidence facts for the cuff-indexed cut components

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) chooses the
face containing the reverse inner cuff dart. This file proves the finite
handoff: component restriction preserves a proper rotation encoding,
an edge incident with the search root belongs to that component,
and an active reverse dart selects its complete face orbit and exact
incidence tables. Identification with the lifted region is separate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Finite conversion preserves every proper component rotation row. -/
theorem gm06CutFiniteRows_map_val (q : ℕ) (data : GM06CutData)
    (hkeys : ∀ d ∈ data.rotations.flatten, d < q) :
    (data.rotations.map (gm06FinLabels q)).map (List.map Fin.val) = data.rotations := by
  rw [List.map_map]
  calc
    _ = data.rotations.map id := by
      apply List.map_congr_left
      intro row hr
      exact gm06FinLabels_map_val q row (fun d hd => hkeys d (List.mem_flatten.mpr ⟨row, hr, hd⟩))
    _ = _ := List.map_id _

/-- Ordinary finite graph-encoding conditions give all typed face-input conditions. -/
theorem gm06CutFiniteRows_valid {m : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts) :
    let rows := data.rotations.map (gm06FinLabels (2 * m))
    let active := gm06FinLabels (2 * m) data.activeDarts
    rows.flatten.Nodup ∧ (∀ d, d ∈ active ↔ d ∈ rows.flatten) ∧
      ∀ d ∈ active, gm06DartReversal m d ∈ active := by
  let rows := data.rotations.map (gm06FinLabels (2 * m))
  let active := gm06FinLabels (2 * m) data.activeDarts
  have hrows := gm06CutFiniteRows_map_val (2 * m) data hkeys
  have hact := gm06FinLabels_map_val (2 * m) data.activeDarts hactive
  have hflat : rows.flatten.map Fin.val = data.rotations.flatten := by rw [List.map_flatten, hrows]
  refine ⟨List.Nodup.of_map Fin.val (hflat ▸ hnd), ?_, ?_⟩
  · intro d
    rw [← List.mem_map_of_injective Fin.val_injective, hact,
      ← List.mem_map_of_injective Fin.val_injective, hflat]
    exact hcover d.val
  · intro d hd
    apply (gm06FinLabels_mem_iff data.activeDarts hactive (gm06DartReversal m d)).mpr
    exact hpair d.val ((gm06FinLabels_mem_iff data.activeDarts hactive d).mp hd)

/-- The finite content of the face selection of Section 10: an active reverse cuff end selects its
actual complete face orbit and its two incidence tables, `gm06IncV` and `gm06IncE`. -/
theorem gm06CutFaceIncidence_spec {n m target : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts) (ht : target ∈ data.activeDarts) :
    ∃ row : List (Fin (2 * m)),
      gm06CutFaceIncidence n m data target = some
        (row.map Fin.val, gm06IncV n data.origins (row.map Fin.val), gm06IncE m (row.map Fin.val)) ∧
      target ∈ row.map Fin.val ∧
      ∃ start ∈ gm06FinLabels (2 * m) data.activeDarts,
        row = gm06OrbitTrace (gm06FacePermutation (data.rotations.map (gm06FinLabels (2 * m)))) start (2 * m) ∧
        List.IsChain (fun a b => gm06FacePermutation (data.rotations.map (gm06FinLabels (2 * m))) a = b)
          (row ++ [start]) := by
  have htarget := hactive target ht
  have hfin := gm06CutFiniteRows_valid data hnd hkeys hactive hcover hpair
  have htfin : (⟨target, htarget⟩ : Fin (2 * m)) ∈ gm06FinLabels (2 * m) data.activeDarts :=
    (gm06FinLabels_mem_iff data.activeDarts hactive _).mpr ht
  obtain ⟨row, hselected, hrow, _, horbit⟩ := gm06SelectedFace_spec
    (data.rotations.map (gm06FinLabels (2 * m))) (gm06FinLabels (2 * m) data.activeDarts)
    ⟨target, htarget⟩ hfin.1 hfin.2.1 hfin.2.2 htfin
  refine ⟨row, ?_, List.mem_map.mpr ⟨⟨target, htarget⟩, hrow, rfl⟩, horbit⟩
  simpa only [gm06CutFaceIncidence, htarget, ↓reduceDIte] using gm06SelectedFaceIncidence_eq data.origins
    (data.rotations.map (gm06FinLabels (2 * m))) (gm06FinLabels (2 * m) data.activeDarts) ⟨target, htarget⟩ row hselected

/-- Component restriction preserves all finite rotation/active-end
conditions used by face enumeration, including reversal closure. -/
theorem gm06CutComponentData_face_encoding {n q : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hbound : ∀ d ∈ data.activeDarts, d < q) :
    let part := gm06CutComponentData data root
    part.rotations.flatten.Nodup ∧
      (∀ d, d ∈ part.activeDarts ↔ d ∈ part.rotations.flatten) ∧
      (∀ d ∈ part.activeDarts, d < q) ∧
      (∀ d ∈ part.rotations.flatten, d < q) ∧
      ∀ d ∈ part.activeDarts, gm06DartMate d ∈ part.activeDarts := by
  have hc : ∀ d, d ∈ (gm06CutComponentData data root).activeDarts ↔
      d ∈ (gm06CutComponentData data root).rotations.flatten := by
    intro d
    rw [gm06CutComponentData_active_iff, gm06CutComponentData_flatten, List.mem_filter, decide_eq_true_eq, hcover]
  have hb : ∀ d ∈ (gm06CutComponentData data root).activeDarts, d < q := by
    intro d hd
    exact hbound d ((gm06CutComponentData_active_iff data root d).mp hd).1
  exact ⟨gm06CutComponentData_nodup data root hnd, hc, hb,
    fun d hd => hb d ((hc d).mpr hd), gm06CutComponentData_mate_closed data root⟩

/-- A complete edge incident with the search root lies in that
component, including a loop whose two stored endpoints coincide. -/
theorem gm06CutComponentData_edge_at_root {n : ℕ} (data : GM06CutData) (root : Fin n) (e : ℕ)
    (he : e ∈ gm06CutEdgeLabels data) (hroot : root.val = (gm06CutEndpoints data e).1)
    (hother : (gm06CutEndpoints data e).2 < n)
    (hrootLive : root.val ∈ data.vertices) (hotherLive : (gm06CutEndpoints data e).2 ∈ data.vertices) :
    e ∈ gm06CutComponentEdges data root ∧
      2 * e ∈ (gm06CutComponentData data root).activeDarts ∧
      2 * e + 1 ∈ (gm06CutComponentData data root).activeDarts := by
  let other : Fin n := ⟨(gm06CutEndpoints data e).2, hother⟩
  have hreach : (gm06CutGraph n data).Reachable root other := by
    by_cases heq : root = other
    · rw [← heq]
    · have hadj : (gm06CutGraph n data).Adj root other :=
        ⟨heq, hrootLive, hotherLive, e, he, Or.inl (Prod.ext hroot.symm rfl)⟩
      exact ⟨SimpleGraph.Walk.cons hadj .nil⟩
  have hfirst : (gm06CutEndpoints data e).1 ∈ gm06CutComponentVertices data root :=
    hroot ▸ gm06CutComponentVertices_root_mem data root
  have hsecond : (gm06CutEndpoints data e).2 ∈ gm06CutComponentVertices data root :=
    (gm06CutComponentVertices_mem_iff data root other).mpr hreach
  have hce := (gm06CutComponentEdges_mem_iff data root e).mpr ⟨he, hfirst, hsecond⟩
  have hp := (gm06CutEdgeLabels_mem_iff data e).mp he
  refine ⟨hce, (gm06CutComponentData_active_iff data root (2 * e)).mpr ⟨hp.1, ?_⟩,
    (gm06CutComponentData_active_iff data root (2 * e + 1)).mpr ⟨hp.2, ?_⟩⟩ <;>
    simpa only [show 2 * e / 2 = e by omega, show (2 * e + 1) / 2 = e by omega] using hce

/-- For the cuff-indexed component, its reverse inner end selects a
face row and equation-(10) incidence. This uses only the stored edge
and live endpoint conditions, with no topological region hypothesis. -/
theorem gm06CutFaceIncidence_inner_cuff {n m base i : ℕ} (data : GM06CutData) (root : Fin n)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hbound : ∀ d ∈ data.activeDarts, d < 2 * m)
    (he : 2 * (base + i) ∈ gm06CutEdgeLabels data)
    (hroot : root.val = (gm06CutEndpoints data (2 * (base + i))).1)
    (hother : (gm06CutEndpoints data (2 * (base + i))).2 < n)
    (hrootLive : root.val ∈ data.vertices)
    (hotherLive : (gm06CutEndpoints data (2 * (base + i))).2 ∈ data.vertices) :
    ∃ row : List (Fin (2 * m)), gm06CutFaceIncidence n m (gm06CutComponentData data root)
      (4 * (base + i) + 1) = some
        (row.map Fin.val, gm06IncV n data.origins (row.map Fin.val), gm06IncE m (row.map Fin.val)) ∧
      4 * (base + i) + 1 ∈ row.map Fin.val := by
  have hc := gm06CutComponentData_face_encoding data root hnd hcover hbound
  have hec := gm06CutComponentData_edge_at_root data root (2 * (base + i)) he hroot hother hrootLive hotherLive
  have hreverse : 4 * (base + i) + 1 ∈ (gm06CutComponentData data root).activeDarts := by
    simpa only [← Nat.mul_assoc] using hec.2.2
  obtain ⟨row, hr, hm, _⟩ := gm06CutFaceIncidence_spec (gm06CutComponentData data root)
    hc.1 hc.2.2.2.1 hc.2.2.1 hc.2.1 hc.2.2.2.2 hreverse
  exact ⟨row, hr, hm⟩

/-- For every inner-cuff-indexed component, the actual RAM query
returns its face and both incidence tables. Component input conditions
are derived from the common graph encoding and its retained cuff edge. -/
theorem gm06CutFaceIncidenceProg_exec_component {w n m base i : ℕ}
    (data : GM06CutData) (root : Fin n) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hcodeFit : 1 + data.rotations.length + 2 * m < 2 ^ w)
    (hnd : data.rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hbound : ∀ d ∈ data.activeDarts, d < 2 * m)
    (horigLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hendsLive : ∀ d ∈ data.activeDarts, data.origins[d]?.getD 0 ∈ data.vertices)
    (hactiveFit : data.activeDarts.length < 2 ^ w)
    (hcuff : 2 * (base + i) ∈ gm06CutEdgeLabels data)
    (hroot : root.val = (gm06CutEndpoints data (2 * (base + i))).1)
    (h600 : s.arrs 600 = gm06EncodeRows (gm06CutComponentData data root).rotations)
    (h604 : s.arrs 604 = (gm06CutComponentData data root).activeDarts)
    (h626 : s.arrs 626 = data.origins) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m)
    (h672 : s.regs 672 = base) (h673 : s.regs 673 = i) :
    ∃ sf t, Exec w gm06CutFaceIncidenceProg s sf t ∧
      t ≤ 1100 * (n + 2 * m + data.rotations.length + 2 * m + data.activeDarts.length + 1) ^ 2 ∧
      TwoPaths.Keeps (667 :: gm06SelectedIncidenceRegs) [600, 601, 602, 603, 604, 605, 606, 607] s sf ∧
      gm06SelectedIncidenceResult sf = gm06CutFaceIncidence n m (gm06CutComponentData data root) (4 * (base + i) + 1) ∧
      ∃ row : List (Fin (2 * m)), gm06SelectedIncidenceResult sf = some
        (row.map Fin.val, gm06IncV n data.origins (row.map Fin.val), gm06IncE m (row.map Fin.val)) ∧
        4 * (base + i) + 1 ∈ row.map Fin.val := by
  let part := gm06CutComponentData data root
  let e := 2 * (base + i)
  have hc := gm06CutComponentData_face_encoding data root hnd hcover hbound
  have hp := (gm06CutEdgeLabels_mem_iff data e).mp hcuff
  have hotherIdx : 2 * e + 1 < data.origins.length := by rw [horigLen]; exact hbound _ hp.2
  have hother : (gm06CutEndpoints data e).2 < n := by
    simpa only [gm06CutEndpoints, Prod.snd, List.getElem?_eq_getElem hotherIdx, Option.getD_some] using
      hvalues _ (List.getElem_mem hotherIdx)
  have hrootLive : root.val ∈ data.vertices := by rw [hroot]; exact hendsLive _ hp.1
  have hotherLive : (gm06CutEndpoints data e).2 ∈ data.vertices := hendsLive _ hp.2
  have hce := gm06CutComponentData_edge_at_root data root e hcuff hroot hother hrootLive hotherLive
  have hqueryActive : 4 * (base + i) + 1 ∈ part.activeDarts := by
    have heq : 2 * e + 1 = 4 * (base + i) + 1 := by dsimp only [e]; omega
    exact heq ▸ hce.2.2
  have hquery : 4 * (base + i) + 1 < 2 * m := hc.2.2.1 _ hqueryActive
  have hlength : part.rotations.length = data.rotations.length := List.length_map _
  have hflat : part.rotations.flatten.length ≤ 2 * m := by
    have hsub := (hc.1.subperm (fun d hd => List.mem_range.mpr (hc.2.2.2.1 d hd))).length_le
    simpa only [List.length_range] using hsub
  have hactLen : part.activeDarts.length ≤ data.activeDarts.length := List.length_filter_le _ _
  have hcode : (gm06EncodeRows part.rotations).length < 2 ^ w := by
    rw [gm06FaceCode_length, hlength]
    omega
  have hwords : ∀ x ∈ gm06EncodeRows part.rotations, x < 2 ^ w := by
    apply gm06EncodeRows_words
    · rw [hlength]
      omega
    · intro row hr
      have hrow := (List.sublist_flatten_of_mem hr).length_le
      have hq : 2 * m < 2 ^ w := by omega
      exact hrow.trans hflat |>.trans_lt hq
    · intro d hd
      have hq : 2 * m < 2 ^ w := by omega
      exact (hc.2.2.2.1 d hd).trans hq
  obtain ⟨sf, t, he, ht, hk, hout⟩ := gm06CutFaceIncidenceProg_exec part s hw hn hcap hc.1
    hc.2.2.2.1 hc.2.2.1 hc.2.1 hc.2.2.2.2 horigLen hvalues hquery hcode hwords
    (hactLen.trans_lt hactiveFit) h600 h604 h626 h648 h649 h672 h673
  have hpoly := gm06CutFaceIncidence_cost_le_polynomial n m part.rotations.length part.rotations.flatten.length part.activeDarts.length
  have hnorm : n + 2 * m + part.rotations.length + part.rotations.flatten.length + part.activeDarts.length + 1 ≤
      n + 2 * m + data.rotations.length + 2 * m + data.activeDarts.length + 1 := by rw [hlength]; omega
  obtain ⟨row, hrow, hmem⟩ := gm06CutFaceIncidence_inner_cuff data root hnd hcover hbound hcuff hroot hother hrootLive hotherLive
  exact ⟨sf, t, he, ht.trans (hpoly.trans (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left hnorm 2))), hk,
    hout, row, hout.trans hrow, hmem⟩

end GraphMinor.Compute
