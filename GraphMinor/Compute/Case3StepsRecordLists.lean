module

public import GraphMinor.Compute.Case3StepsRecordValidation
public import GraphMinor.Compute.Case3StepsScanRecords

/-!
# Member lists lie inside the compass lists

Each compact member vertex maps through the increasing member inclusion.
Each of its directed copies comes from the routed graph, whose
multiplicity is bounded by the compact compass. Thus both lists of every
member record occur in the original-label compass lists.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

/-- Renamed member vertices and full copies belong to the compass lists. -/
theorem case3SelectedRecord_lists_subset {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (i : Case3SelectedGroup x Z) (code : List ℕ) :
    let r := case3SelectedRecord x D Z e i code
    (∀ v ∈ r.vList, v ∈ List.ofFn (fun u : Fin x.n => (e u).1)) ∧
      (∀ a ∈ r.eList, a ∈ D.multiEdgeTriples.map (origEdgeEmb e e.injective)) := by
  dsimp only
  let A := case3SelectedMember x Z i
  let inc := A.verts.orderEmbOfFin rfl
  let orig := e ∘ inc
  have hinj := e.injective.comp inc.injective
  constructor
  · intro v hv
    change v ∈ (List.finRange A.verts.card).map (fun u => origVertexEmb orig hinj u.1) at hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    rw [origVertexEmb_apply_val]
    exact List.mem_ofFn.mpr ⟨inc u, rfl⟩
  · intro a ha
    change a ∈ (case3CompactMember x D Z i).multiEdgeTriples.map (origEdgeEmb orig hinj) at ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    have hb' := ((case3CompactMember x D Z i).mem_multiEdgeTriples_iff b).mp hb
    rcases b with ⟨u, v, q⟩
    obtain ⟨hu, hv, hq⟩ := hb'
    let u' : Fin A.verts.card := ⟨u, hu⟩
    let v' : Fin A.verts.card := ⟨v, hv⟩
    have hqD : q < D.edgeMult (inc u') (inc v') :=
      lt_of_lt_of_le hq (case3RoutedMember_le x D Z (case3RawIndexLabel x i.1) (inc u') (inc v'))
    refine List.mem_map.mpr ⟨((inc u').1, (inc v').1, q), ?_, ?_⟩
    · exact (D.mem_multiEdgeTriples_iff _).mpr ⟨(inc u').2, (inc v').2, hqD⟩
    · change (origVertexEmb e e.injective (inc u').1,
        origVertexEmb e e.injective (inc v').1, q) =
          (origVertexEmb orig hinj u, origVertexEmb orig hinj v, q)
      rw [origVertexEmb_apply_val, origVertexEmb_apply_val,
        origVertexEmb_apply_val orig hinj u', origVertexEmb_apply_val orig hinj v']
      rfl

end GraphMinor.Compute
