module

public import GraphMinor.GM06.Alg34GapDiscLayout
public import GraphMinor.Compute.GM06Alg34DiscDualData

/-!
# Canonical cuff lookup and gap array bounds

The unique supplied cuff has no repeated vertex labels, so both its
length and its matching gap-list length are bounded by the vertex count.
The first-list dual operation agrees with the region lookup at that
unique cuff. These facts connect plain arrays to the geometric dual
lemmas without adding any input function.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- A represented disc has one matching cuff/gap pair and its cuff list is repetition-free. -/
theorem disc_layout_nodup (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S) :
    ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length ∧ L.Nodup := by
  obtain ⟨L, R, hL, hR, hlen⟩ := h.disc_layout hS
  have hmem : L ∈ X.drawing.cuffs := hL.symm ▸ List.mem_cons_self
  exact ⟨L, R, hL, hR, hlen, h.drawing.cuff_nodup L hmem⟩

/-- The live gap array has at most one word per supplied vertex. -/
theorem discGapWords_length_le (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S) :
    X.discGapWords.length ≤ X.drawing.n := by
  obtain ⟨L, R, _, hR, hlen, hLN⟩ := h.disc_layout_nodup hS
  rw [X.discGapWords_singleton R hR, List.length_map, hlen]
  simpa only [Fintype.card_fin] using List.Nodup.length_le_card hLN

/-- The plain dual update uses exactly the region lookup at the unique represented cuff. -/
theorem discDualData_eq_cuff (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S)
    (hR : 0 < X.drawing.regions.length) :
    ∃ c : Fin X.drawing.cuffs.length,
      X.discDualData = X.drawing.dualGapInput X.drawing.cuffs[c] hR (h.gap c).region := by
  obtain ⟨L₀, R, hL₀, hgroups, hlen₀⟩ := h.disc_layout hS
  let c : Fin X.drawing.cuffs.length := ⟨0, by
    rw [hL₀]
    simp only [List.length_cons, List.length_nil]
    omega⟩
  let L := X.drawing.cuffs[c]
  have hget : L = L₀ := by
    simp only [L, Fin.getElem_fin, c, hL₀, List.getElem_cons_zero]
  have hL : X.drawing.cuffs = [L] := hL₀.trans (congrArg (fun l => [l]) hget.symm)
  have hlen : R.length = L.length := hlen₀.trans (congrArg List.length hget.symm)
  have hg : List.ofFn (h.gap c).region = R := by
    simpa only [c, hgroups, List.getElem_cons_zero] using (h.gap c).region_list
  exact ⟨c, X.discDualData_eq L R hL hgroups hR hlen (h.gap c).region hg⟩

end GraphMinor.Compute.GM06GapInputRep
