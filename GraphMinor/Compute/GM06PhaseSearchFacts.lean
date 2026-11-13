module

public import GraphMinor.Compute.GM06Reduction4Phase
public import GraphMinor.Compute.GM06CutFaceFacts
public import GraphMinor.Compute.GM06CandidateInput

/-!
# Bounds passed from selected faces to Reduction 4 searches

Sections 10, 12 and 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
use the computed face's incidence and the path returned by FIND_4.
Successful face decoding gives exactly the two incidence tables and
uses only darts of the component. A successful directed search has
a valid contact, word-bounded darts and at most as many edges as
there are copied vertex slots. These facts justify the final splice.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Every dense incidence entry is either zero or one. -/
theorem gm06IncidenceBits_words (n : ℕ) (labels : List ℕ) :
    ∀ a ∈ gm06IncidenceBits n labels, a = 0 ∨ a = 1 := by
  intro a ha
  obtain ⟨v, hv⟩ := List.mem_ofFn.mp ha
  rw [← hv]
  split <;> simp

/-- A successful numeric selected-face query gives the actual row,
its exact incidence tables, and the dart and length bounds used by FIND_4. -/
theorem gm06CutFaceIncidence_some_facts {n m target : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (ht : target < 2 * m) {row incV incE : List ℕ}
    (h : gm06CutFaceIncidence n m data target = some (row, incV, incE)) :
    incV = gm06IncV n data.origins row ∧ incE = gm06IncE m row ∧ row.Nodup ∧
      row.length ≤ 2 * m ∧ (∀ d ∈ row, d ∈ data.rotations.flatten) ∧
      ∀ e, e < m → incE[e]?.getD 0 ≠ 0 →
        2 * e ∈ data.rotations.flatten ∧ 2 * e + 1 ∈ data.rotations.flatten := by
  let rows := data.rotations.map (gm06FinLabels (2 * m))
  let active := gm06FinLabels (2 * m) data.activeDarts
  have hfin := gm06CutFiniteRows_valid data hnd hkeys hactive hcover hpair
  change (if ht : target < 2 * m then
    gm06SelectedFaceIncidence n data.origins rows active ⟨target, ht⟩ else none) = some (row, incV, incE) at h
  simp only [ht, ↓reduceDIte, gm06SelectedFaceIncidence] at h
  obtain ⟨face, hface, heq⟩ := Option.map_eq_some_iff.mp h
  have hrow : face.map Fin.val = row := congrArg Prod.fst heq
  have hincV : gm06IncV n data.origins (face.map Fin.val) = incV := congrArg (fun p => p.2.1) heq
  have hincE : gm06IncE m (face.map Fin.val) = incE := congrArg (fun p => p.2.2) heq
  have hmem := (gm06SelectFaceRow_some (gm06ActiveFaceRows rows active) ⟨target, ht⟩ face hface).1
  have hspec := gm06ActiveFaceRows_spec rows active hfin.1 hfin.2.1 hfin.2.2
  have hfaceNd : face.Nodup := hspec.1.sublist (List.sublist_flatten_of_mem hmem)
  have hrowNd : row.Nodup := hrow ▸ hfaceNd.map Fin.val_injective
  have hrowLen : row.length ≤ 2 * m := by
    rw [← hrow, List.length_map]
    simpa only [Fintype.card_fin] using hfaceNd.length_le_card
  have hsub : ∀ d ∈ row, d ∈ data.rotations.flatten := by
    intro d hd
    rw [← hrow] at hd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hd
    have hqa : q ∈ active := (hspec.2.1 q).mp (List.mem_flatten.mpr ⟨face, hmem, hq⟩)
    exact (hcover q.val).mp ((gm06FinLabels_mem_iff data.activeDarts hactive q).mp hqa)
  have hrotMate : ∀ d ∈ data.rotations.flatten, gm06DartMate d ∈ data.rotations.flatten :=
    fun d hd => (hcover _).mp (hpair d ((hcover d).mpr hd))
  refine ⟨by simpa only [hrow] using hincV.symm, by simpa only [hrow] using hincE.symm,
    hrowNd, hrowLen, hsub, ?_⟩
  intro e he hnonzero
  apply gm06IncE_complete_pair row data.rotations he hsub hrotMate
  have htable : incE = gm06IncE m row := by simpa only [hrow] using hincE.symm
  rw [← htable]
  exact hnonzero

/-- Finite-label conversion preserves every valid numeric step. -/
theorem gm06PhaseFinSteps_map_val {n : ℕ} (hn : 0 < n) (steps : List (ℕ × ℕ))
    (hvalues : ∀ p ∈ steps, p.2 < n) :
    (gm06PhaseFinSteps n hn steps).map (fun p => (p.1, p.2.val)) = steps := by
  unfold gm06PhaseFinSteps
  rw [List.map_map]
  conv_rhs => rw [← List.map_id steps]
  apply List.map_congr_left
  intro p hp
  exact Prod.ext rfl (Nat.mod_eq_of_lt (hvalues p hp))

/-- Successful numeric FIND_4 gives a positive contact within the
old path, bounded directed darts, and a replacement length at most n. -/
theorem gm06PhaseFind4Words_bounds {n m source j : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper : List ℕ) (steps : List (ℕ × ℕ)) (darts : List ℕ)
    (horig : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (h : gm06PhaseFind4Words n m origins ordinary incV incE upper source steps = some (j, darts)) :
    0 < j ∧ j ≤ steps.length ∧ darts.length ≤ n ∧ ∀ d ∈ darts, d < 2 * m := by
  by_cases hn : 0 < n
  · simp only [gm06PhaseFind4Words, hn, ↓reduceDIte] at h
    let start : Fin n := ⟨source % n, Nat.mod_lt _ hn⟩
    let finSteps := gm06PhaseFinSteps n hn steps
    have hs := gm06Find4Darts_sound origins ordinary incV incE upper start finSteps horig hvalues j darts h
    have hc := gm06Reduction4Contacts_bounds incV incE start.val
      (finSteps.map (fun p => (p.1, p.2.val))) hs.1
    have hlen : finSteps.length = steps.length := by simp only [finSteps, gm06PhaseFinSteps, List.length_map]
    have hbound : ∀ d ∈ darts, d < 2 * m := by
      intro d hd
      exact (gm06CandidateDarts_mem_iff m origins ordinary incV incE upper
        (gm06Find4PathVertices start finSteps) j d).mp (hs.2.2.2 d hd) |>.1
    obtain ⟨result, hfind, hresult⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨q, vertices⟩ := result
    obtain ⟨_, p, hp, hpwords⟩ := gm06Find4_sound (gm06CandidateEnds m origins) ordinary incV incE upper
      start finSteps q vertices hfind
    have hvertices : vertices.length ≤ n := by
      rw [← hpwords, List.length_map]
      simpa only [Fintype.card_fin] using hp.support_nodup.length_le_card
    have hdarts := congrArg Prod.snd hresult
    simp only [Prod.fst, Prod.snd] at hdarts
    have hpathLen : darts.length ≤ vertices.length := by
      rw [← hdarts]
      simp only [gm06PathDarts, List.length_map, List.length_zip]
      exact Nat.min_le_left _ _
    simp only [List.length_map, hlen] at hc
    exact ⟨hc.1, hc.2, hpathLen.trans hvertices, hbound⟩
  · simp only [gm06PhaseFind4Words, hn, ↓reduceDIte, reduceCtorEq] at h

end GraphMinor.Compute
