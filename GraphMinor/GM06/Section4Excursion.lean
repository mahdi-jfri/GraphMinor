module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# An excursion between consecutive boundary vertices

For the uncrossing step in Graph Minors VI, Section 4, page 124, choose a
shortest subpath meeting the inside of the chosen disc, with its two ends on
the chosen path boundary. If an inner vertex were also on that boundary,
one of the two shorter pieces would still meet the inside. Thus only the
ends belong to the prescribed boundary vertex set.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem walkDrawing_append_U
    {S : Type u} [TopologicalSpace S] [T1Space S] (Q : Drawing S) {s u t : S}
    (L : GraphWalk Q.toGraph s u) (R : GraphWalk Q.toGraph u t) :
    (walkDrawing Q (L.append R)).U = (walkDrawing Q L).U ∪ (walkDrawing Q R).U := by
  ext x
  simp only [mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append, mem_union]
  constructor
  · rintro ((hL | hR) | ⟨e, heL | heR, hxe⟩)
    · exact Or.inl (Or.inl hL)
    · exact Or.inr (Or.inl hR)
    · exact Or.inl (Or.inr ⟨e, heL, hxe⟩)
    · exact Or.inr (Or.inr ⟨e, heR, hxe⟩)
  · rintro ((hL | ⟨e, heL, hxe⟩) | (hR | ⟨e, heR, hxe⟩))
    · exact Or.inl (Or.inl hL)
    · exact Or.inr ⟨e, Or.inl heL, hxe⟩
    · exact Or.inl (Or.inr hR)
    · exact Or.inr ⟨e, Or.inr heR, hxe⟩

private theorem isSimple_append_right
    {S : Type u} [TopologicalSpace S] {Q : Drawing S} {s u t : S}
    (L : GraphWalk Q.toGraph s u) (R : GraphWalk Q.toGraph u t)
    (h : (L.append R).IsSimple) : R.IsSimple := by
  induction L with
  | nil _ => exact h
  | cons hl r ih => exact ih R h.of_cons

private theorem isSimple_append_left
    {S : Type u} [TopologicalSpace S] {Q : Drawing S} {s u t : S}
    (L : GraphWalk Q.toGraph s u) (R : GraphWalk Q.toGraph u t)
    (h : (L.append R).IsSimple) : L.IsSimple := by
  induction L with
  | nil _ => exact List.nodup_singleton _
  | cons hl r ih =>
    have hnot := (List.nodup_cons.mp h).1
    have hr := (List.nodup_cons.mp h).2
    exact List.nodup_cons.mpr ⟨fun hx => hnot ((GraphWalk.mem_support_append r R).mpr (Or.inl hx)),
      ih R hr⟩

/-- A shortest path meeting a set, with distinct ends in a specified vertex
set, has no other vertex in that set. This isolates the excursion used for
Graph Minors VI, Section 4, page 124. -/
theorem exists_subpath_meeting_with_no_internal_vertex
    {S : Type u} [TopologicalSpace S] [T1Space S] {Q : Drawing S} {s t : S}
    (hQ : IsPathDrawing Q s t) {B X : Set S} (hs : s ∈ B) (ht : t ∈ B)
    (hst : s ≠ t) (hmeet : (Q.U ∩ X).Nonempty) :
    ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧ ∃ R : Drawing S,
      IsSubpathOf Q R u v ∧ (R.U ∩ X).Nonempty ∧ R.V ∩ B ⊆ {u, v} := by
  classical
  obtain ⟨W₀, hW₀, hV₀, hE₀⟩ := hQ.1
  have hQeq : walkDrawing Q W₀ = Q := by
    apply Drawing.ext_of_V_E
    · rw [walkDrawing_V, hV₀]
    · rw [walkDrawing_E, hE₀]
  let C : ℕ → Prop := fun n => ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧
    ∃ W : GraphWalk Q.toGraph u v, W.IsSimple ∧
      ((walkDrawing Q W).U ∩ X).Nonempty ∧ W.length = n
  have hex : ∃ n, C n := by
    refine ⟨W₀.length, s, hs, t, ht, hst, W₀, hW₀, ?_, rfl⟩
    rw [hQeq]
    exact hmeet
  obtain ⟨u, hu, v, hv, huv, W, hW, hWX, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ {a b : S}, a ∈ B → b ∈ B → a ≠ b →
      ∀ T : GraphWalk Q.toGraph a b, T.IsSimple → ((walkDrawing Q T).U ∩ X).Nonempty →
        Nat.find hex ≤ T.length := by
    intro a b ha hb hab T hT hTX
    exact Nat.find_min' hex ⟨a, ha, b, hb, hab, T, hT, hTX, rfl⟩
  let R := walkDrawing Q W
  have hRQ : R.IsSubdrawing Q := walkDrawing_isSubdrawing Q W
  refine ⟨u, hu, v, hv, huv, R,
    ⟨hRQ, hRQ.U_subset, isPathDrawing_walkDrawing_of_isSimple Q hW huv⟩, hWX, ?_⟩
  intro x hx
  by_cases hxu : x = u
  · exact Or.inl hxu
  by_cases hxv : x = v
  · exact Or.inr hxv
  have hxW : x ∈ W.support := by
    have hxR := hx.1
    rw [walkDrawing_V] at hxR
    exact hxR
  obtain ⟨L, T, hsplit⟩ := W.exists_append_of_mem hxW
  have hLT : (L.append T).IsSimple := hsplit ▸ hW
  have hL := isSimple_append_left L T hLT
  have hT := isSimple_append_right L T hLT
  have hLpos : 0 < L.length := Nat.pos_of_ne_zero (fun h =>
    hxu (GraphWalk.eq_of_length_eq_zero h).symm)
  have hTpos : 0 < T.length := Nat.pos_of_ne_zero (fun h =>
    hxv (GraphWalk.eq_of_length_eq_zero h))
  have hlength : W.length = L.length + T.length := by rw [hsplit, GraphWalk.length_append]
  have hpieces : ((walkDrawing Q L).U ∩ X).Nonempty ∨ ((walkDrawing Q T).U ∩ X).Nonempty := by
    obtain ⟨z, hz, hzX⟩ := hWX
    rw [hsplit, walkDrawing_append_U] at hz
    exact hz.elim (fun hzL => Or.inl ⟨z, hzL, hzX⟩) (fun hzT => Or.inr ⟨z, hzT, hzX⟩)
  rcases hpieces with hLX | hTX
  · have hle := hmin hu hx.2 (Ne.symm hxu) L hL hLX
    omega
  · have hle := hmin hx.2 hv hxv T hT hTX
    omega

end GraphMinor.GM06
