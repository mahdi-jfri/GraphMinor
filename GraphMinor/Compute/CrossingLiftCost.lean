module

public import GraphMinor.Compute.SpecsCrossingRec

/-!
# Counting the records that need path work

Section 12 of the crossing note `docs/crossing/crossing_extractor.tex` bounds the accepted
replacements and contractions by the number of original vertices. Each replacement deletes a
nonempty set, since its recorded component is connected and nonempty. Each contraction deletes one
vertex. Deletions never increase the vertex set. Thus the number of records needing path work, plus
the number of remaining vertices, is at most the original number of vertices.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- The number of replacements and contractions. Deletion records keep both paths unchanged. -/
def liftWorkCount {V : Type*} : List (CrossRecord V) → ℕ
  | [] => 0
  | .repl _ :: rs => liftWorkCount rs + 1
  | .contr _ :: rs => liftWorkCount rs + 1
  | .del _ _ :: rs => liftWorkCount rs

private theorem replacement_drops_card {N : ℕ} {r : ReplRecord (Fin N)} {D : List (Fin N)}
    (h : r.IsValid D) : r.newVerts.ncard < r.verts.ncard := by
  obtain ⟨x, hx⟩ := h.2.2.2.2.2.2.1.1
  have hxdel : x ∈ r.deleted := h.2.2.2.2.2.1 hx
  have hxverts : x ∈ r.verts := h.1 hxdel
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
  intro heq
  have hxnew : x ∈ r.newVerts := heq.symm ▸ hxverts
  exact hxnew.2 hxdel

private theorem contraction_drops_card {N : ℕ} {r : ContractRecord (Fin N)}
    (h : r.IsValid) : r.newVerts.ncard < r.verts.ncard := by
  have hu : r.u ∈ r.verts := h.1 h.2.2.1
  apply Set.ncard_lt_ncard (ht := Set.toFinite _)
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
  intro heq
  have hunew : r.u ∈ r.newVerts := heq.symm ▸ hu
  exact hunew.2 rfl

/-- Section 12's vertex accounting for any history on `Fin N`. The only hypothesis is the
history itself. Initial support, cleanliness, and cycle length assumptions are not needed. -/
theorem liftWorkCount_add_card_le {N : ℕ} {G G' : SimpleGraph (Fin N)}
    {S S' : Set (Fin N)} {D D' : List (Fin N)} {rs : List (CrossRecord (Fin N))}
    (h : IsHistory (G, S, D) rs (G', S', D')) :
    liftWorkCount rs + S'.ncard ≤ S.ncard := by
  induction rs generalizing G S D with
  | nil =>
    cases h
    simp [liftWorkCount]
  | cons r rs ih =>
    cases r with
    | repl r =>
      obtain ⟨rfl, rfl, hv, ht⟩ := h
      have hi := ih ht
      have hd := replacement_drops_card hv
      simp only [liftWorkCount]
      omega
    | contr r =>
      obtain ⟨rfl, rfl, rfl, hv, ht⟩ := h
      have hi := ih ht
      have hd := contraction_drops_card hv
      simp only [liftWorkCount]
      omega
    | del H T =>
      obtain ⟨_, hsub, _, _, _, ht⟩ := h
      have hi := ih ht
      have hc := Set.ncard_le_ncard hsub
      exact hi.trans hc

/-- There are at most `N` records requiring path work in a history on `Fin N`. -/
theorem liftWorkCount_le {N : ℕ} {G G' : SimpleGraph (Fin N)}
    {S S' : Finset (Fin N)} {D D' : List (Fin N)} {rs : List (CrossRecord (Fin N))}
    (h : IsHistoryFin G S D rs G' S' D') : liftWorkCount rs ≤ N := by
  have hi := liftWorkCount_add_card_le h
  have hc : (S : Set (Fin N)).ncard ≤ N := by
    simpa using Set.ncard_le_ncard (Set.subset_univ (S : Set (Fin N)))
  omega

/-- Charging `N + 1` steps of path work per nondeletion record fits the quadratic part of the
corrected lift interface. The record scan itself is charged separately to the used buffer. -/
theorem liftWorkCount_mul_le {N : ℕ} {G G' : SimpleGraph (Fin N)}
    {S S' : Finset (Fin N)} {D D' : List (Fin N)} {rs : List (CrossRecord (Fin N))}
    (h : IsHistoryFin G S D rs G' S' D') :
    liftWorkCount rs * (N + 1) ≤ (N + 1) * (N + 1) := by
  exact Nat.mul_le_mul_right (N + 1) (Nat.le_trans (liftWorkCount_le h) (Nat.le_succ N))

end GraphMinor.Compute.Crossing
