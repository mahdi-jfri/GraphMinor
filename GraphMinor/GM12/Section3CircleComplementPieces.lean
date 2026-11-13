module

public import GraphMinor.GM12.Section3CircleIntersectionGraph
import GraphMinor.GM12.Section3ArcPieces

/-!
# Finitely many pieces outside a circle in a finite graph

For the remaining extraction step used by XII (3.1), page 245, delete
one circle from a finite graph. An edge contained in the circle
contributes nothing. Every other edge meets the circle only at graph
vertices. An interval with finitely many points removed has finitely
many connected pieces. Taking the finite union over the edges and
vertices proves the same statement for the remaining carrier.
-/

public section

namespace GraphMinor.GM12

open Set Surface

private theorem finConn_sUnion_finite
    {S : Type*} [TopologicalSpace S] {K : Set (Set S)} (hK : K.Finite)
    (h : ∀ B ∈ K, FinConn B) : FinConn (⋃₀ K) := by
  induction K, hK using Set.Finite.induction_on with
  | empty => simpa using (finConn_of_isPreconnected (isPreconnected_empty : IsPreconnected (∅ : Set S)))
  | @insert B K hnot hK ih =>
    rw [sUnion_insert]
    exact (h B (mem_insert B K)).union (ih (fun C hC => h C (mem_insert_of_mem B hC)))

private theorem finConn_arc_diff_of_finite_intersection
    {S : Type*} [TopologicalSpace S] {e A : Set S} {u v : S}
    (hL : IsLineWithEnds e u v) (hfin : (e ∩ A).Finite) : FinConn (e \ A) := by
  obtain ⟨p, hp, heq, _, _⟩ := hL.exists_arc
  have himage : p '' Icc (0 : unitInterval) 1 = e := by
    have hI : Icc (0 : unitInterval) 1 = univ := by
      ext t
      simp only [mem_Icc, mem_univ, iff_true]
      exact ⟨unitInterval.nonneg t, unitInterval.le_one t⟩
    rw [hI, image_univ, heq]
  have hcontact : ((p '' Icc (0 : unitInterval) 1) ∩ A).Finite := himage.symm ▸ hfin
  have h := finConn_subarc_diff_set_and_segments hp 0 1 hcontact
    (∅ : Finset Unit) (fun _ => 0) (fun _ => 0)
  simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty, himage] using h

/-- Deleting a circle from a finite graph leaves a finite union of
connected sets, even when the circle includes some complete edges. -/
theorem finConn_gr_diff_circle
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hG : IsGraph V E)
    {A : Set S} (hA : IsOArc A) (hAG : A ⊆ gr V E) : FinConn (gr V E \ A) := by
  have hedge : ∀ e ∈ E, FinConn (e \ A) := by
    intro e he
    rcases hG.edge_or hA hAG he with hsub | hdisj
    · rw [sdiff_eq_empty.mpr hsub]
      exact finConn_of_isPreconnected isPreconnected_empty
    · obtain ⟨u, v, _, hL, _⟩ := hG.edge e he
      apply finConn_arc_diff_of_finite_intersection hL
      apply hG.fin.subset
      rintro x ⟨hxe, hxA⟩
      by_contra hxV
      exact Set.disjoint_left.mp hdisj ⟨hxe, hxV⟩ hxA
  have hvertices : FinConn (V \ A) := by
    have hfinite : (V \ A).Finite := hG.fin.subset sdiff_subset
    have hpieces := finConn_sUnion_finite (hfinite.image (fun x : S => ({x} : Set S)))
      (by rintro _ ⟨x, _, rfl⟩; exact finConn_of_isPreconnected isPreconnected_singleton)
    have heq : ⋃₀ ((fun x : S => ({x} : Set S)) '' (V \ A)) = V \ A := by
      ext x
      simp
    exact heq ▸ hpieces
  have hpieces := finConn_sUnion_finite (hG.fine.image (fun e => e \ A))
    (by rintro _ ⟨e, he, rfl⟩; exact hedge e he)
  have heq : ⋃₀ ((fun e => e \ A) '' E) = (⋃₀ E) \ A := by
    ext x
    simp only [mem_sUnion, mem_image, exists_exists_and_eq_and, mem_sdiff]
    constructor
    · rintro ⟨e, he, hx, hn⟩
      exact ⟨⟨e, he, hx⟩, hn⟩
    · rintro ⟨⟨e, he, hx⟩, hn⟩
      exact ⟨e, he, hx, hn⟩
  change FinConn ((V ∪ ⋃₀ E) \ A)
  rw [union_sdiff_distrib]
  exact hvertices.union (heq ▸ hpieces)

end GraphMinor.GM12
