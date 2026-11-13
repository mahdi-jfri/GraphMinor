module

public import GraphMinor.GM12.Section3MeetingCircleGraph
public import GraphMinor.GM12.Section3SurroundingUnique
public import GraphMinor.GM12.Section3PlanarHomotopicCircle
import GraphMinor.GM12.Section3PuncturedSurface
import GraphMinor.GM12.Section3PuncturedCuffs

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# A finite graph retaining the obstruction from two cuffs

In the circle-intersection reduction used by XII (3.1), page 245,
replace the second selected circle by two homotopic paths in a finite
graph. The graph cannot become planar after filling one cuff: its first
circle identifies that cuff, while the preserved homotopies would make
the second circle surround the same cuff. Uniqueness contradicts the
choice of distinct cuffs.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- Meeting circles around distinct prescribed cuffs contain a connected
finite graph which is not near-planar. The original intersection may
have infinitely many components. -/
theorem exists_nonNearPlanar_finite_graph_of_meeting_surrounding_circles
    {S : Type u} {ι : Type*} [TopologicalSpace S] [T2Space S]
    [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι)
    {i j : ι} (hij : i ≠ j) {F A : Set (discComplement Δ)}
    (hF : IsOArc F) (hA : IsOArc A) (hmeet : (F ∩ A).Nonempty)
    (hsi : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i)))
    (hsj : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ V E, IsGraph V E ∧ IsConnected (gr V E) ∧
      gr V E ⊆ F ∪ A ∧ ¬ GM07.IsNearPlanar (gr V E) := by
  let : ConnectedSpace (discComplement Δ) :=
    Subtype.connectedSpace (discComplement_isConnected hS Δ hΔ hdisj)
  have hsurface := discComplement_isSurface hS Δ hΔ hdisj
  obtain ⟨V, E, x, y, p, q, r, s, hG, hconn, _, hPQ, hAeq, hpr, hqs,
      hFG, hpaths, hsub⟩ :=
    exists_finite_graph_of_meeting_circles_with_homotopic_paths hsurface hF hA hmeet
  refine ⟨V, E, hG, hconn, hsub, ?_⟩
  rintro (hp | ⟨C, hC, hpC⟩)
  · exact hsi.2.2 (isPlanar_mono hFG hp)
  · have hC' := hC
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hC'
    obtain ⟨k, rfl⟩ := hC'
    have hsFk : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ k)) :=
      ⟨hC, isPlanarInCappedCuff_mono hFG hpC, hsi.2.2⟩
    have hsAk : GM07.SurroundsCuff A (Subtype.val ⁻¹' discBd (Δ k)) :=
      ⟨hC, planarInCappedCuff_of_homotopic_paths hsurface p q r s hPQ hA hAeq
        hpr hqs hpaths hpC, hsj.2.2⟩
    have hik := surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hF hsi hsFk
    have hjk := surrounding_cuff_index_unique hS Δ hΔ hdisj hcase hA hsj hsAk
    exact hij (hik.trans hjk.symm)

end GraphMinor.GM12
