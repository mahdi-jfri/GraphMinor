module

public import GraphMinor.GM08.Section9
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section9RingPaths
import GraphMinor.GM08.Section9Paths
import GraphMinor.GM07.Section9MoveOff

/-!
# Linkage of the parallel rings in VIII (9.3)

The radial paths of a nest cross both parallel rings. The boundary
linkage paths cross the inner ring on their way to the boundary of the
disc. Shortening these paths gives both path bounds in VII (9.4).
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A family of `n` disjoint paths gives a lower bound for the maximum
number of disjoint paths. Finiteness of the drawing bounds that maximum. -/
theorem le_maxDisjointPaths_of_paths {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {X Y : Set S} {n : ℕ}
    (h : GM07.HasDisjointPathsBetween D X Y n) : n ≤ GM07.maxDisjointPaths D X Y := by
  exact le_csSup ⟨D.V.ncard, fun _ hk => GM07.hasDisjointPathsBetween_le_ncard_V hk⟩ h

/-- The radial paths of the nest give the path bound between its two
normal parallel rings in the application of VII (9.4) to VIII (9.3). -/
theorem DrawingNest.le_maxDisjointPaths_parallel_rings {S : Type u}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {D : Drawing S} {Δ B₁ B₂ : Set S} (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 2 ≤ s)
    (hB₁ : IsClosedDisc B₁) (hB₂ : IsClosedDisc B₂)
    (hB₁₂ : B₁ ⊆ B₂) (hB₂Δ : B₂ ⊆ Δ)
    (hn₁ : D.IsNormal (discBd B₁)) (hn₂ : D.IsNormal (discBd B₂))
    (hi : (N.circuit ⟨0, by omega⟩).ins ⊆ B₁)
    (ho : B₂ ⊆ discInt (N.circuit ⟨s - 1, by omega⟩).ins) :
    r ≤ GM07.maxDisjointPaths D (discBd B₁) (discBd B₂) := by
  obtain ⟨P, a, b, hP, hdis⟩ := N.exists_radial_path_drawings hΔ hs
  apply le_maxDisjointPaths_of_paths
  apply hasDisjointPathsBetween_normal_discs hΔ hB₁ hB₂ hB₁₂ hB₂Δ hDU hn₁ hn₂ P a b
  · intro i
    refine ⟨(hP i).1, (hP i).2.1, hi ?_, ?_⟩
    · have ha := (hP i).2.2.1
      rw [← (N.circuit _).isInside.2.2.1] at ha
      exact discBd_subset _ ha
    · intro hb
      exact (ho (discInt_subset _ hb)).2
        ((N.circuit _).isInside.2.2.1 ▸ (hP i).2.2.2.1)
  · exact hdis

/-- Boundary linkage of the nest gives the second path bound of VII
(9.4): there are as many paths from the inner parallel ring to the
ambient boundary as there are drawing vertices on that boundary. -/
theorem DrawingNest.boundary_le_maxDisjointPaths_parallel_ring {S : Type u}
    [TopologicalSpace S] [T2Space S]
    {D : Drawing S} {Δ B : Set S} (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    {r s : ℕ} (N : DrawingNest D Δ r s) (hs : 0 < s)
    (hBL : IsBoundaryLinkedNest D Δ N)
    (hB : IsClosedDisc B) (hBΔ : B ⊆ Δ)
    (hn : D.IsNormal (discBd B)) (hbd : D.IsNormal (discBd Δ))
    (hi : (N.circuit ⟨0, hs⟩).ins ⊆ B) :
    (D.V ∩ discBd Δ).ncard ≤ GM07.maxDisjointPaths D (discBd B) (discBd Δ) := by
  obtain ⟨P, hP, hdis⟩ := hBL
  choose hs' a b hsub ha hb hpath using hP
  apply le_maxDisjointPaths_of_paths
  apply hasDisjointPathsBetween_normal_discs hΔ hB hΔ hBΔ (Subset.refl _) hDU hn hbd P a b
  · intro i
    refine ⟨hsub i, hpath i, hi ?_, ?_⟩
    · have ha' : a i ∈ (N.circuit ⟨0, hs⟩).U := ha i
      rw [← (N.circuit _).isInside.2.2.1] at ha'
      exact discBd_subset _ ha'
    · exact fun hx => hx.2 (hb i)
  · exact hdis

end GraphMinor.GM08
