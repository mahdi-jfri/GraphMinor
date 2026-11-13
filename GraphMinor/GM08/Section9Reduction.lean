module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section11Inside
import GraphMinor.GM08.Section9Foundation
import GraphMinor.GM08.Section9Truncation
import GraphMinor.GM08.Section9Sleeve
import GraphMinor.GM11.OArcCircuit

/-!
# The contradiction after a foundation ring is found in VIII (9.1)

Once a foundation ring encloses the first circuit of the nest, retain
`k / 2 + 1` enclosed circuits and trim the radial paths into the sleeve.
The sleeve count contradicts the nest count. A ring with no vertices
has an empty sleeve, which also handles boundary size one.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The sleeve contradiction in Graph Minors VIII (9.1), pages 269–270:
no foundation ring encloses the first circuit of an `(r,s)`-nest in a
truncation when `r,s` are at least the boundary size. This uses the
extra enclosed circuit for even boundary size to correct the small case. -/
theorem IsTruncationInducedBy.not_encloses_first {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hman : ∀ x : S, IsManifoldPoint x)
    {D Dstar : Drawing S} {Δ : Set S} {t : ℕ} {F : Fin t → Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (h : IsTruncationInducedBy D Δ F Dstar) {r s : ℕ} (N : DrawingNest Dstar Δ r s)
    (hpos : 0 < s) (hr : (D.V ∩ discBd Δ).ncard ≤ r)
    (hs : (D.V ∩ discBd Δ).ncard ≤ s) (i : Fin t) :
    ¬ OArcEncloses Δ (F i) (N.circuit ⟨0, hpos⟩).U := by
  intro henc
  have hcard := h.1.ring_card_lt_boundary_card i
  have hk : 0 < (D.V ∩ discBd Δ).ncard := Nat.zero_lt_of_lt hcard
  by_cases hk2 : 2 ≤ (D.V ∩ discBd Δ).ncard
  · obtain ⟨Γ, hΓ, ⟨NΓ⟩⟩ :=
      h.exists_sleeve_nest_of_encloses_first hman hΔ hDU i N hk2 hr hs henc
    exact no_large_nest_in_sleeve hΔ hDU hΓ hk hcard hr NΓ
  · have hk1 : (D.V ∩ discBd Δ).ncard = 1 := by omega
    obtain ⟨Γ, hΓ, hpoints⟩ := h.exists_sleeve_containing_enclosed_points hΔ hDU i
    let C₀ := N.circuit ⟨0, hpos⟩
    have hCΓ : C₀.U ⊆ Γ.U := by
      intro x hx
      apply hpoints x (C₀.U_sub_drawing hx)
      by_cases hxF : x ∈ F i
      · exact Or.inr hxF
      · exact Or.inl (henc x ⟨hx, hxF⟩)
    obtain ⟨C, hC, hCsub, _⟩ := GM11.exists_circuit_of_oArc C₀.isOArc_U hCΓ
    obtain ⟨u, W, _, _, hV, _⟩ := hC
    have hu : u ∈ C.V := by rw [hV]; exact W.start_mem_support
    have hΓpos := hΓ.boundary_card_pos_of_nonempty ⟨u, hCsub.1 hu⟩
    omega

/-- The sleeve contradiction of (9.1) with the disc itself as ambient surface.
The disc supplies all manifold charts needed to cut the radial paths. -/
theorem IsTruncationInducedBy.not_encloses_first_disc {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedDisc (univ : Set S))
    {D Dstar : Drawing S} {t : ℕ} {F : Fin t → Set S}
    (h : IsTruncationInducedBy D univ F Dstar) {r s : ℕ} (N : DrawingNest Dstar univ r s)
    (hpos : 0 < s) (hr : (D.V ∩ discBd (univ : Set S)).ncard ≤ r)
    (hs : (D.V ∩ discBd (univ : Set S)).ncard ≤ s) (i : Fin t) :
    ¬ OArcEncloses univ (F i) (N.circuit ⟨0, hpos⟩).U :=
  h.not_encloses_first (isManifoldPoint_of_univ hS) hS (subset_univ _) N hpos hr hs i

end GraphMinor.GM08
