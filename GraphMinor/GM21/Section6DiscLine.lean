module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.RegionCurve
import GraphMinor.GM06.RegionLocal
import GraphMinor.GM06.Euler
import GraphMinor.GM06.Section3Main
import GraphMinor.GM07.Section11

/-!
# Graph Minors XXI, Section 6: a good line through a region of a disc

The proofs of (6.5), (6.6) and (6.7) in *Graph Minors XXI* (pages 26–29 of the preprint) draw lines
through regions: "let $F_i$ be a good line with ends $a_i, b_i$ and with interior in $r_i$", and
"there is a proper line $F \subseteq \Sigma$ with ends $a, b \in V(\Gamma)$, and with
$F \cap U(\Gamma) = \{a, b\}$". This file proves that such a line exists
(`exists_line_in_region`): if `a ≠ b` are vertices of a proper drawing `Γ` in a closed disc `Σ`,
both in `bd(Σ)` and in the closure of a region `r`, then there is a line with ends `a, b` whose
other points lie in `r \ bd(Σ)`.

From each end a curve enters `r \ bd(Σ)` at once (`GM06.exists_region_entry_path_of_mem_U`), and
`r \ bd(Σ)` is path connected, since it is open and preconnected
(`GM06.isPreconnected_sdiff_bd_of_isOpen`). So `a` and `b` are joined inside
`{a} ∪ (r \ bd(Σ)) ∪ {b}`, and a path between distinct points of a Hausdorff space contains an arc
(`GM07.joinedIn_iff_eq_or_exists_isLineWithEnds`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace DiscLine

open Set Topology GraphMinor.Surface GraphMinor.GM06 unitInterval

universe w

variable {S : Type w} [TopologicalSpace S]

/-- A region of a proper drawing in a closed disc, without `bd(Σ)`, is path connected. -/
theorem isPathConnected_region_sdiff_bd (hS : IsClosedDiscSpace S) (Γ : Drawing S) {r : Set S}
    (hr : r ∈ Γ.R) : IsPathConnected (r \ bd S) := by
  have : LocallyPathConnectedSpace S := locallyPathConnectedSpace_of_isClosedDiscSpace hS
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  have ho : IsOpen r := isOpen_region hS Γ hr
  have hc : IsPreconnected r := (isPathConnected_region hS Γ hr).isConnected.isPreconnected
  have hne : r.Nonempty := (isPathConnected_region hS Γ hr).nonempty
  have ho' : IsOpen (r \ bd S) := ho.sdiff (isClosed_bd_of_isClosedDiscSpace hS)
  exact ho'.isConnected_iff_isPathConnected.mp
    ⟨open_sdiff_bd_nonempty hS ho hne, isPreconnected_sdiff_bd_of_isOpen hS ho hc⟩

/-- A point of `U(Γ)` in the closure of a region `r` is joined to every point of `r \ bd(Σ)` inside
`{p} ∪ (r \ bd(Σ))`. -/
theorem joinedIn_of_mem_closure (hS : IsClosedDiscSpace S) {Γ : Drawing S} (hΓ : Γ.IsProper)
    {r : Set S} (hr : r ∈ Γ.R) {p : S} (hpU : p ∈ Γ.U) (hp : p ∈ closure r) {z : S}
    (hz : z ∈ r \ bd S) : JoinedIn ({p} ∪ (r \ bd S)) p z := by
  obtain ⟨α, h0, h1⟩ := exists_region_entry_path_of_mem_U Γ hS hΓ r hr p hp hpU
  have hα : JoinedIn ({p} ∪ (r \ bd S)) p (α 1) := by
    refine ⟨⟨α, h0, rfl⟩, fun t => ?_⟩
    rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with h2 | h2
    · have : t = 0 := Subtype.ext h2.symm
      change α t ∈ _
      rw [this, h0]
      exact Or.inl rfl
    · exact Or.inr (h1 t h2)
  have hmid : JoinedIn ({p} ∪ (r \ bd S)) (α 1) z :=
    ((isPathConnected_region_sdiff_bd hS Γ hr).joinedIn _ (h1 1 (by simp)) z hz).mono
      subset_union_right
  exact hα.trans hmid

/-- **A good line through a region** (Graph Minors XXI, proofs of (6.5)–(6.7), pages 25–28 of the
preprint). Let `Γ` be a proper drawing in a closed disc `Σ`, let `r` be a region of `Γ`, and let
`a ≠ b` be vertices of `Γ` in the closure of `r`. Then there is a line with ends `a, b` whose other
points lie in `r \ bd(Σ)`. -/
theorem exists_line_in_region (hS : IsClosedDiscSpace S) {Γ : Drawing S} (hΓ : Γ.IsProper)
    {r : Set S} (hr : r ∈ Γ.R) {a b : S} (haV : a ∈ Γ.V) (hbV : b ∈ Γ.V) (hab : a ≠ b)
    (har : a ∈ closure r) (hbr : b ∈ closure r) :
    ∃ F : Set S, IsLineWithEnds F a b ∧ F ⊆ {a, b} ∪ (r \ bd S) := by
  have : T2Space S := t2Space_of_isClosedDiscSpace hS
  obtain ⟨z, hz⟩ := (isPathConnected_region_sdiff_bd hS Γ hr).nonempty
  have ha := joinedIn_of_mem_closure hS hΓ hr (Γ.V_subset_U haV) har hz
  have hb := joinedIn_of_mem_closure hS hΓ hr (Γ.V_subset_U hbV) hbr hz
  have hZ : JoinedIn ({a, b} ∪ (r \ bd S)) a b := by
    refine (ha.mono ?_).trans (hb.mono ?_).symm
    · rintro x (rfl | hx)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hx
    · rintro x (rfl | hx)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr hx
  obtain ⟨F, hFZ, hF⟩ := ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds hZ.source_mem
    hZ.target_mem).mp hZ).resolve_left hab
  exact ⟨F, hF, hFZ⟩

/-- The line of `exists_line_in_region` meets `bd(Σ)` and `U(Γ)` only in its ends. -/
theorem inter_eq_of_subset_region {Γ : Drawing S} {r : Set S} (hr : r ∈ Γ.R) {a b : S}
    {F : Set S} (hF : F ⊆ {a, b} ∪ (r \ bd S)) :
    F ∩ bd S ⊆ {a, b} ∧ F ∩ Γ.U ⊆ {a, b} := by
  constructor
  · rintro x ⟨hxF, hxbd⟩
    rcases hF hxF with hx | hx
    · exact hx
    · exact (hx.2 hxbd).elim
  · rintro x ⟨hxF, hxU⟩
    rcases hF hxF with hx | hx
    · exact hx
    · rcases hr with ⟨z₀, -, rfl⟩
      exact ((connectedComponentIn_subset _ _ hx.1).2 hxU).elim

end DiscLine
end GM21
end GraphMinor
