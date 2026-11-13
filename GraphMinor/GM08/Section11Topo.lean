module

public import GraphMinor.GM08.Section11
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.DiscsInSurface

/-!
# The rings of a foundation, as discs

For the proof of Graph Minors VIII, (11.2) we need some plain facts about an O-arc `F` of a
foundation in the disc `S`.

* `F` bounds a closed disc `Σ = F ∪ ins F`, where `ins F` is the set of points inside `F`, and
  `ins F` is open and not empty (`exists_ring_disc`).
* An edge of a drawing that meets `F` only in vertices is either inside `F` or misses `ins F`,
  because it is connected and `S \ F` is the union of the disjoint open sets `ins F` and `S \ Σ`
  (`edge_inside_or_disjoint`). In the second case its closure also misses `ins F`, since `ins F`
  is open. In the first case its closure lies in `Σ`.
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The points inside an O-arc `F` of the disc `S`. -/
@[expose] def insideSet (F : Set S) : Set S := {x | InsideOArc univ F x}

/-- An O-arc `F` of the disc `S` bounds a closed disc `Σ = F ∪ ins F`, and `ins F` is the interior
of `Σ`. -/
theorem exists_ring_disc (hS : IsClosedDisc (univ : Set S)) {F : Set S} (hF : IsOArc F) :
    ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧ insideSet F = discInt D ∧ F ∪ insideSet F = D := by
  obtain ⟨D, hD, huniq⟩ := disc_oArc univ F hS (subset_univ F) hF
  have hins : insideSet F = discInt D := by
    ext x
    constructor
    · rintro ⟨D', hD', hx⟩
      have : D' = D := huniq D' (subset_univ _) hD'.2.1 hD'.2.2.1
      exact this ▸ hx
    · intro hx
      exact ⟨D, hD, hx⟩
  refine ⟨D, hD.2.1, hD.2.2.1, hins, ?_⟩
  rw [hins, ← hD.2.2.1]
  ext x
  constructor
  · rintro (hx | hx)
    · exact discBd_subset D hx
    · exact hx.1
  · intro hx
    by_cases hb : x ∈ discBd D
    · exact Or.inl hb
    · exact Or.inr ⟨hx, hb⟩

theorem isOpen_insideSet (hS : IsClosedDisc (univ : Set S)) {F : Set S} (hF : IsOArc F) :
    IsOpen (insideSet F) := by
  obtain ⟨D, hD, -, hins, -⟩ := exists_ring_disc hS hF
  rw [hins]
  exact hD.isOpen_discInt (isManifoldPoint_of_univ hS)

theorem insideSet_nonempty (hS : IsClosedDisc (univ : Set S)) {F : Set S} (hF : IsOArc F) :
    (insideSet F).Nonempty := by
  obtain ⟨D, hD, -, hins, -⟩ := exists_ring_disc hS hF
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  rw [hins, c.discInt_eq]
  exact ⟨g 0, 0, Metric.mem_ball_self one_pos, rfl⟩

theorem isClosed_ring (hS : IsClosedDisc (univ : Set S)) {F : Set S} (hF : IsOArc F) :
    IsClosed (F ∪ insideSet F) := by
  have : T2Space S := t2Space_of_univ hS
  obtain ⟨D, hD, -, -, hD'⟩ := exists_ring_disc hS hF
  rw [hD']
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  exact c.isCompact.isClosed

theorem not_mem_insideSet_of_mem {F : Set S} {x : S} (hx : x ∈ F) : x ∉ insideSet F :=
  not_insideOArc_self hx

/-- A connected set that misses an O-arc `F` lies inside `F` or misses the inside of `F`. -/
theorem subset_or_disjoint_insideSet (hS : IsClosedDisc (univ : Set S)) {F : Set S}
    (hF : IsOArc F) {e : Set S} (he : IsPreconnected e) (heF : Disjoint e F) :
    e ⊆ insideSet F ∨ Disjoint e (insideSet F) := by
  have hcl := isClosed_ring hS hF
  have hU : e ⊆ insideSet F ∪ (F ∪ insideSet F)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ insideSet F
    · exact Or.inl hxi
    · refine Or.inr fun hx' => ?_
      rcases hx' with h | h
      · exact Set.disjoint_left.mp heF hx h
      · exact hxi h
  rcases he.subset_or_subset (isOpen_insideSet hS hF) hcl.isOpen_compl
    (Set.disjoint_left.mpr fun x h1 h2 => h2 (Or.inr h1)) hU with h | h
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.mpr fun x hx hxi => h hx (Or.inr hxi))

/-- If an edge `e` misses the inside of `F`, so does its closure. -/
theorem closure_disjoint_insideSet (hS : IsClosedDisc (univ : Set S)) {F : Set S}
    (hF : IsOArc F) {e : Set S} (he : Disjoint e (insideSet F)) :
    Disjoint (closure e) (insideSet F) := by
  have hsub : e ⊆ (insideSet F)ᶜ := fun x hx hxi => Set.disjoint_left.mp he hx hxi
  have := closure_minimal hsub (isOpen_insideSet hS hF).isClosed_compl
  exact Set.disjoint_left.mpr fun x hx hxi => this hx hxi

/-- If `e` is inside `F`, its closure lies in `F ∪ ins F`. -/
theorem closure_subset_ring (hS : IsClosedDisc (univ : Set S)) {F : Set S}
    (hF : IsOArc F) {e : Set S} (he : e ⊆ insideSet F) :
    closure e ⊆ F ∪ insideSet F :=
  closure_minimal (he.trans subset_union_right) (isClosed_ring hS hF)

/-- An edge of a drawing misses every `Γ`-normal set `F`. -/
theorem Drawing.disjoint_of_isNormal {Γ : Drawing S} {F : Set S} (hF : Γ.IsNormal F) {e : Set S}
    (he : e ∈ Γ.E) : Disjoint e F := by
  refine Set.disjoint_left.mpr fun x hxe hxF => ?_
  have hx : x ∈ Γ.U \ Γ.V := he.2.1 hxe
  exact hx.2 (hF ⟨hxF, hx.1⟩)

/-- An edge of `Γ` is inside a `Γ`-normal O-arc `F`, or misses the inside of `F`. -/
theorem edge_inside_or_disjoint (hS : IsClosedDisc (univ : Set S)) {Γ : Drawing S} {F : Set S}
    (hF : IsOArc F) (hnF : Γ.IsNormal F) {e : Set S} (he : e ∈ Γ.E) :
    e ⊆ insideSet F ∨ Disjoint e (insideSet F) :=
  subset_or_disjoint_insideSet hS hF he.2.2.1.isConnected.isPreconnected
    (Drawing.disjoint_of_isNormal hnF he)

end GM08
end GraphMinor
