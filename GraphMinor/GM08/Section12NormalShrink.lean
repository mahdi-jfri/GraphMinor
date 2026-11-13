module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12Shrink
import GraphMinor.GM08.Section12ShrinkDisc
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.SphereDisc

/-!
# Preserving a drawing while shrinking a normal ring

Apply the shrinking construction to the closed point set of the
drawing. Every drawing point inside the old ring stays inside the new
one, and the boundary keeps precisely the same drawing vertices. Thus
the enclosed edges and the ring size do not change. This supplies the
last geometric adjustment of foundation rings on page 267 of VIII.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Shrink a normal ring while keeping every drawing contact and every
enclosed drawing point. The new ring meets the old boundary only at
drawing vertices, as required for the foundation used in Section 12. -/
theorem exists_shrunk_normal_disc {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsSphere S) (D : Drawing S) {B K : Set S}
    (hB : IsClosedDisc B) (hK : IsClosedDisc K) (hKB : K ⊆ discInt B)
    (hn : D.IsNormal (discBd B)) :
    ∃ B' : Set S, IsClosedDisc B' ∧ K ⊆ discInt B' ∧ B' ⊆ B ∧
      D.IsNormal (discBd B') ∧ D.V ∩ discBd B' = D.V ∩ discBd B ∧
      discBd B' ⊆ discInt B ∪ D.V ∧
      D.U ∩ discInt B' = D.U ∩ discInt B := by
  obtain ⟨B', hB', hKB', hsub, hcontact, hbd, hkeep⟩ :=
    exists_shrunk_disc hS hB hK hKB D.isClosed_U
  have hn' : D.IsNormal (discBd B') := by
    intro x hx
    have hxold : x ∈ discBd B ∩ D.U := hcontact ▸ hx
    exact hn hxold
  have hman : ∀ x : S, IsManifoldPoint x := fun x =>
    ((GM11.IsSphere.isClosedSurface hS).1.2.2 x).isManifoldPoint
  refine ⟨B', hB', hKB', hsub, hn', ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxV, hxB'⟩
      exact ⟨hxV, (show x ∈ discBd B ∩ D.U from
        hcontact ▸ (show x ∈ discBd B' ∩ D.U from ⟨hxB', D.V_subset_U hxV⟩)).1⟩
    · rintro ⟨hxV, hxB⟩
      exact ⟨hxV, (show x ∈ discBd B' ∩ D.U from
        hcontact.symm ▸ (show x ∈ discBd B ∩ D.U from ⟨hxB, D.V_subset_U hxV⟩)).1⟩
  · intro x hx
    rcases hbd hx with hin | hU
    · exact .inl hin
    · exact .inr (hn' ⟨hx, hU⟩)
  · exact Subset.antisymm
      (fun x hx => ⟨hx.1, discInt_mono hman hB' hsub hx.2⟩)
      (fun x hx => ⟨hx.1, hkeep x hx.1 hx.2⟩)

/-- The normal-ring shrinking construction in a disc ambient space,
keeping every drawing contact and every enclosed drawing point. The new ring meets the old boundary only at
drawing vertices, as required for the foundation used in Section 12. -/
theorem exists_shrunk_normal_disc_in_disc {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) {B K : Set S}
    (hB : IsClosedDisc B) (hK : IsClosedDisc K) (hKB : K ⊆ discInt B)
    (hn : D.IsNormal (discBd B)) :
    ∃ B' : Set S, IsClosedDisc B' ∧ K ⊆ discInt B' ∧ B' ⊆ B ∧
      D.IsNormal (discBd B') ∧ D.V ∩ discBd B' = D.V ∩ discBd B ∧
      discBd B' ⊆ discInt B ∪ D.V ∧
      D.U ∩ discInt B' = D.U ∩ discInt B := by
  obtain ⟨B', hB', hKB', hsub, hcontact, hbd, hkeep⟩ :=
    exists_shrunk_disc_in_disc hS hB hK hKB D.isClosed_U
  have hn' : D.IsNormal (discBd B') := by
    intro x hx
    have hxold : x ∈ discBd B ∩ D.U := hcontact ▸ hx
    exact hn hxold
  have hman : ∀ x : S, IsManifoldPoint x := fun x =>
    (isSurface_of_closedDisc_univ hS).2.2 x
  refine ⟨B', hB', hKB', hsub, hn', ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxV, hxB'⟩
      exact ⟨hxV, (show x ∈ discBd B ∩ D.U from
        hcontact ▸ (show x ∈ discBd B' ∩ D.U from ⟨hxB', D.V_subset_U hxV⟩)).1⟩
    · rintro ⟨hxV, hxB⟩
      exact ⟨hxV, (show x ∈ discBd B' ∩ D.U from
        hcontact.symm ▸ (show x ∈ discBd B ∩ D.U from ⟨hxB, D.V_subset_U hxV⟩)).1⟩
  · intro x hx
    rcases hbd hx with hin | hU
    · exact .inl hin
    · exact .inr (hn' ⟨hx, hU⟩)
  · exact Subset.antisymm
      (fun x hx => ⟨hx.1, discInt_mono hman hB' hsub hx.2⟩)
      (fun x hx => ⟨hx.1, hkeep x hx.1 hx.2⟩)

end GraphMinor.GM08
