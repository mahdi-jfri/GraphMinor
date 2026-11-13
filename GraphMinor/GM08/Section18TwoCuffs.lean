module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Cuff
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section11

/-!
# A schism between two cuffs

An arc-connected closed set meeting distinct cuffs contains a proper arc
between distinct cuffs. Trim a connecting line at its first and last
boundary contacts. If the original set is normal, so is this arc, and its
vertex count does not increase. This is one extraction case for VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- A normal arc-connected closed set meeting two cuffs contains a normal
schism of type (ii), with no larger vertex count. -/
theorem exists_normal_schism_of_meets_two_cuffs {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) (G : Drawing S) {X C D : Set S}
    (hX : IsClosed X) (hXarc : IsArcConnected X) (hnX : G.IsNormal X)
    (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    (hmC : (X ∩ C).Nonempty) (hmD : (X ∩ D).Nonempty) :
    ∃ P : Set S, P ⊆ X ∧ GM07.IsSchism P ∧ G.IsNormal P ∧
      (G.V ∩ P).ncard ≤ (G.V ∩ X).ncard := by
  have : T2Space S := hS.2.1
  have hCclosed : IsClosed C := by
    obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
    have : CompactSpace C := φ.compactSpace
    exact (isCompact_iff_compactSpace.mpr this).isClosed
  have hDb : D ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hD
    exact connectedComponentIn_subset _ _
  have hCb : C ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hmother : (X ∩ (bd S \ C)).Nonempty := by
    obtain ⟨x, hxX, hxD⟩ := hmD
    exact ⟨x, hxX, hDb hxD, disjoint_left.mp (cuffs_disjoint hD hC hCD.symm) hxD⟩
  have hdis : Disjoint (X ∩ C) (X ∩ (bd S \ C)) := disjoint_left.mpr
    (fun _ h₁ h₂ => h₂.2.2 h₁.2)
  obtain ⟨P, u, v, hPX, hu, hv, hP, hPC, hPother⟩ :=
    GM07.exists_connecting_line_between_disjoint_closed hXarc inter_subset_left inter_subset_left
      (hX.inter hCclosed) (hX.inter (isClosed_other_cuffs hS hC)) hmC hmother hdis
  have huv : u ≠ v := fun heq => hv.2.2 (heq ▸ hu.2)
  have hPbd : P ∩ bd S = {u, v} := by
    apply Subset.antisymm
    · rintro x ⟨hxP, hxbd⟩
      by_cases hxC : x ∈ C
      · exact Or.inl (hPC.subset ⟨hxP, hPX hxP, hxC⟩)
      · exact Or.inr (hPother.subset ⟨hxP, hPX hxP, hxbd, hxC⟩)
    · rintro x (rfl | rfl)
      · exact ⟨hP.left_mem, hCb hu.2⟩
      · exact ⟨hP.right_mem, hv.2.1⟩
  let E := connectedComponentIn (bd S) v
  have hE : E ∈ cuffs S := ⟨v, hv.2.1, rfl⟩
  have hvE : v ∈ E := mem_connectedComponentIn hv.2.1
  have hCE : C ≠ E := fun heq => hv.2.2 (heq.symm ▸ hvE)
  have hsch : GM07.IsSchism P := Or.inr (Or.inl
    ⟨⟨u, v, huv, hPbd, hP⟩, C, hC, E, hE, hCE,
      ⟨u, ⟨v, hP⟩, hu.2⟩, ⟨v, ⟨u, hP.symm⟩, hvE⟩⟩)
  refine ⟨P, hPX, hsch, fun x hx => hnX ⟨hPX hx.1, hx.2⟩, ?_⟩
  exact ncard_le_ncard (fun x hx => ⟨hx.1, hPX hx.2⟩) (G.finite_V.inter_of_left X)

end GraphMinor.GM08
