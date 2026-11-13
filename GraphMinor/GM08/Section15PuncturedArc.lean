module

public import GraphMinor.GM08.Section15PuncturedCylinder
import GraphMinor.GM08.Section15TrimArc
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM11.PaintingRegions

/-!
# The short arc in the adjusted cylinder

A normal line between the separated discs misses their interiors, so
it lies in their cylindrical complement. Pull it back by inclusion,
then shorten it to its first and last cuff contacts. Normality persists
and the vertex count does not increase. This is the arc cut of the
root-preserving adjusted framing in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A normal line between the two empty discs gives a proper normal
arc in their cylindrical complement with no greater vertex count.
This supplies the cut of the adjusted framing in VIII (15.4), page 282. -/
theorem exists_proper_arc_in_two_disc_complement {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S) (hsph : IsSphere S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hDE : Disjoint D E)
    (G : Drawing S) (H : Drawing (GM12.discComplement (![D, E] : Fin 2 → Set S)))
    (hHU : H.U = Subtype.val ⁻¹' G.U) (hHV : H.V = Subtype.val ⁻¹' G.V)
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b)
    (ha : a ∈ discBd D) (hb : b ∈ discBd E) (hn : G.IsNormal L)
    (hoffD : Disjoint L (discInt D)) (hoffE : Disjoint L (discInt E)) :
    let Q := GM12.discComplement (![D, E] : Fin 2 → Set S)
    ∃ (J : Set Q) (u v : Q), IsLineWithEnds J u v ∧
      u.1 ∈ discBd D ∧ v.1 ∈ discBd E ∧ J ∩ bd Q = {u, v} ∧
      H.IsNormal J ∧ (J ∩ H.V).ncard ≤ (L ∩ G.V).ncard := by
  classical
  have : T2Space S := hS.2.1
  let P : Fin 2 → Set S := ![D, E]
  let Q := GM12.discComplement P
  have hP : ∀ i, IsClosedDisc (P i) := by intro i; fin_cases i <;> assumption
  have hdis : Pairwise (fun i j => Disjoint (P i) (P j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hDE
    · exact hDE.symm
    · exact (hij rfl).elim
  obtain ⟨hcyl, hcuffs, hne, hbd⟩ := cylinder_complement_two_discs hS hsph hD hE hDE
  have hC : (Subtype.val : Q → S) ⁻¹' discBd D ∈ cuffs Q := by rw [hcuffs]; exact .inl rfl
  have hF : (Subtype.val : Q → S) ⁻¹' discBd E ∈ cuffs Q := by rw [hcuffs]; exact .inr rfl
  have hLQ : L ⊆ Q := by
    intro x hx
    by_cases hxD : x ∈ D
    · have hxb : x ∈ discBd D := by
        by_contra hn
        exact disjoint_left.mp hoffD hx ⟨hxD, hn⟩
      exact GM12.disc_boundary_subset_discComplement hS P hP hdis 0 hxb
    · by_cases hxE : x ∈ E
      · have hxb : x ∈ discBd E := by
          by_contra hn
          exact disjoint_left.mp hoffE hx ⟨hxE, hn⟩
        exact GM12.disc_boundary_subset_discComplement hS P hP hdis 1 hxb
      · apply subset_closure
        intro h
        obtain ⟨i, hi⟩ := mem_iUnion.mp h
        fin_cases i
        · exact hxD hi
        · exact hxE hi
  let u₀ : Q := ⟨a, hLQ hL.left_mem⟩
  let v₀ : Q := ⟨b, hLQ hL.right_mem⟩
  let J₀ : Set Q := Subtype.val ⁻¹' L
  have hl₀ : IsLineWithEnds J₀ u₀ v₀ := GM07.pull_line IsEmbedding.subtypeVal hL
    (fun x hx => ⟨⟨x, hLQ hx⟩, rfl⟩)
  have hn₀ : H.IsNormal J₀ := by
    intro x hx
    rw [hHU] at hx
    rw [hHV]
    exact hn hx
  have hcount₀ : (J₀ ∩ H.V).ncard ≤ (L ∩ G.V).ncard := by
    have hsub : (Subtype.val : Q → S) '' (J₀ ∩ H.V) ⊆ L ∩ G.V := by
      rintro x ⟨y, hy, rfl⟩
      have hyV := hy.2
      rw [hHV] at hyV
      exact ⟨hy.1, hyV⟩
    have h := ncard_le_ncard hsub (G.finite_V.subset inter_subset_right)
    rwa [ncard_image_of_injective _ Subtype.val_injective] at h
  have : T2Space Q := hcyl.t2Space
  obtain ⟨J, u, v, hJJ, hu, hv, hJ, hJbd⟩ := exists_subarc_between_closed_sets hl₀
    (GM11.isCompact_of_isOArc ((cuff_statement Q hcyl.1).2.2 _ hC)).isClosed
    (GM11.isCompact_of_isOArc ((cuff_statement Q hcyl.1).2.2 _ hF)).isClosed
    (cuffs_disjoint hC hF hne) ha hb
  refine ⟨J, u, v, hJ, hu, hv, ?_, ?_, ?_⟩
  · simpa only [hbd, preimage_union] using hJbd
  · exact fun x hx => hn₀ ⟨hJJ hx.1, hx.2⟩
  · exact (ncard_le_ncard (inter_subset_inter_left _ hJJ)
      (H.finite_V.subset inter_subset_right)).trans hcount₀

end GraphMinor.GM08
