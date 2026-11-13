module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM11.RadialCorners

/-!
# Connected compact subsets of a line

The connected-intersection case of the circle extraction used by
XII (3.1), page 245, reduces to a compact connected subset of an arc.
Its interval preimage contains every point between its minimum and
maximum. If the subset has two distinct points, these extremes are
distinct and parametrize it as a line.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A compact preconnected subset of a line with two distinct points
is a line, with ends corresponding to the extreme parameters. -/
theorem isLineWithEnds_of_compact_preconnected_subset_line
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {L T : Set S} {u v x y : S} (hL : IsLineWithEnds L u v)
    (hTL : T ⊆ L) (hTc : IsCompact T) (hTp : IsPreconnected T)
    (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) :
    ∃ a b, a ≠ b ∧ IsLineWithEnds T a b := by
  obtain ⟨e, _, _⟩ := hL
  let p : unitInterval → S := fun t => (e t).val
  have hpc : Continuous p := continuous_subtype_val.comp e.continuous
  have hpi : Function.Injective p := fun s t he => e.injective (Subtype.ext he)
  have hpemb : IsEmbedding p := IsEmbedding.subtypeVal.comp e.isEmbedding
  let K := p ⁻¹' T
  have hKc : IsCompact K := (hTc.isClosed.preimage hpc).isCompact
  have himage : p '' K = T := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      refine ⟨e.symm ⟨z, hTL hz⟩, ?_, ?_⟩
      · change (e (e.symm ⟨z, hTL hz⟩)).val ∈ T
        simpa only [e.apply_symm_apply] using hz
      · exact congrArg Subtype.val (e.apply_symm_apply _)
  have hKp : IsPreconnected K := hpemb.isInducing.isPreconnected_image.mp (himage.symm ▸ hTp)
  have hKne : K.Nonempty := by
    obtain ⟨t, ht, _⟩ := himage.symm ▸ hx
    exact ⟨t, ht⟩
  obtain ⟨a, ha, hamin⟩ := hKc.exists_isLeast hKne
  obtain ⟨b, hb, hbmax⟩ := hKc.exists_isGreatest hKne
  have hKI : K = Icc a b := Subset.antisymm
    (fun _ ht => ⟨hamin ht, hbmax ht⟩) (hKp.Icc_subset ha hb)
  have hab : a < b := by
    apply lt_of_le_of_ne (hamin hb)
    intro heq
    have hsingle : ∀ z ∈ T, z = p a := by
      intro z hz
      obtain ⟨t, ht, rfl⟩ := himage.symm ▸ hz
      have ht' : t = a := le_antisymm ((hbmax ht).trans_eq heq.symm) (hamin ht)
      exact congrArg p ht'
    exact hxy ((hsingle x hx).trans (hsingle y hy).symm)
  refine ⟨p a, p b, fun he => hab.ne (hpi he), ?_⟩
  have h := isLine_piece hpc hpi hab
  rw [← hKI, himage] at h
  exact h

end GraphMinor.GM12
