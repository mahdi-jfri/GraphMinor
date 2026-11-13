module

public import GraphMinor.GM06.Alg34GapOrderExists
import GraphMinor.Compute.GM06Alg34LabelList

/-!
# Completeness of a nonrepeating cuff segment list

The full ordered cuff construction gives a bijection from cuff vertex
positions to all segments. Any other injective segment list with one
position per cuff vertex must therefore be exhaustive: compose it with
that bijection to obtain an injective self-map of a finite type.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u

/-- An injective segment list with one position per cuff vertex already
lists every segment. The finite counting argument includes an empty cuff. -/
theorem alg34_cuff_segments_complete {S : Type u} [TopologicalSpace S]
    {C : Set S} (hC : IsOArc C) {n : ℕ} (v : Fin n ↪ S)
    (L : List (Fin n)) (hL : L.Nodup) (hmem : ∀ a, a ∈ L ↔ v a ∈ C)
    (segs : Fin L.length → Set S)
    (hs : ∀ i, segs i ∈ segmentsOf C (Set.range v ∩ C))
    (hi : Function.Injective segs) :
    ∀ seg ∈ segmentsOf C (Set.range v ∩ C), ∃ i, segs i = seg := by
  classical
  obtain ⟨K, hK, hKmem, ss, _, hsK, hiK, hcover, _, _, _, _⟩ := alg34_exists_cuff_gap_order hC v
  let A := {seg : Set S // seg ∈ segmentsOf C (Set.range v ∩ C)}
  have hbij : Function.Bijective (fun i : Fin K.length => (⟨ss i, hsK i⟩ : A)) := by
    constructor
    · intro i j he
      exact hiK (congrArg Subtype.val he)
    · intro seg
      obtain ⟨i, he⟩ := hcover seg.val seg.property
      exact ⟨i, Subtype.ext he⟩
  let labelEquiv : {a : Fin n // a ∈ L} ≃ {a : Fin n // a ∈ K} := {
    toFun := fun a => ⟨a.val, (hKmem a.val).mpr ((hmem a.val).mp a.property)⟩
    invFun := fun a => ⟨a.val, (hmem a.val).mpr ((hKmem a.val).mp a.property)⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }
  let indexEquiv : Fin L.length ≃ Fin K.length :=
    (gm06ListNumbering L hL).symm.trans (labelEquiv.trans (gm06ListNumbering K hK))
  let e : Fin L.length ≃ A := indexEquiv.trans (Equiv.ofBijective _ hbij)
  let f : Fin L.length → Fin L.length := fun i => e.symm ⟨segs i, hs i⟩
  have hf : Function.Injective f := by
    intro i j he
    have hh : (⟨segs i, hs i⟩ : A) = ⟨segs j, hs j⟩ := e.symm.injective he
    exact hi (congrArg Subtype.val hh)
  have hsurj := Finite.surjective_of_injective hf
  intro seg hseg
  obtain ⟨i, he⟩ := hsurj (e.symm ⟨seg, hseg⟩)
  have hh : (⟨segs i, hs i⟩ : A) = ⟨seg, hseg⟩ := e.symm.injective he
  exact ⟨i, congrArg Subtype.val hh⟩

end GraphMinor.GM06
