module

public import GraphMinor.GM06.Section5PolarHalfedgeEquiv
public import GraphMinor.GM06.Section2Dual
import Mathlib.Data.Finset.Sort

/-!
# Finite rotation rows from labelled directed ends

The input to VI (5.7), page 133, records each vertex rotation as
an ordered list of directed labels. Given the labels and the polar
rim bijection, sort the finitely many ends by angle. This produces
an ordinary rotation row and its geometric interpretation. The
construction has no feasibility or reduction information.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Every injective finite labelling of the incident ends admits a
rotation row with exactly the polar rim order and all edge directions. -/
theorem exists_polar_rotation_row
    {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {Φ : C(ClosedUnitDisc, S)}
    (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (label : halfEdges Γ γ v → ℕ) (hl : Function.Injective label) :
    ∃ (xs : List ℕ) (z : ℕ → Circle), xs.Nodup ∧
      (∀ r, r ∈ xs ↔ ∃ a, label a = r) ∧
      (∀ a, z (label a) = (d a).1) ∧
      Set.InjOn z {r | r ∈ xs} ∧
      xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)) ∧
      ∀ w : Circle, (∃ e ∈ Γ.E, polarRimMap Φ w ∈ e) ↔ ∃ r ∈ xs, z r = w := by
  classical
  let H := halfEdges Γ γ v
  let : Finite H := (finite_halfEdges Γ γ v).to_subtype
  let : Fintype H := Fintype.ofFinite H
  let z : ℕ → Circle := fun r => if h : ∃ a, label a = r then (d h.choose).1 else 1
  have hz (a : H) : z (label a) = (d a).1 := by
    have h : ∃ b, label b = label a := ⟨a, rfl⟩
    have heq : h.choose = a := hl h.choose_spec
    simp only [z, dite_eq_left h, heq]
  have hdi : Function.Injective (fun a : H => (d a).1) := Subtype.val_injective.comp d.injective
  let f : H → ℝ := fun a => circleStdCoord.angle (d a).1
  have hfi : Function.Injective f := fun a b hab => hdi (circleStdCoord.injective hab)
  let r : H → H → Prop := fun a b => f a ≤ f b
  have : IsTrans H r := ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩
  have : Std.Antisymm r := ⟨fun _ _ hab hba => hfi (le_antisymm hab hba)⟩
  have : Std.Total r := ⟨fun a b => le_total (f a) (f b)⟩
  let L : List H := Finset.univ.sort r
  have hnd : L.Nodup := Finset.sort_nodup _ _
  have hmem (a : H) : a ∈ L := by simp only [L, Finset.mem_sort, Finset.mem_univ]
  have hpair : L.Pairwise (fun a b => f a < f b) := by
    have hp : L.Pairwise r := Finset.pairwise_sort _ _
    apply (hp.and (List.nodup_iff_pairwise_ne.mp hnd)).imp
    intro a b hab
    exact lt_of_le_of_ne hab.1 (fun heq => hab.2 (hfi heq))
  refine ⟨L.map label, z, hnd.map hl, ?_, hz, ?_, ?_, ?_⟩
  · intro r
    constructor
    · rintro hr
      obtain ⟨a, _, ha⟩ := List.mem_map.mp hr
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      exact List.mem_map.mpr ⟨a, hmem a, rfl⟩
  · intro a ha b hb hab
    obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', _, rfl⟩ := List.mem_map.mp hb
    rw [hz, hz] at hab
    exact congrArg label (hdi hab)
  · apply List.pairwise_map.mpr
    simpa only [hz] using hpair
  · intro w
    constructor
    · intro hw
      obtain ⟨a, ha⟩ := d.surjective ⟨w, hw⟩
      refine ⟨label a, List.mem_map.mpr ⟨a, hmem a, rfl⟩, ?_⟩
      exact (hz a).trans (congrArg Subtype.val ha)
    · rintro ⟨r, hr, hrw⟩
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
      rw [hz] at hrw
      exact hrw ▸ (d a).2

end GraphMinor.GM06
