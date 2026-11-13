module

public import GraphMinor.GM19.CutDrawing
import Mathlib.Tactic.NormNum

/-!
# The two lifted lines of a cut edge

Restrict each edge-lift parameter to the unit interval. Composing with
the cutting map gives the original arc, so both lifts are arcs too.
Their interiors are disjoint and cover the preimage of the old open
edge. This constructs the cut edges of the dissection in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe u

/-- An edge lift gives two distinct lines, meeting only over the old
ends and covering the preimage of the open edge. This is the cut-edge
construction in the Euler proof of VIII (18.2), page 286. -/
theorem exists_lines_of_edge_lift {S Y : Type u} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space Y] {ψ : Y → S} {a : unitInterval → S}
    (ha : IsArcMap a) {p : Bool → Prop} {r r' : ℝ → Y}
    (hlift : GM19.IsEdgeLift ψ (extI a) p r r') :
    ∃ X X' : Set Y, IsLineWithEnds X (r 0) (r 1) ∧
      IsLineWithEnds X' (r' 0) (r' 1) ∧
      BijOn ψ X (range a) ∧ BijOn ψ X' (range a) ∧ X ≠ X' ∧
      X ∩ X' ⊆ ψ ⁻¹' {a 0, a 1} ∧
      ψ ⁻¹' (range a \ {a 0, a 1}) ⊆ X ∪ X' := by
  let R : unitInterval → Y := fun t => r t.1
  let R' : unitInterval → Y := fun t => r' t.1
  have hR : ∀ t, ψ (R t) = a t := fun t => by
    simpa only [R, extI_coe] using (hlift.2.2.1 t.1 t.2).1
  have hR' : ∀ t, ψ (R' t) = a t := fun t => by
    simpa only [R', extI_coe] using (hlift.2.2.1 t.1 t.2).2
  have hRc : Continuous R := hlift.1.comp_continuous continuous_subtype_val (fun t => t.2)
  have hR'c : Continuous R' := hlift.2.1.comp_continuous continuous_subtype_val (fun t => t.2)
  have hRi : Function.Injective R := by
    intro s t hst
    exact ha.2 ((hR s).symm.trans ((congrArg ψ hst).trans (hR t)))
  have hR'i : Function.Injective R' := by
    intro s t hst
    exact ha.2 ((hR' s).symm.trans ((congrArg ψ hst).trans (hR' t)))
  have hbij : ∀ (Q : unitInterval → Y), (∀ t, ψ (Q t) = a t) → BijOn ψ (range Q) (range a) := by
    intro Q hQ
    refine ⟨?_, ?_, ?_⟩
    · rintro y ⟨t, rfl⟩
      exact ⟨t, (hQ t).symm⟩
    · rintro y ⟨s, rfl⟩ z ⟨t, rfl⟩ heq
      exact congrArg Q (ha.2 ((hQ s).symm.trans (heq.trans (hQ t))))
    · rintro z ⟨t, rfl⟩
      exact ⟨Q t, mem_range_self t, hQ t⟩
  have hregular : ∀ t : unitInterval, t ≠ 0 → t ≠ 1 → R t ≠ R' t := by
    intro t ht0 ht1
    exact (hlift.2.2.2.2 t.1 t.2 (Or.inl
      ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩)).1
  have hinter : range R ∩ range R' ⊆ ψ ⁻¹' {a 0, a 1} := by
    rintro y ⟨⟨s, rfl⟩, t, ht⟩
    have hts : t = s := ha.2 ((hR' t).symm.trans ((congrArg ψ ht).trans (hR s)))
    subst t
    by_cases hs0 : s = 0
    · exact Or.inl (by rw [hR, hs0])
    by_cases hs1 : s = 1
    · exact Or.inr (by rw [hR, hs1]; rfl)
    exact ((hregular s hs0 hs1) ht.symm).elim
  have hne : range R ≠ range R' := by
    intro heq
    let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
    have ht0 : t ≠ 0 := by intro hh; have hh' := congrArg Subtype.val hh; norm_num [t] at hh'
    have ht1 : t ≠ 1 := by intro hh; have hh' := congrArg Subtype.val hh; norm_num [t] at hh'
    obtain ⟨s, hs⟩ := heq ▸ (mem_range_self t : R t ∈ range R)
    have hst : s = t := ha.2 ((hR' s).symm.trans ((congrArg ψ hs).trans (hR t)))
    exact hregular t ht0 ht1 (by simpa only [hst] using hs.symm)
  refine ⟨range R, range R', (show IsArcMap R from ⟨hRc, hRi⟩).isLineWithEnds,
    (show IsArcMap R' from ⟨hR'c, hR'i⟩).isLineWithEnds, hbij R hR, hbij R' hR', hne, hinter, ?_⟩
  intro y hy
  obtain ⟨t, ht⟩ := hy.1
  have ht0 : t ≠ 0 := fun heq => hy.2 (Or.inl (by rw [← ht, heq]))
  have ht1 : t ≠ 1 := fun heq => hy.2 (Or.inr (by rw [← ht, heq]; rfl))
  have hψy : ψ y = extI a t.1 := by rw [extI_coe, ht]
  rcases (hlift.2.2.2.2 t.1 t.2 (Or.inl
    ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩)).2 y hψy with h | h
  · exact Or.inl ⟨t, h.symm⟩
  · exact Or.inr ⟨t, h.symm⟩

end GraphMinor.GM08
