module

public import GraphMinor.GM06.Section5CollapseRectangle
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-!
# Extending a local contraction by the identity

To use the rectangle contraction in Reduction 3 of VI, page 129, a
map in a closed chart must be extended to the whole cylinder. A
continuous family of maps that fixes the frontier of the chart
extends by the identity. The two formulas agree on that frontier,
so the closed-set pasting lemma proves continuity.
-/

public section

namespace GraphMinor.GM06

open Set Topology

/-- A continuous family in a closed rectangular chart extends by the
identity when it fixes the frontier of the chart. This pasting step
is used for both the contraction and its homotopy in Reduction 3. -/
theorem exists_continuous_glue_of_closed_rectangle
    {S P : Type*} [TopologicalSpace S] [TopologicalSpace P]
    {D : Set S} (hD : IsClosed D) (e : Section5CollapseRectangle ≃ₜ D)
    (Φ : C(P × Section5CollapseRectangle, Section5CollapseRectangle))
    (hfix : ∀ p z, (e z).1 ∈ frontier D → Φ (p, z) = z) :
    ∃ c : C(P × S, S),
      (∀ p z, c (p, (e z).1) = (e (Φ (p, z))).1) ∧
      (∀ p x, x ∉ D → c (p, x) = x) := by
  classical
  let z₀ : Section5CollapseRectangle := (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)
  let J : S → Section5CollapseRectangle := fun x =>
    if hx : x ∈ D then e.symm ⟨x, hx⟩ else z₀
  have hJe (z : Section5CollapseRectangle) : J (e z).1 = z := by
    simp only [J, dite_eq_left (e z).2]
    exact e.symm_apply_apply z
  have hJc : ContinuousOn J D := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply e.symm.continuous.congr
    intro x
    simp only [J, Set.domRestrict_apply, dite_eq_left x.2]
  let c : P × S → S := fun q =>
    if q.2 ∈ D then (e (Φ (q.1, J q.2))).1 else q.2
  have hc1 : ContinuousOn c (univ ×ˢ D) := by
    have hc : ContinuousOn (fun q : P × S => (e (Φ (q.1, J q.2))).1) (univ ×ˢ D) :=
      (continuous_subtype_val.comp e.continuous).continuousOn.comp
        (Φ.continuous.continuousOn.comp
          (continuousOn_fst.prodMk (hJc.comp continuousOn_snd (fun q hq => hq.2)))
          (fun _ _ => mem_univ _)) (fun _ _ => mem_univ _)
    apply hc.congr
    rintro ⟨p, x⟩ ⟨_, hx⟩
    exact ite_eq_left hx
  have hc2 : ContinuousOn c (univ ×ˢ (interior D)ᶜ) := by
    apply continuousOn_snd.congr
    rintro ⟨p, x⟩ ⟨_, hx⟩
    change (if x ∈ D then _ else x) = x
    split_ifs with hxD
    · have hxfr : x ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hxD, hx⟩
      have hJx : (e (J x)).1 = x := by
        simp only [J, dite_eq_left hxD, e.apply_symm_apply]
      rw [hfix p (J x) (hJx.symm ▸ hxfr), hJx]
    · rfl
  have hcover : (univ ×ˢ D) ∪ (univ ×ˢ (interior D)ᶜ) = (univ : Set (P × S)) := by
    ext ⟨p, x⟩
    simp only [mem_union, mem_prod, mem_univ, true_and, iff_true]
    by_cases hx : x ∈ interior D
    · exact Or.inl (interior_subset hx)
    · exact Or.inr hx
  have hc : Continuous c := by
    rw [← continuousOn_univ, ← hcover]
    exact hc1.union_of_isClosed hc2 (isClosed_univ.prod hD)
      (isClosed_univ.prod isOpen_interior.isClosed_compl)
  refine ⟨⟨c, hc⟩, ?_, ?_⟩
  · intro p z
    change (if (e z).1 ∈ D then _ else _) = _
    rw [ite_eq_left (e z).2, hJe]
  · intro p x hx
    exact ite_eq_right hx

end GraphMinor.GM06
