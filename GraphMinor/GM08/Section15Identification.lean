module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section14
import Mathlib.Data.Set.Card

/-!
# Identifying the two lifts of a vertex

When a cut vertex has two lifts, identify them. Keep the resulting
vertex as a root exactly when the original vertex was a root. All
other fibres and roots stay as before. These are the individual root
identifications used to reconstruct a tube from its disc cut in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u'

open Classical in
/-- Identifying a two-point fibre leaves the root rule valid: roots are
exactly the vertices over original roots or in nontrivial fibres. This
is one identification in the short-tube reconstruction in VIII (15.4),
page 282. -/
theorem root_rule_after_pair_identification {α γ : Type*} {V T : Set α}
    {R : Set γ} {f : α → γ} {p q : α} (hfp : f p = f q)
    (hpair : ∀ z ∈ V, f z = f p → z = p ∨ z = q)
    (hroot : ∀ z ∈ V, z ∈ T ↔ f z ∈ R ∨ ∃ w ∈ V, w ≠ z ∧ f w = f z) :
    ∀ z ∈ V \ {p},
      z ∈ (if f q ∈ R then (T \ {p, q}) ∪ {q} else T \ {p, q}) ↔
        f z ∈ R ∨ ∃ w ∈ V \ {p}, w ≠ z ∧ f w = f z := by
  classical
  intro z hz
  have hzp : z ≠ p := hz.2
  by_cases hzq : z = q
  · subst z
    have hno : ¬ ∃ w ∈ V \ {p}, w ≠ q ∧ f w = f q := by
      rintro ⟨w, hw, hwq, he⟩
      rcases hpair w hw.1 (he.trans hfp.symm) with h | h
      · exact hw.2 h
      · exact hwq h
    by_cases hr : f q ∈ R
    · simp [hr]
    · simp only [hr, ↓reduceIte]
      rw [or_iff_left hno]
      simp

  · have hchange : (∃ w ∈ V, w ≠ z ∧ f w = f z) ↔
        ∃ w ∈ V \ {p}, w ≠ z ∧ f w = f z := by
      constructor
      · rintro ⟨w, hw, hwz, he⟩
        have hwp : w ≠ p := by
          intro h
          have hez : f z = f p := he.symm.trans (congrArg f h)
          exact (hpair z hz.1 hez).elim hzp hzq
        exact ⟨w, ⟨hw, hwp⟩, hwz, he⟩
      · rintro ⟨w, hw, hwz, he⟩
        exact ⟨w, hw.1, hwz, he⟩
    have h := hroot z hz.1
    rw [hchange] at h
    by_cases hr : f q ∈ R <;> simpa [hr, hzp, hzq] using h

/-- Identifying one point of a two-point fibre into the other removes
exactly that point from the vertex set. The quotient map to the original
graft is unchanged, as used in VIII (15.4), page 282. -/
theorem pair_identification_map {α : Type u} {γ : Type u'} {β : Type v} {G : Graph α β}
    {f : α → γ} {p q : α} (hq : q ∈ V(G))
    (hpq : p ≠ q) (hfp : f p = f q) :
    V(G.map (identifyVerticesFun p q q)) = V(G) \ {p} ∧
      (G.map (identifyVerticesFun p q q)).map f = G.map f := by
  classical
  constructor
  · rw [vertexSet_map]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      by_cases hwp : w = p
      · simp only [identifyVerticesFun, hwp, true_or, ↓reduceIte]
        exact ⟨hq, hpq.symm⟩
      · by_cases hwq : w = q
        · simp only [identifyVerticesFun, hwq, or_true, ↓reduceIte]
          exact ⟨hq, hpq.symm⟩
        · simpa only [identifyVerticesFun, hwp, hwq, or_self, ↓reduceIte] using (show w ∈ V(G) \ {p} from ⟨hw, hwp⟩)
    · rintro ⟨hz, hzp⟩
      change z ≠ p at hzp
      refine ⟨z, hz, ?_⟩
      by_cases hzq : z = q <;> simp [identifyVerticesFun, hzp, hzq]
  · rw [map_map]
    apply congrArg (fun g => G.map g)
    funext z
    by_cases hzp : z = p
    · simp [identifyVerticesFun, hzp, hfp]
    · by_cases hzq : z = q <;> simp [identifyVerticesFun, hzp, hzq]

end GraphMinor.GM08
