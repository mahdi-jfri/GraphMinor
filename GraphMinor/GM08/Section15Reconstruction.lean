module

public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15Quotient
import GraphMinor.GM08.Section15Identification

/-!
# Reconstructing a graft from paired boundary vertices

Identify one two-point fibre at a time. Each step removes one vertex,
so the process ends. The remaining injective map is a graft isomorphism.
This proves the finite reconstruction used for the disc cut in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u'

/-- A finite graph map with fibres of size at most two is a sequence of
root identifications followed by a graft isomorphism, provided the roots
are exactly the points over target roots or in nontrivial fibres. This
is the reconstruction step for VIII (15.4), page 282. -/
theorem exists_vertexIdChain_of_paired_fibres {α : Type u} {γ : Type u'} {β : Type v}
    (X : Graft α β) (Y : Graft γ β) (f : α → γ) (hG : Y.G = X.G.map f)
    (hf : ∀ z, {w ∈ V(X.G) | f w = z}.ncard ≤ 2)
    (hroot : ∀ z ∈ V(X.G), z ∈ X.T ↔
      f z ∈ Y.T ∨ ∃ w ∈ V(X.G), w ≠ z ∧ f w = f z) :
    ∃ (n : ℕ) (Z : Graft α β), ObtainedByVertexIdChain n X Z ∧ IsGraftIso Z Y := by
  classical
  by_cases hinj : InjOn f V(X.G)
  · refine ⟨0, X, .zero X, isGraftIso_of_injective_vertex_map hG hinj ?_⟩
    intro z hz
    have hno : ¬ ∃ w ∈ V(X.G), w ≠ z ∧ f w = f z := by
      rintro ⟨w, hw, hwz, he⟩
      exact hwz (hinj hw hz he)
    simpa only [hno, or_false] using hroot z hz
  · obtain ⟨p, hp, q, hq, hfp, hpq⟩ :
        ∃ p ∈ V(X.G), ∃ q ∈ V(X.G), f p = f q ∧ p ≠ q := by
      simp only [InjOn, not_forall] at hinj
      obtain ⟨p, hp, q, hq, hfp, hpq⟩ := hinj
      exact ⟨p, hp, q, hq, hfp, hpq⟩
    have hpair := pair_fibre_of_ncard_le_two X.finite_G.1 hp hq hpq hfp (hf (f p))
    have hpT : p ∈ X.T := (hroot p hp).mpr (.inr ⟨q, hq, hpq.symm, hfp.symm⟩)
    have hqT : q ∈ X.T := (hroot q hq).mpr (.inr ⟨p, hp, hpq, hfp⟩)
    let Z : Graft α β := {
      G := X.G.map (identifyVerticesFun p q q)
      T := if f q ∈ Y.T then (X.T \ {p, q}) ∪ {q} else X.T \ {p, q}
      T_subset := by
        rw [(pair_identification_map hq hpq hfp).1]
        intro z hz
        by_cases hr : f q ∈ Y.T
        · simp only [hr, ↓reduceIte, mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff] at hz
          rcases hz with ⟨hz, hn⟩ | rfl
          · exact ⟨X.T_subset hz, fun h => hn (.inl h)⟩
          · exact ⟨hq, hpq.symm⟩
        · simp only [hr, ↓reduceIte] at hz
          exact ⟨X.T_subset hz.1, fun h => hz.2 (.inl h)⟩
      finite_G := ⟨X.finite_G.1.image _, X.finite_G.2⟩ }
    have hVZ : V(Z.G) = V(X.G) \ {p} := (pair_identification_map hq hpq hfp).1
    have hGZ : Y.G = Z.G.map f := hG.trans (pair_identification_map hq hpq hfp).2.symm
    have hfZ : ∀ z, {w ∈ V(Z.G) | f w = z}.ncard ≤ 2 := by
      intro z
      apply (ncard_le_ncard ?_ (X.finite_G.1.subset (sep_subset _ _))).trans (hf z)
      intro w hw
      rw [hVZ] at hw
      exact ⟨hw.1.1, hw.2⟩
    have hrZ : ∀ z ∈ V(Z.G), z ∈ Z.T ↔
        f z ∈ Y.T ∨ ∃ w ∈ V(Z.G), w ≠ z ∧ f w = f z := by
      rw [hVZ]
      exact root_rule_after_pair_identification hfp hpair hroot
    obtain ⟨n, Q, hchain, hiso⟩ := exists_vertexIdChain_of_paired_fibres Z Y f hGZ hfZ hrZ
    have hstep : ObtainedByVertexIdChain 1 X Z := by
      refine .step (.zero X) p q hpT hqT hpq rfl ?_
      by_cases hr : f q ∈ Y.T
      · exact .inr (by simp only [Z, hr, ↓reduceIte])
      · exact .inl (by simp only [Z, hr, ↓reduceIte])
    exact ⟨1 + n, Q, hstep.trans hchain, hiso⟩
termination_by V(X.G).ncard
decreasing_by
  rw [hVZ]
  exact ncard_sdiff_singleton_lt_of_mem hp X.finite_G.1

end GraphMinor.GM08
