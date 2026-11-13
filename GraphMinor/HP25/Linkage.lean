module

public import GraphMinor.HP25.Defs

/-!
# Crossings of a four-tuple are linkages

Humeau and Pous, arXiv:2505.16431v2, Section 2.3 (page 7): "Observe that a graph is $2$-linked
precisely when all tuples of four distinct vertices are crossed". This file proves the statement
behind that sentence for one tuple: `(s₁, s₂, t₁, t₂)` is crossed exactly when there are two
vertex-disjoint paths from `s₁` to `t₁` and from `s₂` to `t₂` (an `(s₁,s₂,t₁,t₂)`-linkage, page 1).

In a tuple of length four the only indices `i < r < j < s` are `0, 1, 2, 3`, which gives one
direction. For the other, a path from `s₁` to `t₁` that is disjoint from a path through `s₂` and
`t₂` has no inner vertex in the tuple, so it is a `T`-path.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A path `p` whose support misses `s₂` and `t₂` is a `T`-path of `[s₁, s₂, t₁, t₂]` between its
ends `s₁` and `t₁`. -/
private theorem isTPath_of_disjoint {s₁ s₂ t₁ t₂ : V} (p : G.Walk s₁ t₁) (hp : p.IsPath)
    (h₂ : s₂ ∉ p.support) (h₄ : t₂ ∉ p.support) :
    IsTPath G [s₁, s₂, t₁, t₂] p := by
  refine ⟨hp, by simp, by simp, fun x hx hxs hxt => ?_⟩
  have hx₂ : x ≠ s₂ := fun h => h₂ (h ▸ hx)
  have hx₄ : x ≠ t₂ := fun h => h₄ (h ▸ hx)
  simp [hxs, hxt, hx₂, hx₄]

/-- Crossings of `(s₁, s₂, t₁, t₂)` are linkages (Humeau and Pous, Section 2.3, page 7): the tuple
is crossed if and only if there are vertex-disjoint paths from `s₁` to `t₁` and from `s₂` to `t₂`. -/
theorem isCrossed_iff_linkage {s₁ s₂ t₁ t₂ : V} :
    IsCrossed G [s₁, s₂, t₁, t₂] ↔
      ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
        P₁.IsPath ∧ P₂.IsPath ∧ P₁.support.Disjoint P₂.support := by
  constructor
  · rintro ⟨a, b, c, d, Q, R, ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ, hR, hdisj⟩
    have hs4 : s < 4 := by
      have := (List.getElem?_eq_some_iff.1 hs).1
      simpa using this
    obtain ⟨rfl, rfl, rfl, rfl⟩ : i = 0 ∧ r = 1 ∧ j = 2 ∧ s = 3 := by omega
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hi hr hj hs
    subst hi hr hj hs
    exact ⟨Q, R, hQ.1, hR.1, hdisj⟩
  · rintro ⟨P₁, P₂, h₁, h₂, hdisj⟩
    refine ⟨s₁, t₁, s₂, t₂, P₁, P₂, ⟨0, 1, 2, 3, by omega, by omega, by omega, by simp, by simp,
      by simp, by simp⟩, ?_, ?_, hdisj⟩
    · exact isTPath_of_disjoint P₁ h₁ (fun h => hdisj h P₂.start_mem_support)
        (fun h => hdisj h P₂.end_mem_support)
    · have hT : IsTPath G [s₂, s₁, t₂, t₁] P₂ :=
        isTPath_of_disjoint P₂ h₂ (fun h => hdisj P₁.start_mem_support h)
          (fun h => hdisj P₁.end_mem_support h)
      refine ⟨hT.1, by simp, by simp, fun x hx hxs hxt => ?_⟩
      have := hT.2.2.2 x hx hxs hxt
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at this ⊢
      tauto

end GraphMinor.HP25
