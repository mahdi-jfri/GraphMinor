module

public import GraphMinor.Kruskal.EdgeChains

/-!
# Extending a replacing chain by one vertex

Lengthening one chain replaces its final segment by two fresh segments.
The new vertex is the next unused internal vertex of that chain. We verify
the vertex set, edge set, and links in the exact definition of a subdivision
step. All other chains retain their names and links.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set

/-- Add one internal vertex to the chain indexed by `e`. This is one
literal edge subdivision, with no intervening graph isomorphism. -/
theorem edgeChains_subdivision_step {V E : Type*} [DecidableEq E] (left right : E → V)
    (n : E → ℕ) (e : E) :
    GM04.IsEdgeSubdivision (edgeChains left right n)
      (edgeChains left right (Function.update n e (n e + 1))) := by
  classical
  set n' := Function.update n e (n e + 1)
  let u := chainStem left e (n e)
  let w : V ⊕ (E × ℕ) := Sum.inl (right e)
  let a : V ⊕ (E × ℕ) := Sum.inr (e, n e)
  have hslot1 : ¬ chainSlot n (e, 2 * n e + 1) := by
    change ¬ (2 * n e + 1 = 2 * n e ∨
      (2 * n e + 1) % 2 = 1 ∧ 2 * n e + 1 < 2 * n e)
    omega
  have hslot2 : ¬ chainSlot n (e, 2 * n e + 2) := by
    change ¬ (2 * n e + 2 = 2 * n e ∨
      (2 * n e + 2) % 2 = 1 ∧ 2 * n e + 2 < 2 * n e)
    omega
  refine ⟨(e, 2 * n e), u, w, a, (e, 2 * n e + 1), (e, 2 * n e + 2),
    edgeChains_final_link left right n e, (by change ¬ n e < n e; omega),
    hslot1, hslot2, (by intro h; have := congrArg Prod.snd h; omega), ?_, ?_, ?_⟩
  · ext z
    cases z with
    | inl v => simp [edgeChains, a]
    | inr z =>
      obtain ⟨f, k⟩ := z
      change k < n' f ↔ Sum.inr (f, k) = a ∨ k < n f
      by_cases hf : f = e
      · subst f
        simp only [n', Function.update_self, a, Sum.inr.injEq, Prod.mk.injEq,
          true_and]
        omega
      · simp only [n', Function.update_of_ne hf, a, Sum.inr.injEq, Prod.mk.injEq,
          hf, false_and, false_or]
  · ext z
    obtain ⟨f, j⟩ := z
    change chainSlot n' (f, j) ↔
      (f, j) = (e, 2 * n e + 1) ∨ (f, j) = (e, 2 * n e + 2) ∨
        chainSlot n (f, j) ∧ (f, j) ≠ (e, 2 * n e)
    by_cases hf : f = e
    · subst f
      simp only [chainSlot, n', Function.update_self, 
        ne_eq, Prod.mk.injEq, true_and]
      omega
    · simp only [chainSlot, n', Function.update_of_ne hf, 
        ne_eq, Prod.mk.injEq, hf, false_and, false_or, not_false_eq_true, and_true]
  · rintro ⟨f, j⟩ x y
    by_cases hf : f = e
    · subst f
      by_cases hj : j = 2 * n e
      · subst j
        have hnew : ¬ chainSlot n' (e, 2 * n e) := by
          simp only [chainSlot, n', Function.update_self, ]
          omega
        have h₁ : 2 * n e ≠ 2 * n e + 1 := by omega
        have h₂ : 2 * n e ≠ 2 * n e + 2 := by omega
        simp only [edgeChains, hnew, false_and, Prod.mk.injEq, true_and,
          h₁, h₂, ne_eq, eq_self, not_true_eq_false, or_false]
      · by_cases hj₁ : j = 2 * n e + 1
        · subst j
          have hnew : chainSlot n' (e, 2 * n e + 1) := by
            simp only [chainSlot, n', Function.update_self, ]
            omega
          have hdiv : (2 * n e + 1) / 2 = n e := by omega
          have hlast : 2 * n e + 1 ≠ 2 * (n e + 1) := by omega
          have hne : 2 * n e + 1 ≠ 2 * n e + 2 := by omega
          have hfin : chainFinish right n' (e, 2 * n e + 1) = Sum.inr (e, n e) := by
            simp only [chainFinish, n', Function.update_self, hlast, ↓reduceIte, hdiv]
          simp only [edgeChains, hnew, hslot1, false_and, and_false, false_or, true_and,
            ne_eq, Prod.mk.injEq, hne, hdiv, hfin, u, w, a, or_false]
        · by_cases hj₂ : j = 2 * n e + 2
          · subst j
            have hnew : chainSlot n' (e, 2 * n e + 2) := by
              simp only [chainSlot, n', Function.update_self, ]
              omega
            have hdiv : (2 * n e + 2) / 2 = n e + 1 := by omega
            have hlast : 2 * n e + 2 = 2 * (n e + 1) := by omega
            have hne : 2 * n e + 2 ≠ 2 * n e + 1 := by omega
            have hfin : chainFinish right n' (e, 2 * n e + 2) = Sum.inl (right e) := by
              simp only [chainFinish, n', Function.update_self, hlast, ↓reduceIte]
            simp only [edgeChains, hnew, hslot2, false_and, and_false, false_or, true_and,
              ne_eq, Prod.mk.injEq, hne, hdiv, hfin, chainStem, u, w, a]
          · have hslot : chainSlot n' (e, j) ↔ chainSlot n (e, j) := by
              simp only [chainSlot, n', Function.update_self, ]
              omega
            have hlast : j ≠ 2 * (n e + 1) := by omega
            have hfinish : chainFinish right n' (e, j) = chainFinish right n (e, j) := by
              simp only [chainFinish, n', Function.update_self, 
                hj, hlast, ↓reduceIte]
            simp only [edgeChains, hslot, hfinish, ne_eq, Prod.mk.injEq, true_and, hj, hj₁, hj₂,
              false_and, or_false, not_false_eq_true]
    · have hslot : chainSlot n' (f, j) ↔ chainSlot n (f, j) := by
        simp only [chainSlot, n', Function.update_of_ne hf, ]
      have hfinish : chainFinish right n' (f, j) = chainFinish right n (f, j) := by
        simp only [chainFinish, n', Function.update_of_ne hf, ]
      simp only [edgeChains, hslot, hfinish, ne_eq, Prod.mk.injEq, hf, false_and,
        or_false, not_false_eq_true, true_and]

end GraphMinor.Kruskal
