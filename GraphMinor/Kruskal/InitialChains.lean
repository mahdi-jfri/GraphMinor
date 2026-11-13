module

public import GraphMinor.Kruskal.EdgeChains

/-!
# The chain graph before any subdivisions

With zero internal vertices, the chain graph is just the original graph
with new names. Its original vertices are tagged by `Sum.inl`, and each
original edge is tagged by segment number zero. The isomorphism works for
loops and parallel edges as well as simple graphs.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set

/-- With no internal vertices, each edge index joins its two original ends. -/
theorem edgeChains_zero_isLink {V E : Type*} (left right : E → V) (e : E) (x y : V) :
    (edgeChains left right (fun _ ↦ 0)).IsLink (e, 0) (Sum.inl x) (Sum.inl y) ↔
      (x = left e ∧ y = right e) ∨ (x = right e ∧ y = left e) := by
  classical
  simp [edgeChains, chainSlot, chainStem, chainFinish]

/-- A graph is isomorphic to its zero-length chain construction. The supplied
end maps orient its actual edges without changing the undirected graph. -/
noncomputable def initialChainsIso {α β : Type*} (G : Graph α β)
    (left right : E(G) → V(G))
    (hends : ∀ e : E(G), G.IsLink e.val (left e).val (right e).val) :
    Iso G (edgeChains left right (fun _ ↦ 0)) where
  vertexEquiv := {
    toFun := fun v ↦ ⟨Sum.inl v, trivial⟩
    invFun := fun v ↦ match v with
      | ⟨Sum.inl x, _⟩ => x
      | ⟨Sum.inr (_, k), hk⟩ => False.elim (Nat.not_lt_zero k hk)
    left_inv := fun _ ↦ rfl
    right_inv := by
      rintro ⟨x, hx⟩
      cases x with
      | inl v => rfl
      | inr p => exact (Nat.not_lt_zero p.2 hx).elim }
  edgeEquiv := {
    toFun := fun e ↦ ⟨(e, 0), Or.inl rfl⟩
    invFun := fun d ↦ d.val.1
    left_inv := fun _ ↦ rfl
    right_inv := by
      rintro ⟨⟨e, j⟩, hj⟩
      apply Subtype.ext
      have hj' : j = 0 := by
        change j = 0 ∨ j % 2 = 1 ∧ j < 0 at hj
        omega
      exact Prod.ext rfl hj'.symm }
  isLink_iff e x y := by
    change G.IsLink e.val x.val y.val ↔
      (edgeChains left right (fun _ ↦ 0)).IsLink (e, 0) (Sum.inl x) (Sum.inl y)
    rw [edgeChains_zero_isLink]
    constructor
    · intro h
      rcases h.eq_and_eq_or_eq_and_eq (hends e) with h | h
      · exact Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩
      · exact Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hends e
      · exact (hends e).symm

end GraphMinor.Kruskal
