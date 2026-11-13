module

public import GraphMinor.GM11.Corners

/-!
# Consecutive labels for the two ends of each edge

The finite input for VI (5.7), page 133, lists each edge's two
endpoints consecutively. A geometric directed end gets twice its
edge index, plus its Boolean end index. Division by two recovers
the edge. The labelling is injective even for the ends of a loop.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- The endpoint-array label of a geometric directed end. -/
def halfEdgeLabel {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {m : ℕ} (edge : Fin m ≃ Γ.E)
    (a : halfEdges Γ γ v) : ℕ :=
  2 * (edge.symm ⟨a.1.1, a.2.1⟩).val + a.1.2.toNat

/-- Every directed end has a valid position in the endpoint array. -/
theorem halfEdgeLabel_lt {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {m : ℕ} (edge : Fin m ≃ Γ.E)
    (a : halfEdges Γ γ v) : halfEdgeLabel edge a < 2 * m := by
  have hi := (edge.symm ⟨a.1.1, a.2.1⟩).isLt
  unfold halfEdgeLabel
  have hb : a.1.2.toNat ≤ 1 := by cases a.1.2 <;> decide
  omega

/-- Dividing the directed label by two returns its actual edge index. -/
theorem halfEdgeLabel_div_two {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {m : ℕ} (edge : Fin m ≃ Γ.E)
    (a : halfEdges Γ γ v) :
    halfEdgeLabel edge a / 2 = (edge.symm ⟨a.1.1, a.2.1⟩).val := by
  unfold halfEdgeLabel
  have hb : a.1.2.toNat ≤ 1 := by cases a.1.2 <;> decide
  omega

/-- The two Boolean ends remain distinct under the array labelling. -/
theorem halfEdgeLabel_injective {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {m : ℕ} (edge : Fin m ≃ Γ.E) :
    Function.Injective (halfEdgeLabel (γ := γ) (v := v) edge) := by
  intro a b hab
  have hi : edge.symm ⟨a.1.1, a.2.1⟩ = edge.symm ⟨b.1.1, b.2.1⟩ := by
    apply Fin.ext
    rw [← halfEdgeLabel_div_two edge a, ← halfEdgeLabel_div_two edge b, hab]
  have he : a.1.1 = b.1.1 := congrArg Subtype.val (edge.symm.injective hi)
  have hb : a.1.2 = b.1.2 := by
    unfold halfEdgeLabel at hab
    rw [hi] at hab
    have hn : a.1.2.toNat = b.1.2.toNat := Nat.add_left_cancel hab
    cases ha : a.1.2 <;> cases hb : b.1.2 <;> simp_all
  exact Subtype.ext (Prod.ext he hb)

/-- Equality of the underlying edge is exactly equality of the quotient label. -/
theorem halfEdgeLabel_edge_iff {S : Type u} [TopologicalSpace S] {Γ : Drawing S}
    {γ : Set S → I → S} {v : S} {m : ℕ} (edge : Fin m ≃ Γ.E)
    (a : halfEdges Γ γ v) (j : Fin m) :
    a.1.1 = (edge j).1 ↔ halfEdgeLabel edge a / 2 = j.val := by
  rw [halfEdgeLabel_div_two]
  constructor
  · intro h
    have hh : (⟨a.1.1, a.2.1⟩ : Γ.E) = edge j := Subtype.ext h
    rw [hh, edge.symm_apply_apply]
  · intro h
    have hh : edge.symm ⟨a.1.1, a.2.1⟩ = j := Fin.ext h
    have he := congrArg edge hh
    rw [edge.apply_symm_apply] at he
    exact congrArg Subtype.val he

end GraphMinor.GM06
