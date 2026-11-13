module

public import GraphMinor.GM08.Section15Menger

/-!
# Boundary linking in tubes

This file defines the classes of Section 16 of Graph Minors VIII and chooses a
normal hoop with the fewest vertices, as in the proof of (16.2), page 283.
The boundary hoops ensure that the set of possible vertex counts is nonempty.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- Boundary linking in a framing, Graph Minors VIII, Section 16, page 282.
The two inner hoops have the order in condition (i), their tube has the width
and length in condition (ii), and disjoint paths join them to the boundary
hoops as in condition (iii). -/
def Tube.IsBoundaryLinked {S : Type w} [TopologicalSpace S] (τ : Tube S) (r s : ℕ) : Prop :=
  ∃ (H₁ H₂ : Set S) (hlam : AreLaminarHoops H₁ H₂)
    (_ : H₁ ⊆ cylinderBetween τ.F₁ τ.F₂) (_ : H₂ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂),
    H₂ ⊆ cylinderBetween τ.F₁ H₁ ∧ H₁ ⊆ cylinderBetween τ.F₂ H₂ ∧
    (r : ℕ∞) ≤ (τ.subTube hlam hN₁ hN₂).width ∧
    s ≤ (τ.subTube hlam hN₁ hN₂).length ∧
    HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₁) (τ.Γ.V ∩ H₁)
      (τ.Γ.V ∩ τ.F₁).ncard ∧
    HasDisjointPaths τ.Γ.toHypergraph.skeleton (τ.Γ.V ∩ τ.F₂) (τ.Γ.V ∩ H₂)
      (τ.Γ.V ∩ τ.F₂).ncard

/-- The class $\mathcal{B}(k)$ of tubular grafts of index at most $k$,
Graph Minors VIII, Section 16, page 282. Integer indices include the convention
$\mathcal{B}(-1)=\emptyset$. -/
def classB {α : Type u} {β : Type v} (k : ℤ) : Set (Graft α β) :=
  {X | IsTubularGraft X ∧ (X.index : ℤ) ≤ k}

/-- The class $\mathcal{B}(k,r,s)$ of grafts with a framing which is not
$(r,s)$-boundary-linked, Graph Minors VIII, Section 16, page 282. -/
def classBUnlinked {α : Type u} {β : Type v} (k r s : ℕ) : Set (Graft α β) :=
  {X | X.index ≤ k ∧ ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ ¬ τ.IsBoundaryLinked r s}

/-- A negative bound on the index allows no grafts. This gives the convention
$\mathcal{B}(-1)=\emptyset$ in Section 16, page 282. -/
theorem classB_neg_one {α : Type u} {β : Type v} :
    classB (α := α) (β := β) (-1) = ∅ := by
  ext X
  simp only [classB, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro _ h
  omega

/-- Choose a normal hoop with the fewest vertices. This is the choice of $k_3$
in the proof of Graph Minors VIII (16.2), page 283. -/
theorem Tube.exists_minimum_hoop {S : Type w} [TopologicalSpace S] (τ : Tube S) :
    ∃ F : Set S, IsHoop F ∧ τ.Γ.IsNormal F ∧
      F ⊆ cylinderBetween τ.F₁ τ.F₂ ∧
      ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
        H ⊆ cylinderBetween τ.F₁ τ.F₂ → (τ.Γ.V ∩ F).ncard ≤ (τ.Γ.V ∩ H).ncard := by
  classical
  let P : ℕ → Prop := fun n => ∃ F : Set S, IsHoop F ∧ τ.Γ.IsNormal F ∧
    F ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (τ.Γ.V ∩ F).ncard = n
  have hex : ∃ n, P n := ⟨_, τ.F₂, τ.isHoop_F₂, τ.isNormal_F₂,
    subset_cylinderBetween_right τ.laminar, rfl⟩
  obtain ⟨F, hF, hNF, hsub, heq⟩ := Nat.find_spec hex
  refine ⟨F, hF, hNF, hsub, fun H hH hNH hHsub => ?_⟩
  rw [heq]
  exact Nat.find_min' hex ⟨H, hH, hNH, hHsub, rfl⟩

end GraphMinor.GM08
