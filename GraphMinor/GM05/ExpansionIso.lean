module

public import GraphMinor.GM05.ExpansionDefs
import GraphMinor.Minor.Basic

/-!
# Relabelling the graph whose expansions are packed

An isomorphism can be composed with the contraction isomorphism of an
expansion. Thus relabelling the fixed graph preserves expansion packings,
hitting sets, and the Erdős–Pósa property. This permits the proof of
Graph Minors V, (8.8), to remove unused ambient edge labels.
-/

public section

namespace GraphMinor.GM05

open Graph Set

universe u v u₁ v₁ u₂ v₂

/-- Compose the source isomorphism of an expansion. -/
theorem IsHExpansion.iso_source {α β α₁ β₁ α₂ β₂ : Type*}
    {H : Graph α₁ β₁} {K : Graph α₂ β₂} {G A : Graph α β}
    (hA : IsHExpansion K G A) (φ : Iso H K) : IsHExpansion H G A := by
  obtain ⟨hAG,C,hC,⟨ψ⟩⟩ := hA
  exact ⟨hAG,C,hC,⟨φ.trans ψ⟩⟩

/-- Relabelling the fixed graph preserves a packing of expansions. -/
theorem HasDisjointExpansions.iso_source {α β α₁ β₁ α₂ β₂ : Type*}
    {H : Graph α₁ β₁} {K : Graph α₂ β₂} {G : Graph α β} {k : ℕ}
    (h : HasDisjointExpansions K G k) (φ : Iso H K) : HasDisjointExpansions H G k := by
  obtain ⟨A,hA,hdisj⟩ := h
  exact ⟨A,fun i ↦ (hA i).iso_source φ,hdisj⟩

/-- Relabelling the fixed graph preserves a hitting set of expansions. -/
theorem HitsExpansions.iso_source {α β α₁ β₁ α₂ β₂ : Type*}
    {H : Graph α₁ β₁} {K : Graph α₂ β₂} {G : Graph α β} {X : Set α}
    (h : HitsExpansions K G X) (φ : Iso H K) : HitsExpansions H G X :=
  fun A hA ↦ h A (hA.iso_source φ.symm)

/-- The Erdős–Pósa property is invariant under graph isomorphism. -/
theorem erdosPosa_of_iso {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {H : Graph α₁ β₁} {K : Graph α₂ β₂} (φ : Iso H K)
    (hK : HasErdosPosaProperty.{u,v,u₂,v₂} K) : HasErdosPosaProperty.{u,v,u₁,v₁} H := by
  intro k
  obtain ⟨k',hk⟩ := hK k
  refine ⟨k',?_⟩
  intro α β G hV hE
  rcases hk G hV hE with hpack|⟨X,hX,hcard,hhit⟩
  · exact Or.inl (hpack.iso_source φ)
  · exact Or.inr ⟨X,hX,hcard,hhit.iso_source φ⟩

end GraphMinor.GM05
