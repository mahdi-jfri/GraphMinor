module

public import GraphMinor.GM04.NumberedDecomposition
public import GraphMinor.GM04.Patchwork.Menger

/-!
# Patchwork results with proved inputs

Menger's theorem supplies the path-separation result. Higman's theorem supplies the
finite-set comparison in the star argument. The bounded-width simulation theorem then
applies to robust patchworks, as in Graph Minors IV, Sections 6–9.
-/

public section

namespace GraphMinor.GM04

open _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

variable {Ω : Type w} [Preorder Ω] {α : Type u} {β : Type v} {ι : Type*}

/-- Graph Minors IV, (8.3), page 249: finite labelled sets in a well-quasi-order
have label-increasing injections along an infinite set of indices. -/
theorem theorem_8_3_proof : Higman83Statement.{u, v} := higman_8_3

omit [Preorder Ω] in
/-- Graph Minors IV, (6.1), page 241, with its tree, path, and finite-set inputs proved. -/
theorem theorem_6_1_proved {P : Patchwork Ω α β} (hrob : P.IsRobust)
    {X₁ X₂ : Set α} (hX₁ : X₁ ⊆ P.G.vertexSet) (hX₂ : X₂ ⊆ P.G.vertexSet) (k : ℕ) :
    (Theorem61Cond1 P X₁ X₂ k ↔ Theorem61Cond2 P X₁ X₂ k) ∧
    (Theorem61Cond2 P X₁ X₂ k ↔ Theorem61Cond3 P X₁ X₂ k) :=
  theorem_6_1_proof menger hrob hX₁ hX₂ k

/-- Graph Minors IV, (8.4), page 249, with its tree, path, and finite-set inputs proved. -/
theorem theorem_8_4_proved (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β) (hrem : ∀ i, (P i).IsRemovable)
    (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    (hcard : ∀ i, (σ i (S i).root).vertexSet.ncard ≤ n)
    (hwqo : ∀ Q : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, Q k = (P i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (Q j) (Q j')) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') :=
  theorem_8_4_proof higman_8_3.{0, 0} hΩ n P hrem S σ hstar htd hcard hwqo

/-- Graph Minors IV, (9.1), page 252, with its tree, path, and finite-set inputs proved. -/
theorem theorem_9_1_proved (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β)
    (hrob : ∀ i, (P i).IsRobust)
    (htw : ∀ i, TreeWidthLE (P i).G n) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') :=
  theorem_9_1_proof theorem_5_3_proved menger higman_8_3.{0, 0} hΩ n P hrob htw

end GraphMinor.GM04
