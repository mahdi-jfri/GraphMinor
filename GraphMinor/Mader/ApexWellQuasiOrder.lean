module

public import GraphMinor.Mader.ApexContainment
public import GraphMinor.Kruskal.DecoratedForests
import Mathlib.Order.WellQuasiOrder

/-!
# Well-quasi-ordering forest attachment graphs

First pass to a subsequence with nondecreasing core edge counts. Apply
labelled Kruskal and Higman to the forest components, using the attachment
count vectors as labels. The resulting address maps and count inequalities
give topological containment by the explicit chain construction.
-/

public section

namespace GraphMinor.Mader

open Kruskal

/-- Forest attachment graphs with a fixed number of chosen vertices are
well-quasi-ordered by topological containment. Component sizes, component
counts, and all edge multiplicities can vary along the sequence. -/
theorem apexForest_wellQuasiOrdered (k : ℕ) (n : ℕ → ℕ)
    (t : ∀ i, Fin (n i) → OrderedTree)
    (f : ∀ i, Fin (n i) → List ℕ → Fin k → ℕ)
    (c : ℕ → Fin k × Fin k → ℕ) :
    ∃ i j, i < j ∧ GM04.IsTopologicalMinor
      (apexForest (t i) (f i) (c i)) (apexForest (t j) (f j) (c j)) := by
  have hcore : WellQuasiOrdered (fun a b : Fin k × Fin k → ℕ ↦ a ≤ b) :=
    wellQuasiOrdered_le
  obtain ⟨η, hη⟩ := hcore.exists_monotone_subseq c
  have hlabel : WellQuasiOrdered (fun a b : Fin k → ℕ ↦ a ≤ b) :=
    wellQuasiOrdered_le
  obtain ⟨i, j, hij, σ, hφ⟩ := exists_labelled_forest_addressEmbedding hlabel
    (fun i ↦ n (η i)) (fun i ↦ t (η i)) (fun i ↦ f (η i))
  choose φ hf using hφ
  exact ⟨η i, η j, η.strictMono hij,
    apexForest_isTopologicalMinor σ φ (f (η i)) (f (η j)) (c (η i)) (c (η j))
      (fun a p b ↦ hf a p b) (fun p ↦ hη i j hij.le p)⟩

end GraphMinor.Mader
