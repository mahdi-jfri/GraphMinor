module

public import GraphMinor.GM04.Cited
import GraphMinor.Mader.FeedbackSet
import GraphMinor.Mader.DeletionRepresentation
import GraphMinor.Mader.ApexWellQuasiOrder
import GraphMinor.Kruskal.TopologicalTransport
import GraphMinor.Minor.Basic

/-!
# Mader's circuit-bound theorem

Graph Minors V (8.1), page 109 gives uniformly bounded sets whose deletion
leaves forests. Pass to a subsequence on which those sets have the same
cardinality. Represent each graph by ordered forest components, attachment
counts, and core counts. Labelled Kruskal, Higman, and the finite-product
order on natural numbers compare this data. The explicit chain embedding
then gives topological containment of the original multigraphs.
-/

public section

namespace GraphMinor.Mader

open Graph Kruskal

universe u v

/-- Mader's theorem in the exact interface cited by Graph Minors IV (1.3),
page 229. The proof uses V (8.1), p. 109 and the labelled Kruskal argument,
with actual edge subdivisions for the resulting containment. -/
theorem mader_circuit : GM04.MaderCircuitStatement.{u, v} := by
  intro n α β G hV hE hno
  obtain ⟨b, X, hX⟩ := exists_forest_deletion_sets n G hV hE hno
  let size : ℕ → Fin (b + 1) := fun i ↦ ⟨(X i).ncard, Nat.lt_succ_of_le (hX i).2.2.1⟩
  have heq : WellQuasiOrdered (fun a b : Fin (b + 1) ↦ a = b) :=
    Finite.wellQuasiOrdered _
  obtain ⟨η, hη⟩ := heq.exists_monotone_subseq size
  let k := (X (η 0)).ncard
  have hsize : ∀ i, (X (η i)).ncard = k := by
    intro i
    exact (congrArg Fin.val (hη 0 i (Nat.zero_le i))).symm
  let a : ∀ i, Fin k ≃ X (η i) := fun i ↦
    (finCongr (hsize i).symm).trans
      (finiteSetEnumeration (X (η i)) (hX (η i)).2.1)
  have hrep : ∀ i, ∃ (m : ℕ) (t : Fin m → OrderedTree)
      (f : Fin m → List ℕ → Fin k → ℕ) (c : Fin k × Fin k → ℕ),
      Nonempty (Iso (apexForest t f c) (G (η i))) := by
    intro i
    exact exists_apexForest_iso (hV (η i)) (hE (η i)) (hX (η i)).1
      (a i) (hX (η i)).2.2.2
  choose m t f c hIso using hrep
  obtain ⟨i, j, hij, htop⟩ := apexForest_wellQuasiOrdered k m t f c
  obtain ⟨φi⟩ := hIso i
  obtain ⟨φj⟩ := hIso j
  exact ⟨η i, η j, η.strictMono hij,
    isTopologicalMinor_iso_target φj (isTopologicalMinor_iso_source φi.symm htop)⟩

end GraphMinor.Mader
