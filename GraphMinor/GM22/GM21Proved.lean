module

public import GraphMinor.GM22.Cited
public import GraphMinor.GM21.Final

/-!
# Graph Minors XXI, (1.1), in the definitions used by XXII

The linkage and tree-decomposition definitions agree with those of XXI.
The resulting equivalence supplies the proved vital-linkage theorem to XXII.
-/

public section

namespace GraphMinor.GM22

open Set Function Topology Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁ u₂ v₂

/-- `GM22.IsVitalPLinkage` and `GM21.Final.IsVitalPLinkage` are definitionally equal. -/
theorem isVitalPLinkage_iff_gm21 {α : Type u} {β : Type v} (G L : Graph α β) (p : ℕ) :
    IsVitalPLinkage G L p ↔ GM21.Final.IsVitalPLinkage G L p :=
  Iff.rfl

/-- `GM22.IsGraphTreeDecomposition` and `GM21.IsGraphTreeDecomposition` have identical fields. -/
theorem isGraphTreeDecomposition_iff_gm21 {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    (G : Graph α β) (T : SimpleGraph ι) (W : ι → Graph α β) :
    IsGraphTreeDecomposition G T W ↔ GM21.IsGraphTreeDecomposition G T W :=
  ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-- `GM22.TreeWidthLE` and `GM21.TreeWidthLE` are equivalent. -/
theorem treeWidthLE_iff_gm21 {α : Type u} {β : Type v} (G : Graph α β) (w_tw : ℕ) :
    TreeWidthLE G w_tw ↔ GM21.TreeWidthLE G w_tw := by
  unfold TreeWidthLE GM21.Final.TreeWidthLE
  refine exists_congr fun ι => exists_congr fun _ => exists_congr fun T => exists_congr fun W => ?_
  rw [isGraphTreeDecomposition_iff_gm21]

/-- `GM22.GM21Theorem11Statement` and `GM21.GM21Theorem11Statement` are equivalent. -/
theorem gm21Theorem11Statement_iff_gm21 :
    GM21Theorem11Statement.{u, v} ↔ GM21.GM21Theorem11Statement.{u, v} := by
  unfold GM21Theorem11Statement GM21.Final.GM21Theorem11Statement
  refine forall_congr' fun p => exists_congr fun w_tw => ?_
  refine forall_congr' fun α => forall_congr' fun β => forall_congr' fun G =>
    forall_congr' fun L => forall_congr' fun _ => forall_congr' fun _ => ?_
  rw [isVitalPLinkage_iff_gm21, treeWidthLE_iff_gm21]

/-- **Graph Minors XXI, (1.1)** in the types of Graph Minors XXII (`GM22.GM21Theorem11Statement`),
proved from `GM21.theorem_1_1_proof`. -/
theorem gm21Theorem11 :
    GM21Theorem11Statement.{u, v} :=
  gm21Theorem11Statement_iff_gm21.mpr GM21.theorem_1_1_proof.{u, v}

end GraphMinor.GM22
