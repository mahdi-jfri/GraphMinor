module

public import GraphMinor.GM05.CircuitPackingDefs
public import GraphMinor.GM05.SeriesParallelDefs
import GraphMinor.GM05.SubtreePacking
import GraphMinor.GM05.ConnectedBags
import GraphMinor.GM05.ShadowMinor
import GraphMinor.GM09.Basic
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Circuit packing in graphs of bounded tree-width

The bags meeting each circuit form a nonempty subtree of the decomposition
tree. Pack these subtrees or hit them with fewer than `k` tree vertices.
Disjoint subtrees give disjoint circuits. The union of the selected bags is
a circuit hitting set of size at most `(k - 1) * (w + 1)`.
-/

public section

namespace GraphMinor.GM05

open Graph Set SimpleGraph GM09 Surface

variable {α β : Type*}

private lemma reachable_of_walk {G : Graph α β} {x y : α} (W : GraphWalk G x y) :
    Relation.ReflTransGen G.Adj x y := by
  induction W with
  | nil _ => exact .refl
  | cons h _ ih => exact .head ⟨_, h⟩ ih

/-- A circuit is connected, also after forgetting loops and parallel copies. -/
theorem circuit_shadow_connected {G C : Graph α β} (hC : IsGraphCircuit G C) :
    (simpleShadow C).Connected := by
  obtain ⟨hCG, u, W, hs, hlen, hV, hE⟩ := hC
  apply (graphConnected_iff_simpleShadow_connected C).mp
  refine ⟨⟨u, W.mem_vertexSet_of_mem_support W.start_mem_support⟩, ?_⟩
  intro x hx y hy
  have hxW : x ∈ W.support := by rwa [hV, mem_ofPred_eq] at hx
  have hyW : y ∈ W.support := by rwa [hV, mem_ofPred_eq] at hy
  obtain ⟨X, X', hX⟩ := W.exists_append_of_mem hxW
  obtain ⟨Y, Y', hY⟩ := W.exists_append_of_mem hyW
  exact reachable_of_walk (X.reverse.append Y)

/-- In a finite graph of width at most `w`, either there are `k` disjoint
circuits, or at most `(k - 1) * (w + 1)` vertices meet every circuit. -/
theorem circuits_pack_or_hit_of_treeWidthLE {G : Graph α β}
    (_hVG : V(G).Finite) {w k : ℕ} (hw : TreeWidthLE (simpleShadow G) w) :
    HasDisjointCircuits G k ∨
      ∃ X ⊆ V(G), X.ncard ≤ (k - 1) * (w + 1) ∧ HitsCircuits G X := by
  classical
  obtain ⟨ι, _, T, χ, htd, hwidth⟩ := hw
  have hcover : (⋃ t, χ t) = V(G) := htd.iUnion_eq
  let I := {C : Graph α β // IsGraphCircuit G C}
  let A : I → Set ι := fun C ↦ {t | (χ t ∩ V(C.1)).Nonempty}
  have hN : ∀ C, (A C).Nonempty := by
    intro C
    obtain ⟨x, hx⟩ := (circuit_shadow_connected C.2).nonempty
    have hxG : x ∈ V(G) := C.2.1.vertexSet_mono hx
    rw [← hcover] at hxG
    obtain ⟨t, ht⟩ := mem_iUnion.mp hxG
    exact ⟨t, x, ht, hx⟩
  have hconv : ∀ C a, a ∈ A C → ∀ b, b ∈ A C → ∀ c,
      OnTreePath T a b c → c ∈ A C := by
    intro C a ha b hb c hp
    exact htd.meets_connected_on_path (simpleShadow_mono C.2.1)
      (circuit_shadow_connected C.2) hp ha hb
  rcases subtrees_pack_or_hit htd.isTree A hN hconv k with
    ⟨f, hf⟩ | ⟨Y, hY, hhit⟩
  · left
    refine ⟨fun i ↦ (f i).1, fun i ↦ (f i).2, ?_⟩
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hxG : x ∈ V(G) := (f i).2.1.vertexSet_mono hxi
    rw [← hcover] at hxG
    obtain ⟨t, ht⟩ := mem_iUnion.mp hxG
    exact Set.disjoint_left.mp (hf hij)
      (show t ∈ A (f i) from ⟨x, ht, hxi⟩) ⟨x, ht, hxj⟩
  · right
    let X : Set α := ⋃ t ∈ Y, χ t
    have hXG : X ⊆ V(G) := by
      intro x hx
      change x ∈ ⋃ t ∈ Y, χ t at hx
      obtain ⟨t, ht⟩ := mem_iUnion.mp hx
      obtain ⟨htY, hx⟩ := mem_iUnion.mp ht
      rw [← hcover]
      exact mem_iUnion.mpr ⟨t, hx⟩
    have hsize : X.ncard ≤ Y.ncard * (w + 1) := by
      have hsame : X = ⋃ t ∈ Y.toFinset, χ t := by
        ext x
        simp [X]
      rw [hsame]
      calc _ ≤ ∑ t ∈ Y.toFinset, (χ t).ncard := Finset.set_ncard_biUnion_le _ _
        _ ≤ ∑ t ∈ Y.toFinset, (w + 1) :=
          Finset.sum_le_sum (fun t ht ↦ hwidth t)
        _ = Y.ncard * (w + 1) := by
          simp only [Finset.sum_const, smul_eq_mul]
          rw [← ncard_eq_toFinset_card' Y]
    refine ⟨X, hXG, hsize.trans (Nat.mul_le_mul_right (w + 1) (by omega)), ?_⟩
    intro C hC
    obtain ⟨t, htY, htA⟩ := hhit ⟨C, hC⟩
    obtain ⟨x, hxχ, hxC⟩ := htA
    refine ⟨x, ?_, hxC⟩
    exact mem_iUnion.mpr ⟨t, mem_iUnion.mpr ⟨htY, hxχ⟩⟩

/-- A circuit hitting set leaves no circuit after its vertices are deleted. -/
theorem HitsCircuits.no_circuit_delete {G : Graph α β} {X : Set α}
    (h : HitsCircuits G X) : ¬ ∃ C, IsGraphCircuit (deleteVertices G X) C := by
  rintro ⟨C, hC⟩
  have hCG : IsGraphCircuit G C := ⟨hC.1.trans (deleteVertices_le G X), hC.2⟩
  obtain ⟨x, hxX, hxC⟩ := h C hCG
  exact (hC.1.vertexSet_mono hxC).2 hxX

end GraphMinor.GM05
