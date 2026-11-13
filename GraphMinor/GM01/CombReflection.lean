module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.RootedEmbeddings
public import Mathlib.Data.Fin.Rev
import Lean.Elab.Tactic.Omega

/-!
# Reversing the comb spine

To choose a long side of the tail comb in Graph Minors I, (4.1), page 55,
the left-hand case is the right-hand case after reversing the spine.
Reflect each spine index and carry its binary copy with it. This map
preserves adjacency and is its own inverse. Its singleton branches give
a rooted model sending the reflected root back to the original root.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set SimpleGraph

/-- Reverse the spine while preserving the word inside each binary copy. -/
def combReflectVertex {N : ℕ} : PathCombVertex N → PathCombVertex N
  | .inl i => .inl i.rev
  | .inr (i, word) => .inr (i.rev, word)

/-- Reversing the spine twice restores every vertex. -/
theorem combReflectVertex_involutive {N : ℕ} :
    Function.Involutive (combReflectVertex : PathCombVertex N → PathCombVertex N) := by
  intro v
  cases v <;> simp only [combReflectVertex, Fin.rev_rev]

/-- Reflection identifies no two comb vertices. -/
theorem combReflectVertex_injective {N : ℕ} :
    Function.Injective (combReflectVertex : PathCombVertex N → PathCombVertex N) :=
  combReflectVertex_involutive.injective

/-- Reflection preserves the valid vertices of the comb. -/
theorem combReflectVertex_mem {γ N : ℕ} {v : PathCombVertex N}
    (hv : v ∈ (pathComb γ N).verts) : combReflectVertex v ∈ (pathComb γ N).verts := by
  cases v with
  | inl i => trivial
  | inr p => exact hv

/-- Reflection preserves spine, attachment and binary-copy edges. -/
theorem combReflectVertex_adj {γ N : ℕ} {v w : PathCombVertex N}
    (hvw : (pathComb γ N).Adj v w) :
    (pathComb γ N).Adj (combReflectVertex v) (combReflectVertex w) := by
  cases v with
  | inl i =>
    cases w with
    | inl j =>
      apply pathComb_spine_adj
      apply pathGraph_adj.mpr
      rcases pathGraph_adj.mp hvw with hforward | hback
      · apply Or.inr
        simp only [Fin.val_rev]
        have hi := i.isLt
        have hj := j.isLt
        omega
      · apply Or.inl
        simp only [Fin.val_rev]
        have hi := i.isLt
        have hj := j.isLt
        omega
    | inr p => exact ⟨congrArg Fin.rev hvw.1, hvw.2⟩
  | inr p =>
    cases w with
    | inl j => exact ⟨congrArg Fin.rev hvw.1, hvw.2⟩
    | inr q => exact ⟨congrArg Fin.rev hvw.1, hvw.2⟩

/-- The reflected comb rooted at the reflected vertex models the original
comb rooted at that vertex. The vertex map is explicitly reflection. -/
noncomputable def rootedCombReflectionModel {γ N : ℕ} (v : (pathComb γ N).verts) :
    RootedMinorModel
      (⟨toGraph (pathComb γ N), ⟨combReflectVertex v.val, combReflectVertex_mem v.property⟩⟩ :
        RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N)))
      (⟨toGraph (pathComb γ N), v⟩ : RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N))) := by
  let f : (pathComb γ N).verts ↪ PathCombVertex N :=
    ⟨fun x ↦ combReflectVertex x.val,
      fun _ _ heq ↦ Subtype.ext (combReflectVertex_injective heq)⟩
  let M := rootedModelOfSubgraphEmbedding (pathComb γ N) (pathComb γ N) f
    (fun x ↦ combReflectVertex_mem x.property)
    (fun h ↦ combReflectVertex_adj h)
    ⟨combReflectVertex v.val, combReflectVertex_mem v.property⟩
  exact M.mono le_rfl (combReflectVertex_involutive v.val)

end GraphMinor.GM01
