module

public import GraphMinor.Compute.GM06Alg511Flow
import Mathlib.Tactic

/-!
# Ordering the initial flow paths by their inner cuff vertices

The linkage in Section 5 of VI, pages 127–128, is indexed by its
prescribed starting vertices. The maximum-flow search may return its
paths in any order. Their starts are distinct because their vertex
supports are disjoint. If the source list has the same length as the
path family, this gives a permutation. Reindex by its inverse to put
each path at its required starting label.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- Reindex a full disjoint path family by any supplied enumeration
of its source set. The result preserves disjointness and simplicity. -/
theorem alg511_exists_source_ordered_flowPaths {n k : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} (source : Fin k → Fin n)
    (hsource : ∀ a ∈ A, ∃ i, source i = a)
    (P : Fin k → ABWalk G A B) (hdisj : PairwiseVertexDisjoint P)
    (hsimple : ∀ i, (P i).walk.IsPath) :
    ∃ Q : Fin k → ABWalk G A B,
      (∀ i, (Q i).start = source i) ∧ PairwiseVertexDisjoint Q ∧
      ∀ i, (Q i).walk.IsPath := by
  classical
  choose idx hidx using fun i => hsource (P i).start (P i).start_mem
  have hidx_inj : Function.Injective idx := by
    intro i j hij
    by_contra hne
    have hstart : (P i).start = (P j).start := by
      rw [← hidx i, ← hidx j, hij]
    exact hdisj i j hne (P i).walk.start_mem_support
      (by rw [hstart]; exact (P j).walk.start_mem_support)
  let e : Fin k ≃ Fin k := Equiv.ofBijective idx
    ⟨hidx_inj, Finite.surjective_of_injective hidx_inj⟩
  let Q := fun i => P (e.symm i)
  refine ⟨Q, ?_, ?_, fun i => hsimple (e.symm i)⟩
  · intro i
    change (P (e.symm i)).start = source i
    rw [← hidx (e.symm i)]
    exact congrArg source (e.apply_symm_apply i)
  · intro i j hij
    exact hdisj (e.symm i) (e.symm j) (e.symm.injective.ne hij)

end GraphMinor.GM06
