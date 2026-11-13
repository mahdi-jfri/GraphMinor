module

public import GraphMinor.GM02.TerminationGraphMaps

/-!
# Terminal support under restriction to a boundary

Attaching vertex-membership proofs to terminal endpoints preserves
support exactly: a subtype vertex is used precisely when its original
vertex was used. The matching-graph description supplies both directions,
since each endpoint's partner also belongs to the stated vertex set.
-/

public section
namespace GraphMinor.GM02
open Set Classical
universe u

/-- Restricting endpoint types pulls the original support back to the
vertex subtype. -/
theorem Termination.onVertices_support {α : Type u} {S : Set α} (A : Termination S) :
    A.onVertices.support = Subtype.val ⁻¹' A.support := by
  ext a
  change a ∈ A.onVertices.support ↔ a.val ∈ A.support
  rw [A.onVertices.mem_support_iff_exists_adj, A.mem_support_iff_exists_adj]
  constructor
  · rintro ⟨b, hab⟩
    rw [A.onVertices_pairGraph] at hab
    exact ⟨b.val, hab⟩
  · rintro ⟨b, hab⟩
    have hpair := A.pairGraph_adj_iff.1 hab
    have hb : b ∈ S := A.vertex_mem _ hpair b (Sym2.mem_mk_right _ _)
    refine ⟨⟨b, hb⟩, ?_⟩
    rw [A.onVertices_pairGraph]
    exact hab

end GraphMinor.GM02
