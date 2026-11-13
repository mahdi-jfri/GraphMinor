module

public import GraphMinor.GM02.CrossingPathLists
import GraphMinor.GM02.PathSupportFilter

/-!
# Recovering the graph of crossing paths

The list encoding for II (2.8) records each path with its two original
endpoints removed. Restore these endpoints to recover the full ordered
support, hence its edges. The paths cover all edges of the two
terminations, so equal list encodings give equal graphs of pairs.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Restoring the original endpoints recovers a chosen crossing path. -/
theorem CrossingScheme.pairPath_support_eq {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) :
    (C.pairPath p).support = p.val.out.1 ::
      (C.pathListArrangement.paths p ++ [p.val.out.2]) := by
  have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
  have hne : p.val.out.1 ≠ p.val.out.2 := by
    intro heq
    apply A₀.not_diag p.val p.property
    rw [← hout, Sym2.mk_isDiag_iff]
    exact heq
  apply support_eq_cons_filter_append (C.pairPath p) (C.pairPath_isPath p) hne
  intro a ha
  rw [decide_eq_true_eq]
  constructor
  · intro h
    constructor
    · intro heq
      apply h.2
      apply (C.pairPath_original_iff p ha).2
      rw [← hout]
      exact Sym2.mem_iff.2 (Or.inl heq)
    · intro heq
      apply h.2
      apply (C.pairPath_original_iff p ha).2
      rw [← hout]
      exact Sym2.mem_iff.2 (Or.inr heq)
  · intro h
    apply C.pairPath_internal_separator p ha
    rw [← hout, Sym2.mem_iff]
    exact fun heq => heq.elim h.1 h.2

/-- Equal internal lists recover the same ordered path supports. -/
theorem CrossingScheme.pairPath_support_eq_of_lists {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} {C D : CrossingScheme G H H' A₀}
    (h : C.pathListArrangement.paths = D.pathListArrangement.paths)
    (p : {p // p ∈ A₀.pairs}) : (C.pairPath p).support = (D.pairPath p).support := by
  rw [C.pairPath_support_eq, D.pairPath_support_eq, h]

/-- Equal internal lists recover the entire graph of the two terminations,
because condition (iv) says that their paths cover every edge. -/
theorem CrossingScheme.pairGraph_eq_of_lists {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} {C D : CrossingScheme G H H' A₀}
    (h : C.pathListArrangement.paths = D.pathListArrangement.paths) :
    C.pairGraph = D.pairGraph := by
  have hedges : ∀ p, (C.pairPath p).edges = (D.pairPath p).edges := by
    intro p
    rw [SimpleGraph.Walk.edges_eq_zipWith_support, SimpleGraph.Walk.edges_eq_zipWith_support,
      CrossingScheme.pairPath_support_eq_of_lists h p]
  apply SimpleGraph.edgeSet_injective
  ext e
  constructor
  · intro he
    obtain ⟨p, hp⟩ := C.path_union.choose_spec.2.2.2 e he
    change e ∈ (C.pairPath p).edges at hp
    rw [hedges p] at hp
    exact (D.pairPath p).edges_subset_edgeSet hp
  · intro he
    obtain ⟨p, hp⟩ := D.path_union.choose_spec.2.2.2 e he
    change e ∈ (D.pairPath p).edges at hp
    rw [← hedges p] at hp
    exact (C.pairPath p).edges_subset_edgeSet hp

end GraphMinor.GM02
