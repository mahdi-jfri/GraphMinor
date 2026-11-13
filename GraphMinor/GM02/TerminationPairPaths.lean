module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.TerminationGraph

/-!
# The paths consisting of termination pairs

The graph of a termination is already a disjoint union of one-edge paths,
one for each pair. This verifies the path-union condition directly and
provides the simplest examples of crossing schemes in II, Section 2.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u

/-- A termination's own matching consists of its prescribed one-edge paths. -/
theorem Termination.isPairPathUnion {α : Type u} {vertices : Set α}
    (A : Termination vertices) : IsPairPathUnion A A.pairGraph A.support := by
  have hadj : ∀ p : {p // p ∈ A.pairs}, A.pairGraph.Adj p.val.out.1 p.val.out.2 := by
    intro p
    apply A.pairGraph_adj_iff.2
    have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
    rw [hout]
    exact p.property
  let P := fun p : {p // p ∈ A.pairs} => (hadj p).toWalk
  have hmem : ∀ p a, a ∈ (P p).support ↔ a ∈ p.val := by
    intro p a
    have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
    conv_rhs => rw [← hout, Sym2.mem_iff]
    simp [P, SimpleGraph.Adj.toWalk]
  refine ⟨P, fun p => Walk.IsPath.of_adj (hadj p), ?_, ?_, ?_⟩
  · intro p q hpq
    apply Set.disjoint_left.2
    intro a hap haq
    have hval : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
    exact Set.disjoint_left.1 (A.disjoint p.val p.property q.val q.property hval)
      ((hmem p a).1 hap) ((hmem q a).1 haq)
  · ext a
    constructor
    · intro ha
      obtain ⟨p, hap⟩ := Set.mem_iUnion.1 ha
      exact Set.mem_iUnion.2 ⟨p.val, Set.mem_iUnion.2 ⟨p.property, (hmem p a).1 hap⟩⟩
    · intro ha
      obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 ha
      obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
      exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, (hmem ⟨p, hp⟩ a).2 hap⟩
  · intro e he
    have hep : e ∈ A.pairs := by
      induction e using Sym2.inductionOn with
      | hf a b => exact A.pairGraph_adj_iff.1 ((SimpleGraph.mem_edgeSet _).1 he)
    refine ⟨⟨e, hep⟩, ?_⟩
    have hout : s(e.out.1, e.out.2) = e := e.out_eq
    simp [P, SimpleGraph.Adj.toWalk, hout]

end GraphMinor.GM02
