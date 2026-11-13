module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.Feasibility
import GraphMinor.GM02.ExpandPairWalk

/-!
# Joining the path pieces of a crossing scheme

The reverse direction of the corrected II (2.9) replaces each edge of its
pair graph by an induced-side path. The paths for different original pairs
remain disjoint when replacement paths meet only at common endpoints.
Concatenate each original pair-graph path, then remove repeated vertices
from the resulting walk. This gives a feasible original termination.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- Join replacements along a disjoint union of pair paths. Replacements
for distinct edges may intersect only at endpoints shared by those edges. -/
theorem feasible_of_pairPathUnion_replacements {α : Type u} {β : Type v}
    {vertices S : Set α} (A : Termination vertices) (G : Graph α β) (F : SimpleGraph α)
    (hU : IsPairPathUnion A F S) (R : ∀ e : F.edgeSet, PairPath (pathGraph G) e.val)
    (hR : ∀ e f, e ≠ f → (R e).vertices ∩ (R f).vertices ⊆ {a | a ∈ e.val ∧ a ∈ f.val}) :
    A.Feasible G := by
  let P := hU.choose
  have hne : ∀ p : {p // p ∈ A.pairs}, p.val.out.1 ≠ p.val.out.2 := by
    intro p heq
    apply A.not_diag p.val p.property
    have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
    rw [← hout, Sym2.mk_isDiag_iff]
    exact heq
  let Q : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val := fun p =>
    ⟨p.val.out.1, p.val.out.2, p.val.out_eq,
      (expandPairWalk R (P p)).bypass, (expandPairWalk R (P p)).bypass_isPath⟩
  refine ⟨Q, ?_⟩
  intro p q hpq
  apply Set.disjoint_left.2
  intro a hap haq
  change a ∈ (expandPairWalk R (P p)).bypass.support at hap
  change a ∈ (expandPairWalk R (P q)).bypass.support at haq
  have hap' := (expandPairWalk R (P p)).support_bypass_subset_support hap
  have haq' := (expandPairWalk R (P q)).support_bypass_subset_support haq
  obtain ⟨e, hep, hae⟩ := mem_expandPairWalk_support_of_ne R (P p) (hne p) hap'
  obtain ⟨f, hfq, haf⟩ := mem_expandPairWalk_support_of_ne R (P q) (hne q) haq'
  have hdis := hU.choose_spec.2.1 p q hpq
  by_cases hef : e = f
  · have hzP : e.val.out.1 ∈ (P p).support :=
      (P p).mem_support_of_mem_edges hep (Sym2.out_fst_mem _)
    have hzQ : e.val.out.1 ∈ (P q).support := by
      rw [hef]
      exact (P q).mem_support_of_mem_edges hfq (Sym2.out_fst_mem _)
    exact Set.disjoint_left.1 hdis hzP hzQ
  · have haef := hR e f hef ⟨hae, haf⟩
    have haP := (P p).mem_support_of_mem_edges hep haef.1
    have haQ := (P q).mem_support_of_mem_edges hfq haef.2
    exact Set.disjoint_left.1 hdis haP haQ

end GraphMinor.GM02
