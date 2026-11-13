module

public import GraphMinor.GM02.CrossingScheme
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Endpoint and internal degrees in a disjoint pair-path union

In the contracted graph for corrected II (2.9), an original terminal is
an endpoint of its own path and no other path. Every other used vertex
is internal. Edge coverage and path disjointness identify all neighbors
of a used vertex with its neighbors on that path. Thus original terminals
have degree one and other used vertices have degree two.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u
variable {α : Type u} {vertices S : Set α} {F : SimpleGraph α} {A : Termination vertices}

/-- A pair endpoint lies on its assigned path in the path-union condition. -/
theorem IsPairPathUnion.endpoint_mem (hU : IsPairPathUnion A F S)
    (p : {p // p ∈ A.pairs}) {a : α} (ha : a ∈ p.val) : a ∈ (hU.choose p).support := by
  have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
  have ha' : a ∈ s(p.val.out.1, p.val.out.2) :=
    (congrArg (fun e : Sym2 α => a ∈ e) hout).mpr ha
  rcases Sym2.mem_iff.1 ha' with rfl | rfl
  · exact (hU.choose p).start_mem_support
  · exact (hU.choose p).end_mem_support

/-- Original terminals on one component path are exactly its own endpoints. -/
theorem IsPairPathUnion.original_iff (hU : IsPairPathUnion A F S)
    (p : {p // p ∈ A.pairs}) {a : α} (ha : a ∈ (hU.choose p).support) :
    a ∈ A.support ↔ a ∈ p.val := by
  constructor
  · intro ha₀
    obtain ⟨q, hqa⟩ := Set.mem_iUnion.1 ha₀
    obtain ⟨hq, haq⟩ := Set.mem_iUnion.1 hqa
    have haQ := hU.endpoint_mem ⟨q, hq⟩ haq
    have hpq : p = ⟨q, hq⟩ := by
      by_contra hn
      exact Set.disjoint_left.1 (hU.choose_spec.2.1 p ⟨q, hq⟩ hn) ha haQ
    rw [hpq]
    exact haq
  · intro hap
    exact Set.mem_iUnion.2 ⟨p.val, Set.mem_iUnion.2 ⟨p.property, hap⟩⟩

/-- Every neighbor of a component vertex lies along that component path. -/
theorem IsPairPathUnion.neighborSet_eq_path (hU : IsPairPathUnion A F S)
    (p : {p // p ∈ A.pairs}) {a : α} (ha : a ∈ (hU.choose p).support) :
    F.neighborSet a = (hU.choose p).toSubgraph.neighborSet a := by
  ext b
  constructor
  · intro hab
    obtain ⟨q, hq⟩ := hU.choose_spec.2.2.2 s(a, b) ((SimpleGraph.mem_edgeSet _).2 hab)
    have haQ := (hU.choose q).fst_mem_support_of_mem_edges hq
    have hpq : p = q := by
      by_contra hn
      exact Set.disjoint_left.1 (hU.choose_spec.2.1 p q hn) ha haQ
    subst q
    exact Walk.adj_toSubgraph_iff_mem_edges.2 hq
  · intro hab
    exact (hU.choose p).toSubgraph.adj_sub hab

/-- An original terminal has degree one; every other used vertex has degree two. -/
theorem IsPairPathUnion.neighborSet_ncard (hU : IsPairPathUnion A F S)
    {a : α} (ha : a ∈ S) : (F.neighborSet a).ncard = if a ∈ A.support then 1 else 2 := by
  have haU : a ∈ ⋃ p, {a | a ∈ (hU.choose p).support} := hU.choose_spec.2.2.1.symm ▸ ha
  obtain ⟨p, hap⟩ := Set.mem_iUnion.1 haU
  rw [hU.neighborSet_eq_path p hap]
  have hp := hU.choose_spec.1 p
  have hn : ¬(hU.choose p).Nil := by
    intro hnil
    have heq := hnil.eq
    apply A.not_diag p.val p.property
    have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
    exact (congrArg Sym2.IsDiag hout).mp (Sym2.mk_isDiag_iff.2 heq)
  by_cases ha₀ : a ∈ A.support
  · have hapair := (hU.original_iff p hap).1 ha₀
    have hout : s(p.val.out.1, p.val.out.2) = p.val := p.val.out_eq
    have ha' : a ∈ s(p.val.out.1, p.val.out.2) :=
      (congrArg (fun e : Sym2 α => a ∈ e) hout).mpr hapair
    rw [ite_eq_left ha₀]
    rcases Sym2.mem_iff.1 ha' with rfl | rfl
    · rw [hp.neighborSet_toSubgraph_startpoint hn, Set.ncard_singleton]
    · rw [hp.neighborSet_toSubgraph_endpoint hn, Set.ncard_singleton]
  · rw [ite_eq_right ha₀]
    obtain ⟨i, hi, hile⟩ := Walk.mem_support_iff_exists_getVert.1 hap
    have hpairNot : a ∉ p.val := fun h => ha₀ ((hU.original_iff p hap).2 h)
    have hi0 : i ≠ 0 := by
      intro h
      have he : p.val.out.1 = a := by simpa only [h, Walk.getVert_zero] using hi
      exact hpairNot (he ▸ Sym2.out_fst_mem p.val)
    have hiend : i ≠ (hU.choose p).length := by
      intro h
      have he : p.val.out.2 = a := by simpa only [h, Walk.getVert_length] using hi
      exact hpairNot (he ▸ Sym2.out_snd_mem p.val)
    have hilt : i < (hU.choose p).length := by omega
    exact hi ▸ hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hilt

end GraphMinor.GM02
