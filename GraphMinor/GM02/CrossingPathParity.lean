module

public import GraphMinor.GM02.CrossingPathLists
import GraphMinor.GM02.TerminationGraph
import GraphMinor.GM02.TerminationRestriction
import GraphMinor.GM02.RecoverCrossingPaths
import GraphMinor.GM02.RecoverCrossingSupports

/-!
# Parity of crossing-path lists

In the small-separator cases of II (2.8), the parity of the number of
internal separator vertices on each path is fixed by its two original
endpoints. Restrict the first termination to that path. Its support has
even size. Every internal vertex belongs to that support, and either
endpoint belongs to it exactly when it is assigned to the first side.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- An edge of the path graph cannot leave a chosen path component. -/
theorem CrossingScheme.pairPath_adj_stays {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) {a b : α} (ha : a ∈ (C.pairPath p).support)
    (hab : C.pairGraph.Adj a b) : b ∈ (C.pairPath p).support := by
  obtain ⟨q, hq⟩ := C.path_union.choose_spec.2.2.2 s(a, b)
    ((SimpleGraph.mem_edgeSet _).2 hab)
  change s(a, b) ∈ (C.pairPath q).edges at hq
  have haq := (C.pairPath q).fst_mem_support_of_mem_edges hq
  have hbq := (C.pairPath q).snd_mem_support_of_mem_edges hq
  have hpq : p = q := by
    by_contra hn
    exact Set.disjoint_left.1 (C.pairPath_disjoint p q hn) ha haq
  exact hpq.symm ▸ hbq

private theorem ncard_list_inter {α : Type u} (l : List α) (hl : l.Nodup) (S : Set α) :
    (S ∩ {a | a ∈ l}).ncard = l.countP (fun a => a ∈ S) := by
  have heq : S ∩ {a | a ∈ l} = ((l.filter (fun a => a ∈ S)).toFinset : Set α) := by
    ext a
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset,
      List.mem_filter, decide_eq_true_eq]
    exact And.comm
  rw [heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup (hl.filter _),
    List.countP_eq_length_filter]

/-- The first matching has even support size on each chosen path. -/
theorem CrossingScheme.even_left_support_on_path {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) :
    Even ((C.pairPath p).support.countP (fun a => a ∈ C.left.support)) := by
  rw [← ncard_list_inter _ (C.pairPath_isPath p).support_nodup]
  apply C.left.even_support_inter
  intro e he a hae ha b hbe
  obtain ⟨c, heq⟩ := Sym2.mem_iff_exists.1 hae
  rw [heq] at he hbe
  rcases Sym2.mem_iff.1 hbe with rfl | rfl
  · exact ha
  · apply C.pairPath_adj_stays p ha
    apply (SimpleGraph.fromEdgeSet_adj _).2
    exact ⟨Finset.mem_union_left _ he,
      fun h => C.left.not_diag _ he (Sym2.mk_isDiag_iff.2 h)⟩

/-- The number of internal vertices plus the first-side endpoint count
is even, since it counts the first matching's support on the path. -/
theorem CrossingScheme.internal_length_parity {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (p : {p // p ∈ A₀.pairs}) :
    Even ((C.pathListArrangement.paths p).length +
      (if p.val.out.1 ∈ C.left.support then 1 else 0) +
      (if p.val.out.2 ∈ C.left.support then 1 else 0)) := by
  have heven := C.even_left_support_on_path p
  have hcount : (C.pathListArrangement.paths p).countP (fun a => a ∈ C.left.support) =
      (C.pathListArrangement.paths p).length := by
    apply List.countP_eq_length.2
    intro a ha
    have hai : a ∈ ⋃ q, {v | v ∈ C.pathListArrangement.paths q} := Set.mem_iUnion.2 ⟨p, ha⟩
    rw [C.listed_vertices_eq] at hai
    exact decide_eq_true hai.1
  rw [C.pairPath_support_eq] at heven
  simpa only [List.countP_cons, List.countP_append, List.countP_singleton, List.countP_nil, Nat.add_zero, Nat.zero_add,
    decide_eq_true_eq, hcount, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heven

/-- Outside the separator, original terminal membership in the first
support is prescribed by condition (i). -/
theorem CrossingScheme.original_left_iff {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    {a : α} (ha : a ∈ A₀.support) (hn : a ∉ V(H) ∩ V(H')) :
    a ∈ C.left.support ↔ a ∈ V(H) \ V(H') := by
  constructor
  · intro h
    have h' : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨h, hn⟩
    rw [C.left_support] at h'
    exact h'.2
  · intro h
    have h' : a ∈ A₀.support ∩ (V(H) \ V(H')) := ⟨ha, h⟩
    rw [← C.left_support] at h'
    exact h'.1

/-- With no original terminal in the separator, all schemes have the
same internal-list length parity for each original pair. -/
theorem CrossingScheme.internal_length_mod_two_eq {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C D : CrossingScheme G H H' A₀)
    (hno : Disjoint (V(H) ∩ V(H')) A₀.support) (p : {p // p ∈ A₀.pairs}) :
    (C.pathListArrangement.paths p).length % 2 = (D.pathListArrangement.paths p).length % 2 := by
  have hs : p.val.out.1 ∈ A₀.support :=
    Set.mem_iUnion.2 ⟨p.val, Set.mem_iUnion.2 ⟨p.property, Sym2.out_fst_mem _⟩⟩
  have ht : p.val.out.2 ∈ A₀.support :=
    Set.mem_iUnion.2 ⟨p.val, Set.mem_iUnion.2 ⟨p.property, Sym2.out_snd_mem _⟩⟩
  have hsn : p.val.out.1 ∉ V(H) ∩ V(H') := fun h => Set.disjoint_left.1 hno h hs
  have htn : p.val.out.2 ∉ V(H) ∩ V(H') := fun h => Set.disjoint_left.1 hno h ht
  have heqs := (C.original_left_iff hs hsn).trans (D.original_left_iff hs hsn).symm
  have heqt := (C.original_left_iff ht htn).trans (D.original_left_iff ht htn).symm
  obtain ⟨i, hi⟩ := C.internal_length_parity p
  obtain ⟨j, hj⟩ := D.internal_length_parity p
  simp only [heqs, heqt] at hi
  omega

end GraphMinor.GM02
