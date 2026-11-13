module

public import GraphMinor.GM10.DiracForest

/-!
# Splitting the cycle in the low-valency proof

To build the `K₄` minor needed for the external input to X (4.2), we
remove one cycle vertex and split the remaining path between two marked
vertices. The two resulting paths are disjoint, joined by an edge, and
contain the marked vertices on opposite sides.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph

universe u

/-- Removing the base vertex from a cycle leaves a path between its two
neighbours. Every other cycle vertex remains in the path. -/
theorem cycle_without_base_path
    {V : Type u} {G : SimpleGraph V} {z : V} (p : G.Walk z z) (hp : p.IsCycle) :
    ∃ (a b : V) (q : G.Walk a b), q.IsPath ∧ z ∉ q.support ∧
      G.Adj z a ∧ G.Adj b z ∧
      (∀ x ∈ q.support, x ∈ p.support) ∧
      (∀ x ∈ p.support, x ≠ z → x ∈ q.support) := by
  cases p with
  | nil => exact (hp.not_nil (by simp)).elim
  | @cons z a _ hza r =>
    have hr : r.IsPath := (SimpleGraph.Walk.cons_isCycle_iff r hza).1 hp |>.1
    have hrr : r.reverse.IsPath := hr.reverse
    have hne : ¬ r.reverse.Nil := fun h ↦ hza.ne (hrr.nil_iff_eq.1 h)
    cases hrev : r.reverse with
    | nil => exact (hne (by rw [hrev]; simp)).elim
    | @cons _ b _ hzb q =>
      rw [hrev] at hrr
      have hq : q.IsPath := hrr.of_cons
      have hzq : z ∉ q.support := (List.nodup_cons.1 hrr.support_nodup).1
      have hsupp : r.support = q.support.reverse ++ [z] := by
        have hs := congrArg SimpleGraph.Walk.support hrev
        rw [SimpleGraph.Walk.support_reverse, SimpleGraph.Walk.support_cons] at hs
        have hs' := congrArg List.reverse hs
        simpa only [List.reverse_reverse, List.reverse_cons] using hs'
      refine ⟨a, b, q.reverse, hq.reverse, ?_, hza, hzb.symm, ?_, ?_⟩
      · simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hzq
      · intro x hx
        rw [SimpleGraph.Walk.support_reverse] at hx
        change x ∈ z :: r.support
        rw [hsupp]
        exact List.Mem.tail _ (List.mem_append_left _ hx)
      · intro x hx hxz
        rw [SimpleGraph.Walk.support_reverse]
        change x ∈ z :: r.support at hx
        rcases List.mem_cons.1 hx with hx | hx
        · exact (hxz hx).elim
        · rw [hsupp] at hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hx
          · exact (hxz (List.mem_singleton.1 hx)).elim

/-- Split a path so that two distinct marked vertices lie in different
pieces. The pieces retain the original ends and are joined by an edge. -/
theorem path_split_between_marked_vertices
    {V : Type u} {G : SimpleGraph V} {a b x y : V} (p : G.Walk a b) :
    p.IsPath → x ∈ p.support → y ∈ p.support → x ≠ y →
    ∃ (c d : V) (P : G.Walk a c) (Q : G.Walk d b),
      P.IsPath ∧ Q.IsPath ∧ G.Adj c d ∧
      Disjoint {v | v ∈ P.support} {v | v ∈ Q.support} ∧
      (∀ v ∈ P.support, v ∈ p.support) ∧
      (∀ v ∈ Q.support, v ∈ p.support) ∧
      ((x ∈ P.support ∧ y ∈ Q.support) ∨ (y ∈ P.support ∧ x ∈ Q.support)) := by
  induction p with
  | nil =>
    intro _ hx hy hxy
    exact (hxy ((List.mem_singleton.1 hx).trans (List.mem_singleton.1 hy).symm)).elim
  | @cons a c b hac p ih =>
    intro hp hx hy hxy
    have htail : p.IsPath := hp.of_cons
    have hanot : a ∉ p.support := (List.nodup_cons.1 hp.support_nodup).1
    by_cases hax : a = x ∨ a = y
    · refine ⟨a, c, SimpleGraph.Walk.nil, p, by simp, htail, hac, ?_, ?_, ?_, ?_⟩
      · rw [Set.disjoint_left]
        intro v hv hv'
        have hva : v = a := List.mem_singleton.1 hv
        exact hanot (hva ▸ hv')
      · intro v hv
        exact List.Mem.head _ |> (List.mem_singleton.1 hv ▸ ·)
      · intro v hv
        exact List.Mem.tail _ hv
      · rcases hax with rfl | rfl
        · exact Or.inl ⟨by simp, (List.mem_cons.1 hy).resolve_left hxy.symm⟩
        · exact Or.inr ⟨by simp, (List.mem_cons.1 hx).resolve_left hxy⟩
    · have hax' : x ≠ a := fun h ↦ hax (Or.inl h.symm)
      have hay' : y ≠ a := fun h ↦ hax (Or.inr h.symm)
      obtain ⟨d, e, P, Q, hP, hQ, hde, hdisj, hPsub, hQsub, hmarks⟩ :=
        ih htail ((List.mem_cons.1 hx).resolve_left hax')
          ((List.mem_cons.1 hy).resolve_left hay') hxy
      have haP : a ∉ P.support := fun h ↦ hanot (hPsub a h)
      refine ⟨d, e, P.cons hac, Q, hP.cons haP, hQ, hde, ?_, ?_, ?_, ?_⟩
      · rw [Set.disjoint_left] at hdisj ⊢
        intro v hv hvQ
        rcases List.mem_cons.1 hv with hva | hv
        · exact hanot (hQsub a (hva ▸ hvQ))
        · exact hdisj hv hvQ
      · intro v hv
        rcases List.mem_cons.1 hv with rfl | hv
        · exact List.Mem.head _
        · exact List.Mem.tail _ (hPsub v hv)
      · intro v hv
        exact List.Mem.tail _ (hQsub v hv)
      · rcases hmarks with ⟨hxP, hyQ⟩ | ⟨hyP, hxQ⟩
        · exact Or.inl ⟨List.Mem.tail _ hxP, hyQ⟩
        · exact Or.inr ⟨List.Mem.tail _ hyP, hxQ⟩

end GraphMinor.GM10
