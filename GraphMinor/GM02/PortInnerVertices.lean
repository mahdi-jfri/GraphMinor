module

public import GraphMinor.GM02.PortRoutes
import GraphMinor.GM02.Section4Feasible

/-!
# Inner vertices of projected routes

Only old non-branch vertices can carry labels in the interior of a
prescribed split path. The path has no repeated vertices, so these labels
do not repeat either. Their exact correspondence with old split vertices
also transfers disjointness between different projected routes.
-/

set_option backward.isDefEq.respectTransparency.types false

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem nodup_filterMap_on {A B : Type*} (f : A → Option B) (l : List A)
    (hn : l.Nodup)
    (hi : ∀ a ∈ l, ∀ b ∈ l, ∀ x, f a = some x → f b = some x → a = b) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    have hn' := List.nodup_cons.1 hn
    have ht := ih hn'.2 (fun b hb c hc x hx hy => hi b (by simp [hb]) c (by simp [hc]) x hx hy)
    cases ha : f a with
    | none => simpa only [List.filterMap_cons, ha] using ht
    | some x =>
      simp only [List.filterMap_cons, ha, List.nodup_cons]
      refine ⟨?_, ht⟩
      rintro hx
      obtain ⟨b, hb, hbx⟩ := List.mem_filterMap.1 hx
      exact hn'.1 ((hi a (by simp) b (by simp [hb]) x ha hbx) ▸ hb)

/-- Projected path interiors have no repeated vertex and avoid all pattern branch vertices. -/
theorem exists_portRoute_inner {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (P : ∀ p : {p // p ∈ (portTermination G H choice).pairs}, PairPath (pathGraph (portGraph G H choice)) p.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices) (i : Fin k) :
    ∃ (inner : List α) (W : Surface.GraphWalk G (ends i).1 (ends i).2),
      W.support = (ends i).1 :: (inner ++ [(ends i).2]) ∧ inner.Nodup ∧
      (∀ y ∈ inner, y ∈ V(G) \ V(H)) ∧
      (∀ y, y ∈ inner ↔ portOld y ∈ (P (portPair G H choice i)).vertices) ∧
      W.edges.Nodup ∧
      (∀ e, e ∈ W.edges ↔ portEdge e ∈ (P (portPair G H choice i)).vertices) := by
  obtain ⟨q, W, hq, hWv, hWe⟩ := exists_portRoute_with_lists G H choice hVH hends P hP i
  have hst : (portTerminal (i, false) : PortVertex α β k) ≠ portTerminal (i, true) := by
    simp [portTerminal]
  obtain ⟨m, hm⟩ := Walk.exists_support_eq q.val hst
  have hn : (portTerminal (i, false) :: (m ++ [portTerminal (i, true)])).Nodup :=
    hm ▸ q.property.support_nodup
  have hmP : ∀ a ∈ m, a ∈ (P (portPair G H choice i)).vertices := by
    intro a ha
    apply hq.le
    rw [hm]
    simp [ha]
  have hms : portTerminal (i, false) ∉ m := by
    intro h
    exact (List.nodup_cons.1 hn).1 (List.mem_append_left _ h)
  have hmt : portTerminal (i, true) ∉ m := by
    intro h
    exact (List.nodup_append.1 (List.nodup_cons.1 hn).2).2.2 _ h _ (by simp) rfl
  have hi : ∀ a ∈ m, ∀ y, portLabel ends a = some y →
      a = portOld y ∧ y ∈ V(G) \ V(H) := by
    intro a ha y hy
    rcases portPath_vertex_cases G H choice P hP i a (hmP a ha) with
      ⟨z, hz, rfl⟩ | ⟨e, he, rfl⟩ | rfl | rfl
    · have hzy : z = y := Option.some.inj hy
      subst z
      exact ⟨rfl, hz⟩
    · cases hy
    · exact (hms ha).elim
    · exact (hmt ha).elim
  refine ⟨m.filterMap (portLabel ends), W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hWv, hm]
    simp [List.filterMap_append, portLabel, portTerminal]
  · apply nodup_filterMap_on _ _ (List.nodup_append.1 (List.nodup_cons.1 hn).2).1
    intro a ha b hb y hya hyb
    exact (hi a ha y hya).1.trans (hi b hb y hyb).1.symm
  · intro y hy
    obtain ⟨a, ha, hay⟩ := List.mem_filterMap.1 hy
    exact (hi a ha y hay).2
  · intro y
    constructor
    · intro hy
      obtain ⟨a, ha, hay⟩ := List.mem_filterMap.1 hy
      exact (hi a ha y hay).1 ▸ hmP a ha
    · intro hy
      have hym := hq.ge hy
      rw [hm] at hym
      have hym' : portOld y ∈ m := by simpa [portOld, portTerminal] using hym
      exact List.mem_filterMap.2 ⟨portOld y, hym', rfl⟩
  · rw [hWe]
    refine List.Nodup.filterMap (fun a b e ha hb => ?_) q.property.support_nodup
    exact ((portEdgeLabel_eq_some_iff a e).1 ha).trans
      ((portEdgeLabel_eq_some_iff b e).1 hb).symm
  · intro e
    rw [hWe, List.mem_filterMap]
    constructor
    · rintro ⟨a, ha, he⟩
      exact (portEdgeLabel_eq_some_iff a e).1 he ▸ hq.le ha
    · intro he
      exact ⟨portEdge e, hq.ge he, rfl⟩

end GraphMinor.GM02
