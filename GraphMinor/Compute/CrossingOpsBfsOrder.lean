module

public import GraphMinor.Compute.CrossingOpsBfsTrace

/-!
# A BFS queue history gives a scan order

When the queue is empty, the discovered set is closed under neighbours, so a new root
cannot reach an earlier discovered vertex. Every other newly discovered vertex has the
vertex currently being scanned as an earlier neighbour. These two facts give `IsScanOrder`.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

universe u
variable {V : Type u} [DecidableEq V]

private theorem mem_prefix_of_idxOf_lt {items fresh : List V} {a b : V}
    (hb : b ∈ items) (hlt : (items ++ fresh).idxOf a < (items ++ fresh).idxOf b) : a ∈ items := by
  by_contra ha
  rw [List.idxOf_append_of_mem hb, List.idxOf_append_of_notMem ha] at hlt
  have := List.idxOf_lt_length_of_mem hb
  omega

omit [DecidableEq V] in
private theorem reachIn_mem_of_closed {G : SimpleGraph V} {T : Set V} {items : List V}
    (hc : ∀ a ∈ items, ∀ b ∈ T, G.Adj a b → b ∈ items) {a b : V}
    (ha : a ∈ items) (hr : ReachIn G T a b) : b ∈ items := by
  obtain ⟨p, hp⟩ := hr
  have hw : ∀ {x y : V} (p : G.Walk x y), (∀ v ∈ p.support, v ∈ T) → x ∈ items → y ∈ items := by
    intro x y p
    induction p with
    | nil => intro _ hx; exact hx
    | @cons x y z hxy p ih =>
      intro hp hx
      apply ih (fun v hv => hp v (by simp [hv]))
      exact hc x hx y (hp y (by simp)) hxy
  exact hw p hp ha

private theorem earlier_neighbour_append_old {G : SimpleGraph V} {T : Set V}
    {items fresh : List V}
    (ho : ∀ a ∈ items, ∀ b ∈ items, items.idxOf a < items.idxOf b → ReachIn G T a b →
      ∃ c ∈ items, items.idxOf c < items.idxOf b ∧ G.Adj c b)
    {a b : V} (hb : b ∈ items)
    (hlt : (items ++ fresh).idxOf a < (items ++ fresh).idxOf b) (hr : ReachIn G T a b) :
    ∃ c ∈ items ++ fresh, (items ++ fresh).idxOf c < (items ++ fresh).idxOf b ∧ G.Adj c b := by
  have ha' := mem_prefix_of_idxOf_lt hb hlt
  have hlt' : items.idxOf a < items.idxOf b := by
    simpa only [List.idxOf_append_of_mem ha', List.idxOf_append_of_mem hb] using hlt
  obtain ⟨c, hc, hcb, hadj⟩ := ho a ha' b hb hlt' hr
  exact ⟨c, List.mem_append_left _ hc, by
    simpa only [List.idxOf_append_of_mem hc, List.idxOf_append_of_mem hb] using hcb, hadj⟩

/-- In a BFS history, every vertex reachable from an earlier queued vertex has an earlier
neighbour. Queue closure is used only when adding a new root. -/
theorem BfsScanTrace.earlier_neighbour {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    ∀ a ∈ items, ∀ b ∈ items, items.idxOf a < items.idxOf b → ReachIn G T a b →
      ∃ c ∈ items, items.idxOf c < items.idxOf b ∧ G.Adj c b := by
  induction h with
  | nil => simp
  | @root items head edges h empty r hr fresh ih =>
    intro a ha b hb hlt hreach
    rcases List.mem_append.mp hb with hb | hb
    · exact earlier_neighbour_append_old ih hb hlt hreach
    · have hbr : b = r := by simpa only [List.mem_singleton] using hb
      subst b
      have hai : a ∈ items := by
        rcases List.mem_append.mp ha with ha | ha
        · exact ha
        · have har : a = r := by simpa only [List.mem_singleton] using ha
          subst a
          exact False.elim (Nat.lt_irrefl _ hlt)
      have hc : ∀ x ∈ items, ∀ y ∈ T, G.Adj x y → y ∈ items := by
        intro x hx y hy hxy
        exact h.closed x (by simpa only [empty, List.take_length] using hx) y hy hxy
      exact False.elim (fresh (reachIn_mem_of_closed hc hai hreach))
  | @scan items head edges h pending fresh hnd hn ih =>
    intro a ha b hb hlt hreach
    rcases List.mem_append.mp hb with hb | hb
    · exact earlier_neighbour_append_old ih hb hlt hreach
    · have hbnot := ((hn b).mp hb).2.2
      have hu : items[head] ∈ items := List.getElem_mem pending
      refine ⟨items[head], List.mem_append_left _ hu, ?_, ((hn b).mp hb).1⟩
      rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_notMem hbnot]
      have := List.idxOf_lt_length_of_mem hu
      omega

/-- A BFS history that has discovered every input vertex gives the scan order required by
Section 7.1. The completed queue will be scanned in precisely this order. -/
theorem BfsScanTrace.isScanOrder {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges)
    (hcover : ∀ v ∈ T, v ∈ items) : IsScanOrder G T items := by
  refine ⟨h.nodup, fun v => ⟨h.mem_set v, hcover v⟩, ?_⟩
  intro i j a b hij hai hbj hr
  obtain ⟨hi, hea⟩ := List.getElem?_eq_some_iff.mp hai
  obtain ⟨hj, heb⟩ := List.getElem?_eq_some_iff.mp hbj
  have ha : a ∈ items := hea ▸ List.getElem_mem hi
  have hb : b ∈ items := heb ▸ List.getElem_mem hj
  have hia : items.idxOf a = i := by rw [← hea]; exact h.nodup.idxOf_getElem i hi
  have hib : items.idxOf b = j := by rw [← heb]; exact h.nodup.idxOf_getElem j hj
  obtain ⟨c, hc, hcb, hadj⟩ := h.earlier_neighbour a ha b hb (by omega) hr
  exact ⟨items.idxOf c, by omega, c, List.getElem?_idxOf hc, hadj⟩

end GraphMinor.Compute.Crossing
