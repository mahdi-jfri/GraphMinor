module

public import GraphMinor.Compute.TwoPathsExtT2
import GraphMinor.HP25.RibList

/-!
# The collapse edges are undone without a bypass

`undoT2Lists` (`TwoPathsExtT2.lean`) undoes one collapse step `y, z, N` on the two vertex lists
of a crossing: the path that uses `y z` gets the window `N` spliced in, and is then shortened with
`bypassList`. A program that does this step by step scans both paths for each record, which costs
`O(N)` per collapse edge, and there can be about `N` collapse edges.

This file shows that, for a valid crossing, the bypass changes nothing, and that the window misses
both paths. Then a program can keep the two paths as linked lists and splice in `O(1 + |N|)` steps.

The reason is the separation in the proof of Claim 5.5 (Humeau and Pous, page 19): "$\{y_j,y_r\}$
separates them from $C$". In the formalization this is `tightZone_closed_of`: from a vertex of the
window, a walk that avoids `y` and `z` stays in a zone that misses `C`
(`GraphMinor/HP25/Sec5Tight.lean`). Suppose a path `Q` of the crossing uses `y z`, and a vertex `x`
of the window lies on `Q`. The path `Q` ends in `C` at both ends, and it meets `y` and `z` only at
the edge `y z`. So one of the two parts of `Q` from `x` to an end avoids `y` and `z`, and that end
lies in the zone. This is impossible, since the ends lie in `C`. The other path `R` misses `y` and
`z`, so it misses the window by `not_mem_window_of_tPath`.

* `spliceT2Lists`, `spliceT2All`: the splice without the bypass;
* `SpliceOK`, `SpliceAllOK`: the facts a linked-list program needs at each step;
* `undoT2Lists_eq_splice`: one step;
* `undoT2Chain_splice`: a whole `T2Chain`. `undoT2All` and `spliceT2All` agree on the steps of the
  chain, last first, and `SpliceAllOK` holds.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*} [DecidableEq V]

/-- Undo one collapse step `y, z, N` on the vertex lists `Q`, `R` of a crossing, without the
bypass: the list that uses `y z` gets the window spliced in. -/
def spliceT2Lists (y z : V) (N Q R : List V) : List V × List V :=
  if t2Uses y z N Q then (rule2PocketChain y z N Q, R)
  else if t2Uses y z N R then (Q, rule2PocketChain y z N R)
  else (Q, R)

/-- `spliceT2Lists` for the steps `steps`, in the order of the list. -/
def spliceT2All : List (V × V × List V) → List V × List V → List V × List V
  | [], qr => qr
  | (y, z, N) :: rest, qr => spliceT2All rest (spliceT2Lists y z N qr.1 qr.2)

/-- The facts that a linked-list program needs for one step `y, z, N` on the lists `Q`, `R`: the
two lists have no repeats and are disjoint, and if one of them uses `y z` (with `N` not empty),
then `N` has no repeats, misses `y` and `z`, and misses both lists. -/
def SpliceOK (y z : V) (N Q R : List V) : Prop :=
  Q.Nodup ∧ R.Nodup ∧ Q.Disjoint R ∧
    (t2Uses y z N Q = true ∨ t2Uses y z N R = true →
      N.Nodup ∧ y ∉ N ∧ z ∉ N ∧ ∀ x ∈ N, x ∉ Q ∧ x ∉ R)

/-- `SpliceOK` at every step of `spliceT2All`, and at the end the lists have no repeats and are
disjoint. -/
def SpliceAllOK : List (V × V × List V) → List V × List V → Prop
  | [], qr => qr.1.Nodup ∧ qr.2.Nodup ∧ qr.1.Disjoint qr.2
  | (y, z, N) :: rest, qr =>
    SpliceOK y z N qr.1 qr.2 ∧ SpliceAllOK rest (spliceT2Lists y z N qr.1 qr.2)

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {V : Type*} [DecidableEq V]

public section

/-- The bypass of a list without repeats is the list itself. -/
theorem bypassList_of_nodup : ∀ {l : List V}, l.Nodup → bypassList l = l
  | [], _ => rfl
  | u :: rest, h => by
    have hu : u ∉ rest := (List.nodup_cons.mp h).1
    have ih := bypassList_of_nodup (List.nodup_cons.mp h).2
    simp only [bypassList, ih, hu, ↓reduceIte]

/-- A chain of `G₀ + yz` that starts in a set closed up to `y` and `z`, and never visits them, lies
in the set. -/
theorem mem_of_chain_closed {G₀ : SimpleGraph V} {y z : V} {Z : Set V}
    (hcl : ∀ v ∈ Z, ∀ w, G₀.Adj v w → w ∈ Z ∨ w = y ∨ w = z) :
    ∀ (u : V) (L : List V), (u :: L).IsChain (G₀ ⊔ edge y z).Adj → u ∈ Z →
      (∀ t ∈ u :: L, t ≠ y ∧ t ≠ z) → ∀ x ∈ u :: L, x ∈ Z
  | u, [], _, hu, _, x, hx => by simp only [List.mem_singleton] at hx; exact hx ▸ hu
  | u, v :: L, hch, hu, ht, x, hx => by
    rw [List.isChain_cons_cons] at hch
    have hv : v ∈ Z := by
      have huy := ht u (by simp)
      have hvy := ht v (by simp)
      rcases hch.1 with h | h
      · rcases hcl u hu v h with h' | h' | h'
        · exact h'
        · exact absurd h' hvy.1
        · exact absurd h' hvy.2
      · simp only [edge_adj] at h
        rcases h.1 with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact absurd h1 huy.1
        · exact absurd h1 huy.2
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact mem_of_chain_closed hcl v L hch.2 hv (fun t h => ht t (List.mem_cons_of_mem _ h)) x hx

variable {C A B : List V} {a b : V} {k : ℕ}

/-- The window of a collapse step has no repeats and misses `y` and `z`. -/
theorem t2Step_window_nodup (step : T2Step V C A B a b k) :
    step.N.Nodup ∧ step.y ∉ step.N ∧ step.z ∉ step.N := by
  have hnd : step.P₀.support.Nodup := step.hP₀.1.support_nodup
  rw [step.hsupp] at hnd
  have hnd' : (step.L₁ ++ (step.y :: (step.N ++ step.z :: step.L₂))).Nodup := by simpa using hnd
  have h2 : (step.y :: (step.N ++ step.z :: step.L₂)).Nodup := (List.nodup_append.mp hnd').2.1
  have h3 := List.nodup_cons.mp h2
  have h4 : (step.N ++ step.z :: step.L₂).Nodup := h3.2
  refine ⟨(List.nodup_append.mp h4).1, fun h => h3.1 (List.mem_append_left _ h), fun h => ?_⟩
  exact (List.nodup_append.mp h4).2.2 step.z h step.z (by simp) rfl

/-- **A path of a crossing that uses a collapse edge misses its window.** -/
theorem t2Step_window_not_mem_of_uses (step : T2Step V C A B a b k) {u v : V}
    (Q : step.G₁.Walk u v) (hQ : IsTPath step.G₁ C Q)
    (hQe : IsListEdge Q.support step.y step.z) : ∀ x ∈ step.N, x ∉ Q.support := by
  classical
  intro x hxN hxQ
  set Z := tightZone step.G₀ {w | w ∈ C ∨ w ∈ step.P₀.support} step.N
  have hcl : ∀ v ∈ Z, ∀ w, step.G₀.Adj v w → w ∈ Z ∨ w = step.y ∨ w = step.z :=
    fun v hv w hvw => tightZone_closed_of step.hrot step.hP₀ step.hsupp step.hind step.hwc
      step.hno hv hvw
  have hxZ : x ∈ Z := Or.inl hxN
  have hnotC : ∀ t ∈ Z, t ∉ C := fun t ht => tightZone_not_mem step.hP₀ step.hsupp ht
  have hnd : Q.support.Nodup := hQ.1.support_nodup
  have hch : Q.support.IsChain step.G₁.Adj := Q.isChain_adj_support
  have hwin := t2Step_window_nodup step
  have hxy : x ≠ step.y := fun h => hwin.2.1 (h ▸ hxN)
  have hxz : x ≠ step.z := fun h => hwin.2.2 (h ▸ hxN)
  obtain ⟨l₀, l₁, hl⟩ := hQe.exists_split
  -- In both orders, `Q.support = l₀ ++ p :: q :: l₁` with `{p, q} = {y, z}`.
  obtain ⟨p, q, hsplit, hpq⟩ : ∃ p q, Q.support = l₀ ++ p :: q :: l₁ ∧
      ((p = step.y ∧ q = step.z) ∨ (p = step.z ∧ q = step.y)) := by
    rcases hl with h | h
    · exact ⟨_, _, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h, Or.inr ⟨rfl, rfl⟩⟩
  rw [hsplit] at hnd hch hxQ
  have hpl₀ : p ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 p h p (by simp) rfl
  have hql₀ : q ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 q h q (by simp) rfl
  have hnd' : (p :: q :: l₁).Nodup := (List.nodup_append.mp hnd).2.1
  have hpl₁ : p ∉ l₁ := fun h => (List.nodup_cons.mp hnd').1 (List.mem_cons_of_mem _ h)
  have hql₁ : q ∉ l₁ := (List.nodup_cons.mp (List.nodup_cons.mp hnd').2).1
  have hyz : ∀ t, t ∉ l₀ ∨ t ∉ l₁ → t ≠ p → t ≠ q → t ≠ step.y ∧ t ≠ step.z := by
    intro t _ htp htq
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨htp, htq⟩
    · exact ⟨htq, htp⟩
  have hxp : x ≠ p := by rcases hpq with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
  have hxq : x ≠ q := by rcases hpq with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
  rcases List.mem_append.mp hxQ with hx₀ | hx₁
  · -- `x` lies before the edge: the part from `x` back to the start `u` avoids `y` and `z`.
    obtain ⟨m₀, m₁, rfl⟩ := List.append_of_mem hx₀
    have hchm : (m₀ ++ [x]).IsChain step.G₁.Adj := by
      have : (m₀ ++ [x]) <+: (m₀ ++ x :: m₁ ++ p :: q :: l₁) := ⟨m₁ ++ p :: q :: l₁, by simp⟩
      exact hch.prefix this
    have hrev : (x :: m₀.reverse).IsChain step.G₁.Adj := by
      have := List.isChain_reverse.mpr hchm
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at this
      refine this.imp ?_
      intro a b h
      exact h.symm
    have hall := mem_of_chain_closed hcl x m₀.reverse hrev hxZ (fun t ht => by
      have ht' : t ∈ m₀ ++ x :: m₁ := by
        rcases List.mem_cons.mp ht with rfl | ht
        · simp
        · exact List.mem_append_left _ (List.mem_reverse.mp ht)
      refine hyz t (Or.inr ?_) (fun h => hpl₀ (h ▸ ht')) (fun h => hql₀ (h ▸ ht'))
      intro h
      exact (List.nodup_append.mp hnd).2.2 t ht' t (by simp [h]) rfl)
    have hu : u ∈ x :: m₀.reverse := by
      have hhead : (m₀ ++ x :: m₁ ++ p :: q :: l₁).head? = some u := by
        rw [← hsplit, ← Walk.cons_tail_support]; rfl
      cases m₀ with
      | nil => simp at hhead; simp [hhead]
      | cons c m₀ => simp at hhead; simp [hhead]
    exact hnotC u (hall u hu) hQ.2.1
  · -- `x` lies after the edge: the part from `x` to the end `v` avoids `y` and `z`.
    rcases List.mem_cons.mp hx₁ with h | hx₁
    · exact hxp h
    rcases List.mem_cons.mp hx₁ with h | hx₁
    · exact hxq h
    obtain ⟨m₀, m₁, rfl⟩ := List.append_of_mem hx₁
    have hchm : (x :: m₁).IsChain step.G₁.Adj := by
      have : (x :: m₁) <:+ (l₀ ++ p :: q :: (m₀ ++ x :: m₁)) := ⟨l₀ ++ p :: q :: m₀, by simp⟩
      exact hch.suffix this
    have hall := mem_of_chain_closed hcl x m₁ hchm hxZ (fun t ht => by
      have ht' : t ∈ m₀ ++ x :: m₁ := List.mem_append_right _ ht
      refine hyz t (Or.inl ?_) (fun h => hpl₁ (h ▸ ht')) (fun h => hql₁ (h ▸ ht'))
      intro h
      exact (List.nodup_append.mp hnd).2.2 t h t (by simp [ht']) rfl)
    have hv : v ∈ x :: m₁ := by
      have hlast : (l₀ ++ p :: q :: (m₀ ++ x :: m₁)).getLast? = some v := by
        rw [← hsplit, List.getLast?_eq_getLast (Walk.support_ne_nil _), Walk.getLast_support]
      have : (l₀ ++ p :: q :: (m₀ ++ x :: m₁)).getLast? = (x :: m₁).getLast? := by
        rw [show l₀ ++ p :: q :: (m₀ ++ x :: m₁) = (l₀ ++ p :: q :: m₀) ++ (x :: m₁) by simp,
          List.getLast?_append_of_ne_nil _ (by simp)]
      rw [this] at hlast
      exact List.mem_of_getLast? hlast
    exact hnotC v (hall v hv) hQ.2.2.1

/-- The splice when `y` comes just before `z`. -/
theorem rule2PocketChain_fwd {y z : V} {N l₀ l₁ : List V} (hnd : (l₀ ++ y :: z :: l₁).Nodup) :
    rule2PocketChain y z N (l₀ ++ y :: z :: l₁) = l₀ ++ y :: N ++ z :: l₁ := by
  have hy0 : y ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 y h y (by simp) rfl
  have hz0 : z ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 z h z (by simp) rfl
  have hyz : y ≠ z := fun h => by
    have := (List.nodup_append.mp hnd).2.1; simp [h] at this
  have hy : (l₀ ++ y :: z :: l₁).idxOf y = l₀.length := by
    rw [List.idxOf_append_of_notMem hy0]; simp
  have hz : (l₀ ++ y :: z :: l₁).idxOf z = l₀.length + 1 := by
    rw [List.idxOf_append_of_notMem hz0, List.idxOf_cons_ne _ hyz]; simp
  simp only [rule2PocketChain, hy, hz, show l₀.length < l₀.length + 1 by omega, ↓reduceIte]
  rw [List.take_left' rfl, show l₀.length + 1 + 1 = (l₀ ++ [y, z]).length by simp,
    show l₀ ++ y :: z :: l₁ = (l₀ ++ [y, z]) ++ l₁ by simp, List.drop_left]
  simp

/-- The splice when `z` comes just before `y`. -/
theorem rule2PocketChain_bwd {y z : V} {N l₀ l₁ : List V} (hnd : (l₀ ++ z :: y :: l₁).Nodup) :
    rule2PocketChain y z N (l₀ ++ z :: y :: l₁) = l₀ ++ z :: N.reverse ++ y :: l₁ := by
  have hy0 : y ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 y h y (by simp) rfl
  have hz0 : z ∉ l₀ := fun h => (List.nodup_append.mp hnd).2.2 z h z (by simp) rfl
  have hyz : y ≠ z := fun h => by
    have := (List.nodup_append.mp hnd).2.1; simp [h] at this
  have hz : (l₀ ++ z :: y :: l₁).idxOf z = l₀.length := by
    rw [List.idxOf_append_of_notMem hz0]; simp
  have hy : (l₀ ++ z :: y :: l₁).idxOf y = l₀.length + 1 := by
    rw [List.idxOf_append_of_notMem hy0, List.idxOf_cons_ne _ hyz.symm]; simp
  simp only [rule2PocketChain, hy, hz, show ¬ l₀.length + 1 < l₀.length by omega, ↓reduceIte]
  rw [List.take_left' rfl, show l₀.length + 1 + 1 = (l₀ ++ [z, y]).length by simp,
    show l₀ ++ z :: y :: l₁ = (l₀ ++ [z, y]) ++ l₁ by simp, List.drop_left]
  simp

omit [DecidableEq V] in
/-- Putting a list `N` disjoint from `l₀ ++ p :: q :: l₁` between `p` and `q` keeps the list
without repeats. -/
theorem nodup_insert_middle {p q : V} {M l₀ l₁ : List V} (hnd : (l₀ ++ p :: q :: l₁).Nodup)
    (hM : M.Nodup) (hMl : ∀ x ∈ M, x ∉ l₀ ++ p :: q :: l₁) :
    (l₀ ++ p :: M ++ q :: l₁).Nodup := by
  have hperm : (l₀ ++ p :: M ++ q :: l₁).Perm (M ++ (l₀ ++ p :: q :: l₁)) := by
    have h1 : l₀ ++ p :: M ++ q :: l₁ = (l₀ ++ [p]) ++ M ++ (q :: l₁) := by simp
    have h2 : l₀ ++ p :: q :: l₁ = (l₀ ++ [p]) ++ (q :: l₁) := by simp
    rw [h1, h2, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  refine hperm.nodup_iff.mpr (List.nodup_append.mpr ⟨hM, hnd, ?_⟩)
  intro x hx y hy hxy
  exact hMl x hx (hxy ▸ hy)

/-- The splice of a list without repeats that uses `y z`, by a window without repeats that misses
the list, has no repeats. -/
theorem rule2PocketChain_nodup {y z : V} {N l : List V} (hnd : l.Nodup) (he : IsListEdge l y z)
    (hN : N.Nodup) (hNl : ∀ x ∈ N, x ∉ l) : (rule2PocketChain y z N l).Nodup := by
  obtain ⟨l₀, l₁, hl | hl⟩ := he.exists_split <;> subst hl
  · rw [rule2PocketChain_fwd hnd]; exact nodup_insert_middle hnd hN hNl
  · rw [rule2PocketChain_bwd hnd]
    exact nodup_insert_middle hnd (List.nodup_reverse.mpr hN) (fun x hx => hNl x
      (List.mem_reverse.mp hx))

/-- **One collapse step, without a bypass.** For a valid crossing after a collapse step, the facts
`SpliceOK` hold, and `undoT2Lists` is `spliceT2Lists`. -/
theorem undoT2Lists_eq_splice (step : T2Step V C A B a b k) [DecidableRel step.G₀.Adj]
    {cr : CrossingWalks step.G₁ C} (hcr : cr.Valid) :
    SpliceOK step.y step.z step.N cr.Q.support cr.R.support ∧
    undoT2Lists step.y step.z step.N cr.Q.support cr.R.support =
      spliceT2Lists step.y step.z step.N cr.Q.support cr.R.support := by
  obtain ⟨-, hQ, hR, hdisj⟩ := hcr
  have hQnd := hQ.1.support_nodup
  have hRnd := hR.1.support_nodup
  have hwin := t2Step_window_nodup step
  -- A path that misses `y` misses the window, by `not_mem_window_of_tPath`.
  have hmiss : ∀ {u v : V} (W : step.G₁.Walk u v), IsTPath step.G₁ C W →
      step.y ∉ W.support → step.z ∉ W.support → ∀ x ∈ step.N, x ∉ W.support := by
    intro u v W hW hyW hzW
    have hWt : transferWalkOption (G := step.G₀) W ≠ none := fun h =>
      hyW ((t2Step_transfer_none_iff step W).mp h).2.mem_left
    obtain ⟨W₀, hW₀⟩ := Option.ne_none_iff_exists'.mp hWt
    have hsW := transferWalkOption_support hW₀
    have hNW := not_mem_window_of_tPath step.hrot step.hP₀ step.hsupp step.hind step.hwc step.hno
      W₀ (transferWalkOption_isTPath hW₀ hW) (by rw [hsW]; exact hyW) (by rw [hsW]; exact hzW)
    intro x hx
    rw [← hsW]; exact hNW x hx
  have hQuse : t2Uses step.y step.z step.N cr.Q.support = true →
      ∀ x ∈ step.N, x ∉ cr.Q.support ∧ x ∉ cr.R.support := by
    intro h x hx
    have hQe := ((t2Uses_iff _ _ _ _).mp h).2
    exact ⟨t2Step_window_not_mem_of_uses step cr.Q hQ hQe x hx,
      hmiss cr.R hR (fun h' => hdisj hQe.mem_left h') (fun h' => hdisj hQe.mem_right h') x hx⟩
  have hRuse : t2Uses step.y step.z step.N cr.R.support = true →
      ∀ x ∈ step.N, x ∉ cr.Q.support ∧ x ∉ cr.R.support := by
    intro h x hx
    have hRe := ((t2Uses_iff _ _ _ _).mp h).2
    exact ⟨hmiss cr.Q hQ (fun h' => hdisj h' hRe.mem_left) (fun h' => hdisj h' hRe.mem_right) x hx,
      t2Step_window_not_mem_of_uses step cr.R hR hRe x hx⟩
  refine ⟨⟨hQnd, hRnd, hdisj, fun h => ⟨hwin.1, hwin.2.1, hwin.2.2, ?_⟩⟩, ?_⟩
  · rcases h with h | h
    · exact hQuse h
    · exact hRuse h
  · unfold undoT2Lists spliceT2Lists
    by_cases hq : t2Uses step.y step.z step.N cr.Q.support = true
    · simp only [hq, ↓reduceIte]
      rw [bypassList_of_nodup (rule2PocketChain_nodup hQnd ((t2Uses_iff _ _ _ _).mp hq).2 hwin.1
        (fun x hx => (hQuse hq x hx).1))]
    · simp only [hq, Bool.false_eq_true, ↓reduceIte]
      by_cases hr : t2Uses step.y step.z step.N cr.R.support = true
      · simp only [hr, ↓reduceIte]
        rw [bypassList_of_nodup (rule2PocketChain_nodup hRnd ((t2Uses_iff _ _ _ _).mp hr).2
          hwin.1 (fun x hx => (hRuse hr x hx).2))]
      · simp only [hr, Bool.false_eq_true, ↓reduceIte]

/-- **A whole chain of collapse steps, without a bypass.** For a valid crossing at the end of a
`T2Chain`, `undoT2Chain` returns a valid crossing with the same ends whose vertex lists are
`spliceT2All` of the old ones, on the steps of the chain last first; and `SpliceAllOK` holds along
the way. -/
theorem undoT2Chain_splice {G H : SimpleGraph V} (chain : T2Chain V C A B a b k G H)
    {cr : CrossingWalks H C} (hcr : cr.Valid) :
    ∃ crG, undoT2Chain chain cr = some crG ∧ crG.Valid ∧ crG.u₁ = cr.u₁ ∧ crG.v₁ = cr.v₁ ∧
      crG.u₂ = cr.u₂ ∧ crG.v₂ = cr.v₂ ∧
      (crG.Q.support, crG.R.support) =
        spliceT2All (t2Steps chain).reverse (cr.Q.support, cr.R.support) ∧
      SpliceAllOK (t2Steps chain).reverse (cr.Q.support, cr.R.support) := by
  induction chain with
  | nil =>
    exact ⟨cr, rfl, hcr, rfl, rfl, rfl, rfl, rfl,
      hcr.2.1.1.support_nodup, hcr.2.2.1.1.support_nodup, hcr.2.2.2⟩
  | snoc step dec chain ih =>
    let _ := dec
    obtain ⟨cr₀, h₀, hv₀, e1, e2, e3, e4, hl₀⟩ := undoT2Edge_lists step hcr
    obtain ⟨hok, heq⟩ := undoT2Lists_eq_splice step hcr
    obtain ⟨crG, hG, hvG, f1, f2, f3, f4, hlG, hokG⟩ := ih hv₀
    rw [hl₀, heq] at hlG hokG
    refine ⟨crG, by simp only [undoT2Chain, h₀, hG], hvG, f1.trans e1, f2.trans e2, f3.trans e3,
      f4.trans e4, ?_, ?_⟩
    · rw [hlG, t2Steps, List.reverse_append, List.reverse_singleton, List.singleton_append,
        spliceT2All]
    · rw [t2Steps, List.reverse_append, List.reverse_singleton, List.singleton_append,
        SpliceAllOK]
      exact ⟨hok, hokG⟩

end

end GraphMinor.Compute.TwoPaths
