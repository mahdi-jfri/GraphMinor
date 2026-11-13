module

public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Filtering deleted neighbours

The first part of a surviving vertex's new list is its old list with deleted neighbours
removed. The deletion marks provide a constant-time test for each old neighbour.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Reading membership marks gives zero or one. -/
theorem eval_membershipMark {w N : ℕ} (a r : ℕ) {s : State} {dl : List ℕ} {y : ℕ}
    (hm : s.arrs a = setAt (List.replicate N 0) dl 1) (hy : s.regs r = y)
    (hyN : y < N) (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some (if y ∈ dl then 1 else 0) := by
  have hlen : y < (s.arrs a).length := by simp only [hm, length_setAt, List.length_replicate]; exact hyN
  have hval : (s.arrs a)[y] = if y ∈ dl then 1 else 0 := by
    simp only [hm]
    rw [getElem_setAt _ _ _ _ (by simpa using hyN)]
    simp
  have he := eval_read (w := w) (a := a) (eval_reg hy (by omega)) hlen
    (by rw [hval]; split <;> omega)
  simpa only [hval] using he

/-- Emit a neighbour when it is not marked for deletion. -/
def emitUnmarkedProg (a_mark buf r_cnt r_y : ℕ) : Cmd :=
  .ite (.read a_mark (.reg r_y)) .skip (emitProg buf r_cnt (.reg r_y))

/-- The mark test emits exactly the undeleted neighbours. -/
theorem emitUnmarkedProg_exec {w N : ℕ} (a_mark buf r_cnt r_y : ℕ)
    {s : State} {dl pre : List ℕ} {k y : ℕ}
    (hm : s.arrs a_mark = setAt (List.replicate N 0) dl 1)
    (hb : IsBuf buf r_cnt pre k s) (hy : s.regs r_y = y)
    (hyN : y < N) (hN : N < 2 ^ w) (hw : 1 < 2 ^ w)
    (hk : (if y ∉ dl then 1 else 0) ≤ k) (hcap : pre.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (emitUnmarkedProg a_mark buf r_cnt r_y) s s' t ∧ t ≤ 10 ∧
      IsBuf buf r_cnt (pre ++ if y ∉ dl then [y] else [])
        (k - if y ∉ dl then 1 else 0) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_cnt → s'.regs r = s.regs r) := by
  classical
  have hev := eval_membershipMark a_mark r_y hm hy hyN hN hw
  by_cases hym : y ∈ dl
  · have hv : (Expr.read a_mark (.reg r_y)).eval w s = some 1 := by simpa [hym] using hev
    refine ⟨s, 3, .ite_true hv (by decide) (.skip s), by omega, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    simpa [hym] using hb
  · have hv : (Expr.read a_mark (.reg r_y)).eval w s = some 0 := by simpa [hym] using hev
    have hk1 : k = (k - 1) + 1 := by
      have : 1 ≤ k := by simpa [hym] using hk
      omega
    obtain ⟨s', hex, hb', ha, hr⟩ := emitReg_exec buf r_cnt r_y
      (by rw [← hk1]; exact hb) hy (by omega) hcap
    exact ⟨s', 9, .ite_false hv hex, by omega, by simpa [hym] using hb', ha, hr⟩

/-- Emit the undeleted entries of one old adjacency list. -/
def emitSurvivingListProg (a_s a_e a_ent a_mark buf R : ℕ) : Cmd :=
  forList a_s a_e a_ent R (R + 1) (R + 2) (R + 3)
    (emitUnmarkedProg a_mark buf (R + 4) (R + 3))

/-- Filtering one old adjacency list takes linear time in its length. -/
theorem emitSurvivingListProg_exec {w N : ℕ} (a_s a_e a_ent a_mark buf R : ℕ)
    {s : State} {dl pre l : List ℕ} {k x st en : ℕ}
    (hent : a_ent ≠ buf) (hmne : a_mark ≠ buf)
    (hl : IsListAt a_s a_e a_ent x st en l s) (hx : s.regs R = x)
    (hm : s.arrs a_mark = setAt (List.replicate N 0) dl 1)
    (hb : IsBuf buf (R + 4) pre k s) (hk : (l.filter (fun y => y ∉ dl)).length ≤ k)
    (hlt : ∀ y ∈ l, y < N) (hN : N < 2 ^ w) (hxw : x < 2 ^ w)
    (hen : en < 2 ^ w) (hw : pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (emitSurvivingListProg a_s a_e a_ent a_mark buf R) s s' t ∧
      t ≤ 9 + 20 * l.length ∧
      IsBuf buf (R + 4) (pre ++ l.filter (fun y => y ∉ dl))
        (k - (l.filter (fun y => y ∉ dl)).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        s'.regs r = s.regs r) := by
  classical
  let g : ℕ → List ℕ := fun y => if y ∉ dl then [y] else []
  have hg : l.flatMap g = l.filter (fun y => y ∉ dl) := by
    clear hl hk hlt
    induction l with
    | nil => rfl
    | cons y l ih =>
      simp only [List.flatMap_cons, List.filter_cons]
      by_cases hy : y ∈ dl <;> simpa [g, hy] using ih
  let Q : ℕ → State → Prop := fun _ z =>
    (∀ a, a ≠ buf → z.arrs a = s.arrs a) ∧
    (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 → z.regs r = s.regs r)
  obtain ⟨s', t, hex, ht, hQ, hb'⟩ := forListEmit_exec (w := w) a_s a_e a_ent R (R + 1)
    (R + 2) (R + 3) buf (R + 4) (emitUnmarkedProg a_mark buf (R + 4) (R + 3))
    x st en l g Q 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) hen hxw hl hx (fun y hy => (hlt y hy).trans hN)
    ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩ hb (by rw [hg]; exact hk)
    (fun j z z' h ha hr => ⟨fun a ha' => by rw [ha, h.1 a ha'],
      fun r h1 h2 h3 h4 => by rw [hr r h1 h2 h3, h.2 r h1 h2 h3 h4]⟩)
    (fun _ z h => h.1 a_ent hent)
    (fun j hj z pre' k' h hrk hrhi hry hb'' hk' hcap => by
      obtain ⟨z', t', he, ht', hb''', ha, hr⟩ := emitUnmarkedProg_exec (w := w)
        a_mark buf (R + 4) (R + 3) ((h.1 a_mark hmne).trans hm) hb'' hry
        (hlt _ (List.getElem_mem hj)) hN (by omega)
        (by by_cases hy : l[j] ∈ dl <;> simpa [g, hy] using hk') (by omega)
      refine ⟨z', t', he, ht', ⟨?_, ?_⟩, ?_, ?_, ?_⟩
      · intro a ha'; rw [ha a ha', h.1 a ha']
      · intro r h1 h2 h3 h4; rw [hr r h4, h.2 r h1 h2 h3 h4]
      · rw [hr (R + 1) (by omega)]; exact hrk
      · rw [hr (R + 2) (by omega)]; exact hrhi
      · by_cases hy : l[j] ∈ dl <;> simpa [g, hy] using hb''')
  exact ⟨s', t, hex, by omega, by simpa only [hg] using hb', hQ.1, hQ.2⟩

end GraphMinor.Compute.Crossing
