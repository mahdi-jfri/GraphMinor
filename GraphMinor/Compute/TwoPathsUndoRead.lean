module

public import GraphMinor.Compute.TwoPathsUndoIns
import GraphMinor.Compute.TwoPathsSweepLoop
import GraphMinor.Compute.TwoPathsSweep
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsRotate

/-!
# Reading a path back from the successor array

At the end of the undo of the collapse edges, each path is written back into its array.
`readProg A` takes the first vertex of the old path in `A` (splicing never changes it), walks the
successor array once to count the vertices, allocates `A`, and walks again to write them.

`readProg_exec`: if the successor array is that of `L` and `L'` (`linkArr`), and the old content of
`A` has the same first vertex as `L`, then `A` becomes `L`, in at most `30 + 30 |L|` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- Write into `A` the path of the successor array that starts at the first vertex of `A`. -/
def readProg (A : Arr) : Cmd :=
  .seq (.ite (.len A) (.assign rUdc (.op .add (.read A (.const 0)) (.const 1)))
    (.assign rUdc (.const 0)))
  (.seq (.assign rUdx (.reg rUdc))
  (.seq (.assign rUdn (.const 0))
  (.seq (.while (.reg rUdc) (.seq (.assign rUdn (.op .add (.reg rUdn) (.const 1)))
      (.assign rUdc (.read aUdNxt (.op .sub (.reg rUdc) (.const 1))))))
  (.seq (.alloc A (.reg rUdn))
  (.seq (.assign rUdc (.reg rUdx))
  (.seq (.assign rUdi (.const 0))
    (forUp rUdi (.reg rUdn) (.seq (.write A (.reg rUdi) (.op .sub (.reg rUdc) (.const 1)))
      (.assign rUdc (.read aUdNxt (.op .sub (.reg rUdc) (.const 1))))))))))))

/-- The registers that `readProg` writes. -/
def readRegs : List ℕ := [rUdc, rUdx, rUdn, rUdi]

/-- The cursor of the walk along `L` after `t` steps: one more than `L[t]`, or `0` at the end. -/
def curOf (L : List ℕ) (t : ℕ) : ℕ := if h : t < L.length then L[t] + 1 else 0

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

variable {w V : ℕ}

/-- One step of the walk along `L` in the successor array of `L, L'`. -/
theorem linkArr_curOf {L L' : List ℕ} (hnd : L.Nodup) (hd : ∀ v ∈ L, v ∉ L' ∧ v < V) {t : ℕ}
    (ht : t < L.length) :
    ∃ h : L[t] < (linkArr V L L').length, (linkArr V L L')[L[t]] = curOf L (t + 1) := by
  have hv := hd L[t] (List.getElem_mem _)
  refine ⟨by rw [length_linkArr]; exact hv.2, ?_⟩
  rw [linkArr_getElem, nextOf_of_not_mem hv.1, Nat.add_zero]
  by_cases h1 : t + 1 < L.length
  · rw [nextOf_getElem hnd h1]; simp [curOf, h1]
  · have hl : L ≠ [] := List.ne_nil_of_length_pos (by omega)
    have : L[t] = L.getLast hl := by rw [List.getLast_eq_getElem]; congr 1; omega
    rw [this, nextOf_last hnd hl]; simp [curOf, h1]

theorem curOf_le {L : List ℕ} (hd : ∀ v ∈ L, v < V) (t : ℕ) : curOf L t ≤ V := by
  unfold curOf; split_ifs with h
  · have := hd _ (List.getElem_mem h); omega
  · omega

/-- The step of both walks: `c := nxt[c - 1]`. -/
theorem walkStep_eval {s : State} {L L' : List ℕ} (hnd : L.Nodup)
    (hd : ∀ v ∈ L, v ∉ L' ∧ v < V) (hnxt : s.arrs aUdNxt = linkArr V L L') {t : ℕ}
    (ht : t < L.length) (hc : s.regs rUdc = curOf L t) (hVw : V < 2 ^ w) :
    (Expr.read aUdNxt (.op .sub (.reg rUdc) (.const 1))).eval w s = some (curOf L (t + 1)) := by
  obtain ⟨hlt, hget⟩ := linkArr_curOf hnd hd ht
  have hcv : curOf L t = L[t] + 1 := by simp [curOf, ht]
  have hcV := curOf_le (fun v h => (hd v h).2) t
  have hsub : (Expr.op .sub (.reg rUdc) (.const 1)).eval w s = some L[t] := by
    have := sub_eval (w := w) (s := s) (reg_eval hc (by omega)) (const_eval' (w := w) (c := 1)
      (by omega))
    rwa [hcv, Nat.add_sub_cancel] at this
  have := read_eval (w := w) (s := s) (a := aUdNxt) hsub (by rw [hnxt]; exact hlt)
    (by simp only [hnxt, hget]; have := curOf_le (fun v h => (hd v h).2) (t + 1); omega)
  simpa only [hnxt, hget] using this

/-- The counting walk. -/
theorem countLoop_exec {L L' : List ℕ} (hnd : L.Nodup) (hd : ∀ v ∈ L, v ∉ L' ∧ v < V)
    (hVw : V < 2 ^ w) (hLw : L.length < 2 ^ w) :
    ∀ d t (s : State), t + d = L.length → s.regs rUdc = curOf L t → s.regs rUdn = t →
      s.arrs aUdNxt = linkArr V L L' →
      ∃ s' c, Exec w (.while (.reg rUdc) (.seq (.assign rUdn (.op .add (.reg rUdn) (.const 1)))
          (.assign rUdc (.read aUdNxt (.op .sub (.reg rUdc) (.const 1)))))) s s' c ∧
        c ≤ 1 + 10 * d ∧ Keeps [rUdn, rUdc] [] s s' ∧ s'.regs rUdn = L.length := by
  intro d
  induction d with
  | zero =>
    intro t s htd hc hn _
    have hc0 : s.regs rUdc = 0 := by rw [hc]; simp [curOf]; omega
    exact ⟨s, _, .while_false (reg_eval hc0 (by omega)), by simp, Keeps.refl _ _ _,
      by rw [hn]; omega⟩
  | succ d ih =>
    intro t s htd hc hn hnxt
    have ht : t < L.length := by omega
    have hcv : curOf L t = L[t] + 1 := by simp [curOf, ht]
    have hcV := curOf_le (fun v h => (hd v h).2) t
    set s₁ := s.setReg rUdn (t + 1)
    have hex₁ : Exec w (.assign rUdn (.op .add (.reg rUdn) (.const 1))) s s₁ 4 :=
      .assign (add_eval (reg_eval hn (by omega)) (const_eval' (w := w) (by omega)) (by omega))
    have hstep := walkStep_eval (w := w) (s := s₁) hnd hd (by simp [s₁, hnxt]) ht
      (by simp [s₁, hc]) hVw
    obtain ⟨s', c, hex, hc', hk, hn'⟩ := ih (t + 1) (s₁.setReg rUdc (curOf L (t + 1)))
      (by omega) (by simp) (by simp [s₁]) (by simp [s₁, hnxt])
    refine ⟨s', _, .while_true (reg_eval hc (by omega)) (by rw [hcv]; omega)
      (.seq hex₁ (.assign hstep)) hex, ?_, ?_, hn'⟩
    · simp only [Expr.cost] at hc' ⊢; omega
    · exact (((Keeps.refl _ _ _).setReg (by simp) _).setReg (by simp) _).trans hk
        (fun r h => h) (fun a h => h)

/-- **Reading a path back.** -/
theorem readProg_exec {A : ℕ} (hA : A ≠ aUdNxt) (hw : 1 < 2 ^ w) {s : State} {L L' : List ℕ}
    (hnd : L.Nodup) (hd : ∀ v ∈ L, v ∉ L' ∧ v < V) (hnxt : s.arrs aUdNxt = linkArr V L L')
    (hhead : (s.arrs A).head? = L.head?) (hVw : V < 2 ^ w) (hLw : L.length < 2 ^ w)
    (hAw : (s.arrs A).length < 2 ^ w) :
    ∃ s' c, Exec w (readProg A) s s' c ∧ c ≤ 30 + 30 * L.length ∧
      Keeps readRegs [A] s s' ∧ s'.arrs A = L := by
  -- the first cursor
  have hc0 : ∃ s₁ c₁, Exec w (.ite (.len A) (.assign rUdc (.op .add (.read A (.const 0))
      (.const 1))) (.assign rUdc (.const 0))) s s₁ c₁ ∧ c₁ ≤ 6 ∧ s₁ = s.setReg rUdc (curOf L 0) := by
    have hlen := len_eval (w := w) (s := s) (x := A) rfl hAw
    cases hAs : s.arrs A with
    | nil =>
      rw [hAs] at hhead hlen
      have hL : L = [] := by cases L <;> simp_all
      subst hL
      exact ⟨_, _, .ite_false hlen (.assign (const_eval' (by omega))), by simp, by simp [curOf]⟩
    | cons a as =>
      rw [hAs] at hhead hlen
      cases L with
      | nil => simp at hhead
      | cons b L₀ =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst hhead
        have haV : a < V := (hd a (by simp)).2
        have hrd : (Expr.read A (.const 0)).eval w s = some a := by
          have := read_eval (w := w) (s := s) (a := A) (const_eval' (w := w) (c := 0) (by omega))
            (by simp [hAs]) (by simp only [hAs, List.getElem_cons_zero]; omega)
          simpa [hAs] using this
        exact ⟨_, _, .ite_true hlen (by simp) (.assign (add_eval hrd (const_eval' (w := w) hw)
          (by omega))), by simp, by simp [curOf]⟩
  obtain ⟨s₁, c₁, hex₁, hc₁, rfl⟩ := hc0
  have hcV0 := curOf_le (fun v h => (hd v h).2) 0
  set s₂ := s.setReg rUdc (curOf L 0)
  set s₃ := s₂.setReg rUdx (curOf L 0)
  set s₄ := s₃.setReg rUdn 0
  obtain ⟨s₅, c₅, hex₅, hc₅, hk₅, hn₅⟩ := countLoop_exec (w := w) hnd hd hVw hLw L.length 0 s₄
    (by omega) (by simp [s₄, s₃, s₂]) (by simp [s₄]) (by simp [s₄, s₃, s₂, hnxt])
  set s₆ := s₅.setArr A (List.replicate L.length 0)
  set s₇ := s₆.setReg rUdc (curOf L 0)
  have hx₆ : s₆.regs rUdx = curOf L 0 := by
    simp only [s₆, State.setArr_regs]; rw [hk₅.1 rUdx (by simp)]; simp [s₄, s₃]
  have hnxt₅ : s₅.arrs aUdNxt = linkArr V L L' := by
    rw [hk₅.2 aUdNxt (by simp)]; simp [s₄, s₃, s₂, hnxt]
  -- the fill loop
  let I : ℕ → State → Prop := fun i st => Keeps [rUdi, rUdc] [A] s₇ st ∧ st.regs rUdi = i ∧
    st.regs rUdc = curOf L i ∧
    st.arrs A = (List.range i).map (fun j => L[j]?.getD 0) ++ List.replicate (L.length - i) 0
  have hI0 : I 0 (s₇.setReg rUdi 0) :=
    ⟨(Keeps.refl _ _ _).setReg (by simp) _, by simp, by simp [s₇], by simp [s₇, s₆]⟩
  have hn₇ : ∀ st, Keeps [rUdi, rUdc] [A] s₇ st → st.regs rUdn = L.length := fun st hk => by
    rw [hk.1 rUdn (by simp)]; simp [s₇, s₆, hn₅]
  obtain ⟨s₈, c₈, hex₈, hc₈, hI₈⟩ := forUp_pot I (fun _ => 0) L.length 11 (r_i := rUdi)
    (hi := .reg rUdn) (body := .seq (.write A (.reg rUdi) (.op .sub (.reg rUdc) (.const 1)))
      (.assign rUdc (.read aUdNxt (.op .sub (.reg rUdc) (.const 1))))) hw hLw
    (fun i _ st hst => ⟨hst.2.1, reg_eval (hn₇ st hst.1) hLw⟩)
    (fun i hi st hst => by
      obtain ⟨hk, hsi, hsc, hsA⟩ := hst
      have hcv : curOf L i = L[i] + 1 := by simp [curOf, hi]
      have hcV := curOf_le (fun v h => (hd v h).2) i
      have hsub : (Expr.op .sub (.reg rUdc) (.const 1)).eval w st = some L[i] := by
        have := sub_eval (w := w) (s := st) (reg_eval hsc (by omega)) (const_eval' (w := w) (c := 1)
          (by omega))
        rwa [hcv, Nat.add_sub_cancel] at this
      set st₁ := st.writeArr A i L[i]
      have hexw : Exec w (.write A (.reg rUdi) (.op .sub (.reg rUdc) (.const 1))) st st₁ 5 :=
        .write (reg_eval hsi (by omega)) hsub (by rw [hsA]; simp; omega)
      have hnxtst : st₁.arrs aUdNxt = linkArr V L L' := by
        simp only [st₁, State.writeArr_arrs_ne _ _ _ (show aUdNxt ≠ A from Ne.symm hA)]
        rw [hk.2 aUdNxt (by simp [Ne.symm hA])]; simp [s₇, s₆, State.setArr_arrs_ne _ _
          (show aUdNxt ≠ A from Ne.symm hA), hnxt₅]
      have hstep := walkStep_eval (w := w) (s := st₁) hnd hd hnxtst hi (by simp [st₁, hsc]) hVw
      refine ⟨st₁.setReg rUdc (curOf L (i + 1)), _, .seq hexw (.assign hstep), by simp, ⟨?_,
        by simp, by simp, ?_⟩, by simp [st₁, hsi]⟩
      · exact ((hk.writeArr (by simp) _ _).setReg (by simp) _).setReg (by simp) _
      · simp only [State.setReg_arrs, st₁, State.writeArr_arrs_self, hsA]
        have := set_range_map (fun j => L[j]?.getD 0) (k := L.length) hi
        simp only [List.getElem?_eq_getElem hi, Option.getD_some] at this
        exact this)
    0 (Nat.zero_le _) _ hI0
  obtain ⟨hk₈, -, -, hA₈⟩ := hI₈
  refine ⟨s₈, _, .seq hex₁ (.seq (.assign (reg_eval (by simp [s₂]) (by omega))) (.seq (.assign
    (const_eval' (by omega))) (.seq hex₅ (.seq (.alloc (reg_eval hn₅ hLw))
    (.seq (.assign (reg_eval hx₆ (by omega))) (.seq (.assign (const_eval' (by omega))) hex₈)))))),
    ?_, ?_, ?_⟩
  · simp only [Expr.cost] at hc₅ hc₈ ⊢; omega
  · have h1 : Keeps readRegs [A] s s₅ :=
      ((((Keeps.refl _ _ _).setReg (by simp [readRegs]) _).setReg (by simp [readRegs]) _).setReg
        (by simp [readRegs]) _).trans (hk₅.mono (by simp [readRegs]) (by simp)) (fun r h => h)
        (fun a h => h)
    have h7 : Keeps readRegs [A] s s₇ :=
      (h1.setArr (a := A) (by simp) _).setReg (r := rUdc) (by simp [readRegs]) _
    exact h7.trans hk₈ (by simp [readRegs]) (by simp)
  · rw [hA₈, Nat.sub_self, List.replicate_zero, List.append_nil]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]

end

end GraphMinor.Compute.TwoPaths
