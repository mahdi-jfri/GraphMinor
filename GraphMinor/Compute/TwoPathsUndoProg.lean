module

public import GraphMinor.Compute.TwoPathsUndoList
public import GraphMinor.Compute.TwoPathsUndoRead
import GraphMinor.Compute.TwoPathsUndoStep
import GraphMinor.Compute.TwoPathsSweep
import GraphMinor.Compute.TwoPathsChild
import GraphMinor.Compute.TwoPathsChord
import GraphMinor.Compute.TwoPathsRotate

/-!
# The undo of all collapse records in linear time

The collapse stage of the completion records each collapse `y, z, N` in `aT2Rec` (as `encodeT2`). To
turn a crossing of the collapsed graph back into a crossing of the input graph, we put each window
`N` back between `y` and `z`, from the last record to the first. With the paths as lists this costs
the length of the paths per record. Here the paths are kept as a successor array instead, so each
record costs `O(1 + |N|)`.

`t2UndoProg` runs in four parts:

1. `offProg` finds where each record starts (`aUdOff`), since the records have different lengths and
   the undo reads them backwards;
2. `linkProg aUdQ; linkProg aUdR` builds the successor array of the two paths (`aUdNxt`);
3. `mainLoop` undoes the records from the last to the first (`recProg`);
4. `readProg aUdQ; readProg aUdR` writes the two paths back.

`t2UndoProg_exec`: if `SpliceAllOK` holds for the records in reverse order, the paths become
`spliceT2All rs.reverse (Q, R)` in at most `120 + 40 (V + |aT2Rec| + |Q| + |R|)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

/-- One round of the offsets pass: record the offset of the record that starts at `rUdpos`, and
move to the next record. -/
def offBody : Cmd :=
  .seq (.write aUdOff (.reg rUdcnt) (.reg rUdpos))
  (.seq (.assign rUdcnt (.op .add (.reg rUdcnt) (.const 1)))
    (.assign rUdpos (.op .add (.op .add (.reg rUdpos) (.const 3))
      (.read aT2Rec (.op .add (.reg rUdpos) (.const 2))))))

/-- The loop of the offsets pass. -/
def offLoop : Cmd := .while (.op .lt (.reg rUdpos) (.len aT2Rec)) offBody

/-- Write the offset of each record of `aT2Rec` into `aUdOff`, and the number of records into
`rUdcnt`. -/
def offProg : Cmd :=
  .seq (.alloc aUdOff (.len aT2Rec))
  (.seq (.assign rUdpos (.const 0))
  (.seq (.assign rUdcnt (.const 0)) offLoop))

/-- Undo the records `rUdcnt - 1`, ..., `0`. -/
def mainLoop : Cmd :=
  .while (.reg rUdcnt) (.seq (.assign rUdcnt (.op .sub (.reg rUdcnt) (.const 1))) recProg)

/-- **The undo of all collapse records**, on the paths in `aUdQ` and `aUdR`. -/
def t2UndoProg : Cmd :=
  .seq offProg
  (.seq (.alloc aUdNxt (.reg rUdV))
  (.seq (linkProg aUdQ)
  (.seq (linkProg aUdR)
  (.seq mainLoop
  (.seq (readProg aUdQ) (readProg aUdR))))))

/-- The registers that `t2UndoProg` writes. -/
def undoRegs : List ℕ := rUdpos :: rUdcnt :: rUdc :: rUdn :: recRegs

/-- The arrays that `t2UndoProg` writes. -/
def undoArrs : List ℕ := [aUdOff, aUdNxt, aUdQ, aUdR]

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

public section

variable {w V : ℕ}

/-! ### The offsets pass -/

theorem offT2_le (rs : List (ℕ × ℕ × List ℕ)) (j : ℕ) : offT2 rs j ≤ (encodeT2 rs).length := by
  have h : encodeT2 rs = encodeT2 (rs.take j) ++ encodeT2 (rs.drop j) := by
    rw [← encodeT2_append, List.take_append_drop]
  rw [offT2_eq, h, List.length_append]
  omega

/-- The third entry of record `m` is the length of its window. -/
theorem encodeT2_get_len {rs : List (ℕ × ℕ × List ℕ)} {m : ℕ} (hm : m < rs.length) :
    ∃ h : offT2 rs m + 2 < (encodeT2 rs).length,
      (encodeT2 rs)[offT2 rs m + 2] = rs[m].2.2.length := by
  have h2 := congrArg (fun l => l[2]?) (drop_offT2_get hm)
  simp only [List.getElem?_drop, List.getElem?_cons_succ, List.getElem?_cons_zero] at h2
  exact List.getElem?_eq_some_iff.mp h2

theorem offLoop_exec (hw : 1 < 2 ^ w) {rs : List (ℕ × ℕ × List ℕ)}
    (hEw : (encodeT2 rs).length + 3 < 2 ^ w) :
    ∀ d m (st : State), m + d = rs.length → st.regs rUdpos = offT2 rs m → st.regs rUdcnt = m →
      st.arrs aT2Rec = encodeT2 rs →
      st.arrs aUdOff = (List.range m).map (offT2 rs) ++
        List.replicate ((encodeT2 rs).length - m) 0 →
      ∃ st' c, Exec w offLoop st st' c ∧ c ≤ 3 + 19 * d ∧
        Keeps [rUdpos, rUdcnt] [aUdOff] st st' ∧ st'.regs rUdcnt = rs.length ∧
        st'.arrs aUdOff = (List.range rs.length).map (offT2 rs) ++
          List.replicate ((encodeT2 rs).length - rs.length) 0 := by
  have hE := length_le_encodeT2 rs
  intro d
  induction d with
  | zero =>
    intro m st hmd hpos hcnt hrec hoff
    have hm : m = rs.length := by omega
    subst hm
    have hc := lt_eval (w := w) (s := st) (reg_eval hpos (by have := offT2_le rs rs.length; omega))
      (len_eval hrec (by omega)) hw
    rw [offT2_length] at hc; simp only [lt_irrefl, ↓reduceIte] at hc
    exact ⟨st, _, .while_false hc, by simp, Keeps.refl _ _ _, hcnt, hoff⟩
  | succ d ih =>
    intro m st hmd hpos hcnt hrec hoff
    have hm : m < rs.length := by omega
    have hlt := offT2_lt hm
    have hc := lt_eval (w := w) (s := st) (reg_eval hpos (by omega)) (len_eval hrec (by omega)) hw
    simp only [hlt, ↓reduceIte] at hc
    obtain ⟨h2, hget⟩ := encodeT2_get_len hm
    have hsucc := offT2_succ hm
    have hle := offT2_le rs (m + 1)
    -- the write
    have hexw : Exec w (.write aUdOff (.reg rUdcnt) (.reg rUdpos)) st
        (st.writeArr aUdOff m (offT2 rs m)) 3 :=
      .write (reg_eval hcnt (by omega)) (reg_eval hpos (by omega)) (by rw [hoff]; simp; omega)
    set s₁ := st.writeArr aUdOff m (offT2 rs m)
    have hex₂ : Exec w (.assign rUdcnt (.op .add (.reg rUdcnt) (.const 1))) s₁
        (s₁.setReg rUdcnt (m + 1)) 4 :=
      .assign (add_eval (reg_eval (by simp [s₁, hcnt]) (by omega)) (const_eval' (w := w) hw)
        (by omega))
    set s₂ := s₁.setReg rUdcnt (m + 1)
    have hrd : (Expr.read aT2Rec (.op .add (.reg rUdpos) (.const 2))).eval w s₂ =
        some rs[m].2.2.length := by
      have hp : (Expr.op .add (.reg rUdpos) (.const 2)).eval w s₂ = some (offT2 rs m + 2) :=
        add_eval (reg_eval (by simp [s₂, s₁, hpos]) (by omega)) (const_eval' (w := w) (by omega))
          (by omega)
      have hr₂ : s₂.arrs aT2Rec = encodeT2 rs := by simp [s₂, s₁, hrec]
      have := read_eval (w := w) (s := s₂) (a := aT2Rec) hp (by rw [hr₂]; exact h2)
        (by simp only [hr₂, hget]; omega)
      simpa only [hr₂, hget] using this
    have hex₃ : Exec w (.assign rUdpos (.op .add (.op .add (.reg rUdpos) (.const 3))
        (.read aT2Rec (.op .add (.reg rUdpos) (.const 2))))) s₂
        (s₂.setReg rUdpos (offT2 rs (m + 1))) 9 := by
      have h3 : (Expr.op .add (.reg rUdpos) (.const 3)).eval w s₂ = some (offT2 rs m + 3) :=
        add_eval (reg_eval (by simp [s₂, s₁, hpos]) (by omega)) (const_eval' (w := w) (by omega))
          (by omega)
      have := Exec.assign (r := rUdpos) (add_eval h3 hrd (by omega))
      rw [hsucc]
      exact this
    obtain ⟨st', c, hex, hc', hk, hcnt', hoff'⟩ := ih (m + 1) (s₂.setReg rUdpos (offT2 rs (m + 1)))
      (by omega) (by simp) (by simp [s₂]) (by simp [s₂, s₁, hrec])
      (by simp only [State.setReg_arrs, s₂, s₁, State.writeArr_arrs_self, hoff]
          exact set_range_map (offT2 rs) (by omega))
    refine ⟨st', _, .while_true hc (by simp) (.seq hexw (.seq hex₂ hex₃)) hex, ?_, ?_, hcnt',
      hoff'⟩
    · simp only [Expr.cost] at hc' ⊢; omega
    · exact ((((Keeps.refl _ _ _).writeArr (a := aUdOff) (by simp) _ _).setReg (r := rUdcnt)
        (by simp) _).setReg (r := rUdpos) (by simp) _).trans hk (fun r h => h) (fun a h => h)

theorem offProg_exec (hw : 1 < 2 ^ w) {rs : List (ℕ × ℕ × List ℕ)} {st : State}
    (hrec : st.arrs aT2Rec = encodeT2 rs) (hEw : (encodeT2 rs).length + 3 < 2 ^ w) :
    ∃ st' c, Exec w offProg st st' c ∧ c ≤ 8 + (encodeT2 rs).length + 19 * rs.length ∧
      Keeps [rUdpos, rUdcnt] [aUdOff] st st' ∧ st'.regs rUdcnt = rs.length ∧
      st'.arrs aUdOff = (List.range rs.length).map (offT2 rs) ++
        List.replicate ((encodeT2 rs).length - rs.length) 0 := by
  set E := (encodeT2 rs).length
  set s₁ := (st.setArr aUdOff (List.replicate E 0)).setReg rUdpos 0
  obtain ⟨st', c, hex, hc, hk, hcnt, hoff⟩ := offLoop_exec hw hEw rs.length 0 (s₁.setReg rUdcnt 0)
    (by omega) (by simp [s₁, offT2_zero]) (by simp) (by simp [s₁, hrec]) (by simp [s₁, E])
  refine ⟨st', _, .seq (.alloc (len_eval hrec (by omega))) (.seq (.assign (const_eval' (by omega)))
    (.seq (.assign (const_eval' (by omega))) hex)), ?_, ?_, hcnt, hoff⟩
  · simp only [Expr.cost] at hc ⊢; omega
  · exact ((((Keeps.refl _ _ _).setArr (a := aUdOff) (by simp) _).setReg (r := rUdpos) (by simp)
      _).setReg (r := rUdcnt) (by simp) _).trans hk (fun r h => h) (fun a h => h)

/-! ### The main loop -/

theorem SpliceAllOK.init : ∀ {l : List (ℕ × ℕ × List ℕ)} {qr : List ℕ × List ℕ},
    SpliceAllOK l qr → qr.1.Nodup ∧ qr.2.Nodup ∧ qr.1.Disjoint qr.2
  | [], _, h => h
  | (_, _, _) :: _, _, h => ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩

/-- The bounds that the main loop needs: all vertices of the records and of the paths are below
`V`. -/
@[expose] def UndoBounds (V : ℕ) (rs : List (ℕ × ℕ × List ℕ)) (Q R : List ℕ) : Prop :=
  (∀ r ∈ rs, r.1 < V ∧ r.2.1 < V ∧ ∀ x ∈ r.2.2, x < V) ∧ (∀ v ∈ Q, v < V) ∧ ∀ v ∈ R, v < V

theorem UndoBounds.splice {rs : List (ℕ × ℕ × List ℕ)} {Q R : List ℕ} (hb : UndoBounds V rs Q R)
    (m : ℕ) :
    (∀ v ∈ (spliceT2All (rs.reverse.take m) (Q, R)).1, v < V) ∧
      ∀ v ∈ (spliceT2All (rs.reverse.take m) (Q, R)).2, v < V := by
  have key : ∀ v, v ∈ (spliceT2All (rs.reverse.take m) (Q, R)).1 ∨
      v ∈ (spliceT2All (rs.reverse.take m) (Q, R)).2 → v < V := by
    intro v hv
    rcases spliceT2All_mem hv with h | h | ⟨r, hr, h⟩
    · exact hb.2.1 v h
    · exact hb.2.2 v h
    · exact (hb.1 r (List.mem_reverse.mp (List.mem_of_mem_take hr))).2.2 v h
  exact ⟨fun v h => key v (Or.inl h), fun v h => key v (Or.inr h)⟩

theorem mainLoop_exec (hw : 1 < 2 ^ w) {rs : List (ℕ × ℕ × List ℕ)} {Q R OFF : List ℕ}
    (hok : SpliceAllOK rs.reverse (Q, R)) (hb : UndoBounds V rs Q R)
    (hOFF : ∀ i < rs.length, ∃ h : i < OFF.length, OFF[i] = offT2 rs i)
    (hVw : 2 * V + 1 < 2 ^ w) (hEw : (encodeT2 rs).length + 3 < 2 ^ w) :
    ∀ j (st : State), j ≤ rs.length → st.regs rUdcnt = j → st.arrs aUdOff = OFF →
      st.arrs aT2Rec = encodeT2 rs →
      st.arrs aUdNxt = linkArr V (spliceT2All (rs.reverse.take (rs.length - j)) (Q, R)).1
        (spliceT2All (rs.reverse.take (rs.length - j)) (Q, R)).2 →
      ∃ st' c, Exec w mainLoop st st' c ∧ c ≤ 1 + 24 * offT2 rs j ∧
        Keeps (rUdcnt :: recRegs) [aUdNxt] st st' ∧
        st'.arrs aUdNxt = linkArr V (spliceT2All rs.reverse (Q, R)).1
          (spliceT2All rs.reverse (Q, R)).2 := by
  have hE := length_le_encodeT2 rs
  intro j
  induction j with
  | zero =>
    intro st _ hcnt _ _ hnxt
    rw [Nat.sub_zero, ← List.length_reverse, List.take_length] at hnxt
    exact ⟨st, _, .while_false (reg_eval hcnt (by omega)), by simp, Keeps.refl _ _ _, hnxt⟩
  | succ j ih =>
    intro st hj hcnt hoff hrec hnxt
    have hjl : j < rs.length := by omega
    set m := rs.length - (j + 1) with hm
    have hmr : m < rs.reverse.length := by simp; omega
    have hrev : rs.reverse[m] = rs[j] := by
      rw [List.getElem_reverse]; congr 1; omega
    have hok' := hok.get hmr
    rw [hrev] at hok'
    have hstep := spliceT2All_take_succ rs.reverse (Q, R) hmr
    rw [hrev, show m + 1 = rs.length - j by omega] at hstep
    obtain ⟨hQV, hRV⟩ := hb.splice m
    have hrj := hb.1 rs[j] (List.getElem_mem _)
    obtain ⟨hjO, hOj⟩ := hOFF j hjl
    set s₁ := st.setReg rUdcnt j
    have hex₁ : Exec w (.assign rUdcnt (.op .sub (.reg rUdcnt) (.const 1))) st s₁ 4 := by
      have := Exec.assign (r := rUdcnt) (sub_eval (w := w) (s := st) (reg_eval hcnt (by omega))
        (const_eval' (w := w) (c := 1) hw))
      simpa using this
    obtain ⟨s₂, c₂, hex₂, hc₂, hk₂, hn₂⟩ := recProg_exec (V := V) hw (st := s₁) (j := j)
      (o := offT2 rs j) (rest := encodeT2 (rs.drop (j + 1))) (by simp [s₁])
      (by simp [s₁, hoff]) hjO hOj (by omega) (by simp [s₁, hrec]) (drop_offT2_get hjl)
      (by simp [s₁, hnxt]) hok' hrj.1 hrj.2.1 hrj.2.2 hQV hRV hVw (by omega)
    rw [← hstep] at hn₂
    have hcnt₂ : s₂.regs rUdcnt = j := by rw [hk₂.1 rUdcnt (by simp [recRegs])]; simp [s₁]
    obtain ⟨st', c, hex, hc, hk, hfin⟩ := ih s₂ (by omega) hcnt₂
      (by rw [hk₂.2 aUdOff (by simp)]; simp [s₁, hoff])
      (by rw [hk₂.2 aT2Rec (by simp)]; simp [s₁, hrec]) hn₂
    refine ⟨st', _, .while_true (reg_eval hcnt (by omega)) (by simp) (.seq hex₁ hex₂) hex, ?_, ?_,
      hfin⟩
    · have := offT2_succ hjl
      simp only [Expr.cost] at hc ⊢; omega
    · exact (((Keeps.refl _ _ _).setReg (r := rUdcnt) (by simp) _).trans hk₂
        (fun r h => by simp [h]) (fun a h => h)).trans hk (fun r h => h) (fun a h => h)

/-! ### The whole undo -/

/-- Two disjoint lists without repeats whose entries are below `V` have at most `V` entries in
all. -/
theorem length_add_le_of_disjoint {L L' : List ℕ} (hnd : L.Nodup) (hnd' : L'.Nodup)
    (hdis : L.Disjoint L') (hV : ∀ v ∈ L, v < V) (hV' : ∀ v ∈ L', v < V) :
    L.length + L'.length ≤ V := by
  have := length_le_of_nodup_lt (n := V) (hnd.append hnd' hdis) (by
    intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hV v h
    · exact hV' v h)
  simpa using this

/-- **The undo of all collapse records.** If the records `rs` (in the order they were made) are
in `aT2Rec`, the paths `Q`, `R` are in `aUdQ`, `aUdR`, and `SpliceAllOK` holds for the records in
reverse order, then `t2UndoProg` writes `spliceT2All rs.reverse (Q, R)` into `aUdQ`, `aUdR`, in time
linear in `V`, `|aT2Rec|`, `|Q|` and `|R|`. -/
theorem t2UndoProg_exec (hw : 1 < 2 ^ w) {rs : List (ℕ × ℕ × List ℕ)} {Q R : List ℕ}
    {st : State} (hok : SpliceAllOK rs.reverse (Q, R)) (hb : UndoBounds V rs Q R)
    (hV : st.regs rUdV = V) (hrec : st.arrs aT2Rec = encodeT2 rs) (hQ : st.arrs aUdQ = Q)
    (hR : st.arrs aUdR = R) (hVw : 2 * V + 1 < 2 ^ w)
    (hEw : (encodeT2 rs).length + 3 < 2 ^ w) :
    ∃ st' c, Exec w t2UndoProg st st' c ∧
      c ≤ 120 + 40 * (V + (encodeT2 rs).length + Q.length + R.length) ∧
      Keeps undoRegs undoArrs st st' ∧ st'.arrs aUdQ = (spliceT2All rs.reverse (Q, R)).1 ∧
      st'.arrs aUdR = (spliceT2All rs.reverse (Q, R)).2 := by
  have hE := length_le_encodeT2 rs
  obtain ⟨hQnd, hRnd, hQR⟩ := hok.init
  dsimp only at hQnd hRnd hQR
  obtain ⟨hQ'nd, hR'nd, hQR'⟩ := hok.final
  have hQV := hb.2.1
  have hRV := hb.2.2
  have hQRV := length_add_le_of_disjoint hQnd hRnd hQR hQV hRV
  obtain ⟨hQ'V, hR'V⟩ := hb.splice rs.length
  rw [← List.length_reverse, List.take_length] at hQ'V hR'V
  have hQR'V := length_add_le_of_disjoint hQ'nd hR'nd hQR' hQ'V hR'V
  -- 1. the offsets
  obtain ⟨s₁, c₁, hex₁, hc₁, hk₁, hcnt₁, hoff₁⟩ := offProg_exec hw hrec hEw
  -- 2. the empty successor array
  have hV₁ : s₁.regs rUdV = V := by rw [hk₁.1 rUdV (by simp)]; exact hV
  set s₂ := s₁.setArr aUdNxt (List.replicate V 0)
  have hex₂ : Exec w (.alloc aUdNxt (.reg rUdV)) s₁ s₂ (1 + V) :=
    .alloc (reg_eval hV₁ (by omega))
  have hk₂ : Keeps undoRegs undoArrs st s₂ :=
    (hk₁.mono (by simp [undoRegs]) (by simp [undoArrs])).setArr (by simp [undoArrs]) _
  have hQ₂ : s₂.arrs aUdQ = Q := by
    simp only [s₂, State.setArr_arrs_ne _ _ (show aUdQ ≠ aUdNxt by decide)]
    rw [hk₁.2 aUdQ (by simp)]; exact hQ
  have hR₂ : s₂.arrs aUdR = R := by
    simp only [s₂, State.setArr_arrs_ne _ _ (show aUdR ≠ aUdNxt by decide)]
    rw [hk₁.2 aUdR (by simp)]; exact hR
  -- 3. the successor array of the two paths
  obtain ⟨s₃, c₃, hex₃, hc₃, hk₃, hn₃⟩ := linkProg_exec (V := V) (A := aUdQ) (L := Q) (L' := [])
    (by decide) hw (st := s₂) hQ₂ hQnd
    (fun v hv => ⟨by simp, hQV v hv⟩) (by simp [s₂, linkArr_nil]) (by omega) (by omega)
  obtain ⟨s₄, c₄, hex₄, hc₄, hk₄, hn₄⟩ := linkProg_exec (V := V) (A := aUdR) (L := R) (L' := Q)
    (by decide) hw (st := s₃)
    (by rw [hk₃.2 aUdR (by simp)]; exact hR₂) hRnd
    (fun v hv => ⟨fun h => hQR h hv, hRV v hv⟩) (by rw [hn₃, linkArr_comm]) (by omega) (by omega)
  have hk₄' : Keeps undoRegs undoArrs st s₄ :=
    (hk₂.trans hk₃ (fun r h => by simp [undoRegs, h]) (by simp [undoArrs])).trans hk₄
      (fun r h => by simp [undoRegs, h])
      (by simp [undoArrs])
  -- 4. the main loop
  have hOFF : ∀ i < rs.length, ∃ h : i < (s₄.arrs aUdOff).length,
      (s₄.arrs aUdOff)[i] = offT2 rs i := by
    have h4 : s₄.arrs aUdOff = s₁.arrs aUdOff := by
      rw [hk₄.2 aUdOff (by simp), hk₃.2 aUdOff (by simp)]; simp [s₂]
    intro i hi
    rw [h4, hoff₁]
    exact ⟨by simp; omega, by rw [List.getElem_append_left (by simpa using hi)]; simp⟩
  obtain ⟨s₅, c₅, hex₅, hc₅, hk₅, hn₅⟩ := mainLoop_exec hw hok hb (fun i hi => hOFF i hi) hVw hEw
    rs.length s₄ le_rfl
    (by rw [hk₄.1 rUdcnt (by simp [recRegs]), hk₃.1 rUdcnt (by simp [recRegs])]; simpa [s₂] using hcnt₁)
    rfl (by rw [hk₄'.2 aT2Rec (by simp [undoArrs])]; exact hrec)
    (by rw [Nat.sub_self, List.take_zero, hn₄, linkArr_comm]; rfl)
  have hk₅' : Keeps undoRegs undoArrs st s₅ :=
    hk₄'.trans hk₅ (fun r h => by rcases List.mem_cons.mp h with h | h <;> simp [undoRegs, h])
      (by simp [undoArrs])
  -- 5. reading the paths back
  have hhead := spliceT2All_head? rs.reverse (Q, R)
  have hQ₅ : s₅.arrs aUdQ = Q := by
    rw [hk₅.2 aUdQ (by simp), hk₄.2 aUdQ (by simp), hk₃.2 aUdQ (by simp)]; exact hQ₂
  have hR₅ : s₅.arrs aUdR = R := by
    rw [hk₅.2 aUdR (by simp), hk₄.2 aUdR (by simp), hk₃.2 aUdR (by simp)]; exact hR₂
  obtain ⟨s₆, c₆, hex₆, hc₆, hk₆, hA₆⟩ := readProg_exec (V := V) (A := aUdQ) (by decide) hw
    (s := s₅) hQ'nd (fun v hv => ⟨fun h => hQR' hv h, hQ'V v hv⟩) hn₅
    (by rw [hQ₅]; exact hhead.1.symm) (by omega) (by omega) (by rw [hQ₅]; omega)
  obtain ⟨s₇, c₇, hex₇, hc₇, hk₇, hA₇⟩ := readProg_exec (V := V) (A := aUdR) (by decide) hw
    (s := s₆) hR'nd (fun v hv => ⟨fun h => hQR' h hv, hR'V v hv⟩)
    (by rw [hk₆.2 aUdNxt (by simp), hn₅, linkArr_comm])
    (by rw [hk₆.2 aUdR (by simp), hR₅]; exact hhead.2.symm) (by omega) (by omega)
    (by rw [hk₆.2 aUdR (by simp), hR₅]; omega)
  refine ⟨s₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))), ?_,
    ?_, by rw [hk₇.2 aUdQ (by simp)]; exact hA₆, hA₇⟩
  · have := offT2_length rs
    omega
  · exact (hk₅'.trans hk₆ (by simp [undoRegs, readRegs, recRegs]) (by simp [undoArrs])).trans hk₇
      (by simp [undoRegs, readRegs, recRegs]) (by simp [undoArrs])

end

end GraphMinor.Compute.TwoPaths
