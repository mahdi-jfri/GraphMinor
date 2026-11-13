module

public import GraphMinor.Compute.GM13SocietyOwnerQuery

/-!
# Writing every loop owner

For each vertex, query the ordered list of division members and write the
last containing member's one-based index. The resulting table is an
explicit part of the multigraph division encoding. Its cost is the vertex
count times the number of division members.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The loop-owner table, with zero for vertices not covered by the records. -/
def gm13LoopOwnerTable {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) : List ℕ :=
  List.ofFn (gm13LastOwner L)

/-- Query one vertex and write its owner. Register 26 stores the first member
address, register 21 the number of members, and register 24 the vertex. -/
def gm13OwnerTableBody : Cmd :=
  .seq (.assign 20 (.reg 26))
    (.seq (.assign 22 (.const 0))
      (.seq (.assign 25 (.const 0))
        (.seq gm13OwnerQueryLoop (.write 30 (.reg 24) (.reg 25)))))

/-- Write one owner index for each vertex. -/
def gm13OwnerTableProg : Cmd :=
  .seq (.alloc 30 (.reg 0))
    (.seq (.assign 24 (.const 0)) (forUp 24 (.reg 0) gm13OwnerTableBody))

/-- The complete table is computed in O(n times member count) time, from
only the serialized records. All other arrays remain unchanged. -/
theorem gm13OwnerTableProg_exec {w n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (pre suf : List ℕ)
    (hw : (pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length < 2 ^ w)
    (hnw : n < 2 ^ w) (hLw : L.length < 2 ^ w) (hw1 : 1 < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2) ++ suf)
    (hn : s.regs 0 = n) (hcount : s.regs 21 = L.length)
    (hstart : s.regs 26 = pre.length) :
    ∃ s' t, Exec w gm13OwnerTableProg s s' t ∧
      t ≤ n * (32 * L.length + 20) + 6 ∧
      s'.arrs 30 = gm13LoopOwnerTable L ∧
      (∀ a : ℕ, a ≠ 30 → s'.arrs a = s.arrs a) := by
  let words := gm13LoopOwnerTable L
  have hlen : words.length = n := List.length_ofFn
  let s₁ := s.setArr 30 (List.replicate n 0)
  have he₁ : Exec w (.alloc 30 (.reg 0)) s s₁ (1 + n) := .alloc (eval_reg hn hnw)
  let s₂ := s₁.setReg 24 0
  have he₂ : Exec w (.assign 24 (.const 0)) s₁ s₂ 2 := .assign (eval_const (by omega))
  let I : ℕ → State → Prop := fun i st =>
    st.regs 24 = i ∧ st.arrs 30 = words.take i ++ List.replicate (n - i) 0 ∧
    (∀ a : ℕ, a ≠ 30 → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ 20 → r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → st.regs r = s.regs r)
  have hinit : I 0 s₂ := by
    refine ⟨by simp [s₂], by simp [s₂, s₁], ?_, ?_⟩
    · intro a ha
      simp [s₂, s₁, ha]
    · intro r h20 h22 h23 h24 h25
      simp [s₂, s₁, h24]
  obtain ⟨s₃, t₃, he₃, ht₃, hI₃⟩ := forUp_exec' I n (32 * L.length + 12)
    (r_i := 24) (hi := .reg 0) (body := gm13OwnerTableBody) hw1 hnw
    (fun i _ st hs => ⟨hs.1, eval_reg
      ((hs.2.2.2 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn) hnw⟩)
    (fun i hi st hs => by
      obtain ⟨hri, hdst, ha, hr⟩ := hs
      let v : Fin n := ⟨i, hi⟩
      let q₁ := st.setReg 20 pre.length
      let q₂ := q₁.setReg 22 0
      let q₃ := q₂.setReg 25 0
      have heq₁ : Exec w (.assign 20 (.reg 26)) st q₁ 2 :=
        .assign (eval_reg ((hr 26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hstart)
          (by simp only [List.length_append] at hw; omega))
      have heq₂ : Exec w (.assign 22 (.const 0)) q₁ q₂ 2 := .assign (eval_const (by omega))
      have heq₃ : Exec w (.assign 25 (.const 0)) q₂ q₃ 2 := .assign (eval_const (by omega))
      obtain ⟨q₄, t₄, heq₄, ht₄, ho₄, ha₄, hr₄⟩ := gm13OwnerQueryLoop_exec
        (w := w) L pre suf v 0 L.length 0 (Nat.zero_add _) hLw hw (s := q₃)
        (by simpa [q₃, q₂, q₁] using (ha 65 (by decide)).trans hin)
        (by simp [q₃, q₂, q₁])
        (by simpa [q₃, q₂, q₁] using
          (hr 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hn)
        (by simpa [q₃, q₂, q₁] using
          (hr 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount)
        (by simp [q₃, q₂]) (by simpa [q₃, q₂, q₁, v] using hri) (by simp [q₃]) hw1
      rw [gm13OwnerFrom_zero] at ho₄
      have hkeep : ∀ r : ℕ, r ≠ 20 → r ≠ 22 → r ≠ 23 → r ≠ 25 → q₄.regs r = st.regs r := by
        intro r h20 h22 h23 h25
        simpa [q₃, q₂, q₁, h20, h22, h25] using hr₄ r h20 h22 h23 h25
      have hri₄ : q₄.regs 24 = i := (hkeep 24 (by decide) (by decide) (by decide) (by decide)).trans hri
      have hword : words[i]'(by omega) = gm13LastOwner L v := by
        simp only [words, gm13LoopOwnerTable, List.getElem_ofFn, v]
      let q₅ := q₄.writeArr 30 i (gm13LastOwner L v)
      have hdlen : i < (q₄.arrs 30).length := by
        rw [ha₄]
        change i < (st.arrs 30).length
        rw [hdst]
        simp only [List.length_append, List.length_take, List.length_replicate]
        omega
      have heq₅ : Exec w (.write 30 (.reg 24) (.reg 25)) q₄ q₅ 3 :=
        .write (eval_reg hri₄ (by omega))
          (eval_reg ho₄ ((gm13LastOwner_le_length L v).trans_lt hLw)) hdlen
      have hset : (words.take i ++ List.replicate (n - i) 0).set i (gm13LastOwner L v) =
          words.take (i + 1) ++ List.replicate (n - (i + 1)) 0 := by
        rw [← hword, List.set_append_right _ _ (by simp [List.length_take, Nat.min_eq_left (show i ≤ words.length by omega)])]
        simp only [List.length_take, Nat.min_eq_left (show i ≤ words.length by omega), Nat.sub_self]
        rw [show n - i = (n - (i + 1)) + 1 by omega, List.replicate_succ,
          List.set_cons_zero, List.take_succ_eq_append_getElem (show i < words.length by omega)]
        simp only [List.append_assoc, List.singleton_append]
      refine ⟨q₅, 2 + (2 + (2 + (t₄ + 3))),
        .seq heq₁ (.seq heq₂ (.seq heq₃ (.seq heq₄ heq₅))), by omega, ?_, hri₄⟩
      refine ⟨by simp [q₅], ?_, ?_, ?_⟩
      · change (q₄.arrs 30).set i (gm13LastOwner L v) = _
        rw [ha₄]
        change (st.arrs 30).set i (gm13LastOwner L v) = _
        rw [hdst, hset]
      · intro a h30
        simpa [q₅, h30, ha₄, q₃, q₂, q₁] using ha a h30
      · intro r h20 h22 h23 h24 h25
        simpa [q₅, h24] using
          (hkeep r h20 h22 h23 h25).trans (hr r h20 h22 h23 h24 h25)) s₂ hinit
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, hI₃.2.2.1⟩
  · simp only [Expr.cost_reg] at ht₃
    have heq : n * (32 * L.length + 20) = n + n * (1 + 6 + (32 * L.length + 12)) := by ring
    omega
  · simpa only [← hlen, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil]
      using hI₃.2.1

end GraphMinor.Compute
