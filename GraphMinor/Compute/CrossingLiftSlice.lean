module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Copying the unchanged parts of a lifted path

The contraction lifts of Section 11 retain a prefix and suffix of the returned path and
insert one or two vertices between them. This file supplies the slice copy used to write
those unchanged parts into a fresh output array. The source and destination offsets and
the length come from registers, so one program works for every path size.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy `r_n` words from source offset `r_src` to destination offset `r_dst`.
Only the loop counter `r_i` changes. The destination is already allocated. -/
def liftCopySliceProg (src dst r_src r_dst r_n r_i : ℕ) : Cmd :=
  .seq (.assign r_i (.const 0))
    (forUp r_i (.reg r_n)
      (.write dst (.op .add (.reg r_dst) (.reg r_i))
        (.read src (.op .add (.reg r_src) (.reg r_i)))))

/-- Copying a slice takes linear time, preserves the other arrays and registers, and does not
read any entry outside the slice. In particular, other source entries need not fit in a word. -/
theorem liftCopySliceProg_exec {w : ℕ} (src dst r_src r_dst r_n r_i : ℕ)
    (hsd : src ≠ dst) (hsi : r_src ≠ r_i) (hdi : r_dst ≠ r_i) (hni : r_n ≠ r_i)
    (pre mid suf A C : List ℕ) (s : State)
    (hsrc : s.arrs src = pre ++ mid ++ suf)
    (hdst : s.arrs dst = A ++ List.replicate mid.length 0 ++ C)
    (hrs : s.regs r_src = pre.length) (hrd : s.regs r_dst = A.length)
    (hrn : s.regs r_n = mid.length)
    (hwords : ∀ x ∈ mid, x < 2 ^ w)
    (hw : pre.length + A.length + mid.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftCopySliceProg src dst r_src r_dst r_n r_i) s s' t ∧
      t ≤ 20 * mid.length + 8 ∧ s'.arrs dst = A ++ mid ++ C ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let I : ℕ → State → Prop := fun j st =>
    st.regs r_i = j ∧
    (∀ r, r ≠ r_i → st.regs r = s.regs r) ∧
    (∀ a, a ≠ dst → st.arrs a = s.arrs a) ∧
    st.arrs dst = A ++ mid.take j ++ List.replicate (mid.length - j) 0 ++ C
  have hinit : I 0 (s.setReg r_i 0) := by
    refine ⟨by simp, fun r hr => by simp [hr], fun a _ => rfl, ?_⟩
    simp [hdst]
  obtain ⟨s', t, he, ht, hI⟩ := forUp_exec' I mid.length 10 hw1 (by omega)
    (r_i := r_i) (hi := .reg r_n)
    (body := .write dst (.op .add (.reg r_dst) (.reg r_i))
      (.read src (.op .add (.reg r_src) (.reg r_i))))
    (fun j hj st hI => ⟨hI.1, eval_reg ((hI.2.1 r_n hni).trans hrn) (by omega)⟩)
    (fun j hj st hI => by
      obtain ⟨hri, hr, ha, hd⟩ := hI
      have hs : st.arrs src = pre ++ mid ++ suf := (ha src hsd).trans hsrc
      have hidx : pre.length + j < (st.arrs src).length := by
        rw [hs]; simp only [List.length_append]; omega
      have hval : (st.arrs src)[pre.length + j]'hidx = mid[j] := by
        simp only [hs]
        rw [List.getElem_append_left (by simp; omega),
          List.getElem_append_right (by omega)]
        simp
      have hread : (Expr.read src (.op .add (.reg r_src) (.reg r_i))).eval w st = some mid[j] := by
        rw [← hval]
        exact eval_read (eval_add (eval_reg ((hr r_src hsi).trans hrs) (by omega))
          (eval_reg hri (by omega)) (by omega)) hidx
          (by rw [hval]; exact hwords _ (List.getElem_mem hj))
      have hpos : (Expr.op .add (.reg r_dst) (.reg r_i)).eval w st = some (A.length + j) :=
        eval_add (eval_reg ((hr r_dst hdi).trans hrd) (by omega))
          (eval_reg hri (by omega)) (by omega)
      have hbound : A.length + j < (st.arrs dst).length := by
        rw [hd]; simp only [List.length_append, List.length_take, List.length_replicate]; omega
      refine ⟨st.writeArr dst (A.length + j) mid[j], 8,
        .write hpos hread hbound, by omega, ?_, ?_⟩
      · refine ⟨by simp, fun r h => by simp [h, hr r h], ?_, ?_⟩
        · intro a h; simp [State.writeArr_arrs_ne _ _ _ h, ha a h]
        · simp only [State.setReg_arrs, State.writeArr_arrs_self, hd]
          have hjlen : mid.length - j = mid.length - (j + 1) + 1 := by omega
          rw [hjlen, List.replicate_succ]
          have hset : (A ++ mid.take j ++ (0 :: List.replicate (mid.length - (j + 1)) 0) ++ C).set
              (A.length + j) mid[j] =
              A ++ mid.take (j + 1) ++ List.replicate (mid.length - (j + 1)) 0 ++ C := by
            have hjtake : (mid.take j).length = j := List.length_take_of_le (by omega)
            rw [List.append_assoc (A ++ _) (0 :: _) C, List.cons_append,
              List.set_append_right _ _ (by simp [hjtake])]
            simp only [List.length_append, hjtake]
            have hsub : A.length + j - (A.length + j) = 0 := Nat.sub_self _
            rw [hsub, List.set_cons_zero, List.take_succ_eq_append_getElem hj]
            simp only [List.append_assoc, List.nil_append, List.cons_append]
          exact hset
      · simp only [State.writeArr_regs, hri])
    (s.setReg r_i 0) hinit
  refine ⟨s', 2 + t, .seq (.assign (eval_const hw0)) he, ?_, ?_, hI.2.2.1, hI.2.1⟩
  · simp only [Expr.cost] at ht
    omega
  · simpa only [List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil] using hI.2.2.2

/-- Load the two offsets and length from expressions, then copy the slice. -/
def liftSliceAtProg (src dst : ℕ) (e_src e_dst e_n : Expr) (R : ℕ) : Cmd :=
  .seq (.assign R e_src)
    (.seq (.assign (R + 1) e_dst)
      (.seq (.assign (R + 2) e_n)
        (liftCopySliceProg src dst R (R + 1) (R + 2) (R + 3))))

/-- Expression arguments are evaluated in command order. The routine preserves registers
below `R`, including registers supplying the offsets, and every other array. -/
theorem liftSliceAtProg_exec {w : ℕ} (src dst R : ℕ) (e_src e_dst e_n : Expr)
    (hsd : src ≠ dst) (pre mid suf A C : List ℕ) (s : State)
    (hsrc : s.arrs src = pre ++ mid ++ suf)
    (hdst : s.arrs dst = A ++ List.replicate mid.length 0 ++ C)
    (hes : e_src.eval w s = some pre.length)
    (hed : e_dst.eval w (s.setReg R pre.length) = some A.length)
    (hen : e_n.eval w ((s.setReg R pre.length).setReg (R + 1) A.length) = some mid.length)
    (hwords : ∀ x ∈ mid, x < 2 ^ w)
    (hw : pre.length + A.length + mid.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftSliceAtProg src dst e_src e_dst e_n R) s s' t ∧
      t ≤ 20 * mid.length + 11 + e_src.cost + e_dst.cost + e_n.cost ∧
      s'.arrs dst = A ++ mid ++ C ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  let s1 := s.setReg R pre.length
  let s2 := s1.setReg (R + 1) A.length
  let s3 := s2.setReg (R + 2) mid.length
  obtain ⟨s4, t4, he4, ht4, hd4, ha4, hr4⟩ := liftCopySliceProg_exec
    src dst R (R + 1) (R + 2) (R + 3) hsd (by omega) (by omega) (by omega)
    pre mid suf A C s3 hsrc hdst
    (by simp [s3, s2, s1]) (by simp [s3, s2]) (by simp [s3]) hwords hw
  refine ⟨s4, _, .seq (.assign hes) (.seq (.assign hed) (.seq (.assign hen) he4)),
    by omega, hd4, ha4, ?_⟩
  intro r hr
  rw [hr4 r (by omega)]
  simp [s3, s2, s1, show r ≠ R + 2 by omega, show r ≠ R + 1 by omega,
    show r ≠ R by omega]

end GraphMinor.Compute.Crossing
