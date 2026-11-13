module

public import GraphMinor.Compute.Algorithm99MoveAProg
public import GraphMinor.Compute.Algorithm91Parse

/-!
# Writing the set `orig(X)` of output (iii) of (9.9)

Output (iii) of Algorithm (9.9) (Graph Minors XIII, page 104) is written as
`2 :: bitSetList X_G ++ block`, where `X_G ⊆ V(G)` is the image `orig(X)` of a set `X` of the
renumbered graph `G_i`. The program `bitImageProg` writes the head `2 :: bitSetList (X.image orig)`
from `bitSetList X` and the list `origList orig`: it allocates `n + 1` zeros, puts the tag `2`
first, and for each `u ∈ X` puts a `1` at position `orig u + 1`.

* `bitImageProg_exec`: the program and its time `≤ 16 v + n + 14`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Function

variable {v n : ℕ}

/-- The set `X ∩ {u | u < j}`, the part of `X` that the loop of `bitImageProg` has read. -/
def bitImagePart (X : Finset (Fin v)) (j : ℕ) : Finset (Fin v) :=
  X.filter (fun u => u.1 < j)

theorem bitImagePart_zero (X : Finset (Fin v)) : bitImagePart X 0 = ∅ := by
  ext u; simp [bitImagePart]

theorem bitImagePart_of_le (X : Finset (Fin v)) {j : ℕ} (hj : v ≤ j) : bitImagePart X j = X := by
  ext u; simp [bitImagePart, show u.1 < j by omega]

theorem bitImagePart_succ_of_mem (X : Finset (Fin v)) {j : ℕ} (hj : j < v)
    (hX : (⟨j, hj⟩ : Fin v) ∈ X) :
    bitImagePart X (j + 1) = insert ⟨j, hj⟩ (bitImagePart X j) := by
  ext u
  simp only [bitImagePart, Finset.mem_filter, Finset.mem_insert, Fin.ext_iff]
  constructor
  · rintro ⟨hu, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
    · exact Or.inr ⟨hu, h⟩
    · exact Or.inl h
  · rintro (h | ⟨hu, hlt⟩)
    · have : u = ⟨j, hj⟩ := Fin.ext h
      exact ⟨this ▸ hX, by omega⟩
    · exact ⟨hu, by omega⟩

theorem bitImagePart_succ_of_not_mem (X : Finset (Fin v)) {j : ℕ} (hj : j < v)
    (hX : (⟨j, hj⟩ : Fin v) ∉ X) :
    bitImagePart X (j + 1) = bitImagePart X j := by
  ext u
  simp only [bitImagePart, Finset.mem_filter]
  constructor
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
    · exact h
    · exact absurd (Fin.ext h : u = ⟨j, hj⟩) (fun h' => hX (h' ▸ hu))
  · rintro ⟨hu, hlt⟩
    exact ⟨hu, by omega⟩

/-- **The program.** From `bitSetList X` in `a_X`, `origList orig` in `a_o` and `n` in register
`r_n`, write `2 :: bitSetList (X.image orig)` to `a_dst`, with loop register `r_i`. -/
def bitImageProg (a_X a_o a_dst : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.alloc a_dst (.op .add (.reg r_n) (.const 1)))
    (.seq (.write a_dst (.const 0) (.const 2))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.len a_X)
          (.ite (.read a_X (.reg r_i))
            (.write a_dst (.op .add (.read a_o (.reg r_i)) (.const 1)) (.const 1))
            .skip))))

/-- Setting position `u + 1` of `2 :: bitSetList S` to `1` inserts `u`. -/
theorem cons_bitSetList_set_one (S : Finset (Fin n)) (u : Fin n) :
    (2 :: bitSetList S).set (u.1 + 1) 1 = 2 :: bitSetList (insert u S) := by
  rw [List.set_cons_succ, Alg91.bitSetList_set_one]

/-- `2 :: bitSetList ∅` is the tag `2` followed by `n` zeros. -/
theorem replicate_set_zero_two (n : ℕ) :
    (List.replicate (n + 1) 0).set 0 2 = 2 :: bitSetList (∅ : Finset (Fin n)) := by
  rw [List.replicate_succ, List.set_cons_zero, Alg91.bitSetList_empty]

/-- **Running `bitImageProg`.** With `bitSetList X` in `a_X`, `origList orig` in `a_o` and `n` in
register `r_n`, the program writes `2 :: bitSetList (X.image orig)` to `a_dst` and changes no
other array and no register except `r_i`. -/
theorem bitImageProg_exec {w : ℕ} (X : Finset (Fin v)) (orig : Fin v → Fin n)
    {a_X a_o a_dst : Arr} {r_n r_i : Reg} (hXd : a_X ≠ a_dst) (hod : a_o ≠ a_dst)
    (hw : 2 < 2 ^ w) (hn_w : n + 1 < 2 ^ w) (hv_w : v < 2 ^ w)
    {s : State} (hX : s.arrs a_X = bitSetList X) (ho : s.arrs a_o = origList orig)
    (hn : s.regs r_n = n) :
    ∃ s' t, Exec w (bitImageProg a_X a_o a_dst r_n r_i) s s' t ∧ t ≤ 16 * v + n + 14 ∧
      s'.arrs a_dst = 2 :: bitSetList (X.image orig) ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_i → s'.regs r = s.regs r) := by
  have hn_w' : n < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  -- the allocation, the tag and the start of the loop
  let s₁ := s.setArr a_dst (List.replicate (n + 1) 0)
  have hex₁ : Exec w (.alloc a_dst (.op .add (.reg r_n) (.const 1))) s s₁ (3 + (n + 1)) := by
    have h := Exec.alloc (w := w) (a := a_dst) (s := s) (m := n + 1)
      (len := .op .add (.reg r_n) (.const 1))
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hn, hn_w', hw0, hn_w])
    simpa [Expr.cost] using h
  let s₂ := s₁.writeArr a_dst 0 2
  have hex₂ : Exec w (.write a_dst (.const 0) (.const 2)) s₁ s₂ 3 := by
    have h := Exec.write (w := w) (a := a_dst) (s := s₁) (i := 0) (v := 2)
      (idx := .const 0) (val := .const 2) (by simp [Expr.eval, checkWord])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁])
    simpa [Expr.cost] using h
  let s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 := by
    have h := Exec.assign (w := w) (r := r_i) (e := .const 0) (s := s₂) (v := 0)
      (by simp [Expr.eval, checkWord])
    simpa [Expr.cost] using h
  have hs₃_dst : s₃.arrs a_dst = 2 :: bitSetList ((bitImagePart X 0).image orig) := by
    simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self]
    rw [bitImagePart_zero, Finset.image_empty]
    exact replicate_set_zero_two n
  have hs₃_arr : ∀ a, a ≠ a_dst → s₃.arrs a = s.arrs a := by
    intro a ha
    simp only [s₃, s₂, s₁, State.setReg_arrs]
    rw [State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]
  have hs₃_reg : ∀ r, r ≠ r_i → s₃.regs r = s.regs r := by
    intro r hr
    simp only [s₃, s₂, s₁]
    rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs, State.setArr_regs]
  -- the loop
  let I : ℕ → State → Prop := fun j st =>
    st.regs r_i = j ∧ st.arrs a_dst = 2 :: bitSetList ((bitImagePart X j).image orig) ∧
      (∀ a, a ≠ a_dst → st.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_i → st.regs r = s.regs r)
  have hloop := Triple.forUp_const (w := w) (r_i := r_i) (hi := .len a_X)
    (body := .ite (.read a_X (.reg r_i))
      (.write a_dst (.op .add (.read a_o (.reg r_i)) (.const 1)) (.const 1)) .skip)
    I v 8 (by omega) hv_w
    (by
      intro j _ st hst
      refine ⟨hst.1, ?_⟩
      simp [Expr.eval, checkWord, hst.2.2.1 a_X hXd, hX, hv_w])
    (by
      intro j hj st hst
      obtain ⟨hreg, hdst, harr, hregs⟩ := hst
      have hj_w : j < 2 ^ w := by omega
      have hXst : st.arrs a_X = bitSetList X := (harr a_X hXd).trans hX
      have host : st.arrs a_o = origList orig := (harr a_o hod).trans ho
      have hjX : j < (st.arrs a_X).length := by rw [hXst, length_bitSetList]; exact hj
      have hjo : j < (st.arrs a_o).length := by rw [host]; simp [origList, hj]
      have hval : (st.arrs a_X)[j]'hjX = if (⟨j, hj⟩ : Fin v) ∈ X then 1 else 0 := by
        simp only [hXst, getElem_bitSetList X j hj]
      have hoval : (st.arrs a_o)[j]'hjo = (orig ⟨j, hj⟩).1 := by
        simp only [host, origList, List.getElem_ofFn]
      have hcond : (Expr.read a_X (.reg r_i)).eval w st =
          some (if (⟨j, hj⟩ : Fin v) ∈ X then 1 else 0) := by
        have h01 : (if (⟨j, hj⟩ : Fin v) ∈ X then 1 else 0) < 2 ^ w := by split_ifs <;> omega
        simp only [Expr.eval, checkWord, hreg, hj_w, ↓reduceIte, hjX, ↓reduceDIte, hval, h01]
      by_cases hmem : (⟨j, hj⟩ : Fin v) ∈ X
      · simp only [hmem, ↓reduceIte] at hcond
        have hidx_lt : (orig ⟨j, hj⟩).1 + 1 < 2 ^ w := by have := (orig ⟨j, hj⟩).2; omega
        have hidx : (Expr.op .add (.read a_o (.reg r_i)) (.const 1)).eval w st =
            some ((orig ⟨j, hj⟩).1 + 1) := by
          have hov : (orig ⟨j, hj⟩).1 < 2 ^ w := by omega
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreg, hj_w, hjo, hoval, hov,
            hidx_lt, hw0]
        have hbound : (orig ⟨j, hj⟩).1 + 1 < (st.arrs a_dst).length := by
          rw [hdst]; simp
        have hexw := Exec.write (w := w) (a := a_dst) (s := st) (val := .const 1) (v := 1) hidx
          (by simp [Expr.eval, checkWord, hw0]) hbound
        refine ⟨_, _, .ite_true hcond one_ne_zero hexw, by simp [Expr.cost], ?_, ?_⟩
        · refine ⟨by simp, ?_, ?_, ?_⟩
          · simp only [State.setReg_arrs, State.writeArr_arrs_self, hdst]
            rw [cons_bitSetList_set_one, bitImagePart_succ_of_mem X hj hmem, Finset.image_insert]
          · intro a ha
            simp only [State.setReg_arrs]
            rw [State.writeArr_arrs_ne _ _ _ ha, harr a ha]
          · intro r hr
            rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs, hregs r hr]
        · rw [State.writeArr_regs, hreg]
      · simp only [hmem, ↓reduceIte] at hcond
        refine ⟨_, _, .ite_false hcond (.skip st), by simp [Expr.cost], ?_, hreg⟩
        refine ⟨by simp, ?_, ?_, ?_⟩
        · simp only [State.setReg_arrs, hdst]
          rw [bitImagePart_succ_of_not_mem X hj hmem]
        · intro a ha
          simp only [State.setReg_arrs]
          exact harr a ha
        · intro r hr
          rw [State.setReg_regs_ne _ _ hr, hregs r hr])
  obtain ⟨s₄, t₄, hex₄, ht₄, hI⟩ := hloop s₃ ⟨by simp [s₃], hs₃_dst, hs₃_arr, hs₃_reg⟩
  obtain ⟨_, hdst₄, harr₄, hreg₄⟩ := hI
  refine ⟨s₄, (3 + (n + 1)) + (3 + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    ?_, harr₄, hreg₄⟩
  · simp only [Expr.cost] at ht₄
    omega
  · rw [hdst₄, bitImagePart_of_le X le_rfl]

end GraphMinor.Compute
