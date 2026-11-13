module

public import GraphMinor.Compute.F92Unpack

/-!
# Source lists for the subwall searches

Scan an inside bitset in vertex order and push each member into an array-backed stack.
The stack has capacity equal to the number of vertices. Its occupied prefix is then copied
into an array of exactly the right length, as required by the breadth-first search.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Members of a bitset among the first `i` vertex numbers, in increasing order. -/
def f92SourcesUpTo {n : ℕ} (X : Finset (Fin n)) (i : ℕ) : List ℕ :=
  ((List.finRange n).take i).flatMap (fun v => if v ∈ X then [v.val] else [])

theorem f92SourcesUpTo_succ {n i : ℕ} (X : Finset (Fin n)) (hi : i < n) :
    f92SourcesUpTo X (i + 1) = f92SourcesUpTo X i ++
      if (⟨i, hi⟩ : Fin n) ∈ X then [i] else [] := by
  exact Alg91.flatMap_take_succ_finRange _ hi

theorem length_f92SourcesUpTo_le {n : ℕ} (X : Finset (Fin n)) :
    ∀ i, (f92SourcesUpTo X i).length ≤ i := by
  intro i
  by_cases hi : i ≤ n
  · induction i with
    | zero => simp [f92SourcesUpTo]
    | succ i ih =>
      rw [f92SourcesUpTo_succ X (by omega), List.length_append]
      have hp := ih (by omega)
      split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> omega
  · have htake : (List.finRange n).take i = (List.finRange n).take n := by
      rw [List.take_of_length_le (by simp; omega), List.take_of_length_le (by simp)]
    have hn : (f92SourcesUpTo X n).length ≤ n := by
      have hb : ∀ j ≤ n, (f92SourcesUpTo X j).length ≤ j := by
        intro j hj
        induction j with
        | zero => simp [f92SourcesUpTo]
        | succ j ih =>
          rw [f92SourcesUpTo_succ X (by omega), List.length_append]
          have hp := ih (by omega)
          split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> omega
      exact hb n le_rfl
    unfold f92SourcesUpTo at *
    rw [htake]
    omega

theorem mem_f92SourcesUpTo_full {n : ℕ} (X : Finset (Fin n)) (v : Fin n) :
    v.val ∈ f92SourcesUpTo X n ↔ v ∈ X := by
  simp only [f92SourcesUpTo, List.take_of_length_le
    (show (List.finRange n).length ≤ n by simp), List.mem_flatMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨u, hu⟩
    split_ifs at hu with h
    · have heq : u = v := Fin.ext (List.mem_singleton.mp hu).symm
      exact heq ▸ h
    · simp at hu
  · intro hv
    exact ⟨v, by simp [hv]⟩

theorem lt_of_mem_f92SourcesUpTo {n i v : ℕ} (X : Finset (Fin n))
    (hv : v ∈ f92SourcesUpTo X i) : v < n := by
  obtain ⟨u, _, hu⟩ := List.mem_flatMap.mp hv
  split_ifs at hu with h
  · have heq := List.mem_singleton.mp hu
    exact heq ▸ u.isLt
  · simp at hu

/-- Scan the bitset into the occupied prefix of a stack of capacity `n`. -/
def f92SourceScanProg (a_set a_buf r_n r_i r_count : ℕ) : Cmd :=
  .seq (.alloc a_buf (.reg r_n))
    (.seq (.assign r_count (.const 0))
      (.seq (.assign r_i (.const 0))
        (forUp r_i (.reg r_n)
          (.ite (.read a_set (.reg r_i)) (stackPush a_buf r_count (.reg r_i)) .skip))))

/-- The scan produces precisely the members of the input bitset, without padding in its
occupied prefix. It writes only the buffer and the two loop registers. -/
theorem f92SourceScanProg_exec {w n : ℕ} (X : Finset (Fin n))
    (a_set a_buf r_n r_i r_count : ℕ) (hab : a_set ≠ a_buf)
    (hni : r_n ≠ r_i) (hnc : r_n ≠ r_count) (hic : r_i ≠ r_count)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hset : IsBitSet X a_set s) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (f92SourceScanProg a_set a_buf r_n r_i r_count) s s' t ∧
      t ≤ 8 + 22 * n ∧ IsStack a_buf r_count n (f92SourcesUpTo X n) s' ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → r ≠ r_count → s'.regs r = s.regs r) := by
  let s₁ := s.setArr a_buf (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_buf (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn])
  let s₂ := s₁.setReg r_count 0
  have hex₂ : Exec w (.assign r_count (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₃ := s₂.setReg r_i 0
  have hex₃ : Exec w (.assign r_i (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let Inv (i : ℕ) (st : State) := st.regs r_n = n ∧ st.regs r_i = i ∧
    IsBitSet X a_set st ∧ IsStack a_buf r_count n (f92SourcesUpTo X i) st
  have hloop : ⦃Inv 0⦄[w]
      forUp r_i (.reg r_n) (.ite (.read a_set (.reg r_i))
        (stackPush a_buf r_count (.reg r_i)) .skip)
      ⦃Inv n⦄ ≤ fun _ => 3 + n * 21 := by
    apply Triple.forUp_const Inv n 14 hw hn
    · intro i _ st hi
      exact ⟨hi.2.1, by simp [Expr.eval, checkWord, hi.1, hn]⟩
    · intro i hi st ⟨hrn', hri, hbits, hstack⟩
      have hiw : i < 2 ^ w := hi.trans hn
      have hread : (Expr.read a_set (.reg r_i)).eval w st =
          some (if (⟨i, hi⟩ : Fin n) ∈ X then 1 else 0) := by
        have hb := hbits.getElem_eq_ite ⟨i, hi⟩
        have hlen := hbits.1
        simp only [Expr.eval, hri, checkWord, hiw, hi, hlen, hb, ↓reduceIte]
        split_ifs <;> simp_all
      have hstep : ∃ st' t, Exec w
          (.ite (.read a_set (.reg r_i)) (stackPush a_buf r_count (.reg r_i)) .skip)
          st st' t ∧ t ≤ 14 ∧
          IsStack a_buf r_count n (f92SourcesUpTo X (i + 1)) st' := by
        by_cases hmem : (⟨i, hi⟩ : Fin n) ∈ X
        · obtain ⟨st', t, hex, ht, hout⟩ :=
            Triple.stackPush_spec a_buf r_count (.reg r_i) n (f92SourcesUpTo X i) i
              hw hn (by have := length_f92SourcesUpTo_le X i; omega) st
              ⟨hstack, by simp [Expr.eval, checkWord, hri, hiw]⟩
          refine ⟨st', 2 + t, .ite_true (by simpa [hmem] using hread) (by omega) hex,
            by dsimp [Expr.cost] at ht; omega, ?_⟩
          simpa only [f92SourcesUpTo_succ X hi, hmem, ↓reduceIte] using hout
        · refine ⟨st, 3, .ite_false (by simpa [hmem] using hread) (.skip st), by omega, ?_⟩
          simpa only [f92SourcesUpTo_succ X hi, hmem, ↓reduceIte, List.append_nil] using hstack
      obtain ⟨st', t, hex, ht, hout⟩ := hstep
      have hregs (r : ℕ) (hr : r ≠ r_count) : st'.regs r = st.regs r :=
        hex.regs_eq_of_not_mem_writtenRegs (by simp [stackPush, Cmd.writtenRegs, hr])
      have harr : st'.arrs a_set = st.arrs a_set :=
        hex.arrs_eq_of_not_mem_writtenArrs (by simp [stackPush, Cmd.writtenArrs, hab])
      refine ⟨st', t, hex, ht, ?_, (hregs r_i hic).trans hri⟩
      refine ⟨?_, by simp, ?_, ?_⟩
      · simp [State.setReg_regs_ne _ _ hni, hregs r_n hnc, hrn']
      · exact hbits.of_arr_eq harr
      · rcases hout with ⟨hlen, hle, hcount, hvals⟩
        exact ⟨hlen, hle, by simpa [State.setReg, hic.symm] using hcount, hvals⟩
  have hinit : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂, s₁, hni, hnc, hrn], by simp [s₃],
      hset.of_arr_eq (by simp [s₃, s₂, s₁, hab]), ?_⟩
    refine ⟨by simp [s₃, s₂, s₁], by simp [f92SourcesUpTo], ?_, ?_⟩
    · simp [s₃, s₂, State.setReg, hic.symm, f92SourcesUpTo]
    · simp [f92SourcesUpTo]
  obtain ⟨s₄, t₄, hex₄, ht₄, _, _, _, hout⟩ := hloop s₃ hinit
  dsimp only at ht₄
  have hex : Exec w (f92SourceScanProg a_set a_buf r_n r_i r_count) s s₄
      ((1 + n) + (2 + (2 + t₄))) := .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, _, hex, by omega, hout, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92SourceScanProg, forUp, stackPush, Cmd.writtenArrs, ha])
  · intro r hri hrc
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92SourceScanProg, forUp, stackPush, Cmd.writtenRegs, hri, hrc])

/-- Materialize a bitset as an array of its members, with no unused trailing entries. -/
def f92SourcesProg (a_set a_buf a_dst r_n r_base : ℕ) : Cmd :=
  .seq (f92SourceScanProg a_set a_buf r_n r_base (r_base + 1))
    (readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 1)) (r_base + 2))

/-- The source preparation program produces exactly the inside vertices in linear time.
It only needs a bitset, a size register, separate buffer and output arrays, and word bounds. -/
theorem f92SourcesProg_exec {w n : ℕ} (X : Finset (Fin n))
    (a_set a_buf a_dst r_n r_base : ℕ) (hab : a_set ≠ a_buf) (hbd : a_buf ≠ a_dst)
    (hr : r_n < r_base) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hset : IsBitSet X a_set s) (hrn : s.regs r_n = n) :
    ∃ s' t, Exec w (f92SourcesProg a_set a_buf a_dst r_n r_base) s s' t ∧
      t ≤ 17 + 38 * n ∧ s'.arrs a_dst = f92SourcesUpTo X n ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hstack, harr₁, hreg₁⟩ :=
    f92SourceScanProg_exec X a_set a_buf r_n r_base (r_base + 1)
      hab (by omega) (by omega) (by omega) hw hn hset hrn
  obtain ⟨hlen, hle, hcount, hvals⟩ := hstack
  have htake : (s₁.arrs a_buf).take (f92SourcesUpTo X n).length = f92SourcesUpTo X n := by
    apply List.ext_getElem
    · simp [hlen, Nat.min_eq_left hle]
    · intro i hi hi'
      rw [List.getElem_take]
      exact hvals i hi'
  have hsplit : s₁.arrs a_buf = f92SourcesUpTo X n ++
      (s₁.arrs a_buf).drop (f92SourcesUpTo X n).length := by
    calc
      s₁.arrs a_buf = (s₁.arrs a_buf).take (f92SourcesUpTo X n).length ++
        (s₁.arrs a_buf).drop (f92SourcesUpTo X n).length :=
          (List.take_append_drop _ _).symm
      _ = _ := congrArg (fun L => L ++ (s₁.arrs a_buf).drop (f92SourcesUpTo X n).length) htake
  have hlenw : (f92SourcesUpTo X n).length < 2 ^ w := hle.trans_lt hn
  obtain ⟨s₂, t₂, hex₂, ht₂, hout, harr₂, hreg₂⟩ :=
    readSliceProg_exec a_buf a_dst (.const 0) (r_base + 1) (r_base + 2)
      hbd (by omega) [] (f92SourcesUpTo X n)
      ((s₁.arrs a_buf).drop (f92SourcesUpTo X n).length) rfl rfl
      (fun v hv => (lt_of_mem_f92SourcesUpTo X hv).trans hn) hw (by simpa using hlenw)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw]) hsplit hcount
  dsimp only [Expr.cost] at ht₂
  have hlength := length_f92SourcesUpTo_le X n
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hout,
    fun a hb hd => (harr₂ a hd).trans (harr₁ a hb), ?_⟩
  intro q hq
  exact (hreg₂ q (by omega)).trans (hreg₁ q (by omega) (by omega))

end GraphMinor.Compute.Alg92
