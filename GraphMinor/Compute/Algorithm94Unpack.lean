module

public import GraphMinor.Compute.Algorithm94Wall

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 3: Wall and Subwall Unpacking (`parseFixedWallProg` and `unpackSubwallAtProg`) -/

/-- Mark `W.branchVert u` in bitset array `a_bits` by reading `a_src[r_off + (3 + u.1)]`. -/
def markBranchVertGenProg {h : ℕ} (a_src a_bits : Arr) (r_off : Reg)
    (u : Fin (elemWallNumVerts h)) : Cmd :=
  .write a_bits (.read a_src (.op .add (.reg r_off) (.const (3 + u.1)))) (.const 1)

theorem readBranchVert_at_off {h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (u : Fin (elemWallNumVerts h))
    (pre suf : List ℕ) {a_src : Arr} {s : State}
    (hsrc : s.arrs a_src = pre ++ W.encList ++ suf) :
    ∃ hin_len : pre.length + (3 + u.1) < (s.arrs a_src).length,
      (s.arrs a_src)[pre.length + (3 + u.1)]'hin_len = (W.branchVert u).1 := by
  have hu_lt := u.2
  have hin_len : pre.length + (3 + u.1) < (s.arrs a_src).length := by
    rw [hsrc]
    simp [List.length_append, W.length_encList]
    omega
  refine ⟨hin_len, ?_⟩
  let hdr := pre ++ [h, elemWallNumVerts h, (elemWallEdges h).length]
  let bvs := (List.finRange (elemWallNumVerts h)).map (fun u' => (W.branchVert u').1)
  let rest :=
    (List.finRange (elemWallEdges h).length).flatMap
      (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++ suf
  have hsplit : s.arrs a_src = hdr ++ (bvs ++ rest) := by
    rw [hsrc]
    unfold WallOfHeight.encList
    simp [hdr, bvs, rest, List.append_assoc]
  have hidx_eq : pre.length + (3 + u.1) = hdr.length + u.1 := by
    simp [hdr]; omega
  apply Alg91.getElem_of_eq hsplit hidx_eq (h₂ := by rw [← hsplit, ← hidx_eq]; exact hin_len)
  rw [List.getElem_append_right (Nat.le_add_right _ _)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simp [bvs, hu_lt])]
  simp [bvs]

theorem markBranchVertGenProg_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (a_src a_bits : ℕ) (r_off : ℕ)
    (u : Fin (elemWallNumVerts h))
    (pre suf : List ℕ) (S : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (pre ++ W.encList).length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ W.encList ++ suf)
    (hoff : s.regs r_off = pre.length)
    (hbits : s.arrs a_bits = bitSetList S) :
    ∃ s' t,
      Exec w (markBranchVertGenProg a_src a_bits r_off u) s s' t ∧
      t ≤ 6 ∧
      s'.arrs a_bits = bitSetList (insert (W.branchVert u) S) ∧
      (∀ a : ℕ, a ≠ a_bits → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, s'.regs r = s.regs r) := by
  have hu_lt := u.2
  have hoff_w : pre.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
  have hc_lt_w : 3 + u.1 < 2 ^ w := by omega
  have hidx_w : pre.length + (3 + u.1) < 2 ^ w := by
    have hlen := W.length_encList
    simp [List.length_append] at htot_w
    omega
  obtain ⟨hin_len, hread⟩ := readBranchVert_at_off W u pre suf hsrc
  have hv_w : (W.branchVert u).1 < 2 ^ w := Nat.lt_trans (W.branchVert u).2 hn_w
  have hidx_eval :
      (Expr.read a_src (.op .add (.reg r_off) (.const (3 + u.1)))).eval w s =
        some (W.branchVert u).1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hoff, hoff_w, hc_lt_w,
      hidx_w, hin_len, hread, hv_w]
  have hval_eval : (Expr.const 1).eval w s = some 1 := by
    simp [Expr.eval, checkWord, hw1]
  have hbound : (W.branchVert u).1 < (s.arrs a_bits).length := by
    rw [hbits, length_bitSetList]
    exact (W.branchVert u).2
  let s' := s.writeArr a_bits (W.branchVert u).1 1
  have hex : Exec w (markBranchVertGenProg a_src a_bits r_off u) s s' 6 :=
    .write hidx_eval hval_eval hbound
  refine ⟨s', 6, hex, le_rfl, ?_,
    fun a ha => State.writeArr_arrs_ne s _ _ ha,
    fun _ => rfl⟩
  simp only [s', State.writeArr_arrs_self, hbits, Alg91.bitSetList_set_one]

/-- Mark a list of branch vertices `us : List (Fin (elemWallNumVerts h))` in `a_bits`. -/
def markBranchVertListGenProg {h : ℕ} (a_src a_bits : Arr) (r_off : Reg) :
    List (Fin (elemWallNumVerts h)) → Cmd
  | [] => .skip
  | u :: us =>
    .seq (markBranchVertGenProg a_src a_bits r_off u)
      (markBranchVertListGenProg a_src a_bits r_off us)

theorem markBranchVertListGenProg_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (a_src a_bits : ℕ) (r_off : ℕ)
    (hne : a_src ≠ a_bits) (pre suf : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (pre ++ W.encList).length < 2 ^ w) :
    ∀ (us : List (Fin (elemWallNumVerts h))) (S : Finset (Fin n)) {s : State}
      (_hsrc : s.arrs a_src = pre ++ W.encList ++ suf)
      (_hoff : s.regs r_off = pre.length)
      (_hbits : s.arrs a_bits = bitSetList S),
      ∃ s' t,
        Exec w (markBranchVertListGenProg a_src a_bits r_off us) s s' t ∧
        t ≤ 1 + 6 * us.length ∧
        s'.arrs a_bits = bitSetList (S ∪ us.toFinset.image W.branchVert) ∧
        (∀ a : ℕ, a ≠ a_bits → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, s'.regs r = s.regs r)
  | [], S, s, _, _, hbits => by
    exact ⟨s, 1, .skip s, le_rfl, by simpa using hbits, fun _ _ => rfl, fun _ => rfl⟩
  | u :: us, S, s, hsrc, hoff, hbits => by
    rcases markBranchVertGenProg_exec W a_src a_bits r_off u pre suf S
        hw1 hn_w hc_w htot_w hsrc hoff hbits with
      ⟨s₁, t₁, hex₁, ht₁, hbits₁, harr₁, hreg₁⟩
    rcases markBranchVertListGenProg_exec W a_src a_bits r_off hne pre suf
        hw1 hn_w hc_w htot_w us (insert (W.branchVert u) S)
        (by rw [harr₁ a_src hne, hsrc])
        (by rw [hreg₁ r_off, hoff])
        hbits₁ with
      ⟨s₂, t₂, hex₂, ht₂, hbits₂, harr₂, hreg₂⟩
    have hset_eq :
        insert (W.branchVert u) S ∪ us.toFinset.image W.branchVert =
          S ∪ (u :: us).toFinset.image W.branchVert := by
      ext x; simp [or_left_comm]
    rw [hset_eq] at hbits₂
    exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by simp [List.length_cons]; omega, hbits₂,
      fun a ha => (harr₂ a ha).trans (harr₁ a ha),
      fun r => (hreg₂ r).trans (hreg₁ r)⟩

/-- Record the start offset (`r_pos + 1`) and length (`a_src[r_pos]`) of a length-prefixed list in
`a_src` at `r_pos`, and advance `r_pos` past the list. -/
def recordLenPrefixedGenProg (a_src : Arr) (r_pos r_start r_len : Reg) : Cmd :=
  .seq (.assign r_len (.read a_src (.reg r_pos)))
    (.seq (.assign r_start (.op .add (.reg r_pos) (.const 1)))
      (.assign r_pos (.op .add (.reg r_start) (.reg r_len))))

theorem recordLenPrefixedGenProg_exec {w n : ℕ} (a_src : ℕ) {r_pos r_start r_len : ℕ}
    (hne_ps : r_pos ≠ r_start) (hne_pl : r_pos ≠ r_len) (hne_sl : r_start ≠ r_len)
    (pre : List ℕ) (L : List (Fin n)) (suf : List ℕ)
    (hw1 : 1 < 2 ^ w)
    (hnext_w : (pre ++ (L.length :: L.map Fin.val)).length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ (L.length :: L.map Fin.val) ++ suf)
    (hpos : s.regs r_pos = pre.length) :
    ∃ s' t,
      Exec w (recordLenPrefixedGenProg a_src r_pos r_start r_len) s s' t ∧
      t ≤ 11 ∧
      s'.regs r_start = pre.length + 1 ∧
      s'.regs r_len = L.length ∧
      s'.regs r_pos = (pre ++ (L.length :: L.map Fin.val)).length ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_start → r ≠ r_len → s'.regs r = s.regs r) := by
  have htot_len : (pre ++ (L.length :: L.map Fin.val)).length = pre.length + 1 + L.length := by
    simp [List.length_append]; omega
  have hpos_w : pre.length < 2 ^ w := by omega
  have hlen_w : L.length < 2 ^ w := by omega
  have hp1_w : pre.length + 1 < 2 ^ w := by omega
  have hsum_w : pre.length + 1 + L.length < 2 ^ w := by omega
  have hin_len : pre.length < (s.arrs a_src).length := by
    rw [hsrc]; simp [List.length_append]
  have hin_read : (s.arrs a_src)[pre.length]'hin_len = L.length := by
    let rest := (L.length :: L.map Fin.val) ++ suf
    have hsplit : s.arrs a_src = pre ++ rest := by rw [hsrc, List.append_assoc]
    have hlen2 : pre.length < (pre ++ rest).length := by simp [rest]
    apply Alg91.getElem_of_eq hsplit rfl (h₂ := hlen2)
    rw [List.getElem_append_right (le_refl pre.length)]
    simp [rest]
  let s₁ := s.setReg r_len L.length
  have hex₁ : Exec w (.assign r_len (.read a_src (.reg r_pos))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hpos, hpos_w, hin_len, hin_read, hlen_w])
  let s₂ := s₁.setReg r_start (pre.length + 1)
  have hex₂ : Exec w (.assign r_start (.op .add (.reg r_pos) (.const 1))) s₁ s₂ 4 :=
    .assign (by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ hne_pl, hpos, hpos_w, hw1, hp1_w])
  let s₃ := s₂.setReg r_pos (pre.length + 1 + L.length)
  have hex₃ : Exec w (.assign r_pos (.op .add (.reg r_start) (.reg r_len))) s₂ s₃ 4 :=
    .assign (by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        State.setReg_regs_ne _ _ hne_sl.symm, hp1_w, hlen_w, hsum_w])
  refine ⟨s₃, 3 + (4 + 4), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃, s₂, State.setReg_regs_ne _ _ hne_ps.symm],
    by simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hne_pl.symm, State.setReg_regs_ne _ _ hne_sl.symm],
    by simp [s₃, htot_len],
    fun _ => rfl,
    fun r hr1 hr2 hr3 => by
      simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
        State.setReg_regs_ne _ _ hr3]⟩

/-- Mark every vertex of a slice `L.map Fin.val` in `a_src` (starting at `r_start` of length `r_len`,
using `r_idx` as loop counter) into bitset array `a_bits`. -/
def markSliceGenProg (a_src a_bits : Arr) (r_start r_len r_idx : Reg) : Cmd :=
  .seq (.assign r_idx (.const 0))
    (forUp r_idx (.reg r_len)
      (.write a_bits (.read a_src (.op .add (.reg r_start) (.reg r_idx))) (.const 1)))

theorem markSliceGenProg_exec {w n : ℕ} (a_src a_bits : ℕ) {r_start r_len r_idx : ℕ}
    (hne_arr : a_src ≠ a_bits) (hne_si : r_start ≠ r_idx) (hne_li : r_len ≠ r_idx)
    (pre : List ℕ) (L : List (Fin n)) (suf : List ℕ)
    (S : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (htot_w : (pre ++ L.map Fin.val).length < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = pre ++ L.map Fin.val ++ suf)
    (hstart : s.regs r_start = pre.length)
    (hlen : s.regs r_len = L.length)
    (hbits : s.arrs a_bits = bitSetList S) :
    ∃ s' t,
      Exec w (markSliceGenProg a_src a_bits r_start r_len r_idx) s s' t ∧
      t ≤ 5 + 14 * L.length ∧
      s'.arrs a_bits = bitSetList (S ∪ L.toFinset) ∧
      (∀ a : ℕ, a ≠ a_bits → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_idx → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : L.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
  have hpre_w : pre.length < 2 ^ w := by simp [List.length_append] at htot_w; omega
  let s₀ := s.setReg r_idx 0
  have hex₀ : Exec w (.assign r_idx (.const 0)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs a_src = s.arrs a_src ∧
    st.arrs a_bits = bitSetList (S ∪ (L.take i).toFinset) ∧
    st.regs r_idx = i ∧
    st.regs r_start = pre.length ∧
    st.regs r_len = L.length ∧
    (∀ a : ℕ, a ≠ a_bits → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_idx → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_idx (.reg r_len)
          (.write a_bits (.read a_src (.op .add (.reg r_start) (.reg r_idx))) (.const 1))
      ⦃Inv L.length⦄ ≤ fun _ => 3 + L.length * (7 + 6) := by
    apply Triple.forUp_const Inv L.length 6 hw1 hlen_w
    · intro i _ st ⟨_, _, hri, _, hrl, _, _⟩
      exact ⟨hri, by simp [Expr.eval, checkWord, hrl, hlen_w]⟩
    · intro i hi st ⟨hsrc_st, hbits_st, hri, hrs, hrl, harrs, hregs⟩
      have hi_w : i < 2 ^ w := by omega
      have hadd_w : pre.length + i < 2 ^ w := by simp [List.length_append] at htot_w; omega
      have hin_len : pre.length + i < (st.arrs a_src).length := by
        rw [hsrc_st, hsrc]; simp [List.length_append]; omega
      have hread : (st.arrs a_src)[pre.length + i]'hin_len = (L[i]'hi).1 := by
        let rest := L.map Fin.val ++ suf
        have hsplit : st.arrs a_src = pre ++ rest := by rw [hsrc_st, hsrc, List.append_assoc]
        have hlen2 : pre.length + i < (pre ++ rest).length := by simp [rest, List.length_append]; omega
        apply Alg91.getElem_of_eq hsplit rfl (h₂ := hlen2)
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem_append_left (by simp [hi])]
        simp
      have hv_w : (L[i]'hi).1 < 2 ^ w := Nat.lt_trans (L[i]'hi).2 hn_w
      have hidx_eval :
          (Expr.read a_src (.op .add (.reg r_start) (.reg r_idx))).eval w st = some (L[i]'hi).1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs, hri, hpre_w, hi_w,
          hadd_w, hin_len, hread, hv_w]
      have hval_eval : (Expr.const 1).eval w st = some 1 := by
        simp [Expr.eval, checkWord, hw1]
      have hbound : (L[i]'hi).1 < (st.arrs a_bits).length := by
        rw [hbits_st, length_bitSetList]
        exact (L[i]'hi).2
      let st' := st.writeArr a_bits (L[i]'hi).1 1
      have hex_w :
          Exec w (.write a_bits (.read a_src (.op .add (.reg r_start) (.reg r_idx))) (.const 1))
            st st' 6 :=
        .write hidx_eval hval_eval hbound
      refine ⟨st', 6, hex_w, le_rfl, ?_, by simp [st', hri]⟩
      have hset_eq :
          insert (L[i]'hi) (S ∪ (L.take i).toFinset) = S ∪ (L.take (i + 1)).toFinset := by
        rw [Alg91.take_add_one_toFinset L hi, Finset.union_insert]
      refine ⟨by simpa [st', State.writeArr_arrs_ne _ _ _ hne_arr] using hsrc_st,
        by simp [st', hbits_st, Alg91.bitSetList_set_one, hset_eq],
        State.setReg_regs_self st' r_idx (i + 1),
        by simp [st', State.setReg_regs_ne _ _ hne_si, hrs],
        by simp [st', State.setReg_regs_ne _ _ hne_li, hrl],
        fun a ha => by
          rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
          exact harrs a ha,
        fun r hr => by
          rw [State.setReg_regs_ne _ _ hr, State.writeArr_regs]
          exact hregs r hr⟩
  have hInv0 : Inv 0 s₀ := by
    refine ⟨rfl, by simpa [s₀] using hbits, by simp [s₀],
      by simp [s₀, State.setReg_regs_ne _ _ hne_si, hstart],
      by simp [s₀, State.setReg_regs_ne _ _ hne_li, hlen],
      fun _ _ => rfl,
      fun r hr => by simp [s₀, State.setReg_regs_ne _ _ hr]⟩
  rcases hLoop s₀ hInv0 with ⟨s₁, t₁, hex₁, ht₁, _, hbits₁, _, _, _, harrs₁, hregs₁⟩
  dsimp only at ht₁
  rw [List.take_length] at hbits₁
  exact ⟨s₁, 2 + t₁, .seq hex₀ hex₁, by omega, hbits₁, harrs₁, hregs₁⟩

/-- Build the successor array `a_succ` for the `k`-th edge of `W : WallOfHeight h G` from `a_src`
(where `W.encList` starts at `r_off` and `(W.internalVerts k).map Fin.val` is at `(r_start, r_len)`):
1. Allocates `a_succ` of length `r_n` (`n`),
2. Sets `r_prev := a_src[r_off + 3 + e.1.1]`,
3. Loops `r_idx` from `0` to `r_len`:
   - `r_curr := a_src[r_start + r_idx]`
   - `a_succ[r_prev] := r_curr + 1`
   - `r_prev := r_curr`
4. Sets `r_curr := a_src[r_off + 3 + e.2.1]` and `a_succ[r_prev] := r_curr + 1`. -/
def buildSuccEdgeProg {h : ℕ} (a_src a_succ : Arr) (r_n r_off r_start r_len r_idx r_prev r_curr : Reg)
    (k : Fin (elemWallEdges h).length) : Cmd :=
  let e := (elemWallEdges h)[k.1]'k.2
  .seq (.alloc a_succ (.reg r_n))
    (.seq (.assign r_prev (.read a_src (.op .add (.reg r_off) (.const (3 + e.1.1)))))
      (.seq (.assign r_idx (.const 0))
        (.seq (forUp r_idx (.reg r_len)
                (.seq (.assign r_curr (.read a_src (.op .add (.reg r_start) (.reg r_idx))))
                  (.seq (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1)))
                    (.assign r_prev (.reg r_curr)))))
          (.seq (.assign r_curr (.read a_src (.op .add (.reg r_off) (.const (3 + e.2.1)))))
            (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1)))))))

theorem buildSuccEdgeProg_exec {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (a_src a_succ : ℕ)
    {r_n r_off r_start r_len r_idx r_prev r_curr : ℕ}
    (k : Fin (elemWallEdges h).length)
    (hne_arr : a_src ≠ a_succ)
    (hr_distinct :
      r_n < r_idx ∧ r_off < r_idx ∧ r_start < r_idx ∧ r_len < r_idx ∧
      r_idx < r_prev ∧ r_prev < r_curr)
    (pre_W pre_L suf_L : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    (htotL_w : (pre_L ++ (W.internalVerts k).map Fin.val).length < 2 ^ w)
    {s : State}
    (hsrcW_full : ∃ suf_W, s.arrs a_src = pre_W ++ W.encList ++ suf_W)
    (hsrcL : s.arrs a_src = pre_L ++ (W.internalVerts k).map Fin.val ++ suf_L)
    (hrn : s.regs r_n = n)
    (hroff : s.regs r_off = pre_W.length)
    (hrstart : s.regs r_start = pre_L.length)
    (hrlen : s.regs r_len = (W.internalVerts k).length) :
    ∃ s' t,
      Exec w (buildSuccEdgeProg a_src a_succ r_n r_off r_start r_len r_idx r_prev r_curr k) s s' t ∧
      t ≤ 21 + n + 20 * (W.internalVerts k).length ∧
      s'.arrs a_succ =
        applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
          (List.replicate n 0) ∧
      (∀ a : ℕ, a ≠ a_succ → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_idx → r ≠ r_prev → r ≠ r_curr → s'.regs r = s.regs r) := by
  rcases hsrcW_full with ⟨suf_W, hsrcW'⟩
  let e := (elemWallEdges h)[k.1]'k.2
  let b₁ := W.branchVert e.1
  let b₂ := W.branchVert e.2
  let L := W.internalVerts k
  have hne_prev_curr : r_prev ≠ r_curr := by omega
  have hne_prev_idx : r_prev ≠ r_idx := by omega
  have hne_idx_prev : r_idx ≠ r_prev := by omega
  have hne_idx_curr : r_idx ≠ r_curr := by omega
  have hne_off_idx : r_off ≠ r_idx := by omega
  have hne_off_prev : r_off ≠ r_prev := by omega
  have hne_off_curr : r_off ≠ r_curr := by omega
  have hne_start_idx : r_start ≠ r_idx := by omega
  have hne_start_prev : r_start ≠ r_prev := by omega
  have hne_start_curr : r_start ≠ r_curr := by omega
  have hne_len_idx : r_len ≠ r_idx := by omega
  have hne_len_prev : r_len ≠ r_prev := by omega
  have hne_len_curr : r_len ≠ r_curr := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  have hpreL_w : pre_L.length < 2 ^ w := by simp [List.length_append] at htotL_w; omega
  have hlenL_w : L.length < 2 ^ w := by simp [L, List.length_append] at htotL_w ⊢; omega
  -- 1. alloc a_succ r_n
  let s₁ := s.setArr a_succ (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_succ (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  -- 2. r_prev := a_src[r_off + (3 + e.1.1)]
  have hsrcW₁ : s₁.arrs a_src = pre_W ++ W.encList ++ suf_W := by
    simp [s₁, show (a_src : Arr) ≠ a_succ from hne_arr, hsrcW']
  obtain ⟨hin1_len, hread1⟩ := readBranchVert_at_off W e.1 pre_W suf_W hsrcW₁
  have hc1_w : 3 + e.1.1 < 2 ^ w := by have := e.1.2; omega
  have hidx1_w : pre_W.length + (3 + e.1.1) < 2 ^ w := by
    have := W.length_encList; simp [List.length_append] at htotW_w; omega
  have hb1_w : b₁.1 < 2 ^ w := Nat.lt_trans b₁.2 hn_w
  let s₂ := s₁.setReg r_prev b₁.1
  have hex₂ :
      Exec w (.assign r_prev (.read a_src (.op .add (.reg r_off) (.const (3 + e.1.1))))) s₁ s₂ 5 :=
    .assign (by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hoff_w, hc1_w,
        hidx1_w, hin1_len, hread1, b₁, hb1_w])
  -- 3. r_idx := 0
  let s₃ := s₂.setReg r_idx 0
  have hex₃ : Exec w (.assign r_idx (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. Loop over i = 0 .. L.length
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs a_src = s.arrs a_src ∧
    st.arrs a_succ = applySuccPairs (pairsFrom b₁ (L.take i)) (List.replicate n 0) ∧
    st.regs r_idx = i ∧
    st.regs r_prev = ((b₁ :: L.take i).getLast (by simp)).1 ∧
    st.regs r_off = pre_W.length ∧
    st.regs r_start = pre_L.length ∧
    st.regs r_len = L.length ∧
    (∀ a : ℕ, a ≠ a_succ → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_idx → r ≠ r_prev → r ≠ r_curr → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_idx (.reg r_len)
          (.seq (.assign r_curr (.read a_src (.op .add (.reg r_start) (.reg r_idx))))
            (.seq (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1)))
              (.assign r_prev (.reg r_curr))))
      ⦃Inv L.length⦄ ≤ fun _ => 3 + L.length * (7 + 12) := by
    apply Triple.forUp_const Inv L.length 12 hw1 hlenL_w
    · intro i _ st ⟨_, _, hri, _, _, _, hrl, _, _⟩
      exact ⟨hri, by simp [Expr.eval, checkWord, hrl, hlenL_w]⟩
    · intro i hi st ⟨hsrc_st, hsucc_st, hri, hrprev, hroff_st, hrs_st, hrl_st, harrs, hregs⟩
      have hi' : i < (W.internalVerts k).length := hi
      let prev_v := (b₁ :: L.take i).getLast (by simp)
      let curr_v := L[i]'hi
      have hi_w : i < 2 ^ w := by omega
      have hadd_w : pre_L.length + i < 2 ^ w := by simp [List.length_append] at htotL_w; omega
      have hin_len : pre_L.length + i < (st.arrs a_src).length := by
        rw [hsrc_st, hsrcL]; simp [List.length_append]; omega
      have hread : (st.arrs a_src)[pre_L.length + i]'hin_len = curr_v.1 := by
        let rest := L.map Fin.val ++ suf_L
        have hsplit : st.arrs a_src = pre_L ++ rest := by rw [hsrc_st, hsrcL, List.append_assoc]
        have hlen2 : pre_L.length + i < (pre_L ++ rest).length := by
          simp [rest, List.length_append]; omega
        apply Alg91.getElem_of_eq hsplit rfl (h₂ := hlen2)
        rw [List.getElem_append_right (Nat.le_add_right _ _)]
        simp only [Nat.add_sub_cancel_left]
        rw [List.getElem_append_left (by simp [hi])]
        simp [curr_v]
      have hcurr_w : curr_v.1 < 2 ^ w := Nat.lt_trans curr_v.2 hn_w
      have hcurr1_w : curr_v.1 + 1 < 2 ^ w := by have := curr_v.2; omega
      have hprev_w : prev_v.1 < 2 ^ w := Nat.lt_trans prev_v.2 hn_w
      let st₁ := st.setReg r_curr curr_v.1
      have hex_a :
          Exec w (.assign r_curr (.read a_src (.op .add (.reg r_start) (.reg r_idx)))) st st₁ 5 :=
        .assign (by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrs_st, hri, hpreL_w, hi_w,
            hadd_w, hin_len, hread, hcurr_w])
      have hbound_succ : prev_v.1 < (st₁.arrs a_succ).length := by
        simp [st₁, hsucc_st, length_applySuccPairs, prev_v.2]
      let st₂ := st₁.writeArr a_succ prev_v.1 (curr_v.1 + 1)
      have hi_eval_b : (Expr.reg r_prev).eval w st₁ = some prev_v.1 := by
        simp [st₁, hne_prev_curr, hrprev, prev_v, hprev_w]
      have hv_eval_b :
          (Expr.op .add (.reg r_curr) (.const 1)).eval w st₁ = some (curr_v.1 + 1) := by
        simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcurr_w, hw1, hcurr1_w]
      have hex_b :
          Exec w (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1))) st₁ st₂ 5 :=
        .write hi_eval_b hv_eval_b hbound_succ
      let st₃ := st₂.setReg r_prev curr_v.1
      have hex_c : Exec w (.assign r_prev (.reg r_curr)) st₂ st₃ 2 :=
        .assign (by simp [st₂, st₁, hcurr_w])
      have hex_step :
          Exec w
            (.seq (.assign r_curr (.read a_src (.op .add (.reg r_start) (.reg r_idx))))
              (.seq (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1)))
                (.assign r_prev (.reg r_curr))))
            st st₃ (5 + (5 + 2)) :=
        .seq hex_a (.seq hex_b hex_c)
      refine ⟨st₃, 12, hex_step, le_rfl, ?_, by
        simp [st₃, st₂, st₁, hne_idx_prev, hne_idx_curr, hri]⟩
      have htake_succ : L.take (i + 1) = L.take i ++ [curr_v] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
      have hpairs_succ :
          pairsFrom b₁ (L.take (i + 1)) = pairsFrom b₁ (L.take i) ++ [(prev_v, curr_v)] := by
        rw [htake_succ, pairsFrom_append b₁ (L.take i) [curr_v] (by simp)]
        rfl
      have hsucc_next :
          (applySuccPairs (pairsFrom b₁ (L.take i)) (List.replicate n 0)).set prev_v.1 (curr_v.1 + 1) =
            applySuccPairs (pairsFrom b₁ (L.take (i + 1))) (List.replicate n 0) := by
        rw [hpairs_succ, applySuccPairs_append, applySuccPairs, applySuccPairs]
      have hlast_next :
          (b₁ :: L.take (i + 1)).getLast (by simp) = curr_v := by
        simp [htake_succ]
      refine ⟨by simpa [st₃, st₂, st₁, State.writeArr_arrs_ne _ _ _ hne_arr] using hsrc_st,
        by simpa [st₃, st₂, st₁, hsucc_st] using hsucc_next,
        State.setReg_regs_self _ r_idx (i + 1),
        by simp [st₃, hlast_next, hne_prev_idx],
        by simp [st₃, st₂, st₁, hne_off_idx, hne_off_prev, hne_off_curr, hroff_st],
        by simp [st₃, st₂, st₁, hne_start_idx, hne_start_prev, hne_start_curr, hrs_st],
        by simp [st₃, st₂, st₁, hne_len_idx, hne_len_prev, hne_len_curr, hrl_st],
        fun a ha => by
          rw [State.setReg_arrs, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha,
            State.setReg_arrs]
          exact harrs a ha,
        fun r h1 h2 h3 => by
          simp [st₃, st₂, st₁, h1, h2, h3, hregs r h1 h2 h3]⟩
  have hInv0 : Inv 0 s₃ := by
    refine ⟨by simp [s₃, s₂, s₁, show (a_src : Arr) ≠ a_succ from hne_arr],
      by simp [s₃, s₂, s₁, pairsFrom, applySuccPairs],
      by simp [s₃],
      by simp [s₃, s₂, hne_prev_idx, b₁],
      by simp [s₃, s₂, s₁, hne_off_idx, hne_off_prev, hroff],
      by simp [s₃, s₂, s₁, hne_start_idx, hne_start_prev, hrstart],
      by simp [s₃, s₂, s₁, hne_len_idx, hne_len_prev, hrlen, L],
      fun a ha => by simp [s₃, s₂, s₁, ha],
      fun r h1 h2 _ => by
        simp [s₃, s₂, s₁, h1, h2]⟩
  rcases hLoop s₃ hInv0 with
    ⟨s₄, t₄, hex₄, ht₄, hsrc₄, hsucc₄, _, hrprev₄, hroff₄, _, _, harr₄, hregs₄⟩
  dsimp [L] at ht₄
  rw [List.take_length] at hsucc₄ hrprev₄
  -- 5. Final write: r_curr := a_src[r_off + (3 + e.2.1)]; a_succ[r_prev] := r_curr + 1
  have hsrcW₄ : s₄.arrs a_src = pre_W ++ W.encList ++ suf_W := by rw [hsrc₄, hsrcW']
  obtain ⟨hin2_len, hread2⟩ := readBranchVert_at_off W e.2 pre_W suf_W hsrcW₄
  have hc2_w : 3 + e.2.1 < 2 ^ w := by have := e.2.2; omega
  have hidx2_w : pre_W.length + (3 + e.2.1) < 2 ^ w := by
    have := W.length_encList; simp [List.length_append] at htotW_w; omega
  have hb2_w : b₂.1 < 2 ^ w := Nat.lt_trans b₂.2 hn_w
  have hb2_1_w : b₂.1 + 1 < 2 ^ w := by have := b₂.2; omega
  let s₅ := s₄.setReg r_curr b₂.1
  have hex₅ :
      Exec w (.assign r_curr (.read a_src (.op .add (.reg r_off) (.const (3 + e.2.1))))) s₄ s₅ 5 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff₄, hoff_w, hc2_w,
        hidx2_w, hin2_len, hread2, b₂, hb2_w])
  let last_v := (b₁ :: L).getLast (by simp)
  have hlast_w : last_v.1 < 2 ^ w := Nat.lt_trans last_v.2 hn_w
  have hbound₅ : last_v.1 < (s₅.arrs a_succ).length := by
    simp [s₅, hsucc₄, length_applySuccPairs, last_v.2]
  let s₆ := s₅.writeArr a_succ last_v.1 (b₂.1 + 1)
  have hi_eval₆ : (Expr.reg r_prev).eval w s₅ = some last_v.1 := by
    simp [s₅, hne_prev_curr, hrprev₄, last_v, hlast_w]
  have hv_eval₆ :
      (Expr.op .add (.reg r_curr) (.const 1)).eval w s₅ = some (b₂.1 + 1) := by
    simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hb2_w, hw1, hb2_1_w]
  have hex₆ :
      Exec w (.write a_succ (.reg r_prev) (.op .add (.reg r_curr) (.const 1))) s₅ s₆ 5 :=
    .write hi_eval₆ hv_eval₆ hbound₅
  have hsucc_final :
      s₆.arrs a_succ =
        applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
          (List.replicate n 0) := by
    simp only [s₆, s₅, State.writeArr_arrs_self, State.setReg_arrs, hsucc₄]
    have hsubdiv : W.subdivPathVerts k = b₁ :: (L ++ [b₂]) := rfl
    rw [hsubdiv, ← pairsFrom_eq_zip_drop_one,
      pairsFrom_append b₁ L [b₂] (by simp), applySuccPairs_append]
    rfl
  refine ⟨s₆, (1 + n) + (5 + (2 + (t₄ + (5 + 5)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hsucc_final,
    fun a ha => by
      simp only [s₆, s₅, State.writeArr_arrs_ne _ _ _ ha, State.setReg_arrs]
      exact harr₄ a ha,
    fun r h1 h2 h3 => by
      simp [s₆, s₅, h3, hregs₄ r h1 h2 h3]⟩

/-- Process the `k`-th edge of `W : WallOfHeight h' G` during `parseFixedWallProg`:
1. `recordLenPrefixedGenProg a_src r_pos 4 5`
2. `markSliceGenProg a_src a_V 4 5 6`
3. If `WallOfHeight.isElemWallPerimEdge h' k = true`, marks `e.1`, `e.2`, and the slice `(4, 5)` in `a_perim`
4. If `buildSucc = true`, runs `buildSuccEdgeProg a_src (baseSuccArr + k.1) 1 3 4 5 6 7 8 k`. -/
def processWallEdgeProg (h' : ℕ) (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : Arr) (r_pos : Reg) (k : Fin (elemWallEdges h').length) : Cmd :=
  let e := (elemWallEdges h')[k.1]'k.2
  .seq (recordLenPrefixedGenProg a_src r_pos 4 5)
    (.seq (markSliceGenProg a_src a_V 4 5 6)
      (.seq
        (if WallOfHeight.isElemWallPerimEdge h' k then
          .seq (markBranchVertGenProg a_src a_perim 3 e.1)
            (.seq (markBranchVertGenProg a_src a_perim 3 e.2)
              (markSliceGenProg a_src a_perim 4 5 6))
        else .skip)
        (if buildSucc then
          buildSuccEdgeProg a_src (baseSuccArr + k.1) 1 3 4 5 6 7 8 k
        else .skip)))

theorem toFinset_subdivPathVerts_eq {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (k : Fin (elemWallEdges h').length) :
    (W.subdivPathVerts k).toFinset =
      insert (W.branchVert ((elemWallEdges h')[k.1]'k.2).1)
        (insert (W.branchVert ((elemWallEdges h')[k.1]'k.2).2)
          (W.internalVerts k).toFinset) := by
  ext v
  simp [WallOfHeight.subdivPathVerts, or_comm, or_left_comm]

theorem insert_insert_union_eq {α : Type*} [DecidableEq α] (b1 b2 : α) (SP S : Finset α) :
    insert b2 (insert b1 SP) ∪ S = SP ∪ insert b1 (insert b2 S) := by
  ext v
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

theorem insert_branchVerts_union_internal_eq_subdiv {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (k : Fin (elemWallEdges h').length) (SP : Finset (Fin n)) :
    insert (W.branchVert ((elemWallEdges h')[k.1]'k.2).2)
      (insert (W.branchVert ((elemWallEdges h')[k.1]'k.2).1) SP) ∪ (W.internalVerts k).toFinset =
      SP ∪ (W.subdivPathVerts k).toFinset := by
  rw [toFinset_subdivPathVerts_eq W k]
  exact insert_insert_union_eq _ _ SP _

theorem processWallEdgeProg_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : ℕ) (r_pos : ℕ) (k : Fin (elemWallEdges h').length)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hsucc_ne : buildSucc = true → ∀ idx : Fin (elemWallEdges h').length,
      baseSuccArr + idx.1 ≠ a_src ∧ baseSuccArr + idx.1 ≠ a_V ∧ baseSuccArr + idx.1 ≠ a_perim)
    (hr_pos : 8 < r_pos)
    (pre_W pre_k suf_k : List ℕ) (SV SP : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    (hnext_w : (pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length < 2 ^ w)
    {s : State}
    (hsrcW : ∃ suf_W, s.arrs a_src = pre_W ++ W.encList ++ suf_W)
    (hsrc_k : s.arrs a_src =
      pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++ suf_k)
    (hr1 : s.regs 1 = n)
    (hr3 : s.regs 3 = pre_W.length)
    (hrpos : s.regs r_pos = pre_k.length)
    (hbitsV : s.arrs a_V = bitSetList SV)
    (hbitsP : s.arrs a_perim = bitSetList SP) :
    ∃ s' t,
      Exec w (processWallEdgeProg h' buildSucc baseSuccArr a_src a_V a_perim r_pos k) s s' t ∧
      t ≤ 55 + n + 48 * (W.internalVerts k).length ∧
      s'.regs r_pos =
        (pre_k ++ ((W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ∧
      s'.arrs a_V = bitSetList (SV ∪ (W.internalVerts k).toFinset) ∧
      s'.arrs a_perim =
        bitSetList (if WallOfHeight.isElemWallPerimEdge h' k then SP ∪ (W.subdivPathVerts k).toFinset else SP) ∧
      (buildSucc = true →
        s'.arrs (baseSuccArr + k.1) =
          applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
            (List.replicate n 0)) ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim →
        (buildSucc = true → a ≠ baseSuccArr + k.1) → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 4 ∨ 8 < r) → r ≠ r_pos → s'.regs r = s.regs r) := by
  have hn_w : n < 2 ^ w := by omega
  -- 1. recordLenPrefixedGenProg a_src r_pos 4 5
  rcases recordLenPrefixedGenProg_exec a_src (r_pos := r_pos) (r_start := 4) (r_len := 5)
      (by omega) (by omega) (by decide) pre_k (W.internalVerts k) suf_k hw1 hnext_w hsrc_k hrpos with
    ⟨s₁, t₁, hex₁, ht₁, hr4_1, hr5_1, hrpos₁, harr₁, hreg₁⟩
  -- 2. markSliceGenProg a_src a_V 4 5 6
  let pre_slice := pre_k ++ [(W.internalVerts k).length]
  have hsrc_slice : s.arrs a_src = pre_slice ++ (W.internalVerts k).map Fin.val ++ suf_k := by
    simpa [pre_slice, List.append_assoc] using hsrc_k
  have hpre_slice_len : pre_slice.length = pre_k.length + 1 := by simp [pre_slice]
  have htot_slice_w : (pre_slice ++ (W.internalVerts k).map Fin.val).length < 2 ^ w := by
    simpa [pre_slice, List.append_assoc] using hnext_w
  rcases markSliceGenProg_exec a_src a_V (r_start := 4) (r_len := 5) (r_idx := 6)
      hne_sV (by decide) (by decide) pre_slice (W.internalVerts k) suf_k SV
      hw1 hn_w htot_slice_w
      (by rw [harr₁, hsrc_slice])
      (by rw [hpre_slice_len]; exact hr4_1)
      hr5_1
      (by rw [harr₁]; exact hbitsV) with
    ⟨s₂, t₂, hex₂, ht₂, hbitsV₂, harr₂, hreg₂⟩
  -- 3. Perimeter marking
  have hsrc₂ : s₂.arrs a_src = s.arrs a_src := by rw [harr₂ a_src hne_sV, harr₁]
  have hr3_2 : s₂.regs 3 = pre_W.length := by
    rw [hreg₂ 3 (by decide), hreg₁ 3 (by omega) (by decide) (by decide), hr3]
  have hr4_2 : s₂.regs 4 = pre_slice.length := by
    rw [hreg₂ 4 (by decide), hpre_slice_len, hr4_1]
  have hr5_2 : s₂.regs 5 = (W.internalVerts k).length := by
    rw [hreg₂ 5 (by decide), hr5_1]
  have hbitsP₂ : s₂.arrs a_perim = bitSetList SP := by
    rw [harr₂ a_perim hne_VP.symm, harr₁, hbitsP]
  have hperim_step :
      ∃ s₃ t₃,
        Exec w
          (if WallOfHeight.isElemWallPerimEdge h' k then
            .seq (markBranchVertGenProg a_src a_perim 3 ((elemWallEdges h')[k.1]'k.2).1)
              (.seq (markBranchVertGenProg a_src a_perim 3 ((elemWallEdges h')[k.1]'k.2).2)
                (markSliceGenProg a_src a_perim 4 5 6))
          else .skip)
          s₂ s₃ t₃ ∧
        t₃ ≤ 17 + 14 * (W.internalVerts k).length ∧
        s₃.arrs a_perim =
          bitSetList (if WallOfHeight.isElemWallPerimEdge h' k then SP ∪ (W.subdivPathVerts k).toFinset else SP) ∧
        (∀ a : ℕ, a ≠ a_perim → s₃.arrs a = s₂.arrs a) ∧
        (∀ r : ℕ, r ≠ 6 → s₃.regs r = s₂.regs r) := by
    cases hperim : WallOfHeight.isElemWallPerimEdge h' k
    · exact ⟨s₂, 1, .skip s₂, by omega, hbitsP₂, fun _ _ => rfl, fun _ _ => rfl⟩
    · rcases hsrcW with ⟨suf_W, hsrcW_eq⟩
      let e := (elemWallEdges h')[k.1]'k.2
      rcases markBranchVertGenProg_exec W a_src a_perim 3 e.1 pre_W suf_W SP
          hw1 hn_w hc_w htotW_w (by rw [hsrc₂, hsrcW_eq]) hr3_2 hbitsP₂ with
        ⟨s₂a, t₂a, hex₂a, ht₂a, hbitsP_a, harr₂a, hreg₂a⟩
      rcases markBranchVertGenProg_exec W a_src a_perim 3 e.2 pre_W suf_W
          (insert (W.branchVert e.1) SP)
          hw1 hn_w hc_w htotW_w
          (by rw [harr₂a a_src hne_sP, hsrc₂, hsrcW_eq])
          (by rw [hreg₂a 3, hr3_2])
          hbitsP_a with
        ⟨s₂b, t₂b, hex₂b, ht₂b, hbitsP_b, harr₂b, hreg₂b⟩
      rcases markSliceGenProg_exec a_src a_perim (r_start := 4) (r_len := 5) (r_idx := 6)
          hne_sP (by decide) (by decide) pre_slice (W.internalVerts k) suf_k
          (insert (W.branchVert e.2) (insert (W.branchVert e.1) SP))
          hw1 hn_w htot_slice_w
          (by rw [harr₂b a_src hne_sP, harr₂a a_src hne_sP, hsrc₂, hsrc_slice])
          (by rw [hreg₂b 4, hreg₂a 4, hr4_2])
          (by rw [hreg₂b 5, hreg₂a 5, hr5_2])
          hbitsP_b with
        ⟨s₂c, t₂c, hex₂c, ht₂c, hbitsP_c, harr₂c, hreg₂c⟩
      have hbitsP_c' : s₂c.arrs a_perim = bitSetList (SP ∪ (W.subdivPathVerts k).toFinset) :=
        hbitsP_c.trans (congrArg bitSetList (insert_branchVerts_union_internal_eq_subdiv W k SP))
      refine ⟨s₂c, t₂a + (t₂b + t₂c),
        Exec.seq hex₂a (.seq hex₂b hex₂c),
        by omega,
        hbitsP_c',
        fun a ha => (harr₂c a ha).trans ((harr₂b a ha).trans (harr₂a a ha)),
        fun r hr => (hreg₂c r hr).trans ((hreg₂b r).trans (hreg₂a r))⟩
  rcases hperim_step with ⟨s₃, t₃, hex₃, ht₃, hbitsP₃, harr₃, hreg₃⟩
  -- 4. Successor array building
  have hsrc₃ : s₃.arrs a_src = s.arrs a_src := by rw [harr₃ a_src hne_sP, hsrc₂]
  have hr1_3 : s₃.regs 1 = n := by
    rw [hreg₃ 1 (by decide), hreg₂ 1 (by decide), hreg₁ 1 (by omega) (by decide) (by decide), hr1]
  have hr3_3 : s₃.regs 3 = pre_W.length := by rw [hreg₃ 3 (by decide), hr3_2]
  have hr4_3 : s₃.regs 4 = pre_slice.length := by rw [hreg₃ 4 (by decide), hr4_2]
  have hr5_3 : s₃.regs 5 = (W.internalVerts k).length := by rw [hreg₃ 5 (by decide), hr5_2]
  have hsucc_step :
      ∃ s₄ t₄,
        Exec w
          (if buildSucc then
            buildSuccEdgeProg a_src (baseSuccArr + k.1) 1 3 4 5 6 7 8 k
          else .skip)
          s₃ s₄ t₄ ∧
        t₄ ≤ 21 + n + 20 * (W.internalVerts k).length ∧
        (buildSucc = true →
          s₄.arrs (baseSuccArr + k.1) =
            applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
              (List.replicate n 0)) ∧
        (∀ a : ℕ, (buildSucc = true → a ≠ baseSuccArr + k.1) → s₄.arrs a = s₃.arrs a) ∧
        (∀ r : ℕ, r ≠ 6 → r ≠ 7 → r ≠ 8 → s₄.regs r = s₃.regs r) := by
    cases hbuild : buildSucc
    · refine ⟨s₃, 1, .skip s₃, by omega, fun h => Bool.noConfusion h,
        fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · have hne_succ_src : a_src ≠ baseSuccArr + k.1 := (hsucc_ne hbuild k).1.symm
      rcases hsrcW with ⟨suf_W, hsrcW_eq⟩
      rcases buildSuccEdgeProg_exec W a_src (baseSuccArr + k.1)
          (r_n := 1) (r_off := 3) (r_start := 4) (r_len := 5) (r_idx := 6) (r_prev := 7) (r_curr := 8)
          k hne_succ_src
          ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
          pre_W pre_slice suf_k hw1 hn1_w hc_w htotW_w htot_slice_w
          (s := s₃)
          ⟨suf_W, by rw [hsrc₃, hsrcW_eq]⟩
          (by rw [hsrc₃, hsrc_slice])
          hr1_3 hr3_3 hr4_3 hr5_3 with
        ⟨s₄, t₄, hex₄, ht₄, hsucc₄, harr₄, hreg₄⟩
      refine ⟨s₄, t₄, hex₄, ht₄, fun _ => hsucc₄,
        fun a ha => harr₄ a (ha rfl), hreg₄⟩
  rcases hsucc_step with ⟨s₄, t₄, hex₄, ht₄, hsucc₄, harr₄, hreg₄⟩
  have hne_V_succ : buildSucc = true → a_V ≠ baseSuccArr + k.1 :=
    fun hb => (hsucc_ne hb k).2.1.symm
  have hne_P_succ : buildSucc = true → a_perim ≠ baseSuccArr + k.1 :=
    fun hb => (hsucc_ne hb k).2.2.symm
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by
      rw [hreg₄ r_pos (by omega) (by omega) (by omega),
        hreg₃ r_pos (by omega), hreg₂ r_pos (by omega), hrpos₁],
    by rw [harr₄ a_V hne_V_succ, harr₃ a_V hne_VP, hbitsV₂],
    by rw [harr₄ a_perim hne_P_succ, hbitsP₃],
    hsucc₄,
    fun a haV haP haS => by
      rw [harr₄ a haS, harr₃ a haP, harr₂ a haV, harr₁],
    fun r hr hne_pos => by
      have hr6 : r ≠ 6 := by omega
      have hr7 : r ≠ 7 := by omega
      have hr8 : r ≠ 8 := by omega
      have hr4 : r ≠ 4 := by omega
      have hr5 : r ≠ 5 := by omega
      rw [hreg₄ r hr6 hr7 hr8, hreg₃ r hr6, hreg₂ r hr6, hreg₁ r hne_pos hr4 hr5]⟩

/-- Union of `(W.internalVerts k).toFinset` over the first `j` edges of `W`. -/
def edgeInternalFinsetUpTo {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) (j : ℕ) :
    Finset (Fin n) :=
  (((List.finRange (elemWallEdges h').length).take j).flatMap W.internalVerts).toFinset

/-- Union of `(W.subdivPathVerts k).toFinset` over perimeter edges among the first `j` edges of `W`. -/
def perimFinsetUpTo {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) (j : ℕ) :
    Finset (Fin n) :=
  ((((List.finRange (elemWallEdges h').length).take j).filter
    (WallOfHeight.isElemWallPerimEdge h')).flatMap W.subdivPathVerts).toFinset

@[simp]
theorem edgeInternalFinsetUpTo_zero {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) :
    edgeInternalFinsetUpTo W 0 = ∅ := by
  simp [edgeInternalFinsetUpTo]

@[simp]
theorem perimFinsetUpTo_zero {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) :
    perimFinsetUpTo W 0 = ∅ := by
  simp [perimFinsetUpTo]

theorem edgeInternalFinsetUpTo_succ {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G)
    {j : ℕ} (hj : j < (elemWallEdges h').length) :
    edgeInternalFinsetUpTo W (j + 1) =
      edgeInternalFinsetUpTo W j ∪ (W.internalVerts ⟨j, hj⟩).toFinset := by
  unfold edgeInternalFinsetUpTo
  have hj_len : j < (List.finRange (elemWallEdges h').length).length := by simp [hj]
  rw [List.take_add_one, List.getElem?_eq_getElem hj_len, Option.toList_some,
    List.flatMap_append, List.flatMap_singleton, List.toFinset_append]
  simp

theorem perimFinsetUpTo_succ {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G)
    {j : ℕ} (hj : j < (elemWallEdges h').length) :
    perimFinsetUpTo W (j + 1) =
      if WallOfHeight.isElemWallPerimEdge h' ⟨j, hj⟩ then
        perimFinsetUpTo W j ∪ (W.subdivPathVerts ⟨j, hj⟩).toFinset
      else
        perimFinsetUpTo W j := by
  unfold perimFinsetUpTo
  have hj_len : j < (List.finRange (elemWallEdges h').length).length := by simp [hj]
  rw [List.take_add_one, List.getElem?_eq_getElem hj_len, Option.toList_some, List.filter_append]
  simp only [List.getElem_finRange]
  by_cases hp : WallOfHeight.isElemWallPerimEdge h' ⟨j, hj⟩ = true
  · simp [hp, List.flatMap_append, List.toFinset_append]
  · simp only [Bool.not_eq_true] at hp
    simp [hp]

theorem branchVerts_union_edgeInternalFinsetUpTo_full {h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) :
    (List.finRange (elemWallNumVerts h')).toFinset.image W.branchVert ∪
      edgeInternalFinsetUpTo W (elemWallEdges h').length = W.vertexFinset := by
  unfold edgeInternalFinsetUpTo WallOfHeight.vertexFinset
  have htake :
      (List.finRange (elemWallEdges h').length).take (elemWallEdges h').length =
        List.finRange (elemWallEdges h').length :=
    List.take_of_length_le (by simp)
  have huniv :
      (List.finRange (elemWallNumVerts h')).toFinset =
        (Finset.univ : Finset (Fin (elemWallNumVerts h'))) := by
    ext u; simp
  rw [htake, huniv]

theorem perimFinsetUpTo_full {h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h' G) :
    perimFinsetUpTo W (elemWallEdges h').length = W.perimeterFinset := by
  unfold perimFinsetUpTo WallOfHeight.perimeterFinset
  have htake :
      (List.finRange (elemWallEdges h').length).take (elemWallEdges h').length =
        List.finRange (elemWallEdges h').length :=
    List.take_of_length_le (by simp)
  rw [htake]

/-- Process the first `j` edges of `W : WallOfHeight h' G` (`j ≤ (elemWallEdges h').length`). -/
def processWallEdgesUpTo (h' : ℕ) (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : Arr) (r_pos : Reg) : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (processWallEdgesUpTo h' buildSucc baseSuccArr a_src a_V a_perim r_pos j)
      (if hj : j < (elemWallEdges h').length then
        processWallEdgeProg h' buildSucc baseSuccArr a_src a_V a_perim r_pos ⟨j, hj⟩
      else .skip)

theorem processWallEdgesUpTo_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h' G) (hW : W.IsValid)
    (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : ℕ) (r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hsucc_ne : buildSucc = true → ∀ idx : Fin (elemWallEdges h').length,
      baseSuccArr + idx.1 ≠ a_src ∧ baseSuccArr + idx.1 ≠ a_V ∧ baseSuccArr + idx.1 ≠ a_perim)
    (hr_pos : 8 < r_pos)
    (pre_W pre_edges suf : List ℕ) (SV₀ : Finset (Fin n))
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h' < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    (htotE_w :
      (pre_edges ++
        (List.finRange (elemWallEdges h').length).flatMap
          (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length <
        2 ^ w) :
    ∀ j (_hj : j ≤ (elemWallEdges h').length) {s : State}
      (_hsrcW : ∃ suf_W, s.arrs a_src = pre_W ++ W.encList ++ suf_W)
      (_hsrcE : s.arrs a_src =
        pre_edges ++
          (List.finRange (elemWallEdges h').length).flatMap
            (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) ++
          suf)
      (_hr1 : s.regs 1 = n)
      (_hr3 : s.regs 3 = pre_W.length)
      (_hrpos : s.regs r_pos = pre_edges.length)
      (_hbitsV : s.arrs a_V = bitSetList SV₀)
      (_hbitsP : s.arrs a_perim = bitSetList (∅ : Finset (Fin n))),
      ∃ s' t,
        Exec w (processWallEdgesUpTo h' buildSucc baseSuccArr a_src a_V a_perim r_pos j) s s' t ∧
        t ≤ 1 + j * (55 + 49 * n) ∧
        s'.regs r_pos =
          (pre_edges ++
            ((List.finRange (elemWallEdges h').length).take j).flatMap
              (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)).length ∧
        s'.arrs a_V = bitSetList (SV₀ ∪ edgeInternalFinsetUpTo W j) ∧
        s'.arrs a_perim = bitSetList (perimFinsetUpTo W j) ∧
        (buildSucc = true →
          ∀ k : Fin (elemWallEdges h').length, k.1 < j →
            s'.arrs (baseSuccArr + k.1) =
              applySuccPairs ((W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1))
                (List.replicate n 0)) ∧
        (∀ a : ℕ, a ≠ a_V → a ≠ a_perim →
          (buildSucc = true → ∀ k : Fin (elemWallEdges h').length, a ≠ baseSuccArr + k.1) →
          s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, (r < 4 ∨ 8 < r) → r ≠ r_pos → s'.regs r = s.regs r)
  | 0, _, s, _, _, _, _, hrpos, hbitsV, hbitsP => by
    exact ⟨s, 1, .skip s, by omega, by simpa using hrpos,
      by simpa using hbitsV, by simpa using hbitsP,
      fun _ _ hk => by omega, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  | j + 1, hj, s, hsrcW, hsrcE, hr1, hr3, hrpos, hbitsV, hbitsP => by
    have hj_lt : j < (elemWallEdges h').length := by omega
    let f : Fin (elemWallEdges h').length → List ℕ :=
      fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val
    rcases processWallEdgesUpTo_exec W hW buildSucc baseSuccArr a_src a_V a_perim r_pos
        hne_sV hne_sP hne_VP hsucc_ne hr_pos pre_W pre_edges suf SV₀
        hw1 hn1_w hc_w htotW_w htotE_w j (by omega) hsrcW hsrcE hr1 hr3 hrpos hbitsV hbitsP with
      ⟨s₁, t₁, hex₁, ht₁, hrpos₁, hbitsV₁, hbitsP₁, hsucc₁, harr₁, hreg₁⟩
    have hsrc₁ : s₁.arrs a_src = s.arrs a_src :=
      harr₁ a_src hne_sV hne_sP (fun hb k => (hsucc_ne hb k).1.symm)
    let pre_j := pre_edges ++ ((List.finRange (elemWallEdges h').length).take j).flatMap f
    let suf_j := ((List.finRange (elemWallEdges h').length).drop (j + 1)).flatMap f ++ suf
    have hsplit :
        pre_edges ++ (List.finRange (elemWallEdges h').length).flatMap f ++ suf =
          pre_j ++ f ⟨j, hj_lt⟩ ++ suf_j := by
      rw [Alg91.flatMap_finRange_eq_take_append_drop f j,
        Alg91.flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, suf_j, List.append_assoc]
    have hnext_le :
        (pre_j ++ f ⟨j, hj_lt⟩).length ≤
          (pre_edges ++ (List.finRange (elemWallEdges h').length).flatMap f).length := by
      rw [Alg91.flatMap_finRange_eq_take_append_drop f j,
        Alg91.flatMap_drop_eq_cons f hj_lt]
      simp [pre_j, List.length_append]
    have hnext_w : (pre_j ++ f ⟨j, hj_lt⟩).length < 2 ^ w :=
      Nat.lt_of_le_of_lt hnext_le htotE_w
    rcases processWallEdgeProg_exec W buildSucc baseSuccArr a_src a_V a_perim r_pos ⟨j, hj_lt⟩
        hne_sV hne_sP hne_VP hsucc_ne hr_pos pre_W pre_j suf_j
        (SV₀ ∪ edgeInternalFinsetUpTo W j) (perimFinsetUpTo W j)
        hw1 hn1_w hc_w htotW_w hnext_w
        (by rcases hsrcW with ⟨suf_W, hW_eq⟩; exact ⟨suf_W, by rw [hsrc₁, hW_eq]⟩)
        (by rw [hsrc₁, hsrcE, hsplit])
        (by rw [hreg₁ 1 (Or.inl (by decide)) (by omega), hr1])
        (by rw [hreg₁ 3 (Or.inl (by decide)) (by omega), hr3])
        hrpos₁ hbitsV₁ hbitsP₁ with
      ⟨s₂, t₂, hex₂, ht₂, hrpos₂, hbitsV₂, hbitsP₂, hsucc₂, harr₂, hreg₂⟩
    have hlen_int : (W.internalVerts ⟨j, hj_lt⟩).length ≤ n :=
      Alg91.length_internalVerts_le_of_isValid hW ⟨j, hj_lt⟩
    have ht₂_bound : t₂ ≤ 55 + 49 * n := by
      have : 48 * (W.internalVerts ⟨j, hj_lt⟩).length ≤ 48 * n :=
        Nat.mul_le_mul_left 48 hlen_int
      omega
    have hrpos₂' :
        s₂.regs r_pos =
          (pre_edges ++ ((List.finRange (elemWallEdges h').length).take (j + 1)).flatMap f).length := by
      rw [hrpos₂, Alg91.flatMap_take_succ_finRange f hj_lt, ← List.append_assoc]
    have hbitsV₂' : s₂.arrs a_V = bitSetList (SV₀ ∪ edgeInternalFinsetUpTo W (j + 1)) := by
      rw [hbitsV₂, edgeInternalFinsetUpTo_succ W hj_lt, Finset.union_assoc]
    have hbitsP₂' : s₂.arrs a_perim = bitSetList (perimFinsetUpTo W (j + 1)) := by
      rw [hbitsP₂, perimFinsetUpTo_succ W hj_lt]
    refine ⟨s₂, t₁ + t₂,
      by simpa [processWallEdgesUpTo, hj_lt] using Exec.seq hex₁ hex₂,
      by rw [Nat.succ_mul]; omega,
      hrpos₂', hbitsV₂', hbitsP₂',
      fun hb k hk => ?_,
      fun a haV haP haS =>
        (harr₂ a haV haP (fun hb => haS hb ⟨j, hj_lt⟩)).trans (harr₁ a haV haP haS),
      fun r hr hne_pos => (hreg₂ r hr hne_pos).trans (hreg₁ r hr hne_pos)⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | hk_eq
    · rw [harr₂ (baseSuccArr + k.1) (hsucc_ne hb k).2.1 (hsucc_ne hb k).2.2
        (fun _ => by change baseSuccArr + k.1 ≠ baseSuccArr + j; omega)]
      exact hsucc₁ hb k hk_lt
    · have hk_fin : k = ⟨j, hj_lt⟩ := Fin.ext hk_eq
      subst hk_fin
      exact hsucc₂ hb

/-- Unpack a wall `W : WallOfHeight h' G` of known height `h'` (`h2' : 2 ≤ h'`) from `a_src`
starting at `r_pos`:
1. `reg 3 := reg r_pos` (saves `pre_W.length`),
2. `reg 14 := a_src[reg 3 + (3 + (elemWallMiddle₁Idx h2').1)]` (loads `(W.seedVert h2').1`),
3. `alloc a_V (reg 1)` and `alloc a_perim (reg 1)`,
4. `markBranchVertListGenProg a_src a_V 3 (List.finRange (elemWallNumVerts h'))`,
5. `reg r_pos := reg 3 + (3 + elemWallNumVerts h')`,
6. `processWallEdgesUpTo h' buildSucc baseSuccArr a_src a_V a_perim r_pos (elemWallEdges h').length`.
Advances `r_pos` to `(pre_W ++ W.encList).length`, populates `IsBitSet W.vertexFinset a_V s'` and
`IsBitSet W.perimeterFinset a_perim s'`, sets `s'.regs 14 = (W.seedVert h2').1`, and if
`buildSucc = true`, populates `IsWallSuccArrs W baseSuccArr s'`. -/
def parseFixedWallProg (h' : ℕ) (h2' : 2 ≤ h') (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : Arr) (r_pos : Reg) : Cmd :=
  .seq (.assign 3 (.reg r_pos))
    (.seq (.assign 14 (.read a_src (.op .add (.reg 3) (.const (3 + (elemWallMiddle₁Idx h2').1)))))
      (.seq (.alloc a_V (.reg 1))
        (.seq (.alloc a_perim (.reg 1))
          (.seq (markBranchVertListGenProg a_src a_V 3 (List.finRange (elemWallNumVerts h')))
            (.seq (.assign r_pos (.op .add (.reg 3) (.const (3 + elemWallNumVerts h'))))
              (processWallEdgesUpTo h' buildSucc baseSuccArr a_src a_V a_perim r_pos
                (elemWallEdges h').length))))))

/-- Upper bound on the step count of `parseFixedWallProg` for a wall of height `h' ≤ h` on `n`
vertices. -/
def parseWallCost (h n : ℕ) : ℕ :=
  15 + 2 * n + 6 * elemWallNumVerts h + 2 * elemWallNumVerts h * (55 + 49 * n)

theorem parseFixedWallProg_exec {w h h' n : ℕ} (h2' : 2 ≤ h') (hle : h' ≤ h)
    {G : MultiDigraph n} (W : WallOfHeight h' G) (hW : W.IsValid)
    (buildSucc : Bool) (baseSuccArr : ℕ)
    (a_src a_V a_perim : ℕ) (r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hsucc_ne : buildSucc = true → ∀ idx : Fin (elemWallEdges h').length,
      baseSuccArr + idx.1 ≠ a_src ∧ baseSuccArr + idx.1 ≠ a_V ∧ baseSuccArr + idx.1 ≠ a_perim)
    (hr_pos : 14 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W.encList).length < 2 ^ w)
    {s : State}
    (hsrcW : s.arrs a_src = pre_W ++ W.encList ++ suf_W)
    (hr1 : s.regs 1 = n)
    (hrpos : s.regs r_pos = pre_W.length) :
    ∃ s' t,
      Exec w (parseFixedWallProg h' h2' buildSucc baseSuccArr a_src a_V a_perim r_pos) s s' t ∧
      t ≤ parseWallCost h n ∧
      s'.regs r_pos = (pre_W ++ W.encList).length ∧
      s'.regs 14 = (W.seedVert h2').1 ∧
      IsBitSet W.vertexFinset a_V s' ∧
      IsBitSet W.perimeterFinset a_perim s' ∧
      (buildSucc = true → IsWallSuccArrs W baseSuccArr s') ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim →
        (buildSucc = true → ∀ k : Fin (elemWallEdges h').length, a ≠ baseSuccArr + k.1) →
        s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 14 → r ≠ r_pos → s'.regs r = s.regs r) := by
  have hn_w : n < 2 ^ w := by omega
  have hV_mono : elemWallNumVerts h' ≤ elemWallNumVerts h := Alg91.elemWallNumVerts_mono hle
  have hc'_w : 3 + elemWallNumVerts h' < 2 ^ w := by omega
  have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  -- 1. reg 3 := reg r_pos
  let s₁ := s.setReg 3 pre_W.length
  have hex₁ : Exec w (.assign 3 (.reg r_pos)) s s₁ 2 :=
    .assign (by simp [hrpos, hoff_w])
  -- 2. reg 14 := a_src[reg 3 + (3 + (elemWallMiddle₁Idx h2').1)]
  let mid_idx := elemWallMiddle₁Idx h2'
  obtain ⟨hin_mid, hread_mid⟩ := readBranchVert_at_off W mid_idx pre_W suf_W hsrcW
  have hcmid_w : 3 + mid_idx.1 < 2 ^ w := by have := mid_idx.2; omega
  have hidx_mid_w : pre_W.length + (3 + mid_idx.1) < 2 ^ w := by
    have := W.length_encList; simp [List.length_append] at htotW_w; omega
  have hseed_w : (W.branchVert mid_idx).1 < 2 ^ w := Nat.lt_trans (W.branchVert mid_idx).2 hn_w
  have heval_seed :
      (Expr.read a_src (.op .add (.reg 3) (.const (3 + mid_idx.1)))).eval w s₁ =
        some (W.seedVert h2').1 := by
    change _ = some (W.branchVert mid_idx).1
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hoff_w, hcmid_w, hidx_mid_w,
      hin_mid, hread_mid, hseed_w]
  let s₂ := s₁.setReg 14 (W.seedVert h2').1
  have hex₂ :
      Exec w (.assign 14 (.read a_src (.op .add (.reg 3) (.const (3 + mid_idx.1))))) s₁ s₂ 5 :=
    .assign heval_seed
  -- 3. alloc a_V (reg 1)
  let s₃ := s₂.setArr a_V (List.replicate n 0)
  have hex₃ : Exec w (.alloc a_V (.reg 1)) s₂ s₃ (1 + n) :=
    .alloc (by simp [s₂, s₁, hr1, hn_w])
  -- 4. alloc a_perim (reg 1)
  let s₄ := s₃.setArr a_perim (List.replicate n 0)
  have hex₄ : Exec w (.alloc a_perim (.reg 1)) s₃ s₄ (1 + n) :=
    .alloc (by simp [s₃, s₂, s₁, hr1, hn_w])
  -- 5. markBranchVertListGenProg a_src a_V 3 (List.finRange (elemWallNumVerts h'))
  have hsrcW₄ : s₄.arrs a_src = pre_W ++ W.encList ++ suf_W := by
    simp [s₄, s₃, s₂, s₁, hne_sP, hne_sV, hsrcW]
  have hbitsV₄ : s₄.arrs a_V = bitSetList (∅ : Finset (Fin n)) := by
    simp [s₄, s₃, hne_VP, Alg91.bitSetList_empty]
  rcases markBranchVertListGenProg_exec W a_src a_V 3 hne_sV pre_W suf_W
      hw1 hn_w hc'_w htotW_w (List.finRange (elemWallNumVerts h')) ∅
      hsrcW₄ (by simp [s₄, s₃, s₂, s₁]) hbitsV₄ with
    ⟨s₅, t₅, hex₅, ht₅, hbitsV₅, harr₅, hreg₅⟩
  rw [Finset.empty_union] at hbitsV₅
  rw [List.length_finRange] at ht₅
  -- 6. reg r_pos := reg 3 + (3 + elemWallNumVerts h')
  let hdr := [h', elemWallNumVerts h', (elemWallEdges h').length] ++
    (List.finRange (elemWallNumVerts h')).map (fun u => (W.branchVert u).1)
  let edgesPart :=
    (List.finRange (elemWallEdges h').length).flatMap
      (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val)
  have hW_eq : W.encList = hdr ++ edgesPart := by
    unfold WallOfHeight.encList; rfl
  let pre_edges := pre_W ++ hdr
  have hpre_edges_len : pre_edges.length = pre_W.length + (3 + elemWallNumVerts h') := by
    simp [pre_edges, hdr]; omega
  have htotE_eq : pre_edges ++ edgesPart = pre_W ++ W.encList := by
    simp [pre_edges, hW_eq, List.append_assoc]
  have hpre_edges_w : pre_edges.length < 2 ^ w := by
    have : pre_edges.length ≤ (pre_W ++ W.encList).length := by
      rw [← htotE_eq]; simp [List.length_append]
    omega
  have hr3_5 : s₅.regs 3 = pre_W.length := by
    rw [hreg₅ 3]; simp [s₄, s₃, s₂, s₁]
  let s₆ := s₅.setReg r_pos pre_edges.length
  have hex₆ :
      Exec w (.assign r_pos (.op .add (.reg 3) (.const (3 + elemWallNumVerts h')))) s₅ s₆ 4 :=
    .assign (by
      rw [hpre_edges_len]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_5, hoff_w, hc'_w,
        show pre_W.length + (3 + elemWallNumVerts h') < 2 ^ w by omega])
  -- 7. processWallEdgesUpTo
  have hsrc₆ : s₆.arrs a_src = s.arrs a_src := by
    simp [s₆, harr₅ a_src hne_sV, s₄, s₃, s₂, s₁, hne_sP, hne_sV]
  have hbitsP₆ : s₆.arrs a_perim = bitSetList (∅ : Finset (Fin n)) := by
    simp [s₆, harr₅ a_perim hne_VP.symm, s₄, Alg91.bitSetList_empty]
  rcases processWallEdgesUpTo_exec W hW buildSucc baseSuccArr a_src a_V a_perim r_pos
      hne_sV hne_sP hne_VP hsucc_ne (by omega)
      pre_W pre_edges suf_W
      ((List.finRange (elemWallNumVerts h')).toFinset.image W.branchVert)
      hw1 hn1_w hc'_w htotW_w (by rw [htotE_eq]; exact htotW_w)
      (elemWallEdges h').length le_rfl (s := s₆)
      ⟨suf_W, by rw [hsrc₆, hsrcW]⟩
      (by rw [hsrc₆, hsrcW, ← htotE_eq])
      (by
        have h1_pos : 1 ≠ r_pos := by omega
        dsimp [s₆]; rw [State.setReg_regs_ne _ _ h1_pos, hreg₅ 1]; simp [s₄, s₃, s₂, s₁, hr1])
      (by
        have h3_pos : 3 ≠ r_pos := by omega
        dsimp [s₆]; rw [State.setReg_regs_ne _ _ h3_pos, hr3_5])
      (by simp [s₆])
      (by simp [s₆, hbitsV₅])
      hbitsP₆ with
    ⟨s₇, t₇, hex₇, ht₇, hrpos₇, hbitsV₇, hbitsP₇, hsucc₇, harr₇, hreg₇⟩
  have htake_all :
      (List.finRange (elemWallEdges h').length).take (elemWallEdges h').length =
        List.finRange (elemWallEdges h').length :=
    List.take_of_length_le (by simp)
  rw [htake_all, htotE_eq] at hrpos₇
  rw [branchVerts_union_edgeInternalFinsetUpTo_full W] at hbitsV₇
  rw [perimFinsetUpTo_full W] at hbitsP₇
  have hE_le : (elemWallEdges h').length ≤ 2 * elemWallNumVerts h :=
    (length_elemWallEdges_le h').trans (Nat.mul_le_mul_left 2 hV_mono)
  have ht₇_bound : t₇ ≤ 1 + 2 * elemWallNumVerts h * (55 + 49 * n) := by
    have : (elemWallEdges h').length * (55 + 49 * n) ≤
        2 * elemWallNumVerts h * (55 + 49 * n) :=
      Nat.mul_le_mul_right _ hE_le
    omega
  refine ⟨s₇, 2 + (5 + ((1 + n) + ((1 + n) + (t₅ + (4 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by unfold parseWallCost; omega,
    hrpos₇,
    by
      have h14_pos : 14 ≠ r_pos := by omega
      rw [hreg₇ 14 (Or.inr (by decide)) (by omega)]
      dsimp [s₆]
      rw [State.setReg_regs_ne _ _ h14_pos, hreg₅ 14]
      simp [s₄, s₃, s₂],
    IsBitSet.of_bitSetList W.vertexFinset a_V s₇ hbitsV₇,
    IsBitSet.of_bitSetList W.perimeterFinset a_perim s₇ hbitsP₇,
    fun hb k => hsucc₇ hb k k.2,
    fun a haV haP haS => by
      rw [harr₇ a haV haP haS]
      simp [s₆, harr₅ a haV, s₄, s₃, s₂, s₁, haP, haV],
    fun r hr hne14 hne_pos => by
      have hr' : r < 4 ∨ 8 < r := by omega
      rw [hreg₇ r hr' hne_pos]
      have hr3 : r ≠ 3 := by omega
      dsimp [s₆, s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ hne_pos, hreg₅ r]
      dsimp [s₄, s₃, s₂, s₁]
      rw [State.setReg_regs_ne _ _ hne14, State.setReg_regs_ne _ _ hr3]⟩

/-- Dispatch over `2 ≤ m' ≤ m` on `reg 3 = a_src[r_pos]` to call
`parseFixedWallProg m' _ false 0 a_src a_V a_perim r_pos`. -/
def unpackSubwallDispatchProg (a_src a_V a_perim : Arr) (r_pos : Reg) : ℕ → Cmd
  | 0 => .skip
  | m + 1 =>
    if hm2 : 2 ≤ m + 1 then
      .ite (.op .eq (.reg 3) (.const (m + 1)))
        (parseFixedWallProg (m + 1) hm2 false 0 a_src a_V a_perim r_pos)
        (unpackSubwallDispatchProg a_src a_V a_perim r_pos m)
    else
      .skip

/-- Unpack a subwall `W_sub : WallOfHeight h_sub G` with `2 ≤ h_sub ≤ h` from `a_src` at `r_pos`:
reads `reg 3 := a_src[r_pos]` (`h_sub`) and dispatches to `parseFixedWallProg h_sub` to populate
`reg 14 = (W_sub.seedVert h2).1`, `IsBitSet W_sub.vertexFinset a_V`,
`IsBitSet W_sub.perimeterFinset a_perim`, and advance `r_pos` past `W_sub.encList`. -/
def unpackSubwallAtProg (h : ℕ) (a_src a_V a_perim : Arr) (r_pos : Reg) : Cmd :=
  .seq (.assign 3 (.read a_src (.reg r_pos)))
    (unpackSubwallDispatchProg a_src a_V a_perim r_pos h)

theorem unpackSubwallDispatchProg_exec {w h h_sub n : ℕ} (h2_sub : 2 ≤ h_sub)
    {G : MultiDigraph n} (W_sub : WallOfHeight h_sub G) (hW_sub : W_sub.IsValid)
    (a_src a_V a_perim : ℕ) (r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : 14 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W_sub.encList).length < 2 ^ w) :
    ∀ m (_hm_le : m ≤ h) (_hh_le : h_sub ≤ m) {s : State}
      (_hsrcW : s.arrs a_src = pre_W ++ W_sub.encList ++ suf_W)
      (_hr1 : s.regs 1 = n)
      (_hr3 : s.regs 3 = h_sub)
      (_hrpos : s.regs r_pos = pre_W.length),
      ∃ s' t,
        Exec w (unpackSubwallDispatchProg a_src a_V a_perim r_pos m) s s' t ∧
        t ≤ 4 * m + parseWallCost h n ∧
        s'.regs r_pos = (pre_W ++ W_sub.encList).length ∧
        s'.regs 14 = (W_sub.seedVert h2_sub).1 ∧
        IsBitSet W_sub.vertexFinset a_V s' ∧
        IsBitSet W_sub.perimeterFinset a_perim s' ∧
        (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 14 → r ≠ r_pos → s'.regs r = s.regs r)
  | 0, _, hh_le, _, _, _, _, _ => by omega
  | m + 1, hm_le, hh_le, s, hsrcW, hr1, hr3, hrpos => by
    have hm2 : 2 ≤ m + 1 := by omega
    have hm1_w : m + 1 < 2 ^ w := by omega
    have hsub_w : h_sub < 2 ^ w := by omega
    have h0_w : 0 < 2 ^ w := by omega
    by_cases hh_eq : h_sub = m + 1
    · -- h_sub = m + 1
      subst hh_eq
      have hcond :
          (Expr.op .eq (.reg 3) (.const (m + 1))).eval w s = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hsub_w, hw1]
      rcases parseFixedWallProg_exec hm2 hm_le W_sub hW_sub false 0 a_src a_V a_perim r_pos
          hne_sV hne_sP hne_VP
          (fun h => Bool.noConfusion h)
          hr_pos pre_W suf_W hw1 hn1_w hc_w htotW_w hsrcW hr1 hrpos with
        ⟨s', t', hex', ht', hrpos', hr14', hV', hP', _, harr', hreg'⟩
      refine ⟨s', 3 + t',
        by simpa [unpackSubwallDispatchProg, hm2] using Exec.ite_true hcond (by omega) hex',
        by omega,
        hrpos', hr14', hV', hP',
        fun a haV haP => harr' a haV haP (fun h => Bool.noConfusion h),
        hreg'⟩
    · -- h_sub < m + 1, so h_sub ≤ m and reg 3 == m + 1 evaluates to 0
      have hcond :
          (Expr.op .eq (.reg 3) (.const (m + 1))).eval w s = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hsub_w, hm1_w, hh_eq, h0_w]
      rcases unpackSubwallDispatchProg_exec h2_sub W_sub hW_sub a_src a_V a_perim r_pos
          hne_sV hne_sP hne_VP hr_pos pre_W suf_W hw1 hn1_w hh_w hc_w htotW_w
          m (by omega) (by omega) hsrcW hr1 hr3 hrpos with
        ⟨s', t', hex', ht', hrpos', hr14', hV', hP', harr', hreg'⟩
      refine ⟨s', 3 + t',
        by simpa [unpackSubwallDispatchProg, hm2] using Exec.ite_false hcond hex',
        by rw [Nat.succ_mul]; omega,
        hrpos', hr14', hV', hP', harr', hreg'⟩

theorem unpackSubwallAtProg_exec {w h h_sub n : ℕ} (h2_sub : 2 ≤ h_sub) (hle : h_sub ≤ h)
    {G : MultiDigraph n} (W_sub : WallOfHeight h_sub G) (hW_sub : W_sub.IsValid)
    (a_src a_V a_perim : ℕ) (r_pos : ℕ)
    (hne_sV : a_src ≠ a_V) (hne_sP : a_src ≠ a_perim) (hne_VP : a_V ≠ a_perim)
    (hr_pos : 14 < r_pos)
    (pre_W suf_W : List ℕ)
    (hw1 : 1 < 2 ^ w) (hn1_w : n + 1 < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htotW_w : (pre_W ++ W_sub.encList).length < 2 ^ w)
    {s : State}
    (hsrcW : s.arrs a_src = pre_W ++ W_sub.encList ++ suf_W)
    (hr1 : s.regs 1 = n)
    (hrpos : s.regs r_pos = pre_W.length) :
    ∃ s' t,
      Exec w (unpackSubwallAtProg h a_src a_V a_perim r_pos) s s' t ∧
      t ≤ 3 + 4 * h + parseWallCost h n ∧
      s'.regs r_pos = (pre_W ++ W_sub.encList).length ∧
      s'.regs 14 = (W_sub.seedVert h2_sub).1 ∧
      IsBitSet W_sub.vertexFinset a_V s' ∧
      IsBitSet W_sub.perimeterFinset a_perim s' ∧
      (∀ a : ℕ, a ≠ a_V → a ≠ a_perim → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, (r < 3 ∨ 8 < r) → r ≠ 14 → r ≠ r_pos → s'.regs r = s.regs r) := by
  have hoff_w : pre_W.length < 2 ^ w := by simp [List.length_append] at htotW_w; omega
  have hsub_w : h_sub < 2 ^ w := by omega
  have hin_len : pre_W.length < (s.arrs a_src).length := by
    rw [hsrcW]; simp [List.length_append, W_sub.length_encList]
  have hread_h : (s.arrs a_src)[pre_W.length]'hin_len = h_sub := by
    let rest := W_sub.encList ++ suf_W
    have hsplit : s.arrs a_src = pre_W ++ rest := by rw [hsrcW, List.append_assoc]
    have hlen2 : pre_W.length < (pre_W ++ rest).length := by
      simp [rest, W_sub.length_encList]
    apply Alg91.getElem_of_eq hsplit rfl (h₂ := hlen2)
    rw [List.getElem_append_right (le_refl pre_W.length)]
    simp [rest, WallOfHeight.encList]
  let s₁ := s.setReg 3 h_sub
  have hex₁ : Exec w (.assign 3 (.read a_src (.reg r_pos))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hrpos, hoff_w, hin_len, hread_h, hsub_w])
  rcases unpackSubwallDispatchProg_exec h2_sub W_sub hW_sub a_src a_V a_perim r_pos
      hne_sV hne_sP hne_VP hr_pos pre_W suf_W hw1 hn1_w hh_w hc_w htotW_w
      h le_rfl hle (s := s₁)
      hsrcW
      (by simp [s₁, hr1])
      (by simp [s₁])
      (by
        have hpos3 : r_pos ≠ 3 := by omega
        dsimp [s₁]; rw [State.setReg_regs_ne _ _ hpos3, hrpos]) with
    ⟨s₂, t₂, hex₂, ht₂, hrpos₂, hr14₂, hV₂, hP₂, harr₂, hreg₂⟩
  refine ⟨s₂, 3 + t₂, .seq hex₁ hex₂, by omega,
    hrpos₂, hr14₂, hV₂, hP₂,
    fun a haV haP => harr₂ a haV haP,
    fun r hr hne14 hne_pos => by
      rw [hreg₂ r hr hne14 hne_pos]
      have hr3 : r ≠ 3 := by omega
      dsimp [s₁]
      rw [State.setReg_regs_ne _ _ hr3]⟩

end GraphMinor.Compute

end
