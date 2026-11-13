module

public import GraphMinor.Compute.TwoPathsSide

/-!
# The subinstances of a split

`childProg i` replaces the instance in memory by subinstance `i` of line 10 of Algorithm 5.1:

1. `sideProg i` writes the lists of `H' = H + F` and the bit set of side `i`
   (`TwoPathsSide.lean`);
2. `restrictGraphProg` (`Restrict.lean`) writes in `aStart`, `aEnd`, `aEnt` the lists of `H'`
   restricted to side `i`, which is the graph `subGraph H' P' A i` (`restrictGraph_sideFin`);
3. `cycProg i` writes in `aCyc` the cycle `subCycle a b A B m i`: `a A b m⁻¹` for side `1`,
   `b B a m` for side `2`, where `P' = a m b`.

The cycle is built in a scratch array from pieces of `aCyc` and `aNewPath` by the loop `appProg`,
which appends `src[E]` to `dst` for a range of values of a counter, and is then copied back.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### Appending pieces of an array -/

/-- For `lo ≤ i < hi`, write `src[E]` at index `rC` of `dst` and add one to `rC`; the expression
`E` may read the counter `rI`. -/
def appProg (rI rC : Reg) (lo hi : Expr) (dst src : Arr) (E : Expr) : Cmd :=
  .seq (.assign rI lo)
    (forUp rI hi (.seq (.write dst (.reg rC) (.read src E))
      (.assign rC (.op .add (.reg rC) (.const 1)))))

theorem set_append_drop (D X R : List ℕ) (v : ℕ) (h : X.length < R.length) :
    (D ++ X ++ R.drop X.length).set (D.length + X.length) v =
      D ++ (X ++ [v]) ++ R.drop (X.length + 1) := by
  rw [List.append_assoc, List.set_append_right _ _ (by omega), Nat.add_sub_cancel_left,
    List.set_append_right _ _ (le_refl _), Nat.sub_self, List.drop_eq_getElem_cons h,
    List.set_cons_zero]
  simp

/-- **Appending.** `appProg` appends `L[g i]` to the content `D` of `dst`, for `vlo ≤ i < vhi`,
over the entries of `R` that follow `D`. -/
theorem appProg_exec {w : ℕ} (rI rC : Reg) (lo hi : Expr) (dst src : Arr) (E : Expr)
    (hds : dst ≠ src) (hIC : rI ≠ rC) (L D R : List ℕ) (g : ℕ → ℕ) (vlo vhi : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hle : vlo ≤ vhi) (hR : vhi - vlo ≤ R.length)
    (hDR : D.length + R.length < 2 ^ w) (hhiw : vhi < 2 ^ w)
    (hlo : lo.eval w s = some vlo)
    (hhi : ∀ st, Keeps [rI, rC] [dst] s st → hi.eval w st = some vhi)
    (hE : ∀ st i, Keeps [rI, rC] [dst] s st → st.regs rI = i → vlo ≤ i → i < vhi →
      E.eval w st = some (g i))
    (hg : ∀ i, vlo ≤ i → i < vhi → g i < L.length) (hL : ∀ x ∈ L, x < 2 ^ w)
    (hsrc : s.arrs src = L) (hdst : s.arrs dst = D ++ R) (hC : s.regs rC = D.length) :
    ∃ s' t, Exec w (appProg rI rC lo hi dst src E) s s' t ∧
      t ≤ lo.cost + hi.cost + 3 + (vhi - vlo) * (hi.cost + E.cost + 13) ∧
      Keeps [rI, rC] [dst] s s' ∧ s'.regs rC = D.length + (vhi - vlo) ∧
      s'.arrs dst = D ++ (List.range' vlo (vhi - vlo)).map (fun i => L.getD (g i) 0) ++
        R.drop (vhi - vlo) := by
  set f : ℕ → ℕ := fun i => L.getD (g i) 0 with hf
  set s₁ := s.setReg rI vlo with hs₁
  have hex₁ : Exec w (.assign rI lo) s s₁ (lo.cost + 1) := .assign hlo
  let I : ℕ → State → Prop := fun i st => Keeps [rI, rC] [dst] s st ∧ st.regs rI = i ∧
    st.regs rC = D.length + (i - vlo) ∧
    st.arrs dst = D ++ (List.range' vlo (i - vlo)).map f ++ R.drop (i - vlo) ∧ vlo ≤ i
  have hI0 : I vlo s₁ := ⟨(Keeps.refl _ _ s).setReg (by simp) _, by simp [s₁],
    by simp [s₁, State.setReg_regs_ne _ _ hIC.symm, hC], by simp [s₁, hdst], le_rfl⟩
  have hloop := forUp_pot I (fun _ => 0) vhi (E.cost + 7) (r_i := rI) (hi := hi)
    (body := .seq (.write dst (.reg rC) (.read src E))
      (.assign rC (.op .add (.reg rC) (.const 1)))) hw hhiw
    (fun i _ st hst => ⟨hst.2.1, hhi st hst.1⟩)
    (fun i hi' st hst => by
      obtain ⟨hks, hri, hrc, hd, hvi⟩ := hst
      have hsrc' : st.arrs src = L := by rw [hks.2 src (by simp [Ne.symm hds]), hsrc]
      have hgi := hg i hvi hi'
      have hv : f i = L[g i] := by simp [f, hgi]
      have hX : ((List.range' vlo (i - vlo)).map f).length = i - vlo := by simp
      have hlt : i - vlo < R.length := by omega
      set st₁ := st.writeArr dst (D.length + (i - vlo)) (f i) with hst₁
      have hex₁ : Exec w (.write dst (.reg rC) (.read src E)) st st₁ (1 + (E.cost + 1) + 1) :=
        .write (reg_eval hrc (by omega))
          (by rw [read_eval (hE st i hks hri hvi hi') (by rw [hsrc']; exact hgi)
            (by simp only [hsrc']; exact hL _ (List.getElem_mem _)), hv]; simp only [hsrc'])
          (by rw [hd]; simp; omega)
      set st₂ := st₁.setReg rC (D.length + (i - vlo) + 1) with hst₂
      have hex₂ : Exec w (.assign rC (.op .add (.reg rC) (.const 1))) st₁ st₂ (1 + 1 + 1 + 1) :=
        .assign (op_eval (a := D.length + (i - vlo)) (b := 1)
          (reg_eval (by simp [st₁, hrc]) (by omega)) (by simp [checkWord, hw])
          (by simp only [BinOp.eval, BinOp.raw, checkWord]; rw [if_pos (by omega)]))
      refine ⟨st₂, _, .seq hex₁ hex₂, ?_, ⟨?_, by simp, ?_, ?_, by omega⟩, ?_⟩
      · omega
      · exact ((hks.writeArr (by simp) _ _).setReg (by simp) _).setReg (by simp) _
      · rw [State.setReg_regs_ne _ _ hIC.symm]; simp only [st₂, State.setReg]; simp; omega
      · simp only [State.setReg_arrs, st₂, st₁, State.writeArr, State.setArr_arrs, ite_true, hd]
        have key := set_append_drop D ((List.range' vlo (i - vlo)).map f) R (f i)
          (by rw [hX]; exact hlt)
        rw [hX] at key
        rw [key, show i + 1 - vlo = (i - vlo) + 1 by omega, List.range'_concat, List.map_append]
        simp [show vlo + (i - vlo) = i by omega]
      · rw [State.setReg_regs_ne _ _ hIC]; simp [st₁, hri])
    vlo hle s₁ hI0
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hc₃, hd₃, -⟩ := hloop
  refine ⟨s₃, _, .seq hex₁ hex₃, ?_, hk₃, hc₃, hd₃⟩
  simp only [Nat.add_zero] at ht₃
  have : (vhi - vlo) * (hi.cost + 6 + (E.cost + 7)) = (vhi - vlo) * (hi.cost + E.cost + 13) := by
    congr 1; omega
  omega

/-! ### The cycle of a subinstance -/

/-- The write cursor of `appProg`. -/
abbrev rAp : Reg := 114

theorem map_range'_getD (L : List ℕ) (lo k : ℕ) (h : lo + k ≤ L.length) :
    (List.range' lo k).map (fun i => L.getD i 0) = (L.drop lo).take k := by
  apply List.ext_getElem (by simp <;> omega)
  intro j h₁ h₂
  simp at h₁
  simp [List.getElem_range', show lo + j < L.length by omega]

theorem map_range'_rev (a b : ℕ) (m : List ℕ) :
    (List.range' 1 m.length).map (fun i => (a :: m ++ [b]).getD ((m.length + 2 - 1) - i) 0) =
      m.reverse := by
  apply List.ext_getElem (by simp)
  intro j h₁ h₂
  simp at h₁
  simp only [List.getElem_map, List.getElem_range', List.getElem_reverse]
  rw [show m.length + 2 - 1 - (1 + 1 * j) = (m.length - 1 - j) + 1 by omega, List.cons_append,
    List.getD_cons_succ]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show m.length - 1 - j < m.length by
    omega), List.getElem?_eq_getElem (show m.length - 1 - j < m.length by omega)]

/-- Write `a A b m⁻¹` (side `1`) in `aCyc`. -/
def cycOne : Cmd :=
  .seq (.alloc aTmp (.op .add (.reg rLenA) (.len aNewPath)))
    (.seq (.assign rAp (.const 0))
      (.seq (appProg rI3 rAp (.const 0) (.op .add (.reg rLenA) (.const 2)) aTmp aCyc (.reg rI3))
        (.seq (appProg rI3 rAp (.const 1) (.op .sub (.len aNewPath) (.const 1)) aTmp aNewPath
            (.op .sub (.op .sub (.len aNewPath) (.const 1)) (.reg rI3)))
          (mapProg rI3 (.len aTmp) aCyc aTmp (.reg rI3)))))

/-- Write `b B a m` (side `2`) in `aCyc`. -/
def cycTwo : Cmd :=
  .seq (.alloc aTmp (.op .sub (.op .add (.op .sub (.len aCyc) (.reg rLenA)) (.len aNewPath))
      (.const 2)))
    (.seq (.assign rAp (.const 0))
      (.seq (appProg rI3 rAp (.op .add (.reg rLenA) (.const 1)) (.len aCyc) aTmp aCyc (.reg rI3))
        (.seq (appProg rI3 rAp (.const 0) (.const 1) aTmp aCyc (.reg rI3))
          (.seq (appProg rI3 rAp (.const 1) (.op .sub (.len aNewPath) (.const 1)) aTmp aNewPath
              (.reg rI3))
            (mapProg rI3 (.len aTmp) aCyc aTmp (.reg rI3))))))

/-- Write the cycle of subinstance `i` in `aCyc`. -/
def cycProg (i : ℕ) : Cmd := if i = 1 then cycOne else cycTwo

theorem vals_lt {w : ℕ} {L : List (Fin n)} (hn : n < 2 ^ w) : ∀ x ∈ L.map Fin.val, x < 2 ^ w :=
  fun x hx => by obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx; have := z.2; omega

theorem const_eval' {w : ℕ} {s : State} {c : ℕ} (h : c < 2 ^ w) :
    (Expr.const c).eval w s = some c := by simp [Expr.eval, checkWord, h]

theorem len_eval {w : ℕ} {s : State} {x : Arr} {L : List ℕ} (h : s.arrs x = L)
    (hL : L.length < 2 ^ w) : (Expr.len x).eval w s = some L.length := by
  simp [Expr.eval, checkWord, h, hL]

theorem add_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (h : a + b < 2 ^ w) : (Expr.op .add A B).eval w s = some (a + b) :=
  op_eval hA hB (by simp [BinOp.eval, BinOp.raw, checkWord, h])

theorem sub_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) : (Expr.op .sub A B).eval w s = some (a - b) :=
  op_eval hA hB (by
    have := Expr.eval_lt hA
    simp [BinOp.eval, BinOp.raw, checkWord, show a - b < 2 ^ w by omega])

/-- **The cycle of side `1`.** -/
theorem cycOne_exec {w : ℕ} {a b : Fin n} {A B m : List (Fin n)} {s : State}
    (hn : 4 * n + 4 < 2 ^ w) (hC : A.length + B.length + 2 ≤ n) (hm : m.length + 2 ≤ n)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aNewPath = (a :: m ++ [b]).map Fin.val) (hlenA : s.regs rLenA = A.length) :
    ∃ s' t, Exec w cycOne s s' t ∧ t ≤ 100 + 70 * n ∧ Keeps [rI3, rAp] [aTmp, aCyc] s s' ∧
      s'.arrs aCyc = (subCycle a b A B m 1).map Fin.val := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hLpl : ((a :: m ++ [b]).map Fin.val).length = m.length + 2 := by simp
  have hLcl : ((a :: A ++ b :: B).map Fin.val).length = A.length + B.length + 2 := by simp; omega
  have hLcw := vals_lt (L := a :: A ++ b :: B) hnw
  have hLpw := vals_lt (L := a :: m ++ [b]) hnw
  have hex₁ : Exec w (.alloc aTmp (.op .add (.reg rLenA) (.len aNewPath))) s
      (s.setArr aTmp (List.replicate (A.length + (m.length + 2)) 0))
      (3 + (A.length + (m.length + 2))) :=
    .alloc (add_eval (b := m.length + 2) (reg_eval hlenA (by omega))
      (by rw [← hLpl]; exact len_eval hpath (by omega)) (by omega))
  set s₁ := s.setArr aTmp (List.replicate (A.length + (m.length + 2)) 0) with hs₁
  set s₂ := s₁.setReg rAp 0 with hs₂
  have hex₂ : Exec w (.assign rAp (.const 0)) s₁ s₂ (1 + 1) := .assign (const_eval' (by omega))
  have hcyc₂ : s₂.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by simp [s₂, s₁, hcyc]
  have hpath₂ : s₂.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by simp [s₂, s₁, hpath]
  have hrep : (List.replicate (A.length + (m.length + 2)) 0).length = A.length + (m.length + 2) :=
    List.length_replicate
  -- The piece `a A b`.
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hc₃, hd₃⟩ := appProg_exec rI3 rAp (.const 0)
    (.op .add (.reg rLenA) (.const 2)) aTmp aCyc (.reg rI3) (by decide) (by decide)
    ((a :: A ++ b :: B).map Fin.val) [] (List.replicate (A.length + (m.length + 2)) 0) id 0
    (A.length + 2) s₂ hw1 (Nat.zero_le _) (by rw [hrep]; omega) (by rw [hrep]; simp; omega)
    (by omega) (const_eval' (by omega))
    (fun st hst => add_eval (reg_eval (by rw [hst.1 rLenA (by decide)]; simp [s₂, s₁, hlenA])
      (by omega)) (const_eval' (by omega)) (by omega))
    (fun st i hst hri _ hi => reg_eval hri (show i < 2 ^ w by omega))
    (fun i _ hi => show i < _ by rw [hLcl]; omega)
    hLcw hcyc₂ (by simp [s₂, s₁]) (by simp [s₂])
  rw [Nat.sub_zero, List.length_nil, Nat.zero_add] at hc₃
  rw [Nat.sub_zero, List.nil_append] at hd₃
  rw [show (fun i => ((a :: A ++ b :: B).map Fin.val).getD (id i) 0) =
    (fun i => ((a :: A ++ b :: B).map Fin.val).getD i 0) from rfl,
    map_range'_getD _ _ _ (by omega), List.drop_zero] at hd₃
  have hpath₃ : s₃.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by
    rw [hk₃.2 _ (by decide)]; exact hpath₂
  have htk : (((a :: A ++ b :: B).map Fin.val).take (A.length + 2)).length = A.length + 2 := by
    rw [List.length_take, hLcl]; omega
  have hdr : ((List.replicate (A.length + (m.length + 2)) 0).drop (A.length + 2)) =
      List.replicate m.length 0 := by
    rw [List.drop_replicate]; congr 1; omega
  rw [hdr] at hd₃
  have hlenP : ∀ st, Keeps [rI3, rAp] [aTmp] s₃ st →
      (Expr.op .sub (.len aNewPath) (.const 1)).eval w st = some (m.length + 1) := fun st hst => by
    have hP : st.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by
      rw [hst.2 aNewPath (by decide)]; exact hpath₃
    have hl : (Expr.len aNewPath).eval w st = some (m.length + 2) := by
      rw [← hLpl]; exact len_eval hP (by rw [hLpl]; omega)
    rw [sub_eval hl (const_eval' (c := 1) (by omega))]; rfl
  -- The piece `m⁻¹`.
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, -, hd₄⟩ := appProg_exec rI3 rAp (.const 1)
    (.op .sub (.len aNewPath) (.const 1)) aTmp aNewPath
    (.op .sub (.op .sub (.len aNewPath) (.const 1)) (.reg rI3)) (by decide) (by decide)
    ((a :: m ++ [b]).map Fin.val)
    (((a :: A ++ b :: B).map Fin.val).take (A.length + 2)) (List.replicate m.length 0)
    (fun i => (m.length + 2 - 1) - i) 1 (m.length + 1) s₃ hw1 (by omega) (by simp)
    (by rw [htk]; simp; omega) (by omega) (const_eval' (by omega)) hlenP
    (fun st i hst hri _ hi => by
      have := sub_eval (hlenP st hst) (reg_eval hri (show i < 2 ^ w by omega))
      rw [this]; congr 1)
    (fun i h1 hi => by rw [hLpl]; omega) hLpw hpath₃ hd₃ (by rw [hc₃, htk])
  have hrev : (List.range' 1 (m.length + 1 - 1)).map
      (fun i => ((a :: m ++ [b]).map Fin.val).getD ((m.length + 2 - 1) - i) 0) =
        (m.map Fin.val).reverse := by
    rw [Nat.add_sub_cancel, show m.length = (m.map Fin.val).length by simp, List.map_append,
      List.map_cons, List.map_cons, List.map_nil]
    exact map_range'_rev _ _ _
  rw [hrev, show m.length + 1 - 1 = m.length by omega, List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil] at hd₄
  have htmp₄ : s₄.arrs aTmp = (subCycle a b A B m 1).map Fin.val := by
    rw [hd₄, show A.length + 2 = (a :: A ++ [b]).length by simp,
      show (a :: A ++ b :: B) = (a :: A ++ [b]) ++ B by simp, List.map_append,
      List.take_left' (by simp)]
    simp [subCycle, List.map_reverse]
  -- Copy back.
  have hlt₄ : ((subCycle a b A B m 1).map Fin.val).length = A.length + (m.length + 2) := by
    simp [subCycle]; omega
  have hlenT : ∀ st, Keeps [rI3] [aCyc] s₄ st →
      (Expr.len aTmp).eval w st = some (A.length + (m.length + 2)) := fun st hst => by
    rw [← hlt₄]; exact len_eval (by rw [hst.2 aTmp (by decide)]; exact htmp₄) (by rw [hlt₄]; omega)
  have hgT : ∀ i < A.length + (m.length + 2), id i < ((subCycle a b A B m 1).map Fin.val).length :=
    fun i hi => by rw [hlt₄]; exact hi
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, hd₅⟩ := mapProg_exec rI3 (.len aTmp) aCyc aTmp (.reg rI3)
    (by decide) (A.length + (m.length + 2)) id ((subCycle a b A B m 1).map Fin.val) s₄ hw1
    (by omega) hlenT (fun st i hst hri hi => reg_eval hri (show i < 2 ^ w by omega))
    hgT (vals_lt hnw) htmp₄
  rw [← hlt₄, show (fun i => ((subCycle a b A B m 1).map Fin.val).getD (id i) 0) =
    (fun i => ((subCycle a b A B m 1).map Fin.val).getD i 0) from rfl, map_getD_self] at hd₅
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_,
    (((((Keeps.refl _ _ s).setArr (by decide) _).setReg (by decide) _).trans hk₃ (by decide)
      (by decide)).trans hk₄ (by decide) (by decide)).trans hk₅ (by decide) (by decide), hd₅⟩
  simp only [Expr.cost, Nat.sub_zero, Nat.add_sub_cancel] at ht₃ ht₄ ht₅
  have h3 : t₃ ≤ 41 + 17 * A.length := by
    have := ht₃; ring_nf at this ⊢; omega
  have h4 : t₄ ≤ 7 + 21 * m.length := by
    have := ht₄; ring_nf at this ⊢; omega
  have h5 : t₅ ≤ 6 + 12 * (A.length + (m.length + 2)) := by
    have := ht₅; ring_nf at this ⊢; omega
  omega

/-- **The cycle of side `2`.** -/
theorem cycTwo_exec {w : ℕ} {a b : Fin n} {A B m : List (Fin n)} {s : State}
    (hn : 4 * n + 4 < 2 ^ w) (hC : A.length + B.length + 2 ≤ n) (hm : m.length + 2 ≤ n)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aNewPath = (a :: m ++ [b]).map Fin.val) (hlenA : s.regs rLenA = A.length) :
    ∃ s' t, Exec w cycTwo s s' t ∧ t ≤ 100 + 70 * n ∧ Keeps [rI3, rAp] [aTmp, aCyc] s s' ∧
      s'.arrs aCyc = (subCycle a b A B m 2).map Fin.val := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hLpl : ((a :: m ++ [b]).map Fin.val).length = m.length + 2 := by simp
  have hLcl : ((a :: A ++ b :: B).map Fin.val).length = A.length + B.length + 2 := by simp; omega
  have hLcw := vals_lt (L := a :: A ++ b :: B) hnw
  have hLpw := vals_lt (L := a :: m ++ [b]) hnw
  have hlc : (Expr.len aCyc).eval w s = some (A.length + B.length + 2) := by
    rw [← hLcl]; exact len_eval hcyc (by rw [hLcl]; omega)
  have hlp : (Expr.len aNewPath).eval w s = some (m.length + 2) := by
    rw [← hLpl]; exact len_eval hpath (by rw [hLpl]; omega)
  have hex₁ : Exec w (.alloc aTmp (.op .sub (.op .add (.op .sub (.len aCyc) (.reg rLenA))
      (.len aNewPath)) (.const 2))) s
      (s.setArr aTmp (List.replicate (B.length + (m.length + 2)) 0))
      (7 + (B.length + (m.length + 2))) := by
    have h := sub_eval (add_eval (sub_eval hlc (reg_eval hlenA (by omega))) hlp (by omega))
      (const_eval' (c := 2) (by omega))
    rw [show A.length + B.length + 2 - A.length + (m.length + 2) - 2 = B.length + (m.length + 2)
      by omega] at h
    exact .alloc h
  set s₁ := s.setArr aTmp (List.replicate (B.length + (m.length + 2)) 0) with hs₁
  set s₂ := s₁.setReg rAp 0 with hs₂
  have hex₂ : Exec w (.assign rAp (.const 0)) s₁ s₂ (1 + 1) := .assign (const_eval' (by omega))
  have hcyc₂ : s₂.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by simp [s₂, s₁, hcyc]
  have hpath₂ : s₂.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by simp [s₂, s₁, hpath]
  have hrep : (List.replicate (B.length + (m.length + 2)) 0).length = B.length + (m.length + 2) :=
    List.length_replicate
  -- The piece `b B`.
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hc₃, hd₃⟩ := appProg_exec rI3 rAp
    (.op .add (.reg rLenA) (.const 1)) (.len aCyc) aTmp aCyc (.reg rI3) (by decide) (by decide)
    ((a :: A ++ b :: B).map Fin.val) [] (List.replicate (B.length + (m.length + 2)) 0) id
    (A.length + 1) (A.length + B.length + 2) s₂ hw1 (by omega) (by rw [hrep]; omega)
    (by rw [hrep]; simp; omega) (by omega)
    (add_eval (reg_eval (by simp [s₂, s₁, hlenA]) (by omega)) (const_eval' (c := 1) (by omega))
      (by omega))
    (fun st hst => by
      rw [← hLcl]; exact len_eval (by rw [hst.2 aCyc (by decide)]; exact hcyc₂)
        (by rw [hLcl]; omega))
    (fun st i hst hri _ hi => reg_eval hri (show i < 2 ^ w by omega))
    (fun i _ hi => show i < _ by rw [hLcl]; omega)
    hLcw hcyc₂ (by simp [s₂, s₁]) (by simp [s₂])
  rw [List.length_nil, Nat.zero_add, show A.length + B.length + 2 - (A.length + 1) = B.length + 1
    by omega] at hc₃
  rw [List.nil_append, show A.length + B.length + 2 - (A.length + 1) = B.length + 1 by omega,
    show (fun i => ((a :: A ++ b :: B).map Fin.val).getD (id i) 0) =
      (fun i => ((a :: A ++ b :: B).map Fin.val).getD i 0) from rfl,
    map_range'_getD _ _ _ (by omega)] at hd₃
  have hbB : (((a :: A ++ b :: B).map Fin.val).drop (A.length + 1)).take (B.length + 1) =
      (b :: B).map Fin.val := by
    rw [show (a :: A ++ b :: B) = (a :: A) ++ (b :: B) by simp, List.map_append,
      List.drop_append_of_le_length (by simp), List.drop_of_length_le (by simp), List.nil_append,
      List.take_of_length_le (by simp)]
  have hdr : (List.replicate (B.length + (m.length + 2)) 0).drop (B.length + 1) =
      List.replicate (m.length + 1) 0 := by
    rw [List.drop_replicate]; congr 1; omega
  rw [hbB, hdr] at hd₃
  have hcyc₃ : s₃.arrs aCyc = (a :: A ++ b :: B).map Fin.val := by
    rw [hk₃.2 _ (by decide)]; exact hcyc₂
  have hpath₃ : s₃.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by
    rw [hk₃.2 _ (by decide)]; exact hpath₂
  -- The piece `a`.
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hc₄, hd₄⟩ := appProg_exec rI3 rAp (.const 0) (.const 1) aTmp
    aCyc (.reg rI3) (by decide) (by decide) ((a :: A ++ b :: B).map Fin.val)
    ((b :: B).map Fin.val) (List.replicate (m.length + 1) 0) id 0 1 s₃ hw1 (by omega)
    (by simp) (by simp; omega) (by omega) (const_eval' (by omega))
    (fun st hst => const_eval' (by omega))
    (fun st i hst hri _ hi => reg_eval hri (show i < 2 ^ w by omega))
    (fun i _ hi => show i < _ by rw [hLcl]; omega)
    hLcw hcyc₃ hd₃ (by rw [hc₃]; simp)
  rw [show (fun i => ((a :: A ++ b :: B).map Fin.val).getD (id i) 0) =
      (fun i => ((a :: A ++ b :: B).map Fin.val).getD i 0) from rfl,
    map_range'_getD _ _ _ (by omega), Nat.sub_zero, List.drop_zero, List.drop_replicate,
    show m.length + 1 - 1 = m.length by omega] at hd₄
  rw [Nat.sub_zero] at hc₄
  have ha1 : ((a :: A ++ b :: B).map Fin.val).take 1 = [a.1] := by simp
  rw [ha1] at hd₄
  have hpath₄ : s₄.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by
    rw [hk₄.2 _ (by decide)]; exact hpath₃
  have hlenP : ∀ st, Keeps [rI3, rAp] [aTmp] s₄ st →
      (Expr.op .sub (.len aNewPath) (.const 1)).eval w st = some (m.length + 1) := fun st hst => by
    have hP : st.arrs aNewPath = (a :: m ++ [b]).map Fin.val := by
      rw [hst.2 aNewPath (by decide)]; exact hpath₄
    have hl : (Expr.len aNewPath).eval w st = some (m.length + 2) := by
      rw [← hLpl]; exact len_eval hP (by rw [hLpl]; omega)
    rw [sub_eval hl (const_eval' (c := 1) (by omega))]; rfl
  -- The piece `m`.
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, -, hd₅⟩ := appProg_exec rI3 rAp (.const 1)
    (.op .sub (.len aNewPath) (.const 1)) aTmp aNewPath (.reg rI3) (by decide) (by decide)
    ((a :: m ++ [b]).map Fin.val) ((b :: B).map Fin.val ++ [a.1]) (List.replicate m.length 0)
    id 1 (m.length + 1) s₄ hw1 (by omega) (by simp) (by simp; omega) (by omega)
    (const_eval' (by omega)) hlenP
    (fun st i hst hri _ hi => reg_eval hri (show i < 2 ^ w by omega))
    (fun i _ hi => show i < _ by rw [hLpl]; omega)
    hLpw hpath₄ hd₄ (by rw [hc₄]; simp)
  rw [show (fun i => ((a :: m ++ [b]).map Fin.val).getD (id i) 0) =
      (fun i => ((a :: m ++ [b]).map Fin.val).getD i 0) from rfl,
    map_range'_getD _ _ _ (by omega), show m.length + 1 - 1 = m.length by omega,
    List.drop_replicate, Nat.sub_self, List.replicate_zero, List.append_nil] at hd₅
  have htmp₅ : s₅.arrs aTmp = (subCycle a b A B m 2).map Fin.val := by
    rw [hd₅]
    have : (((a :: m ++ [b]).map Fin.val).drop 1).take m.length = m.map Fin.val := by
      rw [List.cons_append, List.map_cons, List.drop_one, List.tail_cons, List.map_append]
      exact List.take_left' (by simp)
    rw [this]
    simp [subCycle]
  -- Copy back.
  have hlt₅ : ((subCycle a b A B m 2).map Fin.val).length = B.length + (m.length + 2) := by
    simp [subCycle]; omega
  have hlenT : ∀ st, Keeps [rI3] [aCyc] s₅ st →
      (Expr.len aTmp).eval w st = some (B.length + (m.length + 2)) := fun st hst => by
    rw [← hlt₅]; exact len_eval (by rw [hst.2 aTmp (by decide)]; exact htmp₅) (by rw [hlt₅]; omega)
  have hgT : ∀ i < B.length + (m.length + 2), id i < ((subCycle a b A B m 2).map Fin.val).length :=
    fun i hi => by rw [hlt₅]; exact hi
  obtain ⟨s₆, t₆, hex₆, ht₆, hk₆, hd₆⟩ := mapProg_exec rI3 (.len aTmp) aCyc aTmp (.reg rI3)
    (by decide) (B.length + (m.length + 2)) id ((subCycle a b A B m 2).map Fin.val) s₅ hw1
    (by omega) hlenT (fun st i hst hri hi => reg_eval hri (show i < 2 ^ w by omega))
    hgT (vals_lt hnw) htmp₅
  rw [← hlt₅, show (fun i => ((subCycle a b A B m 2).map Fin.val).getD (id i) 0) =
    (fun i => ((subCycle a b A B m 2).map Fin.val).getD i 0) from rfl, map_getD_self] at hd₆
  refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_,
    ((((((Keeps.refl _ _ s).setArr (by decide) _).setReg (by decide) _).trans hk₃ (by decide)
      (by decide)).trans hk₄ (by decide) (by decide)).trans hk₅ (by decide) (by decide)).trans
      hk₆ (by decide) (by decide), hd₆⟩
  simp only [Expr.cost, Nat.sub_zero, Nat.add_sub_cancel] at ht₃ ht₄ ht₅ ht₆
  rw [show A.length + B.length + 2 - (A.length + 1) = B.length + 1 by omega] at ht₃
  have h3 : t₃ ≤ 7 + 15 * (B.length + 1) := by
    have := ht₃; ring_nf at this ⊢; omega
  have h5 : t₅ ≤ 7 + 17 * m.length := by
    have := ht₅; ring_nf at this ⊢; omega
  have h6 : t₆ ≤ 6 + 12 * (B.length + (m.length + 2)) := by
    have := ht₆; ring_nf at this ⊢; omega
  omega

/-- **The cycle of a subinstance.** -/
theorem cycProg_exec {w : ℕ} (i : ℕ) {a b : Fin n} {A B m : List (Fin n)} {s : State}
    (hn : 4 * n + 4 < 2 ^ w) (hC : A.length + B.length + 2 ≤ n) (hm : m.length + 2 ≤ n)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aNewPath = (a :: m ++ [b]).map Fin.val) (hlenA : s.regs rLenA = A.length) :
    ∃ s' t, Exec w (cycProg i) s s' t ∧ t ≤ 100 + 70 * n ∧ Keeps [rI3, rAp] [aTmp, aCyc] s s' ∧
      s'.arrs aCyc = (subCycle a b A B m i).map Fin.val := by
  unfold cycProg
  by_cases hi : i = 1
  · subst hi; simpa using cycOne_exec hn hC hm hcyc hpath hlenA
  · rw [if_neg hi]
    obtain ⟨s', t, h1, h2, h3, h4⟩ := cycTwo_exec hn hC hm hcyc hpath hlenA
    refine ⟨s', t, h1, h2, h3, ?_⟩
    rw [h4]
    rcases i with _ | _ | i
    · rfl
    · exact absurd rfl hi
    · rfl

/-! ### The subinstance -/

/-- Register holding the capacity of the restricted lists. -/
abbrev rCap : Reg := 106

/-- **Line 10 of Algorithm 5.1.** Replace the instance in memory by subinstance `i`: its graph in
`aStart`, `aEnd`, `aEnt` and its cycle in `aCyc`. -/
def childProg (i : ℕ) : Cmd :=
  .seq (sideProg i)
    (.seq (.assign rCap (.len aUEnt))
      (.seq (restrictGraphProg aUS aUE aUEnt aY aStart aEnd aEnt 40 rCap 107 108 109 110 111 112 113)
        (cycProg i)))

/-- The registers that `childProg` writes. -/
def childRegs : List ℕ := sideRegs ++ List.range' 106 9

/-- The arrays that `childProg` writes. -/
def childArrs : List ℕ := sideArrs ++ [aStart, aEnd, aEnt, aTmp, aCyc]

/-- **The subinstance.** In at most `200 + 250 n + 80 M + 90 n |F|` steps, `childProg i` writes
in `aStart`, `aEnd`, `aEnt` adjacency lists of the graph of subinstance `i` of `H + F` along
`P' = a m b`, and in `aCyc` its cycle. -/
theorem childProg_exec {w : ℕ} {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    {Pv : List (Fin n)} {a b : Fin n} {A B m : List (Fin n)} (i : ℕ) {s : State}
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (hF : IsNewEdgeList H Pv (s.arrs aF))
    (P' : (H ⊔ pairGraph n (s.arrs aF)).Walk a b) (hm : P'.support = a :: m ++ [b])
    (hpath : s.arrs aNewPath = P'.support.map Fin.val)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val) (hlenA : s.regs rLenA = A.length)
    (hC : A.length + B.length + 2 ≤ n) (hmn : m.length + 2 ≤ n)
    (hAP : ∀ v ∈ A, v ∉ P'.support) (h40 : s.regs 40 = n) (hn : 4 * n + 4 < 2 ^ w)
    (hentw : (s.arrs aEnt).length < 2 ^ w) (hFw : (s.arrs aF).length < 2 ^ w)
    (hcapw : totalAdjEntries lists + n * (s.arrs aF).length < 2 ^ w) :
    ∃ s' t, Exec w (childProg i) s s' t ∧
      t ≤ 200 + 250 * n + 80 * totalAdjEntries lists + 90 * (n * (s.arrs aF).length) ∧
      Keeps childRegs childArrs s s' ∧
      IsAdjList (subGraph (H ⊔ pairGraph n (s.arrs aF)) P'.support A i) aStart aEnd aEnt
        (restrictListFamily (sideFin (H ⊔ pairGraph n (s.arrs aF)) P'.support A i)
          (unionList lists (s.arrs aF))) s' ∧
      (s'.arrs aEnt).length = totalAdjEntries lists + n * (s.arrs aF).length ∧
      s'.arrs aCyc = (subCycle a b A B m i).map Fin.val := by
  classical
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hPn : P'.support.length ≤ n := by rw [hm]; simp; omega
  -- Step 1: the lists of `H + F` and the bit set of the side.
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hadj₁, hlen₁, hY₁⟩ := sideProg_exec (B := B) i hadj hF P' hpath
    hPn hcyc hlenA (by omega) hAP h40 hn hentw hFw hcapw
  -- Step 2: the capacity.
  set cap := totalAdjEntries lists + n * (s.arrs aF).length with hcap
  set s₂ := s₁.setReg rCap cap with hs₂
  have hex₂ : Exec w (.assign rCap (.len aUEnt)) s₁ s₂ (1 + 1) :=
    .assign (by rw [← hlen₁]; exact len_eval rfl (by rw [hlen₁]; exact hcapw))
  have hk₂ : Keeps childRegs childArrs s s₂ :=
    (hk₁.mono (by decide) (by decide)).setReg (by decide) _
  -- Step 3: restrict to the side.
  have hTU : totalAdjEntries (unionList lists (s.arrs aF)) ≤ cap := by
    have := sum_unionList_le lists (s.arrs aF); rwa [pre_n] at this
  have hbound : 2 * (edgesInSet (H ⊔ pairGraph n (s.arrs aF))
      (sideFin (H ⊔ pairGraph n (s.arrs aF)) P'.support A i)).card ≤ cap := by
    have h1 := card_edgesInSet_le_card_edgeFinset (H ⊔ pairGraph n (s.arrs aF))
      (sideFin (H ⊔ pairGraph n (s.arrs aF)) P'.support A i)
    have h2 := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₁.2
    omega
  obtain ⟨s₃, t₃, hex₃, ht₃, hadj₃, hlen₃, -, harr₃, hreg₃⟩ := restrictGraphProg_exec
    (H ⊔ pairGraph n (s.arrs aF)) (unionList lists (s.arrs aF))
    (sideFin (H ⊔ pairGraph n (s.arrs aF)) P'.support A i) cap
    aUS aUE aUEnt aY aStart aEnd aEnt 40 rCap 107 108 109 110 111 112 113
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hw1 hnw hcapw hbound (s := s₂)
    (hadj₁.of_arrs_eq (by simp [s₂]) (by simp [s₂]) (by simp [s₂]))
    (by simp only [s₂, State.setReg_arrs]; rw [hlen₁]; exact hcapw)
    (hY₁.of_arr_eq (by simp [s₂]))
    (by rw [State.setReg_regs_ne _ _ (by decide), hk₁.1 40 (by decide)]; exact h40)
    (by simp [s₂])
  rw [restrictGraph_sideFin] at hadj₃
  have hk₃ : Keeps childRegs childArrs s s₃ :=
    ⟨fun r hr => by
      rw [hreg₃ r (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))
        (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))
        (fun e => hr (by rw [e]; decide)) (fun e => hr (by rw [e]; decide))
        (fun e => hr (by rw [e]; decide))]
      exact hk₂.1 r hr,
     fun x hx => by
      rw [harr₃ x (fun e => hx (by rw [e]; decide)) (fun e => hx (by rw [e]; decide))
        (fun e => hx (by rw [e]; decide))]
      exact hk₂.2 x hx⟩
  -- Step 4: the cycle.
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hcyc₄⟩ := cycProg_exec (w := w) i (A := A) (B := B) (m := m)
    (s := s₃) hn hC hmn
    (by
      rw [harr₃ aCyc (by decide) (by decide) (by decide)]
      simp only [s₂, State.setReg_arrs]; rw [hk₁.2 aCyc (by decide)]; exact hcyc)
    (by rw [hk₃.2 aNewPath (by decide), hpath, hm])
    (by rw [hk₃.1 rLenA (by decide)]; exact hlenA)
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    hk₃.trans hk₄ (by decide) (by decide),
    hadj₃.of_arrs_eq (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide)),
    by rw [hk₄.2 _ (by decide)]; exact hlen₃, hcyc₄⟩
  omega

end GraphMinor.Compute.TwoPaths
