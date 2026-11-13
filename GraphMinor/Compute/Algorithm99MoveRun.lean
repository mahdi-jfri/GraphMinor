module

public import GraphMinor.Compute.Logic
public import GraphMinor.Compute.Case3Block

/-!
# Renaming words of an array in place

Output (a) of steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104) is a block in
the labels of the renumbered graph `G'`. To write it in the labels of `G` the program replaces
each vertex word `x` of the block by `orig x`, read from the array that stores `orig`
(`Algorithm99MoveA`). This file gives the two loops that do this on one run of the block:

* `mvRun a o r` replaces the `k` words at positions `P, …, P + k - 1` of array `a` by their
  images in array `o` (`k` in register `r + 1`, `P` in register `r`; `mvRun_exec`);
* `mvTriples a o r` does the same for the first two words of each of `k` edge triples
  (`mvTriples_exec`).

Both move the position register `r` past the run, so that the program can walk through the
block in the order in which the parser `parseCase3Block` reads it.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- Writing at the end of a prefix replaces the next entry. -/
theorem List.set_length_append_cons {α : Type*} (A B : List α) (x y : α) :
    (A ++ x :: B).set A.length y = A ++ y :: B := by
  simp

/-- One step of a run: replace the word `x` at position `P` (register `r`) by `o[x]`. -/
def mvRenameOne (a o : Arr) (r : Reg) : Cmd :=
  .write a (.reg r) (.read o (.read a (.reg r)))

/-- Replace the `k` words from position `P` on (`k` in register `r + 1`, `P` in register `r`)
by their images in array `o`, and move `P` to `P + k`. Register `r + 2` is the loop index. -/
def mvRun (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 2) (.const 0))
    (forUp (r + 2) (.reg (r + 1))
      (.seq (mvRenameOne a o r) (.assign r (.op .add (.reg r) (.const 1)))))

/-- Evaluation of a read whose index and entry are known. -/
theorem mv_eval_read {w : ℕ} {s : State} {a : Arr} {idx : Expr} {i v : ℕ}
    (hidx : idx.eval w s = some i) (hlt : i < (s.arrs a).length) (hv : (s.arrs a)[i] = v)
    (hw : v < 2 ^ w) : (Expr.read a idx).eval w s = some v := by
  simp [Expr.eval, hidx, hlt, hv, checkWord, hw]

/-- The entry of `L ++ x :: R` at position `|L|` is `x`. -/
theorem mv_getElem_mid {L R : List ℕ} {x : ℕ} {L' : List ℕ} (h : L' = L ++ x :: R)
    (hlt : L.length < L'.length) : L'[L.length] = x := by
  subst h
  simp

/-- **A run of vertex words.** If array `a` is `D ++ seg ++ T`, register `r` holds `|D|` and
register `r + 1` holds `|seg|`, and every word of `seg` is an index of array `o`, then `mvRun`
makes `a` equal to `D ++ seg.map (o[·]) ++ T` and moves register `r` to `|D| + |seg|`. -/
theorem mvRun_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D seg T : List ℕ} (ha : s.arrs a = D ++ seg ++ T) (hr : s.regs r = D.length)
    (hk : s.regs (r + 1) = seg.length) (hseg : ∀ x ∈ seg, x < (s.arrs o).length)
    (hseg_w : ∀ x ∈ seg, x < 2 ^ w) (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w)
    (hw1 : 1 < 2 ^ w) (hlen_w : (D ++ seg ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvRun a o r) s s' t ∧ t ≤ 16 * seg.length + 5 ∧
      s'.arrs a = D ++ seg.map (fun x => (s.arrs o).getD x 0) ++ T ∧
      s'.regs r = D.length + seg.length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 2 → s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  have hN_w : seg.length < 2 ^ w := by simp at hlen_w; omega
  let I (i : ℕ) (st : State) : Prop :=
    st.arrs a = D ++ (seg.take i).map φ ++ seg.drop i ++ T ∧ st.regs r = D.length + i ∧
      st.regs (r + 2) = i ∧ st.regs (r + 1) = seg.length ∧
      (∀ b, b ≠ a → st.arrs b = s.arrs b) ∧ (∀ q, q ≠ r → q ≠ r + 2 → st.regs q = s.regs q)
  have hloop : ⦃I 0⦄[w] forUp (r + 2) (.reg (r + 1))
      (.seq (mvRenameOne a o r) (.assign r (.op .add (.reg r) (.const 1)))) ⦃I seg.length⦄ ≤
      fun _ => ((Expr.reg (r + 1)).cost + 2) + seg.length * ((Expr.reg (r + 1)).cost + 6 + 9) := by
    apply Triple.forUp_const I seg.length 9 hw1 hN_w
    · intro i _ st hI
      exact ⟨hI.2.2.1, by simp [Expr.eval, checkWord, hI.2.2.2.1, hN_w]⟩
    · intro i hi st ⟨hA, hP, hI2, hK, hB, hR⟩
      set L₁ := D ++ (seg.take i).map φ with hL₁
      have hL₁len : L₁.length = D.length + i := by simp [hL₁]; omega
      have hsplit : seg.drop i = seg[i] :: seg.drop (i + 1) := List.drop_eq_getElem_cons hi
      have hlist : st.arrs a = L₁ ++ seg[i] :: (seg.drop (i + 1) ++ T) := by
        rw [hA, hsplit]
        simp only [List.append_assoc, List.cons_append]
      have hlen : (st.arrs a).length = (D ++ seg ++ T).length := by
        rw [hA]
        simp
        omega
      have hposlt : L₁.length < (st.arrs a).length := by rw [hlist]; simp
      have hx : seg[i] ∈ seg := List.getElem_mem hi
      have ho : st.arrs o = s.arrs o := hB o hao.symm
      have hxo : seg[i] < (st.arrs o).length := ho ▸ hseg _ hx
      have hval : (st.arrs o)[seg[i]] = φ seg[i] := by
        simp only [hφ, ho]
        rw [List.getD_eq_getElem _ _ (ho ▸ hxo)]
      have hφ_w : φ seg[i] < 2 ^ w := by
        rw [← hval]
        exact ho_w _ (ho ▸ List.getElem_mem hxo)
      have hidx : (Expr.reg r).eval w st = some L₁.length := by
        rw [hL₁len]
        simp [Expr.eval, checkWord, hP]
        omega
      have hread₁ : (Expr.read a (.reg r)).eval w st = some seg[i] :=
        mv_eval_read hidx hposlt (mv_getElem_mid hlist hposlt) (hseg_w _ hx)
      have hread₂ : (Expr.read o (.read a (.reg r))).eval w st = some (φ seg[i]) :=
        mv_eval_read hread₁ hxo hval hφ_w
      have hex₁ : Exec w (mvRenameOne a o r) st (st.writeArr a L₁.length (φ seg[i])) 5 :=
        .write hidx hread₂ hposlt
      set st₁ := st.writeArr a L₁.length (φ seg[i]) with hst₁
      have hpw : D.length + i + 1 < 2 ^ w := by
        have h1 : L₁.length < (D ++ seg ++ T).length := hlen ▸ hposlt
        omega
      have hadd : (Expr.op .add (.reg r) (.const 1)).eval w st₁ = some (D.length + i + 1) := by
        have hP₁ : st₁.regs r = D.length + i := hP
        simp only [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hP₁]
        simp [hpw, show D.length + i < 2 ^ w by omega, show 1 < 2 ^ w from hw1]
      have hex₂ := Exec.assign (r := r) hadd
      refine ⟨_, _, Exec.seq hex₁ hex₂, le_refl _, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · change (st₁.arrs a) = _
        rw [hst₁, State.writeArr_arrs_self, hlist, List.set_length_append_cons]
        rw [List.take_add_one, List.getElem?_eq_getElem hi, hL₁]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          List.append_assoc, List.cons_append, List.nil_append]
      · simp [State.setReg, Function.update]
        romega
      · simp [State.setReg, Function.update]
      · rw [State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega)]
        change st.regs (r + 1) = _
        exact hK
      · intro b hb
        change (Function.update st.arrs a ((st.arrs a).set L₁.length (φ seg[i]))) b = _
        rw [Function.update_of_ne hb]
        exact hB b hb
      · intro q hq1 hq2
        rw [State.setReg_regs_ne _ _ hq2, State.setReg_regs_ne _ _ hq1]
        exact hR q hq1 hq2
      · rw [State.setReg_regs_ne _ _ (by romega)]
        exact hI2
  have hex₀ : Exec w (.assign (r + 2) (.const 0)) s (s.setReg (r + 2) 0) 2 :=
    .assign (by simp [Expr.eval, checkWord])
  have hI₀ : I 0 (s.setReg (r + 2) 0) := by
    refine ⟨by simpa using ha, ?_, by simp, ?_, fun _ _ => rfl, fun q _ hq => ?_⟩
    · rw [State.setReg_regs_ne _ _ (by romega)]; simpa using hr
    · rw [State.setReg_regs_ne _ _ (by romega)]; exact hk
    · exact State.setReg_regs_ne _ _ hq
  obtain ⟨s', t, hex, ht, hA, hP, -, -, hB, hR⟩ := hloop _ hI₀
  refine ⟨s', 2 + t, Exec.seq hex₀ hex, ?_, ?_, hP, hB, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · rw [hA]
    simp
  · intro q hq1 hq2
    rw [hR q hq1 hq2]

/-! ### Runs of edge triples -/

theorem encEdgeTriples_append (l₁ l₂ : List (ℕ × ℕ × ℕ)) :
    encEdgeTriples (l₁ ++ l₂) = encEdgeTriples l₁ ++ encEdgeTriples l₂ := by
  induction l₁ with
  | nil => rfl
  | cons e l₁ ih =>
    obtain ⟨u, v, k⟩ := e
    simp [encEdgeTriples, ih]

theorem length_encEdgeTriples (l : List (ℕ × ℕ × ℕ)) :
    (encEdgeTriples l).length = 3 * l.length := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨u, v, k⟩ := e
    simp [encEdgeTriples, ih]
    omega

/-- The renaming of an edge triple: both ends through `φ`, the copy number kept. -/
def mvTriple (φ : ℕ → ℕ) (e : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (φ e.1, φ e.2.1, e.2.2)

/-- Rename the two ends of each of the `k` edge triples from position `P` on (`k` in register
`r + 4`, `P` in register `r`), and move `P` to `P + 3k`. Register `r + 3` is the loop index;
each step runs `mvRun` on the two ends. -/
def mvTriples (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 3) (.const 0))
    (forUp (r + 3) (.reg (r + 4))
      (.seq (.assign (r + 1) (.const 2))
        (.seq (mvRun a o r) (.assign r (.op .add (.reg r) (.const 1))))))

/-- **A run of edge triples.** If array `a` is `D ++ encEdgeTriples es ++ T`, register `r` holds
`|D|` and register `r + 4` holds `|es|`, and both ends of each triple are indices of array `o`,
then `mvTriples` makes `a` equal to `D ++ encEdgeTriples (es.map (mvTriple (o[·]))) ++ T` and
moves register `r` to `|D| + 3 |es|`. -/
theorem mvTriples_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D T : List ℕ} {es : List (ℕ × ℕ × ℕ)} (ha : s.arrs a = D ++ encEdgeTriples es ++ T)
    (hr : s.regs r = D.length) (hk : s.regs (r + 4) = es.length)
    (hes : ∀ e ∈ es, e.1 < (s.arrs o).length ∧ e.2.1 < (s.arrs o).length)
    (hes_w : ∀ e ∈ es, e.1 < 2 ^ w ∧ e.2.1 < 2 ^ w) (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w)
    (hw3 : 3 < 2 ^ w) (hlen_w : (D ++ encEdgeTriples es ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvTriples a o r) s s' t ∧ t ≤ 53 * es.length + 5 ∧
      s'.arrs a = D ++ encEdgeTriples (es.map (mvTriple (fun x => (s.arrs o).getD x 0))) ++ T ∧
      s'.regs r = D.length + 3 * es.length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  have hw1 : 1 < 2 ^ w := by omega
  have hN_w : es.length < 2 ^ w := by
    simp only [List.length_append, length_encEdgeTriples] at hlen_w
    omega
  let I (i : ℕ) (st : State) : Prop :=
    st.arrs a = D ++ encEdgeTriples ((es.take i).map (mvTriple φ)) ++
        encEdgeTriples (es.drop i) ++ T ∧ st.regs r = D.length + 3 * i ∧
      st.regs (r + 3) = i ∧ st.regs (r + 4) = es.length ∧
      (∀ b, b ≠ a → st.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → st.regs q = s.regs q)
  have hloop : ⦃I 0⦄[w] forUp (r + 3) (.reg (r + 4))
      (.seq (.assign (r + 1) (.const 2))
        (.seq (mvRun a o r) (.assign r (.op .add (.reg r) (.const 1))))) ⦃I es.length⦄ ≤
      fun _ => ((Expr.reg (r + 4)).cost + 2) + es.length * ((Expr.reg (r + 4)).cost + 6 + 43) := by
    apply Triple.forUp_const I es.length 43 hw1 hN_w
    · intro i _ st hI
      exact ⟨hI.2.2.1, by simp [Expr.eval, checkWord, hI.2.2.2.1, hN_w]⟩
    · intro i hi st ⟨hA, hP, hI3, hK, hB, hR⟩
      set e := es[i] with he
      have hsplit : es.drop i = e :: es.drop (i + 1) := List.drop_eq_getElem_cons hi
      set L₁ := D ++ encEdgeTriples ((es.take i).map (mvTriple φ)) with hL₁
      have hL₁len : L₁.length = D.length + 3 * i := by
        simp [hL₁, length_encEdgeTriples]
        omega
      have hA' : st.arrs a = L₁ ++ [e.1, e.2.1] ++ (e.2.2 :: encEdgeTriples (es.drop (i + 1)) ++ T) := by
        rw [hA, hsplit]
        obtain ⟨u, v, k⟩ := e
        simp [encEdgeTriples]
      have hlen : (L₁ ++ [e.1, e.2.1] ++ (e.2.2 :: encEdgeTriples (es.drop (i + 1)) ++ T)).length =
          (D ++ encEdgeTriples es ++ T).length := by
        rw [← hA', hA]
        simp only [List.length_append, length_encEdgeTriples,
          List.length_drop]
        omega
      have hemem : e ∈ es := List.getElem_mem hi
      have ho : st.arrs o = s.arrs o := hB o hao.symm
      -- the count register
      let st₁ := st.setReg (r + 1) 2
      have hex₁ : Exec w (.assign (r + 1) (.const 2)) st st₁ 2 :=
        .assign (by simp [Expr.eval, checkWord]; omega)
      have hr₁ : st₁.regs r = L₁.length := by
        rw [State.setReg_regs_ne _ _ (by romega), hP, hL₁len]
      obtain ⟨st₂, t₂, hex₂, ht₂, hA₂, hP₂, hB₂, hR₂⟩ :=
        mvRun_exec (s := st₁) hao r (D := L₁) (seg := [e.1, e.2.1])
          (T := e.2.2 :: encEdgeTriples (es.drop (i + 1)) ++ T) hA' hr₁ (by simp [st₁])
          (by
            intro x hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            change x < (st.arrs o).length
            rw [ho]
            rcases hx with rfl | rfl
            · exact (hes e hemem).1
            · exact (hes e hemem).2)
          (by
            intro x hx
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
            rcases hx with rfl | rfl
            · exact (hes_w e hemem).1
            · exact (hes_w e hemem).2)
          (by change ∀ y ∈ st.arrs o, y < 2 ^ w; rw [ho]; exact ho_w) hw1 (hlen ▸ hlen_w)
      have hpw : L₁.length + 3 < 2 ^ w := by
        have := hlen ▸ hlen_w
        simp only [List.length_append, List.length_cons, List.length_nil] at this
        omega
      have hadd : (Expr.op .add (.reg r) (.const 1)).eval w st₂ = some (L₁.length + 3) := by
        have hP₂' : st₂.regs r = L₁.length + 2 := by rw [hP₂]; rfl
        simp only [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hP₂']
        simp [show L₁.length + 2 < 2 ^ w by omega, show 1 < 2 ^ w from hw1, hpw]
      have hex₃ := Exec.assign (r := r) hadd
      refine ⟨_, _, Exec.seq hex₁ (Exec.seq hex₂ hex₃), ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [Expr.cost, List.length_cons, List.length_nil] at ht₂ ⊢
        omega
      · change st₂.arrs a = _
        rw [hA₂, List.take_add_one, List.getElem?_eq_getElem hi, hL₁]
        have ho₁ : st₁.arrs o = s.arrs o := ho
        rw [ho₁]
        simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
          encEdgeTriples_append, List.append_assoc, List.cons_append, List.nil_append]
        rw [← he]
        simp [encEdgeTriples, mvTriple, hφ]
      · rw [State.setReg_regs_ne _ _ (by romega), State.setReg_regs_self, hL₁len]
        ring
      · rw [State.setReg_regs_self]
      · rw [State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega),
          hR₂ _ (by romega) (by romega), State.setReg_regs_ne _ _ (by romega)]
        exact hK
      · intro b hb
        change st₂.arrs b = _
        rw [hB₂ b hb]
        exact hB b hb
      · intro q h0 h1 h2 h3
        rw [State.setReg_regs_ne _ _ h3, State.setReg_regs_ne _ _ h0, hR₂ q h0 h2,
          State.setReg_regs_ne _ _ h1]
        exact hR q h0 h1 h2 h3
      · rw [State.setReg_regs_ne _ _ (by romega), hR₂ _ (by romega) (by romega),
          State.setReg_regs_ne _ _ (by romega)]
        exact hI3
  have hex₀ : Exec w (.assign (r + 3) (.const 0)) s (s.setReg (r + 3) 0) 2 :=
    .assign (by simp [Expr.eval, checkWord])
  have hI₀ : I 0 (s.setReg (r + 3) 0) := by
    refine ⟨by rw [State.setReg_arrs, ha]; simp [encEdgeTriples], ?_, by simp, ?_,
      fun _ _ => rfl, fun q _ _ _ hq => ?_⟩
    · rw [State.setReg_regs_ne _ _ (by romega)]; simpa using hr
    · rw [State.setReg_regs_ne _ _ (by romega)]; exact hk
    · exact State.setReg_regs_ne _ _ hq
  obtain ⟨s', t, hex, ht, hA, hP, -, -, hB, hR⟩ := hloop _ hI₀
  refine ⟨s', 2 + t, Exec.seq hex₀ hex, ?_, ?_, hP, hB, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · rw [hA]
    simp [encEdgeTriples, hφ]
  · intro q h0 h1 h2 h3
    rw [hR q h0 h1 h2 h3]

end GraphMinor.Compute
