module

public import GraphMinor.Compute.TwoPathsPath

/-!
# Rotating the cycle

Once a `C`-path from `x` to `y` is known (`TwoPathsPath.lean`), the instance of line 9 of
Algorithm 5.1 asks for the cycle in the form `x A y B`. `rotProg` rotates the cycle in array
`aCyc` so that it starts at `x`, and writes `|A|` in register `rLenA`.

The rotation copies the cycle into a scratch array with shifted indices and copies it back. Both
copies are the loop `mapProg`, which fills an array with entries read from another array.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### Filling an array from another one -/

/-- Fill `dst` (of length `hiE`) by `dst[i] := src[E]`, where `E` may read the counter `rI`. -/
def mapProg (rI : Reg) (hiE : Expr) (dst src : Arr) (E : Expr) : Cmd :=
  .seq (.alloc dst hiE) (.seq (.assign rI (.const 0)) (forUp rI hiE (.write dst (.reg rI) (.read src E))))

theorem read_eval {w : ℕ} {s : State} {a : Arr} {E : Expr} {i : ℕ} (hE : E.eval w s = some i)
    (hi : i < (s.arrs a).length) (hv : (s.arrs a)[i] < 2 ^ w) :
    (Expr.read a E).eval w s = some (s.arrs a)[i] := by
  simp [Expr.eval, hE, hi, checkWord, hv]

theorem op_eval {w : ℕ} {s : State} {A B : Expr} {a b c : ℕ} {bop : BinOp}
    (hA : A.eval w s = some a) (hB : B.eval w s = some b) (hc : bop.eval w a b = some c) :
    (Expr.op bop A B).eval w s = some c := by
  simp [Expr.eval, hA, hB, hc]

theorem set_range_map (f : ℕ → ℕ) {i k : ℕ} (hi : i < k) :
    ((List.range i).map f ++ List.replicate (k - i) 0).set i (f i) =
      (List.range (i + 1)).map f ++ List.replicate (k - (i + 1)) 0 := by
  rw [List.set_append_right _ _ (by simp), show k - i = (k - (i + 1)) + 1 by omega,
    List.replicate_succ, List.length_map, List.length_range, Nat.sub_self, List.set_cons_zero,
    List.range_succ, List.map_append, List.append_assoc]
  rfl

/-- **Filling an array.** `mapProg` writes `L[g i]` at every index `i < k` of `dst`, where `L` is
the content of `src` and `g i` the value of `E` when the counter is `i`. -/
theorem mapProg_exec {w : ℕ} (rI : Reg) (hiE : Expr) (dst src : Arr) (E : Expr) (hds : dst ≠ src)
    (k : ℕ) (g : ℕ → ℕ) (L : List ℕ) (s : State) (hw : 1 < 2 ^ w) (hk : k < 2 ^ w)
    (hhi : ∀ st, Keeps [rI] [dst] s st → hiE.eval w st = some k)
    (hE : ∀ st i, Keeps [rI] [dst] s st → st.regs rI = i → i < k → E.eval w st = some (g i))
    (hg : ∀ i < k, g i < L.length) (hL : ∀ x ∈ L, x < 2 ^ w) (hsrc : s.arrs src = L) :
    ∃ s' t, Exec w (mapProg rI hiE dst src E) s s' t ∧
      t ≤ 2 * hiE.cost + 4 + k * (hiE.cost + E.cost + 10) ∧ Keeps [rI] [dst] s s' ∧
      s'.arrs dst = (List.range k).map (fun i => L.getD (g i) 0) := by
  set f : ℕ → ℕ := fun i => L.getD (g i) 0 with hf
  set s₁ := s.setArr dst (List.replicate k 0) with hs₁
  have hex₁ : Exec w (.alloc dst hiE) s s₁ (hiE.cost + k) := .alloc (hhi s (Keeps.refl _ _ s))
  set s₂ := s₁.setReg rI 0 with hs₂
  have hex₂ : Exec w (.assign rI (.const 0)) s₁ s₂ (1 + 1) := .assign (by simp [checkWord])
  let I : ℕ → State → Prop := fun i st => Keeps [rI] [dst] s st ∧ st.regs rI = i ∧
    st.arrs dst = (List.range i).map f ++ List.replicate (k - i) 0
  have hI0 : I 0 s₂ := ⟨((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, by simp [s₂],
    by simp [s₂, s₁]⟩
  have hloop := forUp_pot I (fun _ => 0) k (E.cost + 3) (r_i := rI) (hi := hiE)
    (body := .write dst (.reg rI) (.read src E)) hw hk
    (fun i _ st hst => ⟨hst.2.1, hhi st hst.1⟩)
    (fun i hi st hst => by
      obtain ⟨hks, hri, hd⟩ := hst
      have hsrc' : st.arrs src = L := by rw [hks.2 src (by simp [Ne.symm hds]), hsrc]
      have hgi := hg i hi
      have hv : f i = L[g i] := by simp [f, hgi]
      refine ⟨st.writeArr dst i (f i), _, .write (reg_eval hri (by omega))
        (by rw [read_eval (hE st i hks hri hi) (by rw [hsrc']; exact hgi)
          (by simp only [hsrc']; exact hL _ (List.getElem_mem _)), hv]; simp only [hsrc'])
        (by rw [hd]; simp; omega), ?_, ⟨?_, by simp, ?_⟩, by simp [hri]⟩
      · simp only [Expr.cost]; omega
      · exact (hks.writeArr (by simp) _ _).setReg (by simp) _
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, hd]
        exact set_range_map f hi)
    0 (Nat.zero_le _) s₂ hI0
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hd₃⟩ := hloop
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, by simpa using hd₃⟩
  have : k * (hiE.cost + 6 + (E.cost + 3)) + k = k * (hiE.cost + E.cost + 10) := by
    rw [show hiE.cost + E.cost + 10 = (hiE.cost + 6 + (E.cost + 3)) + 1 by omega, Nat.mul_succ]
  rw [Nat.sub_zero] at ht₃
  omega

/-! ### The rotation -/

/-- Register holding the index of `x` in the cycle. -/
abbrev rSh : Reg := 97
/-- The counter of the copy loops. -/
abbrev rI3 : Reg := 98
/-- The scratch array of the rotation. -/
abbrev aTmp : Arr := 65

/-- Rotate the cycle in `aCyc` to start at `x = rPx`, and write in `rLenA` the number of vertices
strictly between `x` and `y = rPy`. -/
def rotProg : Cmd :=
  .seq (.assign rSh (.op .sub (.read aPos (.reg rPx)) (.const 1)))
    (.seq (.assign rLenA (.op .sub (.op .mod (.op .sub (.op .add (.read aPos (.reg rPy)) (.reg rk))
        (.read aPos (.reg rPx))) (.reg rk)) (.const 1)))
      (.seq (mapProg rI3 (.reg rk) aTmp aCyc (.op .mod (.op .add (.reg rI3) (.reg rSh)) (.reg rk)))
        (mapProg rI3 (.reg rk) aCyc aTmp (.reg rI3))))

theorem posArr_get {T : List (Fin n)} {x : Fin n} (hx : x ∈ T) (h : x.1 < (posArr T).length) :
    (posArr T)[x.1] = T.idxOf x + 1 := by
  simp [posArr, hx]

theorem map_rotate_eq {T : List (Fin n)} (sh : ℕ) :
    (List.range T.length).map (fun i => (T.map Fin.val).getD ((i + sh) % T.length) 0) =
      (T.rotate sh).map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  have hk : 0 < T.length := by simp at h₁; omega
  have hm : (i + sh) % T.length < T.length := Nat.mod_lt _ hk
  simp [List.getElem_rotate, hm]

theorem map_getD_self (L : List ℕ) : (List.range L.length).map (fun i => L.getD i 0) = L := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp at h₁
  simp [h₁]

/-- **The rotation.** If `x` and `y` are apart on `T`, `rotProg` writes `x A y B` in `aCyc`, a
rotation of `T` with `A` and `B` not empty, and `|A|` in `rLenA`, in at most `29 + 28 |T|` steps. -/
theorem rotProg_exec {w : ℕ} (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w)
    (x y : Fin n) (hx : x ∈ T) (hy : y ∈ T) (hap : Apart T.length (T.idxOf y + 1) (T.idxOf x + 1))
    (s : State) (hcyc : s.arrs aCyc = T.map Fin.val) (hpos : s.arrs aPos = posArr T)
    (hk : s.regs rk = T.length) (hrx : s.regs rPx = x.1) (hry : s.regs rPy = y.1) :
    ∃ (s' : State) (t : ℕ) (A B : List (Fin n)), Exec w rotProg s s' t ∧ t ≤ 29 + 28 * T.length ∧
      T.rotate (T.idxOf x) = x :: A ++ y :: B ∧ A ≠ [] ∧ B ≠ [] ∧
      s'.arrs aCyc = (x :: A ++ y :: B).map Fin.val ∧ s'.regs rLenA = A.length ∧
      Keeps [rSh, rLenA, rI3] [aTmp, aCyc] s s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set k := T.length with hkdef
  set i := T.idxOf x with hi
  set j := T.idxOf y with hj
  have hik : i < k := List.idxOf_lt_length_iff.mpr hx
  have hjk : j < k := List.idxOf_lt_length_iff.mpr hy
  have hlenpos : (posArr T).length = n := by simp [posArr]
  have hev : ∀ st : State, st.regs rPx = x.1 → st.regs rPy = y.1 → st.arrs aPos = posArr T →
      st.regs rk = k → (Expr.read aPos (.reg rPx)).eval w st = some (i + 1) ∧
        (Expr.read aPos (.reg rPy)).eval w st = some (j + 1) ∧
        (Expr.reg rk).eval w st = some k := fun st h1 h2 h3 h4 => by
    refine ⟨?_, ?_, reg_eval h4 (by omega)⟩
    · rw [read_eval (reg_eval h1 (by omega)) (by rw [h3, hlenpos]; exact x.2)
        (by simp only [h3]; rw [posArr_get hx]; omega)]
      simp only [h3]; rw [posArr_get hx]
    · rw [read_eval (reg_eval h2 (by omega)) (by rw [h3, hlenpos]; exact y.2)
        (by simp only [h3]; rw [posArr_get hy]; omega)]
      simp only [h3]; rw [posArr_get hy]
  obtain ⟨hxp, -, -⟩ := hev s hrx hry hpos hk
  have hc1 : ∀ st : State, (Expr.const 1).eval w st = some 1 := fun _ => by simp [checkWord, hw1]
  -- The two assignments.
  set s₁ := s.setReg rSh i with hs₁
  have hex₁ : Exec w (.assign rSh (.op .sub (.read aPos (.reg rPx)) (.const 1))) s s₁
      (1 + 1 + 1 + 1 + 1) := .assign (op_eval hxp (hc1 s) (by
        simp [BinOp.eval, BinOp.raw, checkWord]; omega))
  have hkpos : 0 < k := by omega
  set d := (j + k - i) % k with hd
  have hdk : d < k := Nat.mod_lt _ hkpos
  set s₂ := s₁.setReg rLenA (d - 1) with hs₂
  obtain ⟨hxp₁, hyp₁, hkev₁⟩ := hev s₁ (by simp [s₁, hrx]) (by simp [s₁, hry]) (by simp [s₁, hpos])
    (by simp [s₁, hk])
  have hex₂ : Exec w (.assign rLenA (.op .sub (.op .mod (.op .sub (.op .add
      (.read aPos (.reg rPy)) (.reg rk)) (.read aPos (.reg rPx))) (.reg rk)) (.const 1))) s₁ s₂
      (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := .assign (by
        refine op_eval (a := d) (op_eval (a := j + k - i) (op_eval (a := j + 1 + k) (op_eval hyp₁ hkev₁ ?_)
          hxp₁ ?_) hkev₁ ?_) (hc1 s₁) ?_
        · simp [BinOp.eval, BinOp.raw, checkWord]; omega
        · simp [BinOp.eval, BinOp.raw, checkWord]; omega
        · simp only [BinOp.eval, BinOp.raw, show k ≠ 0 by omega, ite_false, checkWord]
          rw [if_pos (by omega)]
        · simp [BinOp.eval, BinOp.raw, checkWord]; omega)
  -- The positions are apart, so `1 < d < k - 1`.
  have hd12 : 1 < d ∧ d < k - 1 := by
    unfold Apart cdist at hap
    rw [show j + 1 + k - (i + 1) = j + k - i by omega] at hap
    exact hap
  have hij : i ≠ j := fun e => by
    rw [hd, e, show j + k - j = k by omega, Nat.mod_self] at hd12; omega
  obtain ⟨A, B, hrot, hA, hAB⟩ := rotate_split T i j hik hjk hij
  have hTi : T[i] = x := List.getElem_idxOf hik
  have hTj : T[j] = y := List.getElem_idxOf hjk
  rw [hTi, hTj] at hrot
  have hAd : A.length + 1 = d := hA
  have hBd : A.length + B.length + 2 = k := hAB
  -- The first copy: `aTmp` gets the rotation.
  have hLw : ∀ v ∈ T.map Fin.val, v < 2 ^ w := fun v hv => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv; have := z.2; omega
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hd₃⟩ := mapProg_exec rI3 (.reg rk) aTmp aCyc
    (.op .mod (.op .add (.reg rI3) (.reg rSh)) (.reg rk)) (by decide) k (fun i' => (i' + i) % k)
    (T.map Fin.val) s₂ hw1 (by omega)
    (fun st hst => reg_eval (by rw [hst.1 rk (by decide)]; simp [s₂, s₁, hk]) (by omega))
    (fun st i' hst hri hi' => by
      have h1 : st.regs rSh = i := by rw [hst.1 rSh (by decide)]; simp [s₂, s₁]
      have h2 : st.regs rk = k := by rw [hst.1 rk (by decide)]; simp [s₂, s₁, hk]
      refine op_eval (a := i' + i) (op_eval (reg_eval hri (by omega)) (reg_eval h1 (by omega)) ?_)
        (reg_eval h2 (by omega)) ?_
      · simp [BinOp.eval, BinOp.raw, checkWord]; omega
      · simp only [BinOp.eval, BinOp.raw, show k ≠ 0 by omega, ite_false, checkWord]
        rw [if_pos (by have := Nat.mod_lt (i' + i) hkpos; omega)])
    (fun i' _ => by simp only [List.length_map]; exact Nat.mod_lt _ hkpos) hLw
    (by simp [s₂, s₁, hcyc])
  rw [map_rotate_eq] at hd₃
  -- The second copy: back into `aCyc`.
  have hLw' : ∀ v ∈ (T.rotate i).map Fin.val, v < 2 ^ w := fun v hv => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv; have := z.2; omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hd₄⟩ := mapProg_exec rI3 (.reg rk) aCyc aTmp (.reg rI3)
    (by decide) k id ((T.rotate i).map Fin.val) s₃ hw1 (by omega)
    (fun st hst => reg_eval (by rw [hst.1 rk (by decide), hk₃.1 rk (by decide)]; simp [s₂, s₁, hk])
      (by omega))
    (fun st i' hst hri hi' => reg_eval hri (show i' < 2 ^ w by omega))
    (fun i' hi' => by simp only [id, List.length_map, List.length_rotate]; exact hi') hLw' hd₃
  have hlen : ((T.rotate i).map Fin.val).length = k := by simp [k]
  simp only [id] at hd₄
  rw [← hlen, map_getD_self] at hd₄
  refine ⟨s₄, _, A, B, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_, hrot, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₃ ht₄
    omega
  · intro h; subst h; simp at hAd; omega
  · intro h; subst h; simp at hBd; omega
  · rw [hd₄, hrot]
  · rw [hk₄.1 rLenA (by decide), hk₃.1 rLenA (by decide)]; simp only [s₂, State.setReg_regs_self]; omega
  · exact ((((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).trans hk₃
      (by simp) (by simp)).trans hk₄ (by simp) (by simp)

end GraphMinor.Compute.TwoPaths
