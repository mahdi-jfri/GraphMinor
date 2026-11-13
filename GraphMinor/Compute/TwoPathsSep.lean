module

public import GraphMinor.Compute.TwoPathsFind
import GraphMinor.HP25.Lemma33
import Mathlib.Data.List.GetD

/-!
# Line 6 of Algorithm 5.1: does `P` separate `A` from `B`

The instance is the cycle `C = a A b B` in `aCyc` and a `C`-path `P` from `a` to `b` in `aPath`.
`sepProg` runs one search in `H - P` from all the vertices of `A`, with the vertices of `B` as
targets.

* If no target is seen, `P` separates `A` from `B` (`separates_of_noHit`): a walk from `A` to `B`
  that misses `P` would, up to its first vertex in `B`, run through free vertices only, so the
  search would see that vertex.
* If a target is seen, the parents give a path `R` from a vertex of `A` to a vertex of `B`. Its
  inner vertices are not sources, so they are off `C`, and they are off `P`. So `(P, R)` is a
  crossing of `C` (`isCrossing_of_split`), and `sepProg` writes it in arrays `aQ` and `aR`.

The labels are written by `markProg`, a loop that writes one value at the entries of an array
listed in another array.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### Marking a list of vertices -/

/-- Write `c` at the entries `L[i]` of `dst`, for `lo ≤ i < hi`, where `L` is the list in `src`. -/
def markProg (rI : Reg) (lo hi : Expr) (dst src : Arr) (c : ℕ) : Cmd :=
  .seq (.assign rI lo) (forUp rI hi (.write dst (.read src (.reg rI)) (.const c)))

theorem drop_take_succ {α : Type*} {L : List α} {lo i : ℕ} (hlo : lo ≤ i) (hi : i < L.length) :
    (L.take (i + 1)).drop lo = (L.take i).drop lo ++ [L[i]] := by
  rw [take_succ_eq hi, List.drop_append_of_le_length (by simp; omega)]

/-- **Marking.** `markProg` writes `c` at the vertices `L[lo], …, L[hi - 1]`. -/
theorem markProg_exec {w : ℕ} (rI : Reg) (lo hi : Expr) (dst src : Arr) (c : ℕ) (hds : dst ≠ src)
    (L : List (Fin n)) (f : Fin n → ℕ) (vlo vhi : ℕ) (s : State) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hc : c < 2 ^ w) (hle : vlo ≤ vhi) (hhiL : vhi ≤ L.length)
    (hlo : lo.eval w s = some vlo)
    (hhi : ∀ st, Keeps [rI] [dst] s st → hi.eval w st = some vhi)
    (hsrc : s.arrs src = L.map Fin.val) (hdst : s.arrs dst = List.ofFn f) :
    ∃ s' t, Exec w (markProg rI lo hi dst src c) s s' t ∧
      t ≤ lo.cost + hi.cost + 3 + (vhi - vlo) * (hi.cost + 10) ∧ Keeps [rI] [dst] s s' ∧
      s'.arrs dst = List.ofFn (fun v => if v ∈ (L.take vhi).drop vlo then c else f v) := by
  have hvhi : vhi < 2 ^ w := Expr.eval_lt (hhi s (Keeps.refl _ _ s))
  set g : ℕ → Fin n → ℕ := fun i v => if v ∈ (L.take i).drop vlo then c else f v with hg
  set s₁ := s.setReg rI vlo with hs₁
  have hex₁ : Exec w (.assign rI lo) s s₁ (lo.cost + 1) := .assign hlo
  let I : ℕ → State → Prop := fun i st => Keeps [rI] [dst] s st ∧ st.regs rI = i ∧
    st.arrs dst = List.ofFn (g i) ∧ vlo ≤ i
  have hI0 : I vlo s₁ := ⟨(Keeps.refl _ _ s).setReg (by simp) _, by simp [s₁], ?_, le_rfl⟩
  swap
  · 
    simp only [s₁, State.setReg_arrs, hdst, g]
    congr 1; funext v; simp
  have hloop := forUp_pot I (fun _ => 0) vhi 4 (r_i := rI) (hi := hi)
    (body := .write dst (.read src (.reg rI)) (.const c)) hw hvhi
    (fun i _ st hst => ⟨hst.2.1, hhi st hst.1⟩)
    (fun i hi' st hst => by
      obtain ⟨hks, hri, hd, hlo'⟩ := hst
      have hsrc' : st.arrs src = L.map Fin.val := by rw [hks.2 src (by simp [Ne.symm hds]), hsrc]
      have hiL : i < L.length := by omega
      have hx : (Expr.read src (.reg rI)).eval w st = some L[i].1 := by
        rw [read_eval (reg_eval hri (by omega)) (by rw [hsrc']; simpa using hiL)
          (by simp only [hsrc', List.getElem_map]; have := L[i].2; omega)]
        simp [hsrc']
      refine ⟨st.writeArr dst L[i].1 c, _, .write hx (by simp [checkWord, hc])
        (by rw [hd]; simp), ?_, ⟨?_, by simp, ?_, by omega⟩, by simp [hri]⟩
      · simp only [Expr.cost]; omega
      · exact (hks.writeArr (by simp) _ _).setReg (by simp) _
      · simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs, ite_true, hd]
        rw [ofFn_set]
        congr 1; funext v
        simp only [g, Function.update_apply, drop_take_succ hlo' hiL, List.mem_append,
          List.mem_singleton]
        by_cases hv : v = L[i] <;> simp [hv])
    vlo hle s₁ hI0
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, -, hd₂⟩ := hloop
  refine ⟨s₂, _, .seq hex₁ hex₂, ?_, hk₂, hd₂.1⟩
  rw [show hi.cost + 6 + 4 = hi.cost + 10 by omega] at ht₂
  omega

/-! ### The two outcomes -/

/-- **The crossing.** In `C = a A b B`, a `C`-path `Q` from `a` to `b` and a disjoint `C`-path `R`
from a vertex of `A` to a vertex of `B` form a crossing of `C`. -/
theorem isCrossing_of_split {V : Type*} {G : SimpleGraph V} {a b c d : V} {A B : List V}
    (hc : c ∈ A) (hd : d ∈ B) (Q : G.Walk a b) (R : G.Walk c d)
    (hQ : IsTPath G (a :: A ++ b :: B) Q) (hR : IsTPath G (a :: A ++ b :: B) R)
    (hdisj : Q.support.Disjoint R.support) : IsCrossing G (a :: A ++ b :: B) Q R := by
  obtain ⟨i₁, hi₁, rfl⟩ := List.getElem_of_mem hc
  obtain ⟨i₂, hi₂, rfl⟩ := List.getElem_of_mem hd
  refine ⟨⟨0, i₁ + 1, A.length + 1, A.length + 2 + i₂, by omega, by omega, by omega, rfl, ?_, ?_,
    ?_⟩, hQ, hR, hdisj⟩
  · simp [List.getElem?_append_left (show i₁ < A.length by omega), hi₁]
  · simp
  · rw [show A.length + 2 + i₂ = (A.length + 1 + i₂) + 1 by omega, List.cons_append,
      List.getElem?_cons_succ,
      List.getElem?_append_right (by omega), show A.length + 1 + i₂ - A.length = i₂ + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_eq_getElem hi₂]

/-- The labels of the separation test: `P` forbidden, `B` targets, everything else free. -/
def labS {a b : Fin n} {H : SimpleGraph (Fin n)} (P : H.Walk a b) (B : List (Fin n)) (v : Fin n) :
    ℕ :=
  if v ∈ P.support then 2 else if v ∈ B then 3 else 0

/-- **No target seen: `P` separates.** -/
theorem separates_of_noHit {H : SimpleGraph (Fin n)} {a b : Fin n} {A B : List (Fin n)}
    (hnd : (a :: A ++ b :: B).Nodup) {P : H.Walk a b} {s₀ s : State} {items : List ℕ}
    (hs : SInv H (labS P B) (A.map Fin.val) s₀ items items.length s) (hh : s.regs rHit = n) :
    Separates H {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B} := by
  classical
  intro u hu w hw p
  by_contra hno
  have hno' : ∀ v ∈ p.support, v ∉ P.support := fun v hv hvP => hno ⟨v, hv, hvP⟩
  change u ∈ A at hu
  change w ∈ B at hw
  have hAB : ∀ v, v ∈ A → v ∉ B := fun v hvA hvB => by
    simp only [List.cons_append, List.nodup_cons, List.nodup_append, List.mem_cons] at hnd
    exact hnd.2.2.2 v hvA v (Or.inr hvB) rfl
  have hL : ∀ v ∈ p.support, labS P B v = 0 ∨ (labS P B v = 3 ∧ v ∈ B) := fun v hv => by
    unfold labS; rw [if_neg (hno' v hv)]; split_ifs with h <;> simp [h]
  -- The first vertex of a path inside `p` that is not free.
  obtain ⟨t, ht, w', h1, h2, h3⟩ := exists_first_hit {v | labS P B v ≠ 0} p.bypass
    (show labS P B w ≠ 0 by
      rcases hL w p.end_mem_support with h | h
      · simp [labS, hno' w p.end_mem_support, hw] at h
      · omega)
  have hw'p : w'.IsPath := h3 p.bypass_isPath
  have hsub : ∀ y ∈ w'.support, y ∈ p.support := fun y hy => p.support_bypass_subset (h1 y hy)
  have ht3 : labS P B t = 3 := by
    rcases hL t (hsub t w'.end_mem_support) with h | h
    · exact absurd h ht
    · exact h.1
  have hu0 : labS P B u = 0 := by
    rcases hL u p.start_mem_support with h | h
    · exact h
    · exact absurd h.2 (hAB u hu)
  have hrev : w'.reverse.IsPath := (Walk.isPath_reverse_iff _).mpr hw'p
  cases hR : w'.reverse with
  | nil => exact ht (by rw [hu0])
  | @cons _ z _ hz W =>
    rw [hR, Walk.cons_isPath_iff] at hrev
    have hWs : ∀ y ∈ W.support, y ∈ w'.support := fun y hy => by
      rw [← List.mem_reverse, ← Walk.support_reverse, hR]; exact List.mem_cons_of_mem _ hy
    have hW0 : ∀ y ∈ W.reverse.support, labS P B y = 0 := fun y hy => by
      rw [Walk.support_reverse, List.mem_reverse] at hy
      by_contra h0
      exact h0 (by_contra fun h => h2 y (hWs y hy) (fun e => hrev.2 (e ▸ hy)) h |>.elim)
    have hzi : z.1 ∈ items := hs.mem_of_walk (List.mem_map_of_mem hu) W.reverse hW0
    exact hs.noHit hh hzi hz.symm ht3

/-! ### The program -/

/-- **Line 6 of Algorithm 5.1.** Label `B` as targets and `P` as forbidden, take `A` as sources,
search; if a target is seen, write the crossing `(P, R)` in `aQ` and `aR` and set `rFound = 1`,
otherwise set `rFound = 0`. -/
def sepProg : Cmd :=
  .seq (.alloc aLab (.reg 40))
    (.seq (markProg rI2 (.op .add (.reg rLenA) (.const 2)) (.len aCyc) aLab aCyc 3)
      (.seq (markProg rI2 (.const 0) (.len aPath) aLab aPath 2)
        (.seq (mapProg rI3 (.reg rLenA) aSrc aCyc (.op .add (.reg rI3) (.const 1)))
          (.seq (searchProg aStart aEnd aEnt)
            (.ite (.op .eq (.reg rHit) (.reg 40)) (.assign rFound (.const 0))
              (.seq (.assign rFound (.const 1))
                (.seq (.write aPar (.reg rHit) (.reg rHitPar))
                  (.seq (traceProg aR rHit) (mapProg rI3 (.len aPath) aQ aPath (.reg rI3))))))))))

/-- The registers that `sepProg` writes. -/
def sepRegs : List ℕ := List.range' 60 39

/-- The arrays that `sepProg` writes. -/
def sepArrs : List ℕ := [aLab, aPar, aQue, aSrc, aQ, aR]

/-- The result of `sepProg`. -/
def SepRes (H : SimpleGraph (Fin n)) {a b : Fin n} (A B : List (Fin n)) (P : H.Walk a b)
    (s : State) : Prop :=
  (s.regs rFound = 0 ∧ Separates H {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}) ∨
    (s.regs rFound = 1 ∧ CrossingAt H (a :: A ++ b :: B) aQ aR s)

theorem map_getD_succ (a b : Fin n) (A B : List (Fin n)) :
    (List.range A.length).map (fun i => ((a :: A ++ b :: B).map Fin.val).getD (i + 1) 0) =
      A.map Fin.val := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp at h₁
  simp only [List.getElem_map, List.getElem_range, List.map_cons, List.map_append, List.getD_cons_succ]
  rw [List.cons_append, List.getD_cons_succ, List.getD_append _ _ _ _ (by simp; omega)]
  simp [h₁]

/-- **The separation test.** In at most `70 + 120 n + 29 m` steps, `sepProg` finds that `P`
separates `A` from `B`, or writes a crossing of `a A b B` in `aQ` and `aR`. -/
theorem sepProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) {a b : Fin n}
    (A B : List (Fin n)) (P : H.Walk a b) (hnd : (a :: A ++ b :: B).Nodup)
    (hP : IsTPath H (a :: A ++ b :: B) P) (hn : 4 * n + 4 < 2 ^ w) (s : State)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aPath = P.support.map Fin.val) (hlenA : s.regs rLenA = A.length)
    (h40 : s.regs 40 = n) (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w) :
    ∃ s' t, Exec w sepProg s s' t ∧ t ≤ 70 + 120 * n + 29 * totalAdjEntries lists ∧
      Keeps sepRegs sepArrs s s' ∧ SepRes H A B P s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set C := a :: A ++ b :: B with hC
  have hkn : C.length ≤ n := by have := hnd.length_le_card; simpa using this
  have hCk : C.length = A.length + B.length + 2 := by simp [C]; omega
  have hPn : P.support.length ≤ n := by
    have := hP.1.support_nodup.length_le_card; simpa using this
  -- Step 1: all labels free.
  set s₁ := s.setArr aLab (List.replicate n 0) with hs₁
  have hex₁ : Exec w (.alloc aLab (.reg 40)) s s₁ (1 + n) := .alloc (reg_eval h40 hnw)
  -- Step 2: `B` are targets.
  have hC2 : (C.take C.length).drop (A.length + 2) = B := by
    rw [List.take_length]; simp [C]
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hlab₂⟩ := markProg_exec rI2 (.op .add (.reg rLenA) (.const 2))
    (.len aCyc) aLab aCyc 3 (by decide) C (fun _ => 0) (A.length + 2) C.length s₁ hw1 hnw
    (by omega) (by omega) le_rfl
    (op_eval (a := A.length) (b := 2) (reg_eval (by simp [s₁, hlenA]) (by omega))
      (by simp [checkWord]; omega)
      (by simp [BinOp.eval, BinOp.raw, checkWord]; omega))
    (fun st hst => by
      simp [Expr.eval, checkWord, hst.2 aCyc (by decide), s₁, hcyc]; omega)
    (by simp [s₁, hcyc, C]) (by simp [s₁, List.ofFn_const])
  rw [hC2] at hlab₂
  have hpath₂ : s₂.arrs aPath = P.support.map Fin.val := by
    rw [hk₂.2 aPath (by decide)]; simp [s₁, hpath]
  -- Step 3: `P` is forbidden.
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hlab₃⟩ := markProg_exec rI2 (.const 0) (.len aPath) aLab aPath 2
    (by decide) P.support (fun v => if v ∈ B then 3 else 0) 0 P.support.length s₂ hw1 hnw
    (by omega) (Nat.zero_le _) le_rfl (by simp [checkWord])
    (fun st hst => by
      show checkWord w (st.arrs aPath).length = _
      rw [hst.2 aPath (by decide), hpath₂, List.length_map]
      simp only [checkWord, show P.support.length < 2 ^ w by omega, if_true])
    hpath₂ hlab₂
  have hlab₃' : s₃.arrs aLab = List.ofFn (labS P B) := by
    rw [hlab₃, List.take_length, List.drop_zero]; rfl
  have hcyc₃ : s₃.arrs aCyc = C.map Fin.val := by
    rw [hk₃.2 aCyc (by decide), hk₂.2 aCyc (by decide)]; simp [s₁, hcyc]
  have hlenA₃ : s₃.regs rLenA = A.length := by
    rw [hk₃.1 rLenA (by decide), hk₂.1 rLenA (by decide)]; simp [s₁, hlenA]
  -- Step 4: the sources `A`.
  have hAn : A.length ≤ n := by omega
  have hCw : ∀ v ∈ C.map Fin.val, v < 2 ^ w := fun v hv => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv; have := z.2; omega
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hsrc₄⟩ := mapProg_exec rI3 (.reg rLenA) aSrc aCyc
    (.op .add (.reg rI3) (.const 1)) (by decide) A.length (fun i => i + 1) (C.map Fin.val) s₃ hw1
    (by omega) (fun st hst => reg_eval (by rw [hst.1 rLenA (by decide)]; exact hlenA₃) (by omega))
    (fun st i hst hri hi => op_eval (a := i) (b := 1) (reg_eval hri (by omega))
      (by simp [checkWord, hw1])
      (by simp [BinOp.eval, BinOp.raw, checkWord]; omega))
    (fun i hi => by simp; omega) hCw hcyc₃
  rw [map_getD_succ] at hsrc₄
  have hk04 : Keeps [rI2, rI3] [aLab, aSrc] s s₄ :=
    ((((Keeps.refl _ _ s).setArr (by simp) _).trans hk₂ (by simp) (by simp)).trans hk₃ (by simp)
      (by simp)).trans hk₄ (by simp) (by simp)
  have hlab₄ : s₄.arrs aLab = List.ofFn (labS P B) := by rw [hk₄.2 aLab (by decide)]; exact hlab₃'
  have hadj₄ : IsAdjList H aStart aEnd aEnt lists s₄ :=
    hadj.of_arrs_eq (hk04.2 _ (by decide)) (hk04.2 _ (by decide)) (hk04.2 _ (by decide))
  have hent₄ : (s₄.arrs aEnt).length < 2 ^ w := by rw [hk04.2 _ (by decide)]; exact hent
  -- Step 5: the search.
  have hlabS : ∀ v, labS P B v ≤ 3 := fun v => by unfold labS; split_ifs <;> omega
  obtain ⟨s₅, t₅, items, hex₅, ht₅, hsi⟩ := searchProg_exec H lists aStart aEnd aEnt
    (by decide) (by decide) (by decide) (labS P B) hlabS (A.map Fin.val)
    (fun x hx => by obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx; exact z.2)
    s₄ hadj₄ hent₄ (by rw [hk04.1 40 (by decide)]; exact h40) hw4 hnw (by simp; omega) hlab₄ hsrc₄
  have h40₅ : s₅.regs 40 = n := by
    rw [hsi.frame.1 40 (by decide), hk04.1 40 (by decide)]; exact h40
  have hk05 : Keeps sepRegs sepArrs s s₅ :=
    ⟨fun r hr => by
      simp only [sepRegs, List.mem_range'_1] at hr
      have hne : ∀ c : ℕ, 60 ≤ c → c < 99 → r ≠ c := fun c h1 h2 e => by omega
      have hlo : r < 60 ∨ 99 ≤ r := by omega
      rw [hsi.frame.1 r (hlo.imp id fun h => le_trans (by decide) h), hk04.1 r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hne _ (by decide) (by decide), hne _ (by decide) (by decide)⟩)],
     fun x hx => by
      simp only [sepArrs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      rw [hsi.frame.2 x hx.1 hx.2.1 hx.2.2.1, hk04.2 x (by simp [hx.1, hx.2.2.2.1])]⟩
  have hhitle : s₅.regs rHit ≤ n := by
    rcases hsi.hit with ⟨h, -⟩ | ⟨v, u, h, -⟩
    · omega
    · rw [h]; exact v.2.le
  have hcond := eq_eval (A := .reg rHit) (B := .reg 40) (reg_eval (r := rHit) (s := s₅) rfl
    (by omega)) (reg_eval h40₅ hnw) hw1
  have hAB : ∀ z, z ∈ A → z ∉ B := fun z hzA hzB => by
    simp only [C, List.cons_append, List.nodup_cons, List.nodup_append, List.mem_cons] at hnd
    exact hnd.2.2.2 z hzA z (Or.inr hzB) rfl
  by_cases hh : s₅.regs rHit = n
  · -- No target seen: `P` separates.
    refine ⟨s₅.setReg rFound 0, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.ite_true hcond (by simp [hh]) (.assign (show (Expr.const 0).eval w s₅ = some 0 by
        simp [checkWord]))))))), ?_, hk05.setReg (by decide) _,
      Or.inl ⟨by simp, separates_of_noHit hnd hsi hh⟩⟩
    simp only [Expr.cost, List.length_map] at ht₂ ht₃ ht₄ ht₅ ⊢
    have := Nat.mul_le_mul_right 11 (show C.length - (A.length + 2) ≤ n by omega)
    have := Nat.mul_le_mul_right 11 (show P.support.length - 0 ≤ n by omega)
    have := Nat.mul_le_mul_right 14 hAn
    omega
  · -- A target seen: the crossing.
    obtain ⟨v, u, hrv, hpu, hLv, hu, huv⟩ := hsi.hit_of_ne hh
    have hvB : v ∈ B ∧ v ∉ P.support := by
      unfold labS at hLv
      by_cases h1 : v ∈ P.support
      · rw [if_pos h1] at hLv; omega
      · rw [if_neg h1] at hLv
        by_cases h2 : v ∈ B
        · exact ⟨h2, h1⟩
        · rw [if_neg h2] at hLv; omega
    have hvi : v.1 ∉ items := fun h => by have := hsi.free v h; omega
    have hvsrc : v.1 ∉ A.map Fin.val := fun h => by
      obtain ⟨z, hz, hzv⟩ := List.mem_map.mp h
      exact hAB z hz (by rw [Fin.ext hzv] at hz ⊢; exact hvB.1)
    obtain ⟨p, hpar, hpok⟩ := hsi.par
    set s₆ := s₅.setReg rFound 1 with hs₆
    have hex₆ : Exec w (.assign rFound (.const 1)) s₅ s₆ (1 + 1) := .assign (by simp [checkWord, hw1])
    set s₇ := s₆.writeArr aPar v.1 u.1 with hs₇
    have hex₇ : Exec w (.write aPar (.reg rHit) (.reg rHitPar)) s₆ s₇ (1 + 1 + 1) :=
      .write (reg_eval (by simp [s₆, hrv]) (by omega)) (reg_eval (by simp [s₆, hpu]) (by omega))
        (by simp [s₆, hpar])
    have hpar₇ : s₇.arrs aPar = List.ofFn (Function.update p v u.1) := by
      simp only [s₇, State.writeArr, State.setArr_arrs, ite_true, s₆, State.setReg_arrs, hpar]
      exact ofFn_set v _
    obtain ⟨s₈, t₈, r, W, hex₈, ht₈, hW, hr, hWs, hns, hout, hreg₈, harr₈⟩ :=
      traceProg_exec (hpok.snoc hvi hvsrc hu huv) hnw aR (by decide) rHit (by decide) (by decide)
        s₇ v (by simp) (by simp [s₇, s₆, hrv]) (by simp [s₇, s₆, h40₅]) hpar₇
    have hrA : r ∈ A := by
      obtain ⟨z, hz, hzr⟩ := List.mem_map.mp hr
      rwa [← Fin.ext hzr]
    have hfree : ∀ y ∈ W.support, y ≠ v → y.1 ∈ items := fun y hy hyv => by
      rcases List.mem_append.mp (hWs y hy) with h | h
      · exact h
      · exact absurd (Fin.ext (by simpa using h)) hyv
    have hoffP : ∀ y ∈ W.support, y ∉ P.support := fun y hy hyP => by
      by_cases hyv : y = v
      · exact hvB.2 (hyv ▸ hyP)
      · have := hsi.free y (hfree y hy hyv)
        simp [labS, hyP] at this
    have hWT : IsTPath H C W := by
      refine ⟨hW, by simp [C, hrA], by simp [C, hvB.1], fun y hy hyr hyv => ?_⟩
      have h0 := hsi.free y (hfree y hy hyv)
      have hyB : y ∉ B := fun hyB => by simp [labS, hyB, hoffP y hy] at h0
      have hyA : y ∉ A := fun hyA => hns y hy hyr (List.mem_map_of_mem hyA)
      have hya : y ≠ a := fun e => hoffP y hy (e ▸ P.start_mem_support)
      have hyb : y ≠ b := fun e => hoffP y hy (e ▸ P.end_mem_support)
      have : y ∉ C := by simp [C, hya, hyb, hyA, hyB]
      exact ⟨this, this⟩
    have hdisj : P.support.Disjoint W.support := fun y hyP hyW => hoffP y hyW hyP
    have hpath₈ : s₈.arrs aPath = P.support.map Fin.val := by
      rw [harr₈ _ (by decide)]
      simp only [s₇, State.writeArr, State.setArr_arrs, s₆, State.setReg_arrs]
      rw [if_neg (by decide), hk05.2 aPath (by decide)]; exact hpath
    have hPw : ∀ x ∈ P.support.map Fin.val, x < 2 ^ w := fun x hx => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx; have := z.2; omega
    obtain ⟨s₉, t₉, hex₉, ht₉, hk₉, hq₉⟩ := mapProg_exec rI3 (.len aPath) aQ aPath (.reg rI3)
      (by decide) P.support.length id (P.support.map Fin.val) s₈ hw1 (by omega)
      (fun st hst => by
        show checkWord w (st.arrs aPath).length = _
        rw [hst.2 aPath (by decide), hpath₈, List.length_map]
        simp only [checkWord, show P.support.length < 2 ^ w by omega, if_true])
      (fun st i hst hri hi => reg_eval hri (show i < 2 ^ w by omega))
      (fun i hi => by simpa using hi) hPw hpath₈
    simp only [id] at hq₉
    rw [← List.length_map (f := Fin.val), map_getD_self] at hq₉
    have hk78 : Keeps sepRegs sepArrs s₇ s₈ :=
      ⟨fun r' hr' => hreg₈ r' (fun e => hr' (by rw [e]; decide)) (fun e => hr' (by rw [e]; decide)),
       fun x hx => harr₈ x (fun e => hx (by rw [e]; decide))⟩
    have hk09 : Keeps sepRegs sepArrs s s₉ :=
      ((((hk05.setReg (by decide) _).writeArr (by decide) _ _).trans hk78 (fun _ h => h)
        (fun _ h => h)).trans hk₉ (by decide) (by decide))
    refine ⟨s₉, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.ite_false
      (by rw [hcond, if_neg hh]) (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉)))))))), ?_, hk09,
      Or.inr ⟨?_, a, b, r, v, P, W, isCrossing_of_split hrA hvB.1 P W hP hWT hdisj, hq₉, ?_⟩⟩
    · simp only [Expr.cost, List.length_map] at ht₂ ht₃ ht₄ ht₅ ht₉ ⊢
      have := Nat.mul_le_mul_right 11 (show C.length - (A.length + 2) ≤ n by omega)
      have := Nat.mul_le_mul_right 11 (show P.support.length - 0 ≤ n by omega)
      have := Nat.mul_le_mul_right 14 hAn
      have := Nat.mul_le_mul_right 12 hPn
      omega
    · rw [hk₉.1 rFound (by decide), hreg₈ _ (by decide) (by decide)]; simp [s₇, s₆]
    · rw [hk₉.2 aR (by decide)]; exact hout

end GraphMinor.Compute.TwoPaths
