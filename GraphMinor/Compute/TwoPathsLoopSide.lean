module

public import GraphMinor.Compute.TwoPathsChild
public import GraphMinor.Compute.TwoPathsLoopMath

/-!
# Computing the sides of the vertices of the current path

In each step of the loop of Algorithm 5.2 (Humeau and Pous, page 23), we need to know for each
vertex of the current path `P` (stored in `aNewPath`) whether it lies on side `A` and whether it
lies on side `B`. Since every added edge in `F` has both endpoints on `P`, the sides of every vertex
of `P` in `H ⊔ pairGraph N F` are the same as in `H` (`isOnSide_iff_of_edges_in_path`), so the
program searches `H` directly without building `H + F`.

For an arc `S` of `C = a :: A ++ b :: B` (`S = A` at slice `[1, |A| + 1)` or `S = B` at slice
`[|A| + 2, |C|)` of `aCyc`), `arcSideProg lo hi aOut`:
1. allocates `aLab` of size `N` (`0`), marks `C` (`aCyc`) and `P` (`aNewPath`) as `2` (forbidden),
   and marks `S` (`aCyc[lo .. hi)`) back to `0` (free), producing `labArc C Pv S`;
2. copies `S` (`aCyc[lo .. hi)`) into `aSrc` using `appProg`;
3. runs `searchProg aStart aEnd aEnt` on `H`, which starts at `S` and never enters `C` or `P`;
4. scans the adjacency list in `H` of each vertex `Pv[i]` of `aNewPath` and writes `1` to `aOut[i]`
   if `Pv[i]` has a reached neighbour (`aLab[y] = 1`) and `0` otherwise.

By `isOnSide_iff_exists_adj_items`, `aOut` ends equal to `Pv.map (sideBit H C Pv S)`.
`bothSidesProg` runs `arcSideProg` for `A` into `aOnA` and for `B` into `aOnB` in `O(N + M)` steps.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25
open scoped BigOperators

variable {N : ℕ}

/-! ### Scratch arrays and bit values -/

/-- Array holding `1` at index `i` if `Pv[i]` is on side `A`, else `0`. -/
abbrev aOnA : Arr := 65
/-- Array holding `1` at index `i` if `Pv[i]` is on side `B`, else `0`. -/
abbrev aOnB : Arr := 66

/-- `1` if `v` is on side `S` of `C ∪ Pv` in `H`, else `0`. -/
noncomputable def sideBit (H : SimpleGraph (Fin N)) (C Pv S : List (Fin N)) (v : Fin N) : ℕ := by
  classical
  exact if IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v then 1 else 0

theorem sideBit_le_one (H : SimpleGraph (Fin N)) (C Pv S : List (Fin N)) (v : Fin N) :
    sideBit H C Pv S v ≤ 1 := by
  unfold sideBit; split_ifs <;> omega

theorem sideBit_eq_one_iff {H : SimpleGraph (Fin N)} {C Pv S : List (Fin N)} {v : Fin N} :
    sideBit H C Pv S v = 1 ↔ IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v := by
  unfold sideBit; split_ifs with h <;> simp [h]

theorem sideBit_eq_zero_iff {H : SimpleGraph (Fin N)} {C Pv S : List (Fin N)} {v : Fin N} :
    sideBit H C Pv S v = 0 ↔ ¬ IsOnSide H {x | x ∈ C ∨ x ∈ Pv} {x | x ∈ S} v := by
  unfold sideBit; split_ifs with h <;> simp [h]

theorem range_map_getD_eq_map {α β : Type*} (L : List α) (d : α) (f : α → β) :
    (List.range L.length).map (fun i => f (L.getD i d)) = L.map f := by
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp at h₁
  simp [h₁]

theorem len_eval_map {w : ℕ} {s : State} {a : Arr} {L : List (Fin N)}
    (ha : s.arrs a = L.map Fin.val) (hl : L.length < 2 ^ w) :
    (Expr.len a).eval w s = some L.length := by
  simp [Expr.eval, checkWord, ha, hl]

/-! ### Scanning the neighbours of each vertex of `P` -/

/-- Inner body of the neighbour scan: if `aLab[rY] == 1`, set `rFound := 1`. -/
def adjMarkBody : Cmd :=
  .ite (.op .eq (.read aLab (.reg rY)) (.const 1))
    (.assign rFound (.const 1))
    .skip

/-- Outer body of the neighbour scan for vertex `aNewPath[rI2]`: scan its neighbours in `H` and
write `rFound` into `aOut[rI2]`. -/
def adjMarkOuter (aOut : Arr) : Cmd :=
  .seq (.assign rX2 (.read aNewPath (.reg rI2)))
    (.seq (.assign rFound (.const 0))
      (.seq (forList aStart aEnd aEnt rX2 rK2 rHi2 rY adjMarkBody)
        (.write aOut (.reg rI2) (.reg rFound))))

/-- Scan all vertices of `aNewPath` and write their side bits into `aOut`. -/
def adjMarkProg (aOut : Arr) : Cmd :=
  .seq (.alloc aOut (.len aNewPath))
    (.seq (.assign rI2 (.const 0))
      (forUp rI2 (.len aNewPath) (adjMarkOuter aOut)))

/-- One step of `adjMarkBody`. -/
theorem adjMarkBody_exec {w : ℕ} {C Pv S : List (Fin N)} {items : List ℕ}
    (hn : N < 2 ^ w) (hw : 3 < 2 ^ w) (y : ℕ) (hy : y < N) {P_prev : Prop} [Decidable P_prev]
    {s : State}
    (hlab : s.arrs aLab = List.ofFn (fun x : Fin N => if x.1 ∈ items then 1 else labArc C Pv S x))
    (hrY : s.regs rY = y) (hrF : s.regs rFound = if P_prev then 1 else 0) :
    ∃ s' t, Exec w adjMarkBody s s' t ∧ t ≤ 9 ∧
      Keeps [rFound] [] s s' ∧
      s'.regs rFound = if P_prev ∨ y ∈ items then 1 else 0 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hyw : y < 2 ^ w := lt_trans hy hn
  have hval : (if y ∈ items then 1 else labArc C Pv S ⟨y, hy⟩) < 2 ^ w := by
    split_ifs
    · exact hw1
    · have := labArc_le_three C Pv S ⟨y, hy⟩; omega
  have hread : (Expr.read aLab (.reg rY)).eval w s =
      some (if y ∈ items then 1 else labArc C Pv S ⟨y, hy⟩) := by
    rw [read_eval (reg_eval hrY hyw) (by rw [hlab]; simpa using hy)]
    · simp [hlab]
    · simp [hlab, hval]
  have hnot1 : labArc C Pv S ⟨y, hy⟩ ≠ 1 := by
    unfold labArc; split_ifs <;> decide
  by_cases hyi : y ∈ items
  · have hcond : (Expr.op .eq (.read aLab (.reg rY)) (.const 1)).eval w s = some 1 := by
      have := eq_eval hread (const_eval' hw1) hw1
      simpa [hyi] using this
    refine ⟨s.setReg rFound 1, _, .ite_true hcond one_ne_zero (.assign (const_eval' hw1)),
      by simp [Expr.cost], (Keeps.refl _ _ s).setReg (by simp) _, by simp [hyi]⟩
  · have hcond : (Expr.op .eq (.read aLab (.reg rY)) (.const 1)).eval w s = some 0 := by
      have := eq_eval hread (const_eval' hw1) hw1
      simpa [hyi, hnot1] using this
    refine ⟨s, _, .ite_false hcond (.skip _), by simp [Expr.cost], Keeps.refl _ _ s,
      by simp [hyi, hrF]⟩

/-- One outer step `adjMarkOuter aOut` at index `i < Pv.length`. -/
theorem adjMarkOuter_exec {w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {C Pv S : List (Fin N)} {d : Fin N} {items : List ℕ} {aOut : Arr}
    (haOut : aOut = aOnA ∨ aOut = aOnB)
    (hSP : ∀ x ∈ S, x ∉ Pv) {s_init s₀ s : State}
    (hs : SInv H (labArc C Pv S) (S.map Fin.val) s_init items items.length s₀)
    (hadj : IsAdjList H aStart aEnd aEnt lists s₀)
    (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hpath : s₀.arrs aNewPath = Pv.map Fin.val)
    (hn : 4 * N + 4 < 2 ^ w)
    (i : ℕ) (hi : i < Pv.length) (hPn : Pv.length ≤ N)
    (hk : Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ s)
    (hri : s.regs rI2 = i)
    (hout : s.arrs aOut = (List.range i).map (fun j => sideBit H C Pv S (Pv.getD j d)) ++
      List.replicate (Pv.length - i) 0) :
    ∃ s' t, Exec w (adjMarkOuter aOut) s s' t ∧
      t ≤ 17 + 20 * (lists Pv[i]).length ∧
      Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ s' ∧
      s'.regs rI2 = i ∧
      s'.arrs aOut = (List.range (i + 1)).map (fun j => sideBit H C Pv S (Pv.getD j d)) ++
        List.replicate (Pv.length - (i + 1)) 0 := by
  classical
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  have hiw : i < 2 ^ w := by omega
  set x := Pv[i] with hx
  have hxw : x.1 < 2 ^ w := lt_trans x.2 hnw
  have hne_out : ∀ a, a ∈ ([aStart, aEnd, aEnt, aNewPath, aLab] : List Arr) → a ≠ aOut := by
    rcases haOut with rfl | rfl <;> decide
  have hpath_s : s.arrs aNewPath = Pv.map Fin.val := by
    rw [hk.2 aNewPath (by simp [hne_out aNewPath (by decide)])]; exact hpath
  have hread_x : (Expr.read aNewPath (.reg rI2)).eval w s = some x.1 := by
    rw [read_eval (reg_eval hri hiw) (by rw [hpath_s]; simpa using hi)]
    · simp [hpath_s, x]
    · simp [hpath_s, x, hxw]
  set s₁ := s.setReg rX2 x.1 with hs₁
  have hex₁ : Exec w (.assign rX2 (.read aNewPath (.reg rI2))) s s₁ (1 + 1 + 1) :=
    .assign hread_x
  set s₂ := s₁.setReg rFound 0 with hs₂
  have hex₂ : Exec w (.assign rFound (.const 0)) s₁ s₂ (1 + 1) :=
    .assign (const_eval' (by omega))
  obtain ⟨st, en, hlist₀⟩ := hadj.1.2.2 x
  obtain ⟨hmem_lt, -, -, hadj_iff⟩ := hadj.2 x
  have hen_w : en < 2 ^ w := by
    obtain ⟨_, _, hle, _⟩ := hlist₀
    omega
  let II : ℕ → State → Prop := fun j st' =>
    Keeps [rK2, rHi2, rY, rFound] [] s₂ st' ∧
    st'.regs rFound = if ∃ y ∈ (lists x).take j, y ∈ items then 1 else 0
  have hII0 : II 0 s₂ := ⟨Keeps.refl _ _ s₂, by simp [s₂]⟩
  have hlist_of : ∀ st', Keeps [rK2, rHi2, rY, rFound] [] s₂ st' →
      IsListAt aStart aEnd aEnt x.1 st en (lists x) st' := by
    intro st' hst'
    have hk_all : Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ st' :=
      ((hk.setReg (by simp) _).setReg (by simp) _).trans hst' (by decide) (by simp)
    exact hlist₀.of_arrs_eq
      (hk_all.2 aStart (by simp [hne_out aStart (by decide)]))
      (hk_all.2 aEnd (by simp [hne_out aEnd (by decide)]))
      (hk_all.2 aEnt (by simp [hne_out aEnt (by decide)]))
  have hfor := Triple.forList_const aStart aEnd aEnt rX2 rK2 rHi2 rY x.1 st en (lists x) II 9
    adjMarkBody (by decide) (by decide) hw1 hxw hen_w
    (fun z hz => lt_trans (hmem_lt z hz) hnw)
    (fun st' hst' => ⟨hlist_of st' hst'.1, by rw [hst'.1.1 rX2 (by decide)]; simp [s₂, s₁],
      (hst'.1.setReg (by decide) _).setReg (by decide) _, by simp [hst'.2]⟩)
    (fun j _ st' hst' => hlist_of st' hst'.1)
    (fun j hj sv ⟨st', hI, hsv, hrk, hrhi⟩ => by
      subst hsv
      obtain ⟨hk', hrF⟩ := hI
      have hy_lt : (lists x)[j] < N := hmem_lt _ (List.getElem_mem hj)
      have hlab_st' : (st'.setReg rY (lists x)[j]).arrs aLab =
          List.ofFn (fun z : Fin N => if z.1 ∈ items then 1 else labArc C Pv S z) := by
        simp only [State.setReg_arrs]
        rw [hk'.2 aLab (by decide)]
        simp only [s₂, s₁, State.setReg_arrs]
        rw [hk.2 aLab (by simp [hne_out aLab (by decide)])]
        exact hs.lab
      obtain ⟨s', t, hex, ht, hk'', hrF'⟩ :=
        adjMarkBody_exec hnw (by omega) (lists x)[j] hy_lt
          (P_prev := ∃ y ∈ (lists x).take j, y ∈ items)
          (s := st'.setReg rY (lists x)[j]) hlab_st' (by simp) (by simp [hrF])
      have htake : (∃ y ∈ (lists x).take (j + 1), y ∈ items) ↔
          (∃ y ∈ (lists x).take j, y ∈ items) ∨ (lists x)[j] ∈ items := by
        rw [take_succ_eq hj]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨y, hy | rfl, hyi⟩
          · exact Or.inl ⟨y, hy, hyi⟩
          · exact Or.inr hyi
        · rintro (⟨y, hy, hyi⟩ | hyi)
          · exact ⟨y, Or.inl hy, hyi⟩
          · exact ⟨(lists x)[j], Or.inr rfl, hyi⟩
      have hk_step : Keeps [rK2, rHi2, rY, rFound] [] s₂ s' :=
        (hk'.setReg (by decide) _).trans hk'' (by decide) (by decide)
      refine ⟨s', t, hex, ht, ⟨hk_step.setReg (by decide) _, ?_⟩,
        by rw [hk''.1 rK2 (by decide)]; simpa using hrk,
        by rw [hk''.1 rHi2 (by decide)]; simpa using hrhi⟩
      simp only [State.setReg_regs_ne _ _ (show rFound ≠ rK2 by decide), hrF', htake])
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hrF₃⟩ := hfor s₂ hII0
  rw [List.take_length] at hrF₃
  have hiff : (∃ y ∈ lists x, y ∈ items) ↔
      IsOnSide H {z | z ∈ C ∨ z ∈ Pv} {z | z ∈ S} x := by
    rw [isOnSide_iff_exists_adj_items hSP hs (List.getElem_mem hi)]
    constructor
    · rintro ⟨y, hy, hyi⟩
      have hyN : y < N := hmem_lt y hy
      exact ⟨⟨y, hyN⟩, (hadj_iff ⟨y, hyN⟩).mp hy, hyi⟩
    · rintro ⟨w, hadj_w, hwi⟩
      exact ⟨w.1, (hadj_iff w).mpr hadj_w, hwi⟩
  have hrF_bit : s₃.regs rFound = sideBit H C Pv S x := by
    simp only [hrF₃, sideBit, hiff]
  have hri₃ : s₃.regs rI2 = i := by
    rw [hk₃.1 rI2 (by decide)]; simp [s₂, s₁, hri]
  have hout₃ : s₃.arrs aOut = (List.range i).map (fun j => sideBit H C Pv S (Pv.getD j d)) ++
      List.replicate (Pv.length - i) 0 := by
    rw [hk₃.2 aOut (by simp)]; simp [s₂, s₁, hout]
  have hbit_lt : sideBit H C Pv S x < 2 ^ w := by
    have := sideBit_le_one H C Pv S x; omega
  set s₄ := s₃.writeArr aOut i (sideBit H C Pv S x) with hs₄
  have hex₄ : Exec w (.write aOut (.reg rI2) (.reg rFound)) s₃ s₄ (1 + 1 + 1) :=
    .write (reg_eval hri₃ hiw) (reg_eval hrF_bit hbit_lt) (by rw [hout₃]; simp; omega)
  have hk_all : Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ s₄ :=
    (((hk.setReg (by simp) _).setReg (by simp) _).trans hk₃ (by decide) (by simp)).writeArr
      (by simp) _ _
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by dsimp only at ht₃; omega, hk_all, by simp [s₄, hri₃], ?_⟩
  simp only [s₄, State.writeArr_arrs_self, hout₃]
  have hgetD : sideBit H C Pv S x = sideBit H C Pv S (Pv.getD i d) := by
    simp [x, List.getD_eq_getElem?_getD, hi]
  rw [hgetD]
  exact set_range_map (fun j => sideBit H C Pv S (Pv.getD j d)) hi

/-- Full execution of `adjMarkProg aOut`: writes `Pv.map (sideBit H C Pv S)` into `aOut`. -/
theorem adjMarkProg_exec {w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {C Pv S : List (Fin N)} {items : List ℕ} {aOut : Arr}
    (haOut : aOut = aOnA ∨ aOut = aOnB) (hPv_nd : Pv.Nodup) (hPv_ne : Pv ≠ [])
    (hSP : ∀ x ∈ S, x ∉ Pv) {s_init s₀ : State}
    (hs : SInv H (labArc C Pv S) (S.map Fin.val) s_init items items.length s₀)
    (hadj : IsAdjList H aStart aEnd aEnt lists s₀)
    (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hpath : s₀.arrs aNewPath = Pv.map Fin.val)
    (hn : 4 * N + 4 < 2 ^ w) :
    ∃ s' t, Exec w (adjMarkProg aOut) s₀ s' t ∧
      t ≤ 8 + 25 * N + 20 * totalAdjEntries lists ∧
      Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ s' ∧
      s'.arrs aOut = Pv.map (sideBit H C Pv S) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hPn : Pv.length ≤ N := by have := hPv_nd.length_le_card; simpa using this
  have hPw : Pv.length < 2 ^ w := by omega
  have hne_path : aNewPath ≠ aOut := by rcases haOut with rfl | rfl <;> decide
  set d := Pv[0]'(List.length_pos_of_ne_nil hPv_ne)
  set g : ℕ → ℕ := fun j => sideBit H C Pv S (Pv.getD j d)
  set s₁ := s₀.setArr aOut (List.replicate Pv.length 0) with hs₁
  have hex₁ : Exec w (.alloc aOut (.len aNewPath)) s₀ s₁ (1 + Pv.length) :=
    .alloc (len_eval_map hpath hPw)
  set s₂ := s₁.setReg rI2 0 with hs₂
  have hex₂ : Exec w (.assign rI2 (.const 0)) s₁ s₂ (1 + 1) :=
    .assign (const_eval' (by omega))
  let OI : ℕ → State → Prop := fun i st =>
    Keeps [rI2, rX2, rK2, rHi2, rY, rFound] [aOut] s₀ st ∧
    st.regs rI2 = i ∧
    st.arrs aOut = (List.range i).map g ++ List.replicate (Pv.length - i) 0
  have hOI0 : OI 0 s₂ := ⟨((Keeps.refl _ _ s₀).setArr (by simp) _).setReg (by simp) _,
    by simp [s₂], by simp [s₂, s₁]⟩
  have hloop := Triple.forUp_sum OI Pv.length
    (fun i => 17 + 20 * degOf lists ((Pv.map Fin.val).getD i 0))
    (r_i := rI2) (hi := .len aNewPath) (body := adjMarkOuter aOut) (w := w) hw1 hPw
    (fun i _ st hst => ⟨hst.2.1, len_eval_map (by rw [hst.1.2 aNewPath (by simp [hne_path])]; exact hpath) hPw⟩)
    (fun i hi st hst => by
      obtain ⟨s', t, hex, ht, hk', hri', hout''⟩ :=
        adjMarkOuter_exec (d := d) haOut hSP hs hadj hent hpath hn i hi hPn hst.1 hst.2.1 hst.2.2
      refine ⟨s', t, hex, ?_, ⟨hk'.setReg (by simp) _, by simp, hout''⟩, hri'⟩
      have hd : degOf lists ((Pv.map Fin.val).getD i 0) = (lists Pv[i]).length := by
        simp [degOf, List.getD_eq_getElem?_getD, hi]
      show t ≤ 17 + 20 * degOf lists ((Pv.map Fin.val).getD i 0)
      rw [hd]; exact ht)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hout₃⟩ := hloop s₂ hOI0
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, ?_⟩
  · have hsum := sum_deg_cycle_le lists hPv_nd
    simp only [Expr.cost] at ht₃
    have e : ∑ j ∈ Finset.range Pv.length, (1 + 6 + (17 + 20 * degOf lists
        ((Pv.map Fin.val).getD j 0))) = 24 * Pv.length + 20 * ∑ j ∈ Finset.range Pv.length,
          degOf lists ((Pv.map Fin.val).getD j 0) := by
      rw [Finset.mul_sum, show 24 * Pv.length = ∑ _j ∈ Finset.range Pv.length, 24 by simp [mul_comm],
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e] at ht₃
    omega
  · rw [Nat.sub_self, List.replicate_zero, List.append_nil] at hout₃
    rw [hout₃]
    exact range_map_getD_eq_map Pv d (sideBit H C Pv S)

/-! ### Full search and side marking for one arc -/

/-- Compute `sideBit H C Pv S` for every vertex of `aNewPath` (`Pv`) into `aOut`, where `S` is the
slice `aCyc[lo .. hi)`. -/
def arcSideProg (lo hi : Expr) (aOut : Arr) : Cmd :=
  .seq (.alloc aLab (.reg 40))
    (.seq (markProg rI2 (.const 0) (.len aCyc) aLab aCyc 2)
      (.seq (markProg rI2 (.const 0) (.len aNewPath) aLab aNewPath 2)
        (.seq (markProg rI2 lo hi aLab aCyc 0)
          (.seq (.alloc aSrc (.op .sub hi lo))
            (.seq (.assign rAp (.const 0))
              (.seq (appProg rI3 rAp lo hi aSrc aCyc (.reg rI3))
                (.seq (searchProg aStart aEnd aEnt)
                  (adjMarkProg aOut))))))))

/-- Registers modified by `arcSideProg` and `bothSidesProg`. -/
def loopSideRegs : List ℕ := List.range' 60 60

/-- Arrays modified by `arcSideProg` and `bothSidesProg`. -/
def loopSideArrs : List ℕ := [aLab, aPar, aQue, aSrc, aOnA, aOnB]

/-- Execution of `arcSideProg lo hi aOut` for a slice `S = (C.take vhi).drop vlo` of `C`. -/
theorem arcSideProg_exec {w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {C Pv : List (Fin N)} {lo hi : Expr} {vlo vhi : ℕ} {aOut : Arr}
    (haOut : aOut = aOnA ∨ aOut = aOnB)
    (hCn : C.length ≤ N) (hPv_nd : Pv.Nodup) (hPv_ne : Pv ≠ [])
    (hle : vlo ≤ vhi) (hhiC : vhi ≤ C.length)
    (hSP : ∀ x ∈ (C.take vhi).drop vlo, x ∉ Pv)
    (hlo_cost : lo.cost ≤ 4) (hhi_cost : hi.cost ≤ 4)
    {s : State}
    (hlo : ∀ st, Keeps loopSideRegs [aLab, aSrc] s st → lo.eval w st = some vlo)
    (hhi : ∀ st, Keeps loopSideRegs [aLab, aSrc] s st → hi.eval w st = some vhi)
    (h40 : s.regs 40 = N)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcyc : s.arrs aCyc = C.map Fin.val)
    (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hn : 4 * N + 4 < 2 ^ w) :
    ∃ s' t, Exec w (arcSideProg lo hi aOut) s s' t ∧
      t ≤ 100 + 140 * N + 49 * totalAdjEntries lists ∧
      Keeps loopSideRegs [aLab, aPar, aQue, aSrc, aOut] s s' ∧
      s'.arrs aOut = Pv.map (sideBit H C Pv ((C.take vhi).drop vlo)) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : N < 2 ^ w := by omega
  have hPn : Pv.length ≤ N := by have := hPv_nd.length_le_card; simpa using this
  set S := (C.take vhi).drop vlo with hS
  -- Step 1: alloc aLab
  set s₁ := s.setArr aLab (List.replicate N 0) with hs₁
  have hex₁ : Exec w (.alloc aLab (.reg 40)) s s₁ (1 + N) := .alloc (reg_eval h40 hnw)
  have hk₁ : Keeps loopSideRegs [aLab, aSrc] s s₁ := (Keeps.refl _ _ s).setArr (by decide) _
  -- Step 2: mark C as 2
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hlab₂⟩ := markProg_exec rI2 (.const 0) (.len aCyc) aLab aCyc 2
    (by decide) C (fun _ => 0) 0 C.length s₁ hw1 hnw (by omega) (Nat.zero_le _) le_rfl
    (const_eval' (by omega))
    (fun st hst => len_eval_map (by rw [hst.2 aCyc (by decide), hk₁.2 aCyc (by decide)]; exact hcyc)
      (by omega))
    (by rw [hk₁.2 aCyc (by decide)]; exact hcyc) (by simp [s₁, List.ofFn_const])
  rw [List.take_length, List.drop_zero] at hlab₂
  have hk₁₂ : Keeps loopSideRegs [aLab, aSrc] s s₂ := hk₁.trans hk₂ (by decide) (by decide)
  -- Step 3: mark Pv as 2
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hlab₃⟩ := markProg_exec rI2 (.const 0) (.len aNewPath) aLab
    aNewPath 2 (by decide) Pv (fun v => if v ∈ C then 2 else 0) 0 Pv.length s₂ hw1 hnw (by omega)
    (Nat.zero_le _) le_rfl (const_eval' (by omega))
    (fun st hst => len_eval_map (by rw [hst.2 aNewPath (by decide), hk₁₂.2 aNewPath (by decide)]; exact hpath)
      (by omega))
    (by rw [hk₁₂.2 aNewPath (by decide)]; exact hpath) hlab₂
  rw [List.take_length, List.drop_zero] at hlab₃
  have hk₁₃ : Keeps loopSideRegs [aLab, aSrc] s s₃ := hk₁₂.trans hk₃ (by decide) (by decide)
  -- Step 4: mark S as 0
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hlab₄⟩ := markProg_exec rI2 lo hi aLab aCyc 0 (by decide)
    C (fun v => if v ∈ Pv then 2 else if v ∈ C then 2 else 0) vlo vhi s₃ hw1 hnw (by omega)
    hle hhiC (hlo s₃ hk₁₃)
    (fun st hst => hhi st (hk₁₃.trans hst (by decide) (by decide)))
    (by rw [hk₁₃.2 aCyc (by decide)]; exact hcyc) hlab₃
  have hlab₄' : s₄.arrs aLab = List.ofFn (labArc C Pv S) := hlab₄
  have hk₁₄ : Keeps loopSideRegs [aLab, aSrc] s s₄ := hk₁₃.trans hk₄ (by decide) (by decide)
  -- Step 5: alloc aSrc and copy S into aSrc
  have hsub_eval : (Expr.op .sub hi lo).eval w s₄ = some (vhi - vlo) :=
    sub_eval (hhi s₄ hk₁₄) (hlo s₄ hk₁₄)
  set s₅ := s₄.setArr aSrc (List.replicate (vhi - vlo) 0) with hs₅
  have hex₅ : Exec w (.alloc aSrc (.op .sub hi lo)) s₄ s₅ ((hi.cost + lo.cost + 1) + (vhi - vlo)) :=
    .alloc hsub_eval
  set s₆ := s₅.setReg rAp 0 with hs₆
  have hex₆ : Exec w (.assign rAp (.const 0)) s₅ s₆ (1 + 1) := .assign (const_eval' (by omega))
  have hk₁₆ : Keeps loopSideRegs [aLab, aSrc] s s₆ :=
    (hk₁₄.setArr (by decide) _).setReg (by decide) _
  have hCw : ∀ v ∈ C.map Fin.val, v < 2 ^ w := fun v hv => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.mp hv; exact lt_trans z.2 hnw
  obtain ⟨s₇, t₇, hex₇, ht₇, hk₇, -, hsrc₇⟩ := appProg_exec rI3 rAp lo hi aSrc aCyc (.reg rI3)
    (by decide) (by decide) (C.map Fin.val) [] (List.replicate (vhi - vlo) 0) (fun i => i) vlo vhi s₆ hw1
    hle (by simp) (by simp; omega) (by omega) (hlo s₆ hk₁₆)
    (fun st hst => hhi st (hk₁₆.trans hst (by decide) (by decide)))
    (fun _ i _ hri _ _ => reg_eval hri (by omega))
    (fun i _ hi' => by simp; omega) hCw
    (by rw [hk₁₆.2 aCyc (by decide)]; exact hcyc) (by simp [s₆, s₅]) (by simp [s₆])
  have hsrc₇' : s₇.arrs aSrc = S.map Fin.val := by
    rw [hsrc₇, List.nil_append, List.drop_replicate, Nat.sub_self, List.replicate_zero,
      List.append_nil, map_range'_getD (C.map Fin.val) vlo (vhi - vlo) (by simp; omega),
      ← List.map_drop, ← List.map_take, ← List.drop_take]
  have hk₁₇ : Keeps loopSideRegs [aLab, aSrc] s s₇ := hk₁₆.trans hk₇ (by decide) (by decide)
  have hlab₇ : s₇.arrs aLab = List.ofFn (labArc C Pv S) := by
    rw [hk₇.2 aLab (by decide)]; simp [s₆, s₅, hlab₄']
  have hadj₇ : IsAdjList H aStart aEnd aEnt lists s₇ :=
    hadj.of_arrs_eq (hk₁₇.2 aStart (by decide)) (hk₁₇.2 aEnd (by decide))
      (hk₁₇.2 aEnt (by decide))
  have hent₇ : (s₇.arrs aEnt).length < 2 ^ w := by rw [hk₁₇.2 aEnt (by decide)]; exact hent
  -- Step 6: searchProg
  have hSLen : S.length ≤ N := by simp [S]; omega
  obtain ⟨s₈, t₈, items, hex₈, ht₈, hsi⟩ := searchProg_exec H lists aStart aEnd aEnt
    (by decide) (by decide) (by decide) (labArc C Pv S) (labArc_le_three C Pv S) (S.map Fin.val)
    (fun x hx => by obtain ⟨z, -, rfl⟩ := List.mem_map.mp hx; exact z.2)
    s₇ hadj₇ hent₇ (by rw [hk₁₇.1 40 (by decide)]; exact h40) hw4 hnw (by simp; omega) hlab₇ hsrc₇'
  have hk₁₈ : Keeps loopSideRegs [aLab, aPar, aQue, aSrc, aOut] s s₈ :=
    (hk₁₇.mono (by decide) (by rcases haOut with rfl | rfl <;> decide)).trans hsi.frame.keeps
      (by decide) (by rcases haOut with rfl | rfl <;> decide)
  -- Step 7: adjMarkProg
  have hadj₈ : IsAdjList H aStart aEnd aEnt lists s₈ :=
    hadj.of_arrs_eq (hk₁₈.2 aStart (by rcases haOut with rfl | rfl <;> decide))
      (hk₁₈.2 aEnd (by rcases haOut with rfl | rfl <;> decide))
      (hk₁₈.2 aEnt (by rcases haOut with rfl | rfl <;> decide))
  have hent₈ : (s₈.arrs aEnt).length < 2 ^ w := by
    rw [hk₁₈.2 aEnt (by rcases haOut with rfl | rfl <;> decide)]; exact hent
  have hpath₈ : s₈.arrs aNewPath = Pv.map Fin.val := by
    rw [hk₁₈.2 aNewPath (by rcases haOut with rfl | rfl <;> decide)]; exact hpath
  obtain ⟨s₉, t₉, hex₉, ht₉, hk₉, hout₉⟩ :=
    adjMarkProg_exec haOut hPv_nd hPv_ne hSP hsi hadj₈ hent₈ hpath₈ hn
  have hk_fin : Keeps loopSideRegs [aLab, aPar, aQue, aSrc, aOut] s s₉ :=
    hk₁₈.trans hk₉ (by decide) (by rcases haOut with rfl | rfl <;> decide)
  refine ⟨s₉, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
    (.seq hex₇ (.seq hex₈ hex₉))))))), ?_, hk_fin, hout₉⟩
  simp only [Expr.cost, List.length_map] at ht₂ ht₃ ht₄ ht₇ ht₈
  have ht₄' : (vhi - vlo) * (hi.cost + 10) ≤ N * 14 :=
    Nat.mul_le_mul (by omega) (by omega)
  have ht₇' : (vhi - vlo) * (hi.cost + 1 + 13) ≤ N * 18 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

/-- Compute the sides `A` (`aOnA`) and `B` (`aOnB`) of all vertices of `aNewPath` (`Pv`). -/
def bothSidesProg : Cmd :=
  .seq (arcSideProg (.const 1) (.op .add (.reg rLenA) (.const 1)) aOnA)
    (arcSideProg (.op .add (.reg rLenA) (.const 2)) (.len aCyc) aOnB)

theorem drop_take_arcA (a b : Fin N) (A B : List (Fin N)) :
    ((a :: A ++ b :: B).take (A.length + 1)).drop 1 = A := by
  simp

theorem drop_take_arcB (a b : Fin N) (A B : List (Fin N)) :
    ((a :: A ++ b :: B).take (a :: A ++ b :: B).length).drop (A.length + 2) = B := by
  rw [List.take_length]
  rw [show a :: A ++ b :: B = (a :: A ++ [b]) ++ B by simp,
    show A.length + 2 = (a :: A ++ [b]).length by simp, List.drop_left]

/-- **Computing both sides.** In at most `200 + 280 N + 98 M` steps (`M` the number of adjacency
entries of `H`), `bothSidesProg` writes `Pv.map (sideBit H C Pv A)` into `aOnA` and
`Pv.map (sideBit H C Pv B)` into `aOnB`. -/
theorem bothSidesProg_exec {w : ℕ} {H : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {a b : Fin N} {A B Pv : List (Fin N)}
    (hC_nd : (a :: A ++ b :: B).Nodup) (hPv_nd : Pv.Nodup) (hPv_ne : Pv ≠ [])
    (hAP : ∀ x ∈ A, x ∉ Pv) (hBP : ∀ x ∈ B, x ∉ Pv)
    {s : State}
    (h40 : s.regs 40 = N) (hlenA : s.regs rLenA = A.length)
    (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hent : (s.arrs aEnt).length < 2 ^ w)
    (hcyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val)
    (hpath : s.arrs aNewPath = Pv.map Fin.val)
    (hn : 4 * N + 4 < 2 ^ w) :
    ∃ s' t, Exec w bothSidesProg s s' t ∧
      t ≤ 200 + 280 * N + 98 * totalAdjEntries lists ∧
      Keeps loopSideRegs loopSideArrs s s' ∧
      s'.arrs aOnA = Pv.map (sideBit H (a :: A ++ b :: B) Pv A) ∧
      s'.arrs aOnB = Pv.map (sideBit H (a :: A ++ b :: B) Pv B) := by
  have hw1 : 1 < 2 ^ w := by omega
  set C := a :: A ++ b :: B with hC
  have hCn : C.length ≤ N := by have := hC_nd.length_le_card; simpa using this
  have hClen : C.length = A.length + B.length + 2 := by simp [C]; omega
  -- First arc: A
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hA⟩ := arcSideProg_exec (C := C) (Pv := Pv)
    (lo := .const 1) (hi := .op .add (.reg rLenA) (.const 1)) (vlo := 1) (vhi := A.length + 1)
    (aOut := aOnA) (Or.inl rfl) hCn hPv_nd hPv_ne (by omega) (by omega)
    (by rw [drop_take_arcA]; exact hAP) (by simp [Expr.cost]) (by simp [Expr.cost])
    (fun _ _ => const_eval' hw1)
    (fun st hst => add_eval (reg_eval (by rw [hst.1 rLenA (by decide)]; exact hlenA) (by omega))
      (const_eval' hw1) (by omega))
    h40 hadj hent hcyc hpath hn
  rw [drop_take_arcA] at hA
  -- Second arc: B
  have h40₁ : s₁.regs 40 = N := by rw [hk₁.1 40 (by decide)]; exact h40
  have hlenA₁ : s₁.regs rLenA = A.length := by rw [hk₁.1 rLenA (by decide)]; exact hlenA
  have hadj₁ : IsAdjList H aStart aEnd aEnt lists s₁ :=
    hadj.of_arrs_eq (hk₁.2 aStart (by decide)) (hk₁.2 aEnd (by decide)) (hk₁.2 aEnt (by decide))
  have hent₁ : (s₁.arrs aEnt).length < 2 ^ w := by rw [hk₁.2 aEnt (by decide)]; exact hent
  have hcyc₁ : s₁.arrs aCyc = C.map Fin.val := by rw [hk₁.2 aCyc (by decide)]; exact hcyc
  have hpath₁ : s₁.arrs aNewPath = Pv.map Fin.val := by
    rw [hk₁.2 aNewPath (by decide)]; exact hpath
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hB⟩ := arcSideProg_exec (C := C) (Pv := Pv)
    (lo := .op .add (.reg rLenA) (.const 2)) (hi := .len aCyc)
    (vlo := A.length + 2) (vhi := C.length)
    (aOut := aOnB) (Or.inr rfl) hCn hPv_nd hPv_ne (by omega) le_rfl
    (by rw [drop_take_arcB]; exact hBP) (by simp [Expr.cost]) (by simp [Expr.cost])
    (fun st hst => add_eval (reg_eval (by rw [hst.1 rLenA (by decide)]; exact hlenA₁) (by omega))
      (const_eval' (by omega)) (by omega))
    (fun st hst => len_eval_map (by rw [hst.2 aCyc (by decide)]; exact hcyc₁) (by omega))
    h40₁ hadj₁ hent₁ hcyc₁ hpath₁ hn
  rw [drop_take_arcB] at hB
  have hk₁' : Keeps loopSideRegs loopSideArrs s s₁ := hk₁.mono (by decide) (by decide)
  have hk₂' : Keeps loopSideRegs loopSideArrs s₁ s₂ := hk₂.mono (by decide) (by decide)
  have hk_all : Keeps loopSideRegs loopSideArrs s s₂ :=
    hk₁'.trans hk₂' (by decide) (by decide)
  refine ⟨s₂, _, .seq hex₁ hex₂, by omega, hk_all, ?_, hB⟩
  rw [hk₂.2 aOnA (by decide)]; exact hA

end GraphMinor.Compute.TwoPaths
