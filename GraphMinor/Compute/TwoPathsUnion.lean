module

public import GraphMinor.Compute.TwoPathsSep

/-!
# The adjacency lists of `H + F`

After a completion with new edges `F` (a flat list `u₀ v₀ u₁ v₁ …` in array `aF`), line 10 of
Algorithm 5.1 works in the graph `H + F`. `unionProg` writes adjacency lists of
`H ⊔ pairGraph n F` in arrays `aUS`, `aUE`, `aUEnt`: the list of a vertex `u` is its list in `H`
followed by its partners in `F` (`fParts`).

For each vertex the program scans all of `F`, so it takes `O(n + m + n |F|)` steps. Since
`|F| < 2 |P'|`, this is within the bound `O(|P'| (n + m + 1))` of the split.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### The lists -/

/-- The partners of `u` in the pairs `0, …, j - 1` of `F`. -/
def fPartsUpTo (F : List ℕ) (u : ℕ) (j : ℕ) : List ℕ :=
  (List.range j).flatMap fun i =>
    (if F.getD (2 * i) 0 = u then [F.getD (2 * i + 1) 0] else []) ++
      (if F.getD (2 * i + 1) 0 = u then [F.getD (2 * i) 0] else [])

/-- The partners of `u` in `F`. -/
def fParts (F : List ℕ) (u : ℕ) : List ℕ := fPartsUpTo F u (F.length / 2)

/-- The list of `u` in `H + F`. -/
def unionList (lists : Fin n → List ℕ) (F : List ℕ) (u : Fin n) : List ℕ :=
  lists u ++ fParts F u.1

theorem fPartsUpTo_succ (F : List ℕ) (u j : ℕ) :
    fPartsUpTo F u (j + 1) = fPartsUpTo F u j ++
      ((if F.getD (2 * j) 0 = u then [F.getD (2 * j + 1) 0] else []) ++
        (if F.getD (2 * j + 1) 0 = u then [F.getD (2 * j) 0] else [])) := by
  simp [fPartsUpTo, List.range_succ, List.flatMap_append]

theorem length_fPartsUpTo_le (F : List ℕ) (u j : ℕ) : (fPartsUpTo F u j).length ≤ 2 * j := by
  induction j with
  | zero => simp [fPartsUpTo]
  | succ j ih =>
    rw [fPartsUpTo_succ, List.length_append, List.length_append]
    have h1 : (if F.getD (2 * j) 0 = u then [F.getD (2 * j + 1) 0] else []).length ≤ 1 := by
      split_ifs <;> simp
    have h2 : (if F.getD (2 * j + 1) 0 = u then [F.getD (2 * j) 0] else []).length ≤ 1 := by
      split_ifs <;> simp
    omega

theorem mem_fParts {F : List ℕ} {u x : ℕ} :
    x ∈ fParts F u ↔ ∃ i, 2 * i + 1 < F.length ∧
      ((F[2 * i]? = some u ∧ F[2 * i + 1]? = some x) ∨
        (F[2 * i + 1]? = some u ∧ F[2 * i]? = some x)) := by
  unfold fParts fPartsUpTo
  simp only [List.mem_flatMap, List.mem_range, List.mem_append]
  constructor
  · rintro ⟨i, hi, h⟩
    have h1 : 2 * i + 1 < F.length := by omega
    refine ⟨i, h1, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem h1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 * i < F.length by omega),
      List.getElem?_eq_getElem h1, Option.getD_some] at h
    split_ifs at h with ha hb <;> simp_all
  · rintro ⟨i, h1, h⟩
    refine ⟨i, by omega, ?_⟩
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem h1] at h
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 * i < F.length by omega),
      List.getElem?_eq_getElem h1, Option.getD_some]
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp at ha hb; left; simp [ha, hb]
    · simp at ha hb; right; simp [ha, hb]

/-- What the `i`-th pair of a new edge list says. -/
theorem IsNewEdgeList.pair {H : SimpleGraph (Fin n)} {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) {i : ℕ} (hi : 2 * i + 1 < F.length) :
    ∃ u v : Fin n, F[2 * i]? = some u.1 ∧ F[2 * i + 1]? = some v.1 ∧ u ≠ v ∧ ¬ H.Adj u v := by
  obtain ⟨u, v, h1, h2, h3, -, -, h4⟩ := hF.2.1 i hi
  exact ⟨u, v, h1, h2, h3, h4⟩

theorem fParts_lt {H : SimpleGraph (Fin n)} {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) {u x : ℕ} (hx : x ∈ fParts F u) : x < n := by
  obtain ⟨i, hi, h⟩ := mem_fParts.mp hx
  obtain ⟨a, b, ha, hb, -, -⟩ := hF.pair hi
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · rw [hb] at h; cases h; exact b.2
  · rw [ha] at h; cases h; exact a.2

/-- A partner of `u` in `F` is a neighbour of `u` in `pairGraph n F` and not in `H`. -/
theorem pairGraph_of_mem_fParts {H : SimpleGraph (Fin n)} {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) {u x : Fin n} (hx : x.1 ∈ fParts F u.1) :
    (pairGraph n F).Adj u x ∧ ¬ H.Adj u x := by
  obtain ⟨i, hi, h⟩ := mem_fParts.mp hx
  obtain ⟨a, b, ha, hb, hab, hH⟩ := hF.pair hi
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [ha] at h1; rw [hb] at h2
    have e1 : a = u := Fin.ext (by simpa using h1)
    have e2 : b = x := Fin.ext (by simpa using h2)
    subst e1 e2
    exact ⟨⟨hab, i, Or.inl ⟨ha, hb⟩⟩, hH⟩
  · rw [hb] at h1; rw [ha] at h2
    have e1 : b = u := Fin.ext (by simpa using h1)
    have e2 : a = x := Fin.ext (by simpa using h2)
    subst e1 e2
    exact ⟨⟨Ne.symm hab, i, Or.inr ⟨ha, hb⟩⟩, fun h => hH h.symm⟩

theorem mem_fParts_of_pairGraph {F : List ℕ} {u x : Fin n} (h : (pairGraph n F).Adj u x) :
    x.1 ∈ fParts F u.1 := by
  obtain ⟨-, i, h⟩ := h
  have hi : 2 * i + 1 < F.length := by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> exact (List.getElem?_eq_some_iff.mp h).1
  exact mem_fParts.mpr ⟨i, hi, h.imp id fun h => ⟨h.2, h.1⟩⟩

theorem nodup_fParts {H : SimpleGraph (Fin n)} {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) (u : ℕ) : (fParts F u).Nodup := by
  unfold fParts fPartsUpTo
  rw [List.nodup_flatMap]
  have hget : ∀ i, i < F.length / 2 → ∃ a b : Fin n, F.getD (2 * i) 0 = a.1 ∧
      F.getD (2 * i + 1) 0 = b.1 ∧ a ≠ b ∧ F[2 * i]? = some a.1 ∧ F[2 * i + 1]? = some b.1 :=
    fun i hi => by
      obtain ⟨a, b, ha, hb, hab, -⟩ := hF.pair (show 2 * i + 1 < F.length by omega)
      exact ⟨a, b, by simp [List.getD_eq_getElem?_getD, ha], by simp [List.getD_eq_getElem?_getD, hb],
        hab, ha, hb⟩
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, hab, -, -⟩ := hget i (List.mem_range.mp hi)
    rw [ha, hb]
    by_cases h1 : a.1 = u <;> by_cases h2 : b.1 = u
    · exact absurd (Fin.ext (h1.trans h2.symm)) hab
    all_goals simp [h1, h2]
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij x hx1 hx2
    simp only [List.getElem_range, List.length_range] at hi hj hx1 hx2
    obtain ⟨a, b, ha, hb, hab, ha', hb'⟩ := hget i hi
    obtain ⟨c, d, hc, hd, hcd, hc', hd'⟩ := hget j hj
    rw [ha, hb] at hx1; rw [hc, hd] at hx2
    apply hF.2.2 i j hij (by omega)
    rw [ha', hb', hc', hd']
    simp only [List.mem_append] at hx1 hx2
    split_ifs at hx1 hx2 <;> simp_all

/-- **The lists of `H + F`.** -/
theorem isAdjListFamily_union {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hfam : IsAdjListFamily H lists) {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) : IsAdjListFamily (H ⊔ pairGraph n F) (unionList lists F) := by
  intro u
  obtain ⟨hlt, hnd, -, hmem⟩ := hfam u
  have hlt' : ∀ x ∈ unionList lists F u, x < n := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    · exact hlt x h
    · exact fParts_lt hF h
  have hnd' : (unionList lists F u).Nodup := by
    refine List.nodup_append.mpr ⟨hnd, nodup_fParts hF u.1, fun x hx y hy hxy => ?_⟩
    subst hxy
    have hxn := hlt x hx
    exact (pairGraph_of_mem_fParts hF (x := ⟨x, hxn⟩) hy).2 ((hmem ⟨x, hxn⟩).mp hx)
  refine ⟨hlt', hnd', ?_, fun v => ?_⟩
  · have hsub : (unionList lists F u).toFinset ⊆ Finset.range n := fun x hx => by
      simpa using hlt' x (List.mem_toFinset.mp hx)
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd', Finset.card_range] at this
    exact this
  · simp only [unionList, List.mem_append, sup_adj]
    constructor
    · rintro (h | h)
      · exact Or.inl ((hmem v).mp h)
      · exact Or.inr (pairGraph_of_mem_fParts hF h).1
    · rintro (h | h)
      · exact Or.inl ((hmem v).mpr h)
      · exact Or.inr (mem_fParts_of_pairGraph h)

/-! ### Lists under construction -/

/-- The sum of `f u` over the vertices `u < v`. -/
def pre (f : Fin n → ℕ) (v : ℕ) : ℕ := ∑ u : Fin n, if u.1 < v then f u else 0

theorem pre_zero (f : Fin n → ℕ) : pre f 0 = 0 := by simp [pre]

theorem pre_succ (f : Fin n → ℕ) (v : Fin n) : pre f (v.1 + 1) = pre f v.1 + f v := by
  unfold pre
  have hfv : f v = ∑ u : Fin n, if u = v then f u else 0 := by simp
  rw [hfv, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases h : u = v
  · subst h; simp
  · have : u.1 ≠ v.1 := fun e => h (Fin.ext e)
    by_cases h' : u.1 < v.1
    · simp [h', show u.1 < v.1 + 1 by omega, h]
    · simp [h', show ¬ u.1 < v.1 + 1 by omega, h]

theorem pre_mono (f : Fin n → ℕ) {u v : ℕ} (h : u ≤ v) : pre f u ≤ pre f v :=
  Finset.sum_le_sum fun x _ => by split_ifs <;> omega

theorem pre_n (f : Fin n → ℕ) : pre f n = ∑ u, f u :=
  Finset.sum_congr rfl fun u _ => by simp [u.2]

/-- The lists of the vertices `u < v` are in place, each at offset `pre`. -/
def Built (dS dE dEnt : Arr) (L : Fin n → List ℕ) (v : ℕ) (st : State) : Prop :=
  ∀ u : Fin n, u.1 < v → IsListAt dS dE dEnt u.1 (pre (fun u => (L u).length) u.1)
    (pre (fun u => (L u).length) u.1 + (L u).length) (L u) st

/-- Register of the current vertex. -/
abbrev rUV : Reg := 100
/-- Register of the write cursor. -/
abbrev rUC : Reg := 101
/-- Registers of the scan of a list. -/
abbrev rUK : Reg := 102
abbrev rUH : Reg := 103
/-- Register of the scan of `F`. -/
abbrev rUJ : Reg := 104
/-- Register of the sum of the degrees. -/
abbrev rUT : Reg := 105
/-- The lists of `H + F`. -/
abbrev aUS : Arr := 51
abbrev aUE : Arr := 52
abbrev aUEnt : Arr := 53

/-- Append the value of `val` to the list of the current vertex. -/
def uAppend (val : Expr) : Cmd := listAppend aUE aUEnt rUV rUC val

theorem built_append {L : Fin n → List ℕ} {v : Fin n} {st : State} {c x y : ℕ}
    (hb : Built aUS aUE aUEnt L v.1 st) (hc : pre (fun u => (L u).length) v.1 ≤ c) :
    Built aUS aUE aUEnt L v.1 (((st.writeArr aUEnt c x).setReg rUC y).writeArr aUE v.1 y) := by
  intro u hu
  obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩ := hb u hu
  have hmono := pre_mono (fun u => (L u).length) (show u.1 + 1 ≤ v.1 by omega)
  rw [pre_succ] at hmono
  refine ⟨by simpa using hu_st, by simpa using hu_en, by simpa using hen_ent, hdiff,
    by simpa using hst, ?_, hle, ?_⟩
  · simp only [State.writeArr_arrs_self]
    rw [List.getElem_set_ne (by omega)]
    simpa using hen
  · intro k hk
    simp only [State.writeArr_arrs_ne _ _ _ (show aUEnt ≠ aUE by decide), State.setReg_arrs,
      State.writeArr_arrs_self]
    rw [List.getElem_set_ne (by omega)]
    exact helem k hk

/-- **Appending.** -/
theorem uAppend_exec {w : ℕ} {L : Fin n → List ℕ} {v : Fin n} {l : List ℕ} {st : State}
    {val : Expr} {x : ℕ} (hb : Built aUS aUE aUEnt L v.1 st)
    (hcur : IsListAt aUS aUE aUEnt v.1 (pre (fun u => (L u).length) v.1)
      (pre (fun u => (L u).length) v.1 + l.length) l st)
    (hv : st.regs rUV = v.1) (hc : st.regs rUC = pre (fun u => (L u).length) v.1 + l.length)
    (hroom : pre (fun u => (L u).length) v.1 + l.length < (st.arrs aUEnt).length)
    (hval : val.eval w st = some x) (hw : 1 < 2 ^ w) (hcw : (st.arrs aUEnt).length < 2 ^ w)
    (hnw : n < 2 ^ w) :
    ∃ st', Exec w (uAppend val) st st' (val.cost + 9) ∧ Built aUS aUE aUEnt L v.1 st' ∧
      IsListAt aUS aUE aUEnt v.1 (pre (fun u => (L u).length) v.1)
        (pre (fun u => (L u).length) v.1 + (l ++ [x]).length) (l ++ [x]) st' ∧
      st'.regs rUC = pre (fun u => (L u).length) v.1 + l.length + 1 ∧
      (∀ r, r ≠ rUC → st'.regs r = st.regs r) ∧
      (∀ a, a ≠ aUE → a ≠ aUEnt → st'.arrs a = st.arrs a) ∧
      (∀ a, (st'.arrs a).length = (st.arrs a).length) := by
  set p := pre (fun u => (L u).length) v.1 with hp
  have hv' := v.2
  obtain ⟨s', k, hex, hk, hpost, -, hc'⟩ := Triple.listAppend_spec (w := w) aUS aUE aUEnt rUV rUC val
    v.1 p l x (by decide) (by decide) (by decide) (by decide) hw (by omega) (by omega) st
    ⟨hcur, hv, hc, hroom, hval⟩
  -- The explicit final state.
  set s₃ := ((st.writeArr aUEnt (p + l.length) x).setReg rUC (p + l.length + 1)).writeArr aUE v.1
    (p + l.length + 1) with hs₃
  have hlt : p + l.length + 1 < 2 ^ w := by omega
  have hlt' : p + l.length < 2 ^ w := by omega
  have hex₃ : Exec w (uAppend val) st s₃ (1 + val.cost + 1 + (4 + 3)) :=
    .seq (.write (by simp [Expr.eval, checkWord, hc, hlt']) hval hroom)
      (.seq (.assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, hlt', hlt,
        show w ≠ 0 by rintro rfl; simp at hw]))
        (.write (by simp [Expr.eval, checkWord, hv]; omega) (by simp [Expr.eval, checkWord]; omega)
          (by obtain ⟨-, hu_en, -⟩ := hcur; simpa using hu_en)))
  obtain ⟨rfl, -⟩ := Exec.deterministic hex hex₃
  refine ⟨s₃, by convert hex₃ using 1; omega, built_append hb (by omega), hpost, ?_, ?_, ?_, ?_⟩
  · simp [s₃]
  · intro r hr; simp [s₃, hr]
  · intro a h1 h2; simp [s₃, State.writeArr_arrs_ne _ _ _ h1, State.writeArr_arrs_ne _ _ _ h2]
  · intro a; simp [s₃]

/-! ### One vertex -/

/-- Append the partner of the current vertex in pair `rUJ` of `F`, if it has one there. -/
def uPair : Cmd :=
  .seq (.ite (.op .eq (.read aF (.op .mul (.const 2) (.reg rUJ))) (.reg rUV))
      (uAppend (.read aF (.op .add (.op .mul (.const 2) (.reg rUJ)) (.const 1)))) .skip)
    (.ite (.op .eq (.read aF (.op .add (.op .mul (.const 2) (.reg rUJ)) (.const 1))) (.reg rUV))
      (uAppend (.read aF (.op .mul (.const 2) (.reg rUJ)))) .skip)

/-- Write the list of the current vertex: its list in `H`, then its partners in `F`. -/
def uVertex : Cmd :=
  .seq (.write aUS (.reg rUV) (.reg rUC))
    (.seq (.write aUE (.reg rUV) (.reg rUC))
      (.seq (.assign rUK (.read aStart (.reg rUV)))
        (.seq (.assign rUH (.read aEnd (.reg rUV)))
          (.seq (forUp rUK (.reg rUH) (uAppend (.read aEnt (.reg rUK))))
            (.seq (.assign rUJ (.const 0))
              (forUp rUJ (.op .div (.len aF) (.const 2)) uPair))))))

/-- The registers that `unionProg` writes. -/
def uRegs : List ℕ := [rUV, rUC, rUK, rUH, rUJ, rUT]

/-- The arrays that `unionProg` writes. -/
def uArrs : List ℕ := [aUS, aUE, aUEnt]

/-- The state while the list of `v` is written, with `l` written so far. -/
structure UCur (L : Fin n → List ℕ) (s₀ : State) (v : Fin n) (l : List ℕ) (st : State) : Prop where
  keeps : Keeps uRegs uArrs s₀ st
  built : Built aUS aUE aUEnt L v.1 st
  cur : IsListAt aUS aUE aUEnt v.1 (pre (fun u => (L u).length) v.1)
    (pre (fun u => (L u).length) v.1 + l.length) l st
  rv : st.regs rUV = v.1
  rc : st.regs rUC = pre (fun u => (L u).length) v.1 + l.length
  len : (st.arrs aUEnt).length = (s₀.arrs aUEnt).length
  pfx : l <+: L v
  lenS : (st.arrs aUS).length = n
  lenE : (st.arrs aUE).length = n

theorem UCur.append {w : ℕ} {L : Fin n → List ℕ} {s₀ : State} {v : Fin n} {l : List ℕ}
    {st : State} (h : UCur L s₀ v l st) {val : Expr} {x : ℕ} (hval : val.eval w st = some x)
    (hpfx : l ++ [x] <+: L v) (hw : 1 < 2 ^ w) (hcw : (s₀.arrs aUEnt).length < 2 ^ w)
    (hnw : n < 2 ^ w) (hcap : pre (fun u => (L u).length) n ≤ (s₀.arrs aUEnt).length) :
    ∃ st', Exec w (uAppend val) st st' (val.cost + 9) ∧ UCur L s₀ v (l ++ [x]) st' ∧
      (∀ r, r ≠ rUC → st'.regs r = st.regs r) ∧ (∀ a, a ∉ uArrs → st'.arrs a = st.arrs a) := by
  have hroom : pre (fun u => (L u).length) v.1 + l.length < (st.arrs aUEnt).length := by
    have h1 := hpfx.length_le
    have h2 := pre_mono (fun u => (L u).length) (show v.1 + 1 ≤ n from v.2)
    rw [pre_succ] at h2
    simp only [List.length_append, List.length_singleton] at h1
    rw [h.len]; omega
  obtain ⟨st', hex, hb, hcur, hrc, hregs, harrs, hlens⟩ := uAppend_exec h.built h.cur h.rv h.rc hroom
    hval hw (by rw [h.len]; exact hcw) hnw
  refine ⟨st', hex, ⟨h.keeps.trans ⟨fun r hr => hregs r (fun e => hr (by rw [e]; decide)),
      fun a ha => harrs a (fun e => ha (by rw [e]; decide)) (fun e => ha (by rw [e]; decide))⟩
      (fun _ h => h) (fun _ h => h), hb, hcur, by rw [hregs _ (by decide)]; exact h.rv,
      by rw [hrc]; simp; omega, by rw [hlens]; exact h.len, hpfx, by rw [hlens]; exact h.lenS,
      by rw [hlens]; exact h.lenE⟩, hregs, fun a ha => harrs a
      (fun e => ha (by rw [e]; decide)) (fun e => ha (by rw [e]; decide))⟩

theorem UCur.setReg {L : Fin n → List ℕ} {s₀ : State} {v : Fin n} {l : List ℕ} {st : State}
    (h : UCur L s₀ v l st) {r : Reg} (hr : r ∈ uRegs) (h1 : r ≠ rUV) (h2 : r ≠ rUC) (x : ℕ) :
    UCur L s₀ v l (st.setReg r x) :=
  ⟨h.keeps.setReg hr x, h.built, h.cur, by rw [State.setReg_regs_ne _ _ (Ne.symm h1)]; exact h.rv,
    by rw [State.setReg_regs_ne _ _ (Ne.symm h2)]; exact h.rc, h.len, h.pfx, h.lenS, h.lenE⟩

/-- **The list of `v` in `H`.** -/
theorem hLoop_exec {w : ℕ} {lists : Fin n → List ℕ} {L : Fin n → List ℕ} {s₀ : State}
    {v : Fin n} {st : State} {st0 en0 : ℕ}
    (hlist : IsListAt aStart aEnd aEnt v.1 st0 en0 (lists v) s₀)
    (hlt : ∀ x ∈ lists v, x < n) (hpL : lists v <+: L v)
    (h : UCur L s₀ v [] st) (hk : st.regs rUK = st0) (hh : st.regs rUH = en0)
    (hw : 1 < 2 ^ w) (hcw : (s₀.arrs aUEnt).length < 2 ^ w) (hnw : n < 2 ^ w)
    (hentw : (s₀.arrs aEnt).length < 2 ^ w)
    (hcap : pre (fun u => (L u).length) n ≤ (s₀.arrs aUEnt).length) :
    ∃ st' t, Exec w (forUp rUK (.reg rUH) (uAppend (.read aEnt (.reg rUK)))) st st' t ∧
      t ≤ 3 + 18 * (lists v).length ∧ UCur L s₀ v (lists v) st' ∧
      (∀ r, r ≠ rUC → r ≠ rUK → st'.regs r = st.regs r) ∧
      (∀ a, a ∉ uArrs → st'.arrs a = st.arrs a) := by
  obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst, hen, hle, helem⟩ := hlist
  have hen0w : en0 < 2 ^ w := by omega
  have hsrc : ∀ st' : State, Keeps uRegs uArrs s₀ st' → st'.arrs aEnt = s₀.arrs aEnt :=
    fun st' hk' => hk'.2 aEnt (by decide)
  let I : ℕ → State → Prop := fun k st' => UCur L s₀ v ((lists v).take (k - st0)) st' ∧
    st'.regs rUK = k ∧ st0 ≤ k ∧ (∀ r, r ≠ rUC → r ≠ rUK → st'.regs r = st.regs r) ∧
    (∀ a, a ∉ uArrs → st'.arrs a = st.arrs a)
  have hI0 : I st0 st := ⟨by simpa using h, hk, le_rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩
  have hloop := forUp_pot I (fun _ => 0) en0 11 (r_i := rUK) (hi := .reg rUH)
    (body := uAppend (.read aEnt (.reg rUK))) hw hen0w
    (fun k _ st' hst => ⟨hst.2.1, reg_eval (by rw [hst.2.2.2.1 rUH (by decide) (by decide)]; exact hh)
      hen0w⟩)
    (fun k hk' st' hst => by
      obtain ⟨hu, hrk, hlo, hregs, harrs⟩ := hst
      have hkl : k - st0 < (lists v).length := by omega
      have hx : (s₀.arrs aEnt)[k]'(by omega) = (lists v)[k - st0] := by
        have := helem (k - st0) hkl
        simp only [show st0 + (k - st0) = k by omega] at this
        exact this
      have hval : (Expr.read aEnt (.reg rUK)).eval w st' = some (lists v)[k - st0] := by
        rw [read_eval (reg_eval hrk (by omega)) (by rw [hsrc st' hu.keeps]; omega)
          (by simp only [hsrc st' hu.keeps]; rw [hx]; have := hlt _ (List.getElem_mem hkl); omega)]
        simp only [hsrc st' hu.keeps]; rw [hx]
      have htake : (lists v).take (k - st0) ++ [(lists v)[k - st0]] =
          (lists v).take (k + 1 - st0) := by
        rw [show k + 1 - st0 = (k - st0) + 1 by omega, take_succ_eq hkl]
      obtain ⟨st'', hex, hu', hregs', harrs'⟩ := hu.append hval
        (by rw [htake]; exact (List.take_prefix _ _).trans hpL) hw hcw hnw hcap
      rw [htake] at hu'
      refine ⟨st'', _, hex, by simp only [Expr.cost]; omega, ⟨hu'.setReg (by decide) (by decide)
        (by decide) _, by simp, by omega, fun r h1 h2 => ?_, fun a ha => ?_⟩, ?_⟩
      · rw [State.setReg_regs_ne _ _ h2, hregs' r h1, hregs r h1 h2]
      · rw [State.setReg_arrs, harrs' a ha, harrs a ha]
      · rw [hregs' _ (by decide)]; exact hrk)
    st0 (by omega) st hI0
  obtain ⟨st', t, hex, ht, hu, -, -, hregs, harrs⟩ := hloop
  refine ⟨st', t, hex, ?_, ?_, hregs, harrs⟩
  · simp only [Expr.cost] at ht
    rw [show en0 - st0 = (lists v).length by omega] at ht
    omega
  · rwa [show en0 - st0 = (lists v).length by omega, List.take_length] at hu

theorem UCur.condAppend {w : ℕ} {L : Fin n → List ℕ} {s₀ : State} {v : Fin n} {l : List ℕ}
    {st : State} (h : UCur L s₀ v l st) {cond val : Expr} {c : Prop} [Decidable c] {x : ℕ}
    (hcond : cond.eval w st = some (if c then 1 else 0)) (hval : val.eval w st = some x)
    (hpfx : l ++ (if c then [x] else []) <+: L v) (hw : 1 < 2 ^ w)
    (hcw : (s₀.arrs aUEnt).length < 2 ^ w) (hnw : n < 2 ^ w)
    (hcap : pre (fun u => (L u).length) n ≤ (s₀.arrs aUEnt).length) :
    ∃ st' t, Exec w (.ite cond (uAppend val) .skip) st st' t ∧ t ≤ cond.cost + val.cost + 9 ∧
      UCur L s₀ v (l ++ if c then [x] else []) st' ∧
      (∀ r, r ≠ rUC → st'.regs r = st.regs r) ∧ (∀ a, a ∉ uArrs → st'.arrs a = st.arrs a) := by
  by_cases hc : c
  · simp only [hc, if_true] at hcond hpfx ⊢
    obtain ⟨st', hex, hu, hregs, harrs⟩ := h.append hval hpfx hw hcw hnw hcap
    exact ⟨st', _, .ite_true hcond one_ne_zero hex, le_rfl, hu, hregs, harrs⟩
  · simp only [hc, if_false, List.append_nil] at hcond hpfx ⊢
    exact ⟨st, _, .ite_false hcond (.skip st), by have := val.cost_pos; omega, h,
      fun _ _ => rfl, fun _ _ => rfl⟩

theorem getD_eq_get {F : List ℕ} {i : ℕ} (h : i < F.length) : F.getD i 0 = F[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **One pair of `F`.** -/
theorem uPair_exec {w : ℕ} {L : Fin n → List ℕ} {s₀ : State} {v : Fin n} {l : List ℕ}
    {st : State} (h : UCur L s₀ v l st) {j : ℕ} (hj : st.regs rUJ = j)
    (hjF : 2 * j + 1 < (s₀.arrs aF).length) (hFlt : ∀ x ∈ s₀.arrs aF, x < n)
    (hpfx : l ++ ((if (s₀.arrs aF).getD (2 * j) 0 = v.1 then [(s₀.arrs aF).getD (2 * j + 1) 0]
        else []) ++ (if (s₀.arrs aF).getD (2 * j + 1) 0 = v.1 then [(s₀.arrs aF).getD (2 * j) 0]
        else [])) <+: L v)
    (hw : 1 < 2 ^ w) (hcw : (s₀.arrs aUEnt).length < 2 ^ w) (hnw : n < 2 ^ w)
    (hFw : (s₀.arrs aF).length < 2 ^ w)
    (hcap : pre (fun u => (L u).length) n ≤ (s₀.arrs aUEnt).length) :
    ∃ st' t, Exec w uPair st st' t ∧ t ≤ 42 ∧
      UCur L s₀ v (l ++ ((if (s₀.arrs aF).getD (2 * j) 0 = v.1 then
        [(s₀.arrs aF).getD (2 * j + 1) 0] else []) ++
        (if (s₀.arrs aF).getD (2 * j + 1) 0 = v.1 then [(s₀.arrs aF).getD (2 * j) 0] else [])))
        st' ∧
      (∀ r, r ≠ rUC → st'.regs r = st.regs r) ∧ (∀ a, a ∉ uArrs → st'.arrs a = st.arrs a) := by
  set F := s₀.arrs aF with hF
  have hFst : ∀ st' : State, Keeps uRegs uArrs s₀ st' → st'.arrs aF = F :=
    fun st' hk => hk.2 aF (by decide)
  have h0 : 2 * j < F.length := by omega
  have h2w : 2 < 2 ^ w := by omega
  have ha := F.getElem_mem h0
  have hb := F.getElem_mem hjF
  have hav := hFlt _ ha
  have hbv := hFlt _ hb
  rw [getD_eq_get h0, getD_eq_get hjF] at hpfx ⊢
  -- The expressions, in any state with the same `rUJ`, `rUV` and `aF`.
  have hE : ∀ st' : State, Keeps uRegs uArrs s₀ st' → st'.regs rUJ = j → st'.regs rUV = v.1 →
      (Expr.read aF (.op .mul (.const 2) (.reg rUJ))).eval w st' = some F[2 * j] ∧
      (Expr.read aF (.op .add (.op .mul (.const 2) (.reg rUJ)) (.const 1))).eval w st' =
        some F[2 * j + 1] ∧ (Expr.reg rUV).eval w st' = some v.1 := fun st' hk hj' hv' => by
    have hm : (Expr.op .mul (.const 2) (.reg rUJ)).eval w st' = some (2 * j) :=
      op_eval (a := 2) (b := j) (by simp [checkWord, h2w]) (reg_eval hj' (by omega))
        (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)
    have hm1 : (Expr.op .add (.op .mul (.const 2) (.reg rUJ)) (.const 1)).eval w st' =
        some (2 * j + 1) :=
      op_eval (b := 1) hm (by simp [checkWord, hw]) (by simp [BinOp.eval, BinOp.raw, checkWord]; omega)
    refine ⟨?_, ?_, reg_eval hv' (by have := v.2; omega)⟩
    · rw [read_eval hm (by rw [hFst st' hk]; exact h0) (by simp only [hFst st' hk]; omega)]
      simp only [hFst st' hk]
    · rw [read_eval hm1 (by rw [hFst st' hk]; exact hjF) (by simp only [hFst st' hk]; omega)]
      simp only [hFst st' hk]
  obtain ⟨e1, e2, e3⟩ := hE st h.keeps hj h.rv
  obtain ⟨st₁, t₁, hex₁, ht₁, hu₁, hregs₁, harrs₁⟩ := h.condAppend (c := F[2 * j] = v.1)
    (eq_eval e1 e3 hw) e2
    (by rw [← List.append_assoc] at hpfx; exact (List.prefix_append _ _).trans hpfx) hw hcw hnw hcap
  obtain ⟨f1, f2, f3⟩ := hE st₁ hu₁.keeps (by rw [hregs₁ _ (by decide)]; exact hj) hu₁.rv
  obtain ⟨st₂, t₂, hex₂, ht₂, hu₂, hregs₂, harrs₂⟩ := hu₁.condAppend (c := F[2 * j + 1] = v.1)
    (eq_eval f2 f3 hw) f1 (by rw [List.append_assoc]; exact hpfx) hw hcw hnw hcap
  refine ⟨st₂, _, .seq hex₁ hex₂, ?_, by rw [← List.append_assoc]; exact hu₂,
    fun r hr => by rw [hregs₂ r hr, hregs₁ r hr], fun a ha => by rw [harrs₂ a ha, harrs₁ a ha]⟩
  simp only [Expr.cost] at ht₁ ht₂
  omega

theorem fPartsUpTo_prefix (F : List ℕ) (u : ℕ) {j j' : ℕ} (h : j ≤ j') :
    fPartsUpTo F u j <+: fPartsUpTo F u j' := by
  induction j' with
  | zero => rw [Nat.le_zero.mp h]
  | succ j' ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · rw [fPartsUpTo_succ]; exact (ih (by omega)).trans (List.prefix_append _ _)
    · rw [h]

/-- The state between two vertices: the lists of the vertices `u < v` are written. -/
structure UVert (L : Fin n → List ℕ) (s₀ : State) (v : ℕ) (st : State) : Prop where
  keeps : Keeps uRegs uArrs s₀ st
  built : Built aUS aUE aUEnt L v st
  rv : st.regs rUV = v
  rc : st.regs rUC = pre (fun u => (L u).length) v
  lenS : (st.arrs aUS).length = n
  lenE : (st.arrs aUE).length = n
  len : (st.arrs aUEnt).length = (s₀.arrs aUEnt).length

/-- **One vertex.** -/
theorem uVertex_exec {w : ℕ} {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {s₀ : State}
    (hadj : IsAdjList H aStart aEnd aEnt lists s₀) (hFlt : ∀ x ∈ s₀.arrs aF, x < n)
    {v : Fin n} {st : State} (h : UVert (unionList lists (s₀.arrs aF)) s₀ v.1 st)
    (hw : 1 < 2 ^ w) (h2w : 2 < 2 ^ w) (hcw : (s₀.arrs aUEnt).length < 2 ^ w) (hnw : n < 2 ^ w)
    (hentw : (s₀.arrs aEnt).length < 2 ^ w) (hFw : (s₀.arrs aF).length < 2 ^ w)
    (hcap : pre (fun u => (unionList lists (s₀.arrs aF) u).length) n ≤ (s₀.arrs aUEnt).length) :
    ∃ st' t, Exec w uVertex st st' t ∧
      t ≤ 22 + 18 * (lists v).length + 51 * ((s₀.arrs aF).length / 2) ∧
      UVert (unionList lists (s₀.arrs aF)) s₀ (v.1 + 1) (st'.setReg rUV (v.1 + 1)) ∧
      st'.regs rUV = v.1 := by
  set F := s₀.arrs aF with hF
  set L := unionList lists F with hL
  set p := pre (fun u => (L u).length) v.1 with hp
  have hv2 := v.2
  obtain ⟨hst0, hen0, hlist⟩ : ∃ st0 en0, IsListAt aStart aEnd aEnt v.1 st0 en0 (lists v) s₀ :=
    hadj.1.2.2 v
  obtain ⟨hlt, -, -, -⟩ := hadj.2 v
  have hsrc : ∀ a, a ∉ uArrs → st.arrs a = s₀.arrs a := fun a ha => h.keeps.2 a ha
  have hpn : p + (L v).length ≤ (s₀.arrs aUEnt).length := by
    have h2 := pre_mono (fun u => (L u).length) (show v.1 + 1 ≤ n from v.2)
    rw [pre_succ] at h2; omega
  -- Steps 1 and 2: the empty list of `v`.
  set st₁ := st.writeArr aUS v.1 p with hst₁
  have hex₁ : Exec w (.write aUS (.reg rUV) (.reg rUC)) st st₁ (1 + 1 + 1) :=
    .write (reg_eval h.rv (by omega)) (reg_eval h.rc (by omega)) (by rw [h.lenS]; exact v.2)
  set st₂ := st₁.writeArr aUE v.1 p with hst₂
  have hex₂ : Exec w (.write aUE (.reg rUV) (.reg rUC)) st₁ st₂ (1 + 1 + 1) :=
    .write (reg_eval (by simp [st₁, h.rv]) (by omega)) (reg_eval (by simp [st₁, h.rc, hp]) (by omega))
      (by simp [st₁, h.lenE])
  have hu₂ : UCur L s₀ v [] st₂ := by
    refine ⟨(h.keeps.writeArr (by decide) _ _).writeArr (by decide) _ _, fun u hu => ?_, ?_,
      by simp [st₂, st₁, h.rv], by simp [st₂, st₁, h.rc, p], by simp [st₂, st₁, h.len],
      List.nil_prefix, by simp [st₂, st₁, h.lenS], by simp [st₂, st₁, h.lenE]⟩
    · obtain ⟨hu_st, hu_en, hen_ent, hdiff, hst', hen', hle, helem⟩ := h.built u hu
      have hne : u.1 ≠ v.1 := by omega
      refine ⟨by simpa [st₂, st₁] using hu_st, by simpa [st₂, st₁] using hu_en,
        by simpa [st₂, st₁] using hen_ent, hdiff, ?_, ?_, hle, fun k hk => by
          simpa [st₂, st₁] using helem k hk⟩
      · simp only [st₂, st₁, State.writeArr_arrs_ne _ _ _ (show aUS ≠ aUE by decide),
          State.writeArr_arrs_self]
        rw [List.getElem_set_ne (Ne.symm hne)]; exact hst'
      · simp only [st₂, st₁, State.writeArr_arrs_self,
          State.writeArr_arrs_ne _ _ _ (show aUE ≠ aUS by decide)]
        rw [List.getElem_set_ne (Ne.symm hne)]; exact hen'
    · refine ⟨by simp [st₂, st₁, h.lenS], by simp [st₂, st₁, h.lenE], ?_, by simp, ?_, ?_,
        le_rfl, fun k hk => by simp at hk⟩
      · simp [st₂, st₁, h.len]; omega
      · simp only [st₂, st₁, State.writeArr_arrs_ne _ _ _ (show aUS ≠ aUE by decide),
          State.writeArr_arrs_self]
        simp [hp]
      · simp only [st₂, st₁, State.writeArr_arrs_self]; simp [hp]
  -- Step 3: the bounds of the list of `v` in `H`.
  have hlist' := hlist
  obtain ⟨hu_st, hu_en, hen_ent, hdiff, hstv, henv, hle, -⟩ := hlist
  have hk₂ := hu₂.keeps
  set st₃ := st₂.setReg rUK hst0 with hst₃
  have hex₃ : Exec w (.assign rUK (.read aStart (.reg rUV))) st₂ st₃ (2 + 1) := .assign (by
    rw [read_eval (reg_eval hu₂.rv (by omega)) (by rw [hk₂.2 aStart (by decide)]; exact hu_st)
      (by simp only [hk₂.2 aStart (by decide)]; rw [hstv]; omega)]
    simp only [hk₂.2 aStart (by decide)]; rw [hstv])
  set st₄ := st₃.setReg rUH hen0 with hst₄
  have hex₄ : Exec w (.assign rUH (.read aEnd (.reg rUV))) st₃ st₄ (2 + 1) := .assign (by
    have hk₃ : st₃.arrs aEnd = s₀.arrs aEnd := by simp [st₃, hk₂.2 aEnd (by decide)]
    rw [read_eval (reg_eval (v := v.1) (by simp [st₃, hu₂.rv]) (by omega))
      (by rw [hk₃]; exact hu_en)
      (by simp only [hk₃]; rw [henv]; omega)]
    simp only [hk₃]; rw [henv])
  have hu₄ : UCur L s₀ v [] st₄ :=
    (hu₂.setReg (r := rUK) (by decide) (by decide) (by decide) _).setReg (r := rUH) (by decide)
      (by decide) (by decide) _
  -- Step 4: the list of `v` in `H`.
  obtain ⟨st₅, t₅, hex₅, ht₅, hu₅, hregs₅, harrs₅⟩ := hLoop_exec hlist' hlt
    (List.prefix_append _ _) hu₄ (by simp [st₄, st₃]) (by simp [st₄]) hw hcw hnw hentw hcap
  -- Step 5: the partners in `F`.
  set st₆ := st₅.setReg rUJ 0 with hst₆
  have hex₆ : Exec w (.assign rUJ (.const 0)) st₅ st₆ (1 + 1) := .assign (by simp [checkWord])
  have hFst : ∀ st' : State, Keeps uRegs uArrs s₀ st' → st'.arrs aF = F :=
    fun st' hk => hk.2 aF (by decide)
  have hdiv : ∀ st' : State, Keeps uRegs uArrs s₀ st' →
      (Expr.op .div (.len aF) (.const 2)).eval w st' = some (F.length / 2) := fun st' hk => by
    refine op_eval (a := F.length) (b := 2)
      (by simp only [Expr.eval, hFst st' hk, checkWord, if_pos hFw])
      (by simp [checkWord, h2w]) ?_
    simp [BinOp.eval, BinOp.raw, checkWord]; omega
  let J : ℕ → State → Prop := fun j st' => UCur L s₀ v (lists v ++ fPartsUpTo F v.1 j) st' ∧
    st'.regs rUJ = j ∧ (∀ r, r ≠ rUC → r ≠ rUJ → st'.regs r = st₆.regs r)
  have hu₆ : UCur L s₀ v (lists v) st₆ :=
    hu₅.setReg (r := rUJ) (by decide) (by decide) (by decide) 0
  have hJ0 : J 0 st₆ := ⟨by simpa [fPartsUpTo] using hu₆, by simp [st₆], fun _ _ _ => rfl⟩
  have hloop := forUp_pot J (fun _ => 0) (F.length / 2) 42 (r_i := rUJ)
    (hi := .op .div (.len aF) (.const 2)) (body := uPair) hw (by omega)
    (fun j _ st' hst => ⟨hst.2.1, hdiv st' hst.1.keeps⟩)
    (fun j hj st' hst => by
      obtain ⟨hu, hrj, hregs⟩ := hst
      have hpfx : (lists v ++ fPartsUpTo F v.1 j) ++
          ((if F.getD (2 * j) 0 = v.1 then [F.getD (2 * j + 1) 0] else []) ++
            (if F.getD (2 * j + 1) 0 = v.1 then [F.getD (2 * j) 0] else [])) =
          lists v ++ fPartsUpTo F v.1 (j + 1) := by
        rw [fPartsUpTo_succ, List.append_assoc]
      have hj1 : 2 * j + 1 < F.length := by omega
      have hpL : lists v ++ fPartsUpTo F v.1 (j + 1) <+: L v := by
        show _ <+: lists v ++ fPartsUpTo F v.1 (F.length / 2)
        exact (List.prefix_append_right_inj (lists v)).mpr
          (fPartsUpTo_prefix F v.1 (show j + 1 ≤ F.length / 2 by omega))
      obtain ⟨st'', t, hex, ht, hu', hregs', -⟩ := uPair_exec hu hrj hj1 hFlt
        (by rw [hpfx]; exact hpL) hw hcw hnw hFw hcap
      rw [hpfx] at hu'
      refine ⟨st'', t, hex, by omega, ⟨hu'.setReg (by decide) (by decide) (by decide) _,
        by simp, fun r h1 h2 => ?_⟩, by rw [hregs' _ (by decide)]; exact hrj⟩
      rw [State.setReg_regs_ne _ _ h2, hregs' r h1, hregs r h1 h2])
    0 (Nat.zero_le _) st₆ hJ0
  obtain ⟨st₇, t₇, hex₇, ht₇, hu₇, -, hregs₇⟩ := hloop
  -- Step 6: the list of `v` is written.
  have hLv : lists v ++ fPartsUpTo F v.1 (F.length / 2) = L v := rfl
  rw [hLv] at hu₇
  refine ⟨st₇, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))), ?_,
    ⟨hu₇.keeps.setReg (by decide) _, fun u hu => ?_, by simp, ?_, by simp [hu₇.lenS],
      by simp [hu₇.lenE], by simp [hu₇.len]⟩, ?_⟩
  · simp only [Expr.cost] at ht₅ ht₇ ⊢
    omega
  · rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hu | hu
    · exact hu₇.built u hu
    · have e : u = v := Fin.ext hu
      subst e
      exact hu₇.cur
  · simp only [State.setReg_regs_ne _ _ (show rUC ≠ rUV by decide)]
    rw [hu₇.rc, pre_succ]
  · rw [hregs₇ rUV (by decide) (by decide)]
    simp only [st₆, State.setReg_regs_ne _ _ (show rUV ≠ rUJ by decide)]
    rw [hregs₅ rUV (by decide) (by decide)]
    simp [st₄, st₃, hu₂.rv]

/-! ### The program -/

/-- The sum of the degrees in `H`, in `rUT`. -/
def degSum : Cmd :=
  .seq (.assign rUT (.const 0)) (.seq (.assign rUV (.const 0)) (forUp rUV (.reg 40)
    (.assign rUT (.op .add (.reg rUT) (.op .sub (.read aEnd (.reg rUV)) (.read aStart (.reg rUV)))))))

/-- **The lists of `H + F`.** -/
def unionProg : Cmd :=
  .seq degSum
    (.seq (.alloc aUS (.reg 40))
      (.seq (.alloc aUE (.reg 40))
        (.seq (.alloc aUEnt (.op .add (.reg rUT) (.op .mul (.reg 40) (.len aF))))
          (.seq (.assign rUC (.const 0))
            (.seq (.assign rUV (.const 0)) (forUp rUV (.reg 40) uVertex))))))

theorem degSum_exec {w : ℕ} {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {s : State}
    (hadj : IsAdjList H aStart aEnd aEnt lists s) (h40 : s.regs 40 = n) (hw : 1 < 2 ^ w)
    (hnw : n < 2 ^ w) (hTw : totalAdjEntries lists < 2 ^ w)
    (hentw : (s.arrs aEnt).length < 2 ^ w) :
    ∃ s' t, Exec w degSum s s' t ∧ t ≤ 7 + 15 * n ∧ Keeps [rUT, rUV] [] s s' ∧
      s'.regs rUT = totalAdjEntries lists := by
  set f : Fin n → ℕ := fun u => (lists u).length with hf
  set s₁ := (s.setReg rUT 0).setReg rUV 0 with hs₁
  have hpre_le : ∀ v, pre f v ≤ totalAdjEntries lists := fun v => by
    unfold pre totalAdjEntries; exact Finset.sum_le_sum fun u _ => by split_ifs <;> simp [f]
  let I : ℕ → State → Prop := fun v st => Keeps [rUT, rUV] [] s st ∧ st.regs rUV = v ∧
    st.regs rUT = pre f v
  have hI0 : I 0 s₁ := ⟨((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _, by simp [s₁],
    by simp [s₁, pre_zero]⟩
  have hloop := forUp_pot I (fun _ => 0) n 8 (r_i := rUV) (hi := .reg 40)
    (body := .assign rUT (.op .add (.reg rUT) (.op .sub (.read aEnd (.reg rUV))
      (.read aStart (.reg rUV))))) hw hnw
    (fun v _ st hst => ⟨hst.2.1, reg_eval (by rw [hst.1.1 40 (by decide)]; exact h40) hnw⟩)
    (fun v hv st hst => by
      obtain ⟨hk, hrv, hrt⟩ := hst
      obtain ⟨st0, en0, hu_st, hu_en, hen_ent, hdiff, hst0, hen0, hle, -⟩ := hadj.1.2.2 ⟨v, hv⟩
      simp only [Fin.val_mk] at hu_st hu_en hst0 hen0 hdiff
      have hS : st.arrs aStart = s.arrs aStart := hk.2 _ (by simp)
      have hE : st.arrs aEnd = s.arrs aEnd := hk.2 _ (by simp)
      have hsucc := pre_succ f ⟨v, hv⟩
      simp only [Fin.val_mk] at hsucc
      have hdf : en0 - st0 = f ⟨v, hv⟩ := hdiff
      have hle' := hpre_le (v + 1)
      have hlv := hpre_le v
      have e1 : (Expr.read aEnd (.reg rUV)).eval w st = some en0 := by
        rw [read_eval (reg_eval hrv (by omega)) (by rw [hE]; exact hu_en)
          (by simp only [hE]; simp only [hen0]; omega)]
        simp only [hE]; exact congrArg some hen0
      have e2 : (Expr.read aStart (.reg rUV)).eval w st = some st0 := by
        rw [read_eval (reg_eval hrv (by omega)) (by rw [hS]; exact hu_st)
          (by simp only [hS]; simp only [hst0]; omega)]
        simp only [hS]; exact congrArg some hst0
      refine ⟨st.setReg rUT (pre f (v + 1)), _, .assign (op_eval (reg_eval hrt (by omega))
        (op_eval (c := en0 - st0) e1 e2 (by simp [BinOp.eval, BinOp.raw, checkWord]; omega))
        (by simp only [BinOp.eval, BinOp.raw, checkWord]; rw [if_pos (by omega)]; congr 1; omega)),
        by simp only [Expr.cost]; omega,
        ⟨(hk.setReg (by simp) _).setReg (by simp) _, by simp, by simp⟩, by simp [hrv]⟩)
    0 (Nat.zero_le _) s₁ hI0
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, -, hT₂⟩ := hloop
  refine ⟨s₂, _, .seq (.assign (by simp [checkWord])) (.seq (.assign (by simp [checkWord])) hex₂),
    ?_, hk₂, ?_⟩
  · simp only [Expr.cost] at ht₂ ⊢; omega
  · rw [hT₂, pre_n]; rfl

theorem IsNewEdgeList.lt {H : SimpleGraph (Fin n)} {Pv : List (Fin n)} {F : List ℕ}
    (hF : IsNewEdgeList H Pv F) : ∀ x ∈ F, x < n := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨k, hk⟩ := hF.1
  rcases Nat.even_or_odd i with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨a, b, ha, -, -, -⟩ := hF.pair (i := j) (by omega)
    rw [show 2 * j = i by omega, List.getElem?_eq_getElem hi] at ha
    rw [Option.some_injective _ ha]; exact a.2
  · obtain ⟨a, b, -, hb, -, -⟩ := hF.pair (i := j) (by omega)
    rw [show 2 * j + 1 = i by omega, List.getElem?_eq_getElem hi] at hb
    rw [Option.some_injective _ hb]; exact b.2

theorem sum_unionList_le (lists : Fin n → List ℕ) (F : List ℕ) :
    pre (fun u => (unionList lists F u).length) n ≤ totalAdjEntries lists + n * F.length := by
  rw [pre_n]
  unfold totalAdjEntries unionList
  simp only [List.length_append]
  rw [Finset.sum_add_distrib]
  have : ∑ u : Fin n, (fParts F u.1).length ≤ ∑ _u : Fin n, F.length :=
    Finset.sum_le_sum fun u _ => (length_fPartsUpTo_le F u.1 _).trans (by omega)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

/-- **The lists of `H + F`.** `unionProg` writes adjacency lists of `H ⊔ pairGraph n F` in
`aUS`, `aUE`, `aUEnt`, in at most `21 + 46 n + 19 m + 27 n |F|` steps. -/
theorem unionProg_exec {w : ℕ} {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    {Pv : List (Fin n)} {s : State} (hadj : IsAdjList H aStart aEnd aEnt lists s)
    (hF : IsNewEdgeList H Pv (s.arrs aF)) (h40 : s.regs 40 = n) (hn : 4 * n + 4 < 2 ^ w)
    (hentw : (s.arrs aEnt).length < 2 ^ w) (hFw : (s.arrs aF).length < 2 ^ w)
    (hcapw : totalAdjEntries lists + n * (s.arrs aF).length < 2 ^ w) :
    ∃ s' t, Exec w unionProg s s' t ∧
      t ≤ 21 + 46 * n + 19 * totalAdjEntries lists + 27 * (n * (s.arrs aF).length) ∧
      Keeps uRegs uArrs s s' ∧
      IsAdjList (H ⊔ pairGraph n (s.arrs aF)) aUS aUE aUEnt (unionList lists (s.arrs aF)) s' ∧
      (s'.arrs aUEnt).length = totalAdjEntries lists + n * (s.arrs aF).length := by
  have hw1 : 1 < 2 ^ w := by omega
  have h2w : 2 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set F := s.arrs aF with hFdef
  set T := totalAdjEntries lists with hT
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hT₁⟩ := degSum_exec hadj h40 hw1 hnw (by omega) hentw
  have h40₁ : s₁.regs 40 = n := by rw [hk₁.1 40 (by decide)]; exact h40
  have hF₁ : s₁.arrs aF = F := hk₁.2 aF (by simp)
  set s₂ := s₁.setArr aUS (List.replicate n 0) with hs₂
  set s₃ := s₂.setArr aUE (List.replicate n 0) with hs₃
  set s₄ := s₃.setArr aUEnt (List.replicate (T + n * F.length) 0) with hs₄
  have hex₂ : Exec w (.alloc aUS (.reg 40)) s₁ s₂ (1 + n) := .alloc (reg_eval h40₁ hnw)
  have hex₃ : Exec w (.alloc aUE (.reg 40)) s₂ s₃ (1 + n) := .alloc (reg_eval (by simp [s₂, h40₁]) hnw)
  have hex₄ : Exec w (.alloc aUEnt (.op .add (.reg rUT) (.op .mul (.reg 40) (.len aF)))) s₃ s₄
      (1 + (1 + 1 + 1) + 1 + (T + n * F.length)) :=
    .alloc (op_eval (reg_eval (v := T) (by simp only [s₃, s₂, State.setArr_regs]; exact hT₁)
        (by omega))
      (op_eval (c := n * F.length) (reg_eval (by simp [s₃, s₂, h40₁]) hnw)
        (show (Expr.len aF).eval w s₃ = some F.length by
          simp only [Expr.eval, s₃, s₂, State.setArr_arrs_ne _ _ (show aF ≠ aUE by decide),
            State.setArr_arrs_ne _ _ (show aF ≠ aUS by decide), hF₁, checkWord]
          rw [if_pos hFw])
        (by simp only [BinOp.eval, BinOp.raw, checkWord]; rw [if_pos (by omega)]))
      (by simp only [BinOp.eval, BinOp.raw, checkWord]; rw [if_pos (by omega)]))
  set s₅ := (s₄.setReg rUC 0).setReg rUV 0 with hs₅
  have hk₄ : Keeps uRegs uArrs s s₄ :=
    (((hk₁.mono (by decide) (by simp)).setArr (by decide) _).setArr (by decide) _).setArr
      (by decide) _
  have hadj₄ : IsAdjList H aStart aEnd aEnt lists s₄ :=
    hadj.of_arrs_eq (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide)) (hk₄.2 _ (by decide))
  have hF₄ : s₄.arrs aF = F := hk₄.2 aF (by decide)
  have hcap : pre (fun u => (unionList lists (s₄.arrs aF) u).length) n ≤ (s₄.arrs aUEnt).length := by
    rw [hF₄]; simpa [s₄] using sum_unionList_le lists F
  have hV0 : UVert (unionList lists (s₄.arrs aF)) s₄ 0 s₅ :=
    ⟨((Keeps.refl _ _ s₄).setReg (by decide) _).setReg (by decide) _, fun u hu => absurd hu (by omega),
      by simp [s₅], by simp [s₅, pre_zero], by simp [s₅, s₄, s₃, s₂], by simp [s₅, s₄, s₃],
      by simp [s₅]⟩
  have hloop := forUp_pot (UVert (unionList lists (s₄.arrs aF)) s₄)
    (fun st => 18 * pre (fun u => (lists u).length) (st.regs rUV)) n
    (22 + 51 * (F.length / 2)) (r_i := rUV) (hi := .reg 40) (body := uVertex) hw1 hnw
    (fun v _ st hst => ⟨hst.rv, reg_eval (by rw [hst.keeps.1 40 (by decide)]; simp [s₄, s₃, s₂, h40₁])
      hnw⟩)
    (fun v hv st hst => by
      obtain ⟨st', t, hex, ht, hV, hrv⟩ := uVertex_exec (v := ⟨v, hv⟩) hadj₄
        (by rw [hF₄]; exact hF.lt) hst hw1 h2w
        (by rw [show (s₄.arrs aUEnt).length = T + n * F.length by simp [s₄]]; exact hcapw) hnw
        (by rw [hk₄.2 _ (by decide)]; exact hentw) (by rw [hF₄]; exact hFw) hcap
      refine ⟨st', t, hex, ?_, hV, hrv⟩
      have hs : pre (fun u => (lists u).length) (v + 1) =
          pre (fun u => (lists u).length) v + (lists ⟨v, hv⟩).length :=
        pre_succ (fun u => (lists u).length) ⟨v, hv⟩
      simp only [State.setReg_regs_self, hst.rv]
      rw [hs, ← hF₄]; omega)
    0 (Nat.zero_le _) s₅ hV0
  obtain ⟨s₆, t₆, hex₆, ht₆, hV₆⟩ := hloop
  rw [hF₄] at hV₆
  have hΦ : 18 * pre (fun u => (lists u).length) (s₆.regs rUV) = 18 * T := by
    rw [hV₆.rv, pre_n]; rfl
  have hΦ0 : 18 * pre (fun u => (lists u).length) (s₅.regs rUV) = 0 := by
    simp [s₅, pre_zero]
  have key : n * (1 + 6 + (22 + 51 * (F.length / 2))) ≤ 29 * n + 26 * (n * F.length) := by
    have h51 : 51 * (F.length / 2) ≤ 26 * F.length := by omega
    calc n * (1 + 6 + (22 + 51 * (F.length / 2)))
        = 29 * n + n * (51 * (F.length / 2)) := by ring
      _ ≤ 29 * n + n * (26 * F.length) := by gcongr
      _ = 29 * n + 26 * (n * F.length) := by ring
  refine ⟨s₆, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq (.assign (by simp [checkWord]))
    (.seq (.assign (by simp [checkWord])) hex₆))))), ?_, hk₄.trans hV₆.keeps (fun _ h => h)
    (fun _ h => h), ⟨⟨hV₆.lenS, hV₆.lenE, fun u => ⟨_, _, hV₆.built u u.2⟩⟩,
    isAdjListFamily_union hadj.2 hF⟩, by rw [hV₆.len]; simp [s₄]⟩
  simp only [Expr.cost, Nat.sub_zero] at ht₆ ⊢
  rw [hΦ, hΦ0] at ht₆
  omega

end GraphMinor.Compute.TwoPaths
