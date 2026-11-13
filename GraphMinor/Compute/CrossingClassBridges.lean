module

public import GraphMinor.Compute.TwoPathsSweepLoop
public import GraphMinor.Compute.CrossingClassBridgeMath
import GraphMinor.HP25.Prop34Tools

/-!
# The Bridges of `BridgeCross` on the Word RAM: Off-Cycle Components and Chords

This file implements the first phase of $\operatorname{BridgeCross}(K, D)$ (Section 5 of
`docs/crossing/crossing_extractor.tex`): it finds the $D$-bridges defined at the start of Section 5.
It marks the cycle vertices, searches the components off the cycle, and lists the chords. Each
component is stored as a slice of the search queue. Together these slices and chords give a
complete list of the bridges.

Starting from a state where `aStart, aEnd, aEnt` (`40, 41, 42`) hold the adjacency lists `lists` of
`G : SimpleGraph (Fin n)`, `aCyc` (`43`) holds `D.map Fin.val`, and register `40` holds `n`:
1. `TwoPaths.cycSetup` marks `D` in `aPos` (`64`) and `aLab` (`60`) and sets `rk` (`74`) to `|D|`.
2. `compFindProg` sweeps `rV2 = 0 .. n - 1`, running `pushV` and `searchLoop` to discover each
   off-cycle component `segs[γ]` in `aQue[aCompSt[γ] .. aCompEn[γ])` and recording `aCompOf[u] = γ`
   for every `u ∈ segs[γ]`.
3. `chordEnumProg` scans `i = 0 .. |D| - 1` and `y ∈ lists D[i]`, recording every chord `(i, j)`
   with `i < j` and `Apart |D| (j + 1) (i + 1)` in `(aChordI, aChordJ)` (`105, 106`).
4. We prove that `bridges := compBridges ++ chordBridges` satisfies
   `ValidBridgeList G (List.finRange n) D bridges` in $O(n + m)$ steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.HP25 GraphMinor.Crossing GraphMinor.Compute.Crossing
  GraphMinor.Compute.TwoPaths

variable {n : ℕ}

/-! ### Registers and Arrays for `BridgeCross` (`100+`, disjoint from `TwoPaths`'s `40..96`) -/

/-- Output flag of `bridgeCrossCoreProg` (`1` if a crossing was found, `0` otherwise). -/
abbrev rFoundCross : Reg := 100
/-- Number of off-cycle component bridges `K`. -/
abbrev rNumComp : Reg := 101
/-- Number of chord bridges `M_ch`. -/
abbrev rNumChords : Reg := 102
/-- Total number of bridges `K + M_ch`. -/
abbrev rNumBridges : Reg := 103
/-- Total number of bridge-attachment incidences. -/
abbrev rTotAtt : Reg := 104
/-- Bridge index register `γ`. -/
abbrev rG : Reg := 105
/-- Scratch / chord index register `m`. -/
abbrev rM : Reg := 106
/-- Scratch cursor register. -/
abbrev rCur : Reg := 107
/-- Scratch register 1. -/
abbrev rTmp1 : Reg := 108
/-- Scratch register 2. -/
abbrev rTmp2 : Reg := 109

/-- Output array for the first crossing path `Q`. -/
abbrev aOutQ : Arr := 100
/-- Output array for the second crossing path `R`. -/
abbrev aOutR : Arr := 101
/-- Start offset in `aQue` of off-cycle component `γ`. -/
abbrev aCompSt : Arr := 102
/-- End offset in `aQue` of off-cycle component `γ`. -/
abbrev aCompEn : Arr := 103
/-- Component index `γ` of each off-cycle vertex `u`. -/
abbrev aCompOf : Arr := 104
/-- First cycle index `i` of chord bridge `m`. -/
abbrev aChordI : Arr := 105
/-- Second cycle index `j` of chord bridge `m`. -/
abbrev aChordJ : Arr := 106
/-- Start offset in `aAttEnt` of attachment list of bridge `γ`. -/
abbrev aAttSt : Arr := 107
/-- End offset in `aAttEnt` of attachment list of bridge `γ`. -/
abbrev aAttEn : Arr := 108
/-- Length / write cursor of attachment list of bridge `γ`. -/
abbrev aAttLen : Arr := 109
/-- Last cycle position `i + 1` at which component `γ` was seen. -/
abbrev aLastAtt : Arr := 110
/-- Flat CSR entries of attachment index lists for all bridges. -/
abbrev aAttEnt : Arr := 111

/-! ### Helper: Converting `List ℕ` with elements `< n` to `List (Fin n)` -/

/-- Convert a list of natural numbers to `List (Fin n)` by filtering for `< n`. -/
def bridgeToFinList (n : ℕ) (l : List ℕ) : List (Fin n) :=
  l.filterMap (fun x => if hx : x < n then some ⟨x, hx⟩ else none)

theorem bridgeToFinList_map_val {l : List ℕ} (hlt : ∀ x ∈ l, x < n) :
    (bridgeToFinList n l).map Fin.val = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx : x < n := hlt x List.mem_cons_self
    have ih' := ih (fun y hy => hlt y (List.mem_cons_of_mem _ hy))
    simp only [bridgeToFinList, List.filterMap_cons, hx, ↓reduceDIte, List.map_cons]
    exact congrArg (x :: ·) ih'

theorem length_bridgeToFinList {l : List ℕ} (hlt : ∀ x ∈ l, x < n) :
    (bridgeToFinList n l).length = l.length := by
  rw [← List.length_map Fin.val, bridgeToFinList_map_val hlt]

theorem getElem?_bridgeToFinList_val {l : List ℕ} (hlt : ∀ x ∈ l, x < n) (k : ℕ)
    (hk : k < (bridgeToFinList n l).length) :
    l[k]? = some ((bridgeToFinList n l)[k]'hk).1 := by
  have hmap : ((bridgeToFinList n l).map Fin.val)[k]? = some ((bridgeToFinList n l)[k]'hk).1 := by
    rw [List.getElem?_eq_getElem (by simp [hk]), List.getElem_map]
  rwa [bridgeToFinList_map_val hlt] at hmap

theorem mem_bridgeToFinList_iff {l : List ℕ} (hlt : ∀ x ∈ l, x < n) (u : Fin n) :
    u ∈ bridgeToFinList n l ↔ u.1 ∈ l := by
  conv_rhs => rw [← bridgeToFinList_map_val hlt]
  exact (List.mem_map_of_injective Fin.val_injective).symm

theorem nodup_bridgeToFinList {l : List ℕ} (hlt : ∀ x ∈ l, x < n) (hnd : l.Nodup) :
    (bridgeToFinList n l).Nodup := by
  rw [← List.nodup_map_iff Fin.val_injective, bridgeToFinList_map_val hlt]
  exact hnd

/-! ### Part 1: Off-Cycle Component Discovery (`compFindProg`) -/

/-- Write the component index `rNumComp` into `aCompOf[aQue[rJ]]`. -/
def recordCompElem : Cmd :=
  .seq (.assign rU2 (.read aQue (.reg rJ)))
    (.write aCompOf (.reg rU2) (.reg rNumComp))

/-- When a non-empty segment `aQue[rSt .. rTail)` was discovered, record its slice in
`aCompSt[rNumComp], aCompEn[rNumComp]`, label its vertices in `aCompOf`, and increment `rNumComp`. -/
def recordComp : Cmd :=
  .ite (.op .lt (.reg rSt) (.reg rTail))
    (.seq (.write aCompSt (.reg rNumComp) (.reg rSt))
      (.seq (.write aCompEn (.reg rNumComp) (.reg rTail))
        (.seq (.assign rJ (.reg rSt))
          (.seq (forUp rJ (.reg rTail) recordCompElem)
            (.assign rNumComp (.op .add (.reg rNumComp) (.const 1)))))))
    .skip

/-- One vertex step of off-cycle component discovery. -/
def compFindStep : Cmd :=
  .seq (.assign rSt (.reg rTail))
    (.seq pushV
      (.seq (searchLoop aStart aEnd aEnt)
        recordComp))

/-- Discover all off-cycle connected components of `G - V(D)`. -/
def compFindProg : Cmd :=
  .seq (.alloc aPar (.reg 40))
    (.seq (queueInit aQue rHead rTail (.reg 40))
      (.seq (.assign rHit (.reg 40))
        (.seq (.alloc aCompSt (.reg 40))
          (.seq (.alloc aCompEn (.reg 40))
            (.seq (.alloc aCompOf (.reg 40))
              (.seq (.assign rNumComp (.const 0))
                (.seq (.assign rV2 (.const 0))
                  (forUp rV2 (.reg 40) compFindStep))))))))

/-- Registers written by `compFindProg`. -/
def compFindRegs : List ℕ :=
  [60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, rSt, rJ, rV2, rU2, rNumComp]

/-- Arrays written by `compFindProg`. -/
def compFindArrs : List ℕ :=
  [aLab, aPar, aQue, aCompSt, aCompEn, aCompOf]

/-- Invariant describing the discovered off-cycle component segments `segs`. -/
structure CompSegsOK (H : SimpleGraph (Fin n)) (T : List (Fin n))
    (segs : List (List (Fin n))) (items : List ℕ) (s : State) : Prop where
  numComp : s.regs rNumComp = segs.length
  segs_le_items : segs.length ≤ items.length
  len_st : (s.arrs aCompSt).length = n
  len_en : (s.arrs aCompEn).length = n
  len_of : (s.arrs aCompOf).length = n
  nonempty : ∀ seg ∈ segs, seg ≠ []
  nodup_seg : ∀ seg ∈ segs, seg.Nodup
  off_cyc : ∀ seg ∈ segs, ∀ u ∈ seg, u ∉ T
  mem_items_iff : ∀ u : Fin n, u.1 ∈ items ↔ ∃ (γ : ℕ) (hγ : γ < segs.length), u ∈ segs[γ]'hγ
  disjoint_segs : ∀ (γ₁ γ₂ : ℕ) (h₁ : γ₁ < segs.length) (h₂ : γ₂ < segs.length),
    γ₁ ≠ γ₂ → ∀ u : Fin n, u ∈ segs[γ₁]'h₁ → u ∉ segs[γ₂]'h₂
  comp_reach : ∀ (γ : ℕ) (hγ : γ < segs.length), ∀ u ∈ segs[γ]'hγ, ∀ v : Fin n,
    v ∈ segs[γ]'hγ ↔ v ∉ T ∧ (restrict H {z | z ∉ T}).Reachable u v
  slices : ∀ (γ : ℕ) (hγ : γ < segs.length),
    ∃ st en : ℕ,
      (s.arrs aCompSt)[γ]? = some st ∧
      (s.arrs aCompEn)[γ]? = some en ∧
      en ≤ items.length ∧
      st + (segs[γ]'hγ).length = en ∧
      ∀ (k : ℕ) (hk : k < (segs[γ]'hγ).length),
        items[st + k]? = some ((segs[γ]'hγ)[k]'hk).1
  compOf_eq : ∀ (γ : ℕ) (hγ : γ < segs.length) (u : Fin n),
    u ∈ segs[γ]'hγ → (s.arrs aCompOf)[u.1]? = some γ

theorem CompSegsOK.of_state {_H : SimpleGraph (Fin n)} {_T : List (Fin n)}
    {_segs : List (List (Fin n))} {_items : List ℕ} {s s' : State}
    (h : CompSegsOK _H _T _segs _items s)
    (hr : s'.regs rNumComp = s.regs rNumComp)
    (hst : s'.arrs aCompSt = s.arrs aCompSt)
    (hen : s'.arrs aCompEn = s.arrs aCompEn)
    (hof : s'.arrs aCompOf = s.arrs aCompOf) :
    CompSegsOK _H _T _segs _items s' where
  numComp := by rw [hr, h.numComp]
  segs_le_items := h.segs_le_items
  len_st := by rw [hst, h.len_st]
  len_en := by rw [hen, h.len_en]
  len_of := by rw [hof, h.len_of]
  nonempty := h.nonempty
  nodup_seg := h.nodup_seg
  off_cyc := h.off_cyc
  mem_items_iff := h.mem_items_iff
  disjoint_segs := h.disjoint_segs
  comp_reach := h.comp_reach
  slices := fun γ hγ => by
    rw [hst, hen]
    exact h.slices γ hγ
  compOf_eq := fun γ hγ u hu => by
    rw [hof]
    exact h.compOf_eq γ hγ u hu

/-- Potential function for `compFindProg`: `51` per queued vertex and `119` per adjacency entry. -/
def compFindPot (lists : Fin n → List ℕ) (s : State) : ℕ :=
  51 * s.regs rTail + 119 * popDeg lists (s.arrs aQue) (s.regs rTail)

theorem compFindPot_eq {lists : Fin n → List ℕ} {items : List ℕ} {h : ℕ} {s : State}
    (hq : IsQueueHistory aQue rHead rTail n items h s) :
    compFindPot lists s = 51 * items.length + 119 * popDeg lists items items.length := by
  unfold compFindPot
  rw [hq.2.2.2.1, popDeg_queue hq]

/-- Loop invariant of `compFindProg` after checking vertices `< v`. -/
def CompFindInv (H : SimpleGraph (Fin n)) (T : List (Fin n)) (s₀ : State) (v : ℕ) (s : State) :
    Prop :=
  Keeps compFindRegs compFindArrs s₀ s ∧ s.regs rV2 = v ∧
    ∃ (items src : List ℕ) (segs : List (List (Fin n))),
      SInv H (labT T) src s items items.length s ∧
      CompSegsOK H T segs items s ∧
      ∀ x : Fin n, x.1 < v → x ∉ T → x.1 ∈ items

/-- Execution of `recordComp` after `searchLoop` finishes. -/
theorem recordComp_exec {w : ℕ} (H : SimpleGraph (Fin n)) (T : List (Fin n))
    (hw1 : 1 < 2 ^ w) (hnw : n < 2 ^ w)
    (items seg_nat : List ℕ) (segs : List (List (Fin n))) (s : State)
    (hq : IsQueueHistory aQue rHead rTail n (items ++ seg_nat) (items ++ seg_nat).length s)
    (hnd : (items ++ seg_nat).Nodup)
    (hlt : ∀ x ∈ items ++ seg_nat, x < n)
    (hoff : ∀ a : Fin n, a.1 ∈ seg_nat → a ∉ T)
    (hreach_seg : ∀ a b : Fin n, a.1 ∈ seg_nat →
      (b.1 ∈ seg_nat ↔ b ∉ T ∧ (restrict H {z | z ∉ T}).Reachable a b))
    (hrst : s.regs rSt = items.length)
    (hcomp : CompSegsOK H T segs items s) :
    ∃ s' t, Exec w recordComp s s' t ∧
      t ≤ 22 + 13 * seg_nat.length ∧
      Keeps [rJ, rU2, rNumComp] [aCompSt, aCompEn, aCompOf] s s' ∧
      ∃ segs' : List (List (Fin n)),
        CompSegsOK H T segs' (items ++ seg_nat) s' := by
  have hitf_le : (items ++ seg_nat).length ≤ n := length_le_of_nodup_lt hnd hlt
  have htail : s.regs rTail = (items ++ seg_nat).length := hq.2.2.2.1
  have hst_w : items.length < 2 ^ w := by simp at hitf_le; omega
  have htl_w : (items ++ seg_nat).length < 2 ^ w := by omega
  have hcond : (Expr.op .lt (.reg rSt) (.reg rTail)).eval w s =
      some (if items.length < (items ++ seg_nat).length then 1 else 0) :=
    lt_eval (reg_eval hrst hst_w) (reg_eval htail htl_w) hw1
  by_cases hne : seg_nat = []
  · subst hne
    have hcond0 : (Expr.op .lt (.reg rSt) (.reg rTail)).eval w s = some 0 := by
      simpa using hcond
    refine ⟨s, _, .ite_false hcond0 (.skip _), by simp [Expr.cost], Keeps.refl _ _ s, segs, ?_⟩
    simpa using hcomp
  · have hseg_pos : 0 < seg_nat.length := List.length_pos_iff.mpr hne
    have hlt_len : items.length < (items ++ seg_nat).length := by simp [hseg_pos]
    have hcond1 : (Expr.op .lt (.reg rSt) (.reg rTail)).eval w s = some 1 := by
      rw [hcond]; simp [hseg_pos]
    set K := segs.length
    have hK_lt_n : K < n := by
      have := hcomp.segs_le_items
      simp only [List.length_append] at hitf_le
      omega
    have hK_w : K < 2 ^ w := lt_trans hK_lt_n hnw
    set s₁ := s.writeArr aCompSt K items.length
    have hex₁ : Exec w (.write aCompSt (.reg rNumComp) (.reg rSt)) s s₁ 3 :=
      .write (reg_eval hcomp.numComp hK_w) (reg_eval hrst hst_w) (by rw [hcomp.len_st]; exact hK_lt_n)
    set s₂ := s₁.writeArr aCompEn K (items ++ seg_nat).length
    have hex₂ : Exec w (.write aCompEn (.reg rNumComp) (.reg rTail)) s₁ s₂ 3 :=
      .write (reg_eval (by simp [s₁, hcomp.numComp, K]) hK_w)
        (reg_eval (by simp [s₁, htail]) htl_w)
        (by simp [s₁, hcomp.len_en]; exact hK_lt_n)
    set s₃ := s₂.setReg rJ items.length
    have hex₃ : Exec w (.assign rJ (.reg rSt)) s₂ s₃ 2 :=
      .assign (reg_eval (by simp [s₂, s₁, hrst]) hst_w)
    let LI : ℕ → State → Prop := fun j st =>
      items.length ≤ j ∧
      st.regs rJ = j ∧
      st.regs rTail = (items ++ seg_nat).length ∧
      st.regs rNumComp = K ∧
      st.arrs aQue = s.arrs aQue ∧
      st.arrs aCompSt = s₂.arrs aCompSt ∧
      st.arrs aCompEn = s₂.arrs aCompEn ∧
      (st.arrs aCompOf).length = n ∧
      Keeps [rJ, rU2, rNumComp] [aCompSt, aCompEn, aCompOf] s st ∧
      (∀ (γ : ℕ) (hγ : γ < K) (u : Fin n), u ∈ segs[γ]'hγ →
        (st.arrs aCompOf)[u.1]? = some γ) ∧
      (∀ (k : ℕ) (hk : k < seg_nat.length), k < j - items.length →
        (st.arrs aCompOf)[seg_nat[k]'hk]? = some K)
    have hLI0 : LI items.length s₃ := by
      refine ⟨le_rfl, by simp [s₃], by simp [s₃, s₂, s₁, htail],
        by simp [s₃, s₂, s₁, hcomp.numComp, K], by simp [s₃, s₂, s₁], by simp [s₃], by simp [s₃],
        by simp [s₃, s₂, s₁, hcomp.len_of],
        ((Keeps.refl _ _ s).writeArr (by simp) _ _).writeArr (by simp) _ _ |>.setReg (by simp) _,
        fun γ hγ u hu => by simpa [s₃, s₂, s₁] using hcomp.compOf_eq γ hγ u hu,
        fun k _ hk => by omega⟩
    have hloop := forUp_pot LI (fun _ => 0) (items ++ seg_nat).length 6
      (r_i := rJ) (hi := .reg rTail) (body := recordCompElem) hw1 htl_w
      (fun j _ st hst => ⟨hst.2.1, reg_eval hst.2.2.1 htl_w⟩)
      (fun j hj st hst => by
        obtain ⟨hj_lo, hrj, hrtl, hrK, hque, hst_arr, hen_arr, hlen_of, hkp, hold_of, hnew_of⟩ := hst
        have hq_len : (st.arrs aQue).length = n := by rw [hque, hq.1]
        have hj_n : j < n := lt_of_lt_of_le hj hitf_le
        have hlt_a : j < (st.arrs aQue).length := by omega
        have hu_elem : (st.arrs aQue)[j]'hlt_a = (items ++ seg_nat)[j] := by
          have h := hq.2.2.2.2.2 j hj
          simpa [hque] using h
        have hk_lt : j - items.length < seg_nat.length := by
          simp only [List.length_append] at hj; omega
        have hitem_eq : (items ++ seg_nat)[j] = seg_nat[j - items.length]'hk_lt :=
          List.getElem_append_right hj_lo
        have hu_n : (items ++ seg_nat)[j] < n := hlt _ (List.getElem_mem hj)
        have hread : (Expr.read aQue (.reg rJ)).eval w st = some (items ++ seg_nat)[j] := by
          simp [Expr.eval, checkWord, hrj, show j < 2 ^ w by omega, hlt_a, hu_elem,
            show (items ++ seg_nat)[j] < 2 ^ w by omega]
        set st₁ := st.setReg rU2 (items ++ seg_nat)[j]
        set st₂ := st₁.writeArr aCompOf (items ++ seg_nat)[j] K
        have he₁ : Exec w (.assign rU2 (.read aQue (.reg rJ))) st st₁ 3 := .assign hread
        have he₂ : Exec w (.write aCompOf (.reg rU2) (.reg rNumComp)) st₁ st₂ 3 :=
          .write (reg_eval (by simp [st₁]) (by omega))
            (reg_eval (by simp [st₁, hrK]) hK_w)
            (by simp [st₁, hlen_of, hu_n])
        refine ⟨st₂, _, .seq he₁ he₂, by omega,
          ⟨by omega, by simp, by simp [st₂, st₁, hrtl], by simp [st₂, st₁, hrK],
           by simp [st₂, st₁, hque], by simp [st₂, st₁, hst_arr], by simp [st₂, st₁, hen_arr],
           by simp [st₂, st₁, hlen_of],
           ((hkp.setReg (by simp) _).writeArr (by simp) _ _).setReg (by simp) _,
           fun γ hγ u hu => ?_, fun k hk hk_bound => ?_⟩,
          by simp [st₂, st₁, hrj]⟩
        · have hu_items : u.1 ∈ items := (hcomp.mem_items_iff u).mpr ⟨γ, hγ, hu⟩
          have hu_seg : (items ++ seg_nat)[j] ∈ seg_nat := by
            rw [hitem_eq]; exact List.getElem_mem hk_lt
          have hne_u : (items ++ seg_nat)[j] ≠ u.1 := fun heq =>
            List.disjoint_of_nodup_append hnd (heq ▸ hu_items) hu_seg
          simp only [State.setReg_arrs, st₂, State.writeArr_arrs_self, st₁,
            List.getElem?_set_ne hne_u]
          exact hold_of γ hγ u hu
        · simp only [State.setReg_arrs, st₂, State.writeArr_arrs_self, st₁]
          by_cases hkj : k = j - items.length
          · subst hkj
            have hlen_k : seg_nat[j - items.length] < (st.arrs aCompOf).length := by
              rw [hlen_of, ← hitem_eq]; exact hu_n
            simp [hitem_eq, List.getElem?_set_self hlen_k]
          · have hk_lt' : k < j - items.length := by omega
            have hnd_seg : seg_nat.Nodup := (List.nodup_append.mp hnd).2.1
            have hne_k : (items ++ seg_nat)[j] ≠ seg_nat[k] := by
              rw [hitem_eq]
              intro heq
              exact hkj ((hnd_seg.getElem_inj_iff).mp heq).symm
            rw [List.getElem?_set_ne hne_k]
            exact hnew_of k hk hk_lt')
      items.length (by omega) s₃ hLI0
    obtain ⟨s₄, t₄, hex₄, ht₄, _, _, hrtl₄, hrK₄, hque₄, hst₄, hen₄, hlen_of₄, hkp₄, hold₄, hnew₄⟩ :=
      hloop
    set s₅ := s₄.setReg rNumComp (K + 1)
    have hK1_w : K + 1 < 2 ^ w := by omega
    have hex₅ : Exec w (.assign rNumComp (.op .add (.reg rNumComp) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrK₄, hK_w, hw1, hK1_w])
    have hex_true : Exec w recordComp s s₅ (3 + (3 + (3 + (2 + (t₄ + 4))))) :=
      .ite_true hcond1 one_ne_zero
        (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))))
    have hlt_seg : ∀ x ∈ seg_nat, x < n := fun x hx => hlt x (List.mem_append_right _ hx)
    set seg_fin := bridgeToFinList n seg_nat
    have hseg_len : seg_fin.length = seg_nat.length := length_bridgeToFinList hlt_seg
    refine ⟨s₅, _, hex_true, ?_, hkp₄.setReg (by simp) _, segs ++ [seg_fin], ?_⟩
    · simp only [Expr.cost] at ht₄
      have hdiff : (items ++ seg_nat).length - items.length = seg_nat.length := by simp
      rw [hdiff] at ht₄
      omega
    · refine ⟨by simp [s₅, K], ?_, by simp [s₅, hst₄, s₂, s₁, hcomp.len_st],
        by simp [s₅, hen₄, s₂, s₁, hcomp.len_en], by simp [s₅, hlen_of₄], ?_, ?_, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · have := hcomp.segs_le_items
        simp only [List.length_append, List.length_singleton]
        omega
      · intro seg hseg
        rcases List.mem_append.mp hseg with hseg | hseg
        · exact hcomp.nonempty seg hseg
        · simp only [List.mem_singleton] at hseg
          subst hseg
          exact List.ne_nil_of_length_pos (by omega)
      · intro seg hseg
        rcases List.mem_append.mp hseg with hseg | hseg
        · exact hcomp.nodup_seg seg hseg
        · simp only [List.mem_singleton] at hseg
          subst hseg
          exact nodup_bridgeToFinList hlt_seg (List.nodup_append.mp hnd).2.1
      · intro seg hseg u hu
        rcases List.mem_append.mp hseg with hseg | hseg
        · exact hcomp.off_cyc seg hseg u hu
        · simp only [List.mem_singleton] at hseg
          subst hseg
          exact hoff u ((mem_bridgeToFinList_iff hlt_seg u).mp hu)
      · intro u
        rw [List.mem_append, hcomp.mem_items_iff u, ← mem_bridgeToFinList_iff hlt_seg u]
        constructor
        · rintro (⟨γ, hγ, hu⟩ | hu)
          · refine ⟨γ, by simp; omega, ?_⟩
            simpa [List.getElem_append_left hγ] using hu
          · refine ⟨K, by simp [K], ?_⟩
            simpa [K] using hu
        · rintro ⟨γ, hγ, hu⟩
          simp only [List.length_append, List.length_singleton] at hγ
          rcases Nat.lt_succ_iff_lt_or_eq.mp hγ with hγ_lt | rfl
          · left
            refine ⟨γ, hγ_lt, ?_⟩
            simpa [List.getElem_append_left hγ_lt] using hu
          · right
            simpa [K] using hu
      · intro γ₁ γ₂ h₁ h₂ hne_g u hu₁ hu₂
        simp only [List.length_append, List.length_singleton] at h₁ h₂
        rcases Nat.lt_succ_iff_lt_or_eq.mp h₁ with h₁_lt | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp h₂ with h₂_lt | rfl
        · rw [List.getElem_append_left h₁_lt] at hu₁
          rw [List.getElem_append_left h₂_lt] at hu₂
          exact hcomp.disjoint_segs γ₁ γ₂ h₁_lt h₂_lt hne_g u hu₁ hu₂
        · rw [List.getElem_append_left h₁_lt] at hu₁
          simp only [List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_singleton] at hu₂
          have hu_it : u.1 ∈ items := (hcomp.mem_items_iff u).mpr ⟨γ₁, h₁_lt, hu₁⟩
          have hu_seg : u.1 ∈ seg_nat := (mem_bridgeToFinList_iff hlt_seg u).mp hu₂
          exact List.disjoint_of_nodup_append hnd hu_it hu_seg
        · simp only [List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_singleton] at hu₁
          rw [List.getElem_append_left h₂_lt] at hu₂
          have hu_it : u.1 ∈ items := (hcomp.mem_items_iff u).mpr ⟨γ₂, h₂_lt, hu₂⟩
          have hu_seg : u.1 ∈ seg_nat := (mem_bridgeToFinList_iff hlt_seg u).mp hu₁
          exact List.disjoint_of_nodup_append hnd hu_it hu_seg
        · exact hne_g rfl
      · intro γ hγ u hu v
        simp only [List.length_append, List.length_singleton] at hγ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hγ with hγ_lt | rfl
        · simp only [List.getElem_append_left hγ_lt] at hu ⊢
          exact hcomp.comp_reach γ hγ_lt u hu v
        · simp only [List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_singleton] at hu ⊢
          rw [mem_bridgeToFinList_iff hlt_seg v]
          exact hreach_seg u v ((mem_bridgeToFinList_iff hlt_seg u).mp hu)
      · intro γ hγ
        simp only [List.length_append, List.length_singleton] at hγ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hγ with hγ_lt | rfl
        · obtain ⟨st, en, hst_g, hen_g, hen_le, hlen_g, hget_g⟩ := hcomp.slices γ hγ_lt
          have hne_K : K ≠ γ := Nat.ne_of_gt hγ_lt
          refine ⟨st, en, ?_, ?_, by simp; omega, ?_, ?_⟩
          · simp [s₅, hst₄, s₂, s₁, List.getElem?_set_ne hne_K, hst_g]
          · simp [s₅, hen₄, s₂, s₁, List.getElem?_set_ne hne_K, hen_g]
          · simpa [List.getElem_append_left hγ_lt] using hlen_g
          · intro k hk
            simp only [List.getElem_append_left hγ_lt] at hk ⊢
            rw [List.getElem?_append_left (by omega)]
            exact hget_g k hk
        · refine ⟨items.length, (items ++ seg_nat).length, ?_, ?_, le_rfl, ?_, ?_⟩
          · simp [s₅, hst₄, s₂, s₁, K, hcomp.len_st, hK_lt_n]
          · simp [s₅, hen₄, s₂, s₁, K, hcomp.len_en, hK_lt_n]
          · simp [hseg_len]
          · intro k hk
            simp only [List.getElem_append_right le_rfl, Nat.sub_self,
              List.getElem_singleton] at hk ⊢
            rw [List.getElem?_append_right (by omega)]
            simp only [Nat.add_sub_cancel_left]
            exact getElem?_bridgeToFinList_val hlt_seg k hk
      · intro γ hγ u hu
        simp only [List.length_append, List.length_singleton] at hγ
        rcases Nat.lt_succ_iff_lt_or_eq.mp hγ with hγ_lt | rfl
        · rw [List.getElem_append_left hγ_lt] at hu
          simpa [s₅] using hold₄ γ hγ_lt u hu
        · simp only [List.getElem_append_right le_rfl, Nat.sub_self,
            List.getElem_singleton] at hu
          have hu_seg : u.1 ∈ seg_nat := (mem_bridgeToFinList_iff hlt_seg u).mp hu
          obtain ⟨k, hk, hk_eq⟩ := List.getElem_of_mem hu_seg
          have hres_k := hnew₄ k hk (by simp [hk])
          simpa [s₅, hk_eq] using hres_k

/-- One round of `compFindProg`. -/
theorem compFindStep_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hadj₀ : IsAdjList H aStart aEnd aEnt lists s₀)
    (hn₀ : s₀.regs 40 = n) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (v : ℕ) (hv : v < n) (s : State) (hs : CompFindInv H T s₀ v s) :
    ∃ s' t, Exec w compFindStep s s' t ∧
      t + compFindPot lists s ≤ 65 + compFindPot lists (s'.setReg rV2 (v + 1)) ∧
      CompFindInv H T s₀ (v + 1) (s'.setReg rV2 (v + 1)) ∧ s'.regs rV2 = v := by
  obtain ⟨hk, hrv, items, src, segs, hsi, hcomp, hall⟩ := hs
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hL0 : ∀ x, labT T x ≤ 3 := fun x => by unfold labT; split_ifs <;> omega
  have hlen : items.length ≤ n := length_le_of_nodup_lt hsi.nodup hsi.lt
  have htail : s.regs rTail = items.length := hsi.queue.2.2.2.1
  set s₁ := s.setReg rSt items.length
  have hex₁ : Exec w (.assign rSt (.reg rTail)) s s₁ 2 :=
    .assign (reg_eval htail (by omega))
  have hsi₁ : SInv H (labT T) src s₁ items items.length s₁ :=
    hsi.transfer (fun r h1 h2 => by
      have : r ≠ rSt := by rintro rfl; exact absurd h2 (by decide)
      simp [s₁, this]) (fun a _ => by simp [s₁])
  have hk₁ : Keeps compFindRegs compFindArrs s₀ s₁ :=
    hk.setReg (by simp [compFindRegs]) _
  have hn₁ : s₁.regs 40 = n := by
    rw [hk₁.1 40 (by decide), hn₀]
  have hadj₁ : IsAdjList H aStart aEnd aEnt lists s₁ :=
    hadj₀.of_arrs_eq (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide)) (hk₁.2 _ (by decide))
  obtain ⟨s₂, t₂, hex₂, ht₂, hcase⟩ := pushV_exec H (labT T) hL0 src s₁ hn₁ hw4 hnw items s₁
    hsi₁ ⟨v, hv⟩ (by simp [s₁, hrv])
  obtain ⟨e₁, src₁, he₁_le, hsi₂, hsrc₁, hvcase⟩ : ∃ e₁ src₁ : List ℕ,
      e₁.length ≤ 1 ∧
      SInv H (labT T) src₁ s₁ (items ++ e₁) items.length s₂ ∧
      (∀ r : Fin n, r.1 ∈ src₁ → r.1 ∉ src → r.1 = v) ∧
      (v ∈ items ++ e₁ ∨ labT T ⟨v, hv⟩ ≠ 0) := by
    rcases hcase with ⟨hni, hl0, hs'⟩ | ⟨hor, hs'⟩
    · refine ⟨[v], src ++ [v], by simp, hs', fun r h1 h2 => ?_, Or.inl (by simp)⟩
      rw [List.mem_append, List.mem_singleton] at h1
      exact h1.resolve_left h2
    · refine ⟨[], src, by simp, by simpa using hs', fun r h1 h2 => absurd h1 h2, ?_⟩
      simpa using hor
  obtain ⟨s₃, t₃, extra, hex₃, -, ht₃, hsi₃⟩ := searchLoop_exec H lists aStart aEnd aEnt
    (by decide) (by decide) (by decide) (labT T) hL0 src₁ s₁ hadj₁
    (by rw [hk₁.2 _ (by decide)]; exact hent) hn₁ hw4 hnw _ (items ++ e₁) items.length s₂ rfl
    hsi₂
  set seg_nat := e₁ ++ extra
  have hitf : items ++ e₁ ++ extra = items ++ seg_nat := by simp [seg_nat]
  have hoff : ∀ a : Fin n, a.1 ∈ seg_nat → a ∉ T := fun a ha =>
    labT_eq_zero.1 (hsi₃.free a (by rw [hitf]; exact List.mem_append_right _ ha))
  obtain ⟨p, -, hpok⟩ := hsi₃.par
  have hcl_old : ∀ u : Fin n, u.1 ∈ items → ∀ v', H.Adj u v' → labT T v' ≠ 0 ∨ v'.1 ∈ items :=
    fun u hu v' hv' => hsi.closed u (by simpa using hu) v' hv'
  have hroot : ∀ x : Fin n, x.1 ∈ seg_nat → (restrict H {z | z ∉ T}).Reachable ⟨v, hv⟩ x := by
    intro x hx
    rw [hitf] at hpok
    obtain ⟨r, hr1, hr2, hreach⟩ := seg_root (src := src) hpok
      (by rw [← hitf]; exact hsi₃.free) hcl_old hsi.srcs (by rw [← hitf]; exact hsi₃.nodup) x hx
    have : r = ⟨v, hv⟩ := Fin.ext (hsrc₁ r hr1 hr2)
    rw [← this]; exact hreach
  have hcl_new : ∀ u : Fin n, u.1 ∈ items ++ seg_nat → ∀ v', H.Adj u v' →
      labT T v' ≠ 0 ∨ v'.1 ∈ items ++ seg_nat := by
    intro u hu v' hv'
    have hcl₃ := hsi₃.closed u
    rw [List.take_length, hitf] at hcl₃
    exact hcl₃ hu v' hv'
  have hnd : (items ++ seg_nat).Nodup := by rw [← hitf]; exact hsi₃.nodup
  have hfree : ∀ z : Fin n, z.1 ∈ items ++ seg_nat → z ∉ T := fun z hz =>
    labT_eq_zero.1 (hsi₃.free z (by rwa [hitf]))
  have hcross : ∀ u u' : Fin n, u.1 ∈ items → u'.1 ∈ seg_nat →
      ¬ (restrict H {z | z ∉ T}).Reachable u u' := by
    intro u u' hu hu' hreach
    obtain ⟨W, hW⟩ := exists_walk_of_reachable_restrict hreach
      (hfree u (List.mem_append_left _ hu))
    have := mem_of_walk_closed hcl_old W hu (fun z hz => labT_eq_zero.2 (hW z hz))
    exact List.disjoint_of_nodup_append hnd this hu'
  have hreach_seg : ∀ a b : Fin n, a.1 ∈ seg_nat →
      (b.1 ∈ seg_nat ↔ b ∉ T ∧ (restrict H {z | z ∉ T}).Reachable a b) := by
    intro a b ha
    constructor
    · intro hb
      exact ⟨hoff b hb, (hroot a ha).symm.trans (hroot b hb)⟩
    · rintro ⟨hbT, hreach⟩
      obtain ⟨W, hW⟩ := exists_walk_of_reachable_restrict hreach (hoff a ha)
      have hb_itf : b.1 ∈ items ++ seg_nat :=
        mem_of_walk_closed hcl_new W (List.mem_append_right _ ha)
          (fun z hz => labT_eq_zero.2 (hW z hz))
      rcases List.mem_append.mp hb_itf with hb_it | hb_seg
      · exact absurd hreach.symm (hcross b a hb_it ha)
      · exact hb_seg
  have hkeep₃ : ∀ r, r < 60 ∨ 71 ≤ r → s₃.regs r = s₁.regs r := hsi₃.frame.1
  have hkeepA₃ : ∀ a, a ≠ aLab → a ≠ aPar → a ≠ aQue → s₃.arrs a = s₁.arrs a := hsi₃.frame.2
  have hcomp₃ : CompSegsOK H T segs items s₃ :=
    hcomp.of_state
      (by rw [hkeep₃ rNumComp (Or.inr (by decide))]; simp [s₁])
      (by rw [hkeepA₃ aCompSt (by decide) (by decide) (by decide)]; simp [s₁])
      (by rw [hkeepA₃ aCompEn (by decide) (by decide) (by decide)]; simp [s₁])
      (by rw [hkeepA₃ aCompOf (by decide) (by decide) (by decide)]; simp [s₁])
  have hq₃ : IsQueueHistory aQue rHead rTail n (items ++ seg_nat) (items ++ seg_nat).length s₃ := by
    simpa [hitf] using hsi₃.queue
  have hlt₃ : ∀ x ∈ items ++ seg_nat, x < n := by
    simpa [hitf] using hsi₃.lt
  have hrst₃ : s₃.regs rSt = items.length := by
    rw [hkeep₃ rSt (Or.inr (by decide))]; simp [s₁]
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, segs', hcomp₄⟩ :=
    recordComp_exec H T hw1 hnw items seg_nat segs s₃ hq₃ hnd hlt₃ hoff hreach_seg hrst₃ hcomp₃
  set s₅ := s₄.setReg rV2 (v + 1)
  have hex : Exec w compFindStep s s₄ (2 + (t₂ + (t₃ + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  have hr₅ : ∀ r, 60 ≤ r → r < 71 → s₅.regs r = s₃.regs r := by
    intro r h1 h2
    have hne_v2 : r ≠ rV2 := by rintro rfl; exact absurd h2 (by decide)
    have hnot_rec : r ∉ [rJ, rU2, rNumComp] := by interval_cases r <;> decide
    rw [State.setReg_regs_ne _ _ hne_v2, hk₄.1 r hnot_rec]
  have ha₅ : ∀ a, a = aLab ∨ a = aPar ∨ a = aQue → s₅.arrs a = s₃.arrs a := by
    intro a ha
    have hnot_rec : a ∉ [aCompSt, aCompEn, aCompOf] := by
      rcases ha with rfl | rfl | rfl <;> decide
    rw [State.setReg_arrs, hk₄.2 a hnot_rec]
  have hsi₅ : SInv H (labT T) src₁ s₅ (items ++ seg_nat) (items ++ seg_nat).length s₅ := by
    simpa [hitf] using hsi₃.transfer hr₅ ha₅
  have hcomp₅ : CompSegsOK H T segs' (items ++ seg_nat) s₅ :=
    hcomp₄.of_state (by simp [s₅]) (by simp [s₅]) (by simp [s₅]) (by simp [s₅])
  refine ⟨s₄, _, hex, ?_, ⟨?_, by simp, items ++ seg_nat, src₁, segs', hsi₅, hcomp₅, ?_⟩, ?_⟩
  · -- Time bound via potential
    rw [compFindPot_eq hsi.queue, compFindPot_eq hsi₅.queue]
    have hseg_len : seg_nat.length = e₁.length + extra.length := by simp [seg_nat]
    have hlen_e1 : (items ++ e₁).length = items.length + e₁.length := by simp
    have hlen_seg : (items ++ seg_nat).length = items.length + seg_nat.length := by simp
    have q1 := popDeg_append_length lists items e₁
    have q2 := popDeg_append_length lists items seg_nat
    have hle_itf : items.length ≤ (items ++ seg_nat).length := by simp
    have hmono := popDeg_add lists (items ++ seg_nat) items.length
      ((items ++ seg_nat).length - items.length) (by omega)
    rw [Nat.add_sub_cancel' hle_itf] at hmono
    have hpd0 : popDeg lists (items ++ seg_nat) items.length ≤
        popDeg lists (items ++ seg_nat) (items ++ seg_nat).length := by
      rw [hmono]; omega
    rw [hitf] at ht₃
    omega
  · -- Keeps frame
    have hk₃ : Keeps compFindRegs compFindArrs s₀ s₃ :=
      hk₁.trans hsi₃.frame.keeps (by decide) (by decide)
    exact (hk₃.trans hk₄ (by decide) (by decide)).setReg (by simp [compFindRegs]) _
  · -- All vertices < v + 1 off T are in items ++ seg_nat
    intro x hx hxT
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | hx
    · exact List.mem_append_left _ (hall x hx hxT)
    · rcases hvcase with h | h
      · rw [hx, ← hitf]
        exact List.mem_append_left extra h
      · exact absurd (by
          have : x = ⟨v, hv⟩ := Fin.ext hx
          rw [this]; by_contra hc; exact h (labT_eq_zero.2 hc)) hxT
  · rw [hk₄.1 rV2 (by decide), hkeep₃ rV2 (Or.inr (by decide))]
    simp [s₁, hrv]

/-- **Execution of `compFindProg`.** Discovers all off-cycle connected components of `H - V(T)` in
at most `18 + 130 * n + 119 * totalAdjEntries lists` steps. -/
theorem compFindProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hadj₀ : IsAdjList H aStart aEnd aEnt lists s₀)
    (hn₀ : s₀.regs 40 = n) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hlab : s₀.arrs aLab = List.ofFn (labT T)) :
    ∃ s' t, Exec w compFindProg s₀ s' t ∧
      t ≤ 18 + 130 * n + 119 * totalAdjEntries lists ∧
      Keeps compFindRegs compFindArrs s₀ s' ∧
      ∃ (items : List ℕ) (segs : List (List (Fin n))),
        IsQueueHistory aQue rHead rTail n items items.length s' ∧
        CompSegsOK H T segs items s' ∧
        (∀ x : Fin n, x ∉ T → x.1 ∈ items) ∧ (∀ v ∈ items, v < n) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have h40 : (Expr.reg 40).eval w s₀ = some n := reg_eval hn₀ hnw
  set s₁ := s₀.setArr aPar (List.replicate n 0)
  set s₂ := s₁.setArr aQue (List.replicate n 0)
  set s₃ := s₂.setReg rHead 0
  set s₄ := s₃.setReg rTail 0
  set s₅ := s₄.setReg rHit n
  set s₆ := s₅.setArr aCompSt (List.replicate n 0)
  set s₇ := s₆.setArr aCompEn (List.replicate n 0)
  set s₈ := s₇.setArr aCompOf (List.replicate n 0)
  set s₉ := s₈.setReg rNumComp 0
  set s₁₀ := s₉.setReg rV2 0
  have hqi : Exec w (queueInit aQue rHead rTail (.reg 40)) s₁ s₄ ((1 + n) + (2 + 2)) :=
    .seq (.alloc (reg_eval (by simp [s₁, hn₀]) hnw))
      (.seq (.assign (by simp [checkWord])) (.assign (by simp [checkWord])))
  have hhit : Exec w (.assign rHit (.reg 40)) s₄ s₅ 2 :=
    .assign (reg_eval (by simp [s₄, s₃, s₂, s₁, hn₀]) hnw)
  have hal_st : Exec w (.alloc aCompSt (.reg 40)) s₅ s₆ (1 + n) :=
    .alloc (reg_eval (by simp [s₅, s₄, s₃, s₂, s₁, hn₀]) hnw)
  have hal_en : Exec w (.alloc aCompEn (.reg 40)) s₆ s₇ (1 + n) :=
    .alloc (reg_eval (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hn₀]) hnw)
  have hal_of : Exec w (.alloc aCompOf (.reg 40)) s₇ s₈ (1 + n) :=
    .alloc (reg_eval (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hn₀]) hnw)
  have hnc0 : Exec w (.assign rNumComp (.const 0)) s₈ s₉ 2 := .assign (by simp [checkWord])
  have hv0 : Exec w (.assign rV2 (.const 0)) s₉ s₁₀ 2 := .assign (by simp [checkWord])
  have hk₁₀ : Keeps compFindRegs compFindArrs s₀ s₁₀ :=
    ((((((((((Keeps.refl _ _ s₀).setArr (by simp [compFindArrs]) _).setArr
      (by simp [compFindArrs]) _).setReg (by simp [compFindRegs]) _).setReg
      (by simp [compFindRegs]) _).setReg (by simp [compFindRegs]) _).setArr
      (by simp [compFindArrs]) _).setArr (by simp [compFindArrs]) _).setArr
      (by simp [compFindArrs]) _).setReg (by simp [compFindRegs]) _).setReg
      (by simp [compFindRegs]) _
  have hI0 : CompFindInv H T s₀ 0 s₁₀ := by
    refine ⟨hk₁₀, by simp [s₁₀], [], [], [],
      ⟨⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩, ?_, List.nodup_nil, by simp, by simp, ?_,
        ⟨fun _ => 0, ?_, fun x hx => by simp at hx⟩, by simp, ?_, by simp⟩,
      ⟨by simp [s₁₀, s₉], le_rfl,
        by simp [s₁₀, s₉, s₈, s₇, s₆], by simp [s₁₀, s₉, s₈, s₇], by simp [s₁₀, s₉, s₈],
        by simp, by simp, by simp, by simp,
        fun _ _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h,
        fun _ h => by simp at h⟩,
      fun x hx => by omega⟩
    · exact ⟨by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂], by simp,
        by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃],
        by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄], le_rfl, fun i hi => by simp at hi⟩
    · simp only [List.not_mem_nil, ↓reduceIte]
      simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hlab]
    · simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, List.ofFn_const]
    · exact Or.inl ⟨by simp [s₁₀, s₉, s₈, s₇, s₆, s₅], fun v ⟨u, hu, _⟩ => by simp at hu⟩
  have hloop := forUp_pot (CompFindInv H T s₀) (compFindPot lists) n 65
    (r_i := rV2) (hi := .reg 40) (body := compFindStep) hw1 hnw
    (fun i _ st hst => ⟨hst.2.1, reg_eval (by rw [hst.1.1 40 (by decide)]; exact hn₀) hnw⟩)
    (fun i hi st hst => compFindStep_exec H lists T hn s₀ hadj₀ hn₀ hent i hi st hst)
    0 (Nat.zero_le _) s₁₀ hI0
  obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hk₁₁, -, items, src, segs, hsi, hcomp, hall⟩ := hloop
  have hpot0 : compFindPot lists s₁₀ = 0 := by
    simp [compFindPot, s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, popDeg]
  have hpot11 : compFindPot lists s₁₁ ≤ 51 * n + 119 * totalAdjEntries lists := by
    rw [compFindPot_eq hsi.queue]
    have h1 := length_le_of_nodup_lt hsi.nodup hsi.lt
    have h2 : popDeg lists items items.length ≤ totalAdjEntries lists := by
      unfold popDeg; rw [List.take_length]; exact sum_degOf_le lists hsi.nodup hsi.lt
    omega
  refine ⟨s₁₁, _,
    .seq (.alloc h40) (.seq hqi (.seq hhit (.seq hal_st (.seq hal_en
      (.seq hal_of (.seq hnc0 (.seq hv0 hex₁₁))))))),
    ?_, hk₁₁, items, segs, hsi.queue, hcomp, (fun x hx => hall x x.2 hx), hsi.lt⟩
  simp only [Expr.cost] at ht₁₁ ⊢
  omega

/-- From `IsQueueHistory` and `CompSegsOK`, each component `γ < segs.length` is stored as a slice
`IsListAt aCompSt aCompEn aQue γ st en ((segs[γ]).map Fin.val) s`. -/
theorem CompSegsOK.isListAt {H : SimpleGraph (Fin n)} {T : List (Fin n)}
    {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hq : IsQueueHistory aQue rHead rTail n items items.length s)
    (hcomp : CompSegsOK H T segs items s) {γ : ℕ} (hγ : γ < segs.length) :
    ∃ st en : ℕ,
      IsListAt aCompSt aCompEn aQue γ st en ((segs[γ]'hγ).map Fin.val) s := by
  have hit_le : items.length ≤ n := hq.2.1
  have hsegs_le_n : segs.length ≤ n := le_trans hcomp.segs_le_items hit_le
  obtain ⟨st, en, hst, hen, hen_le, hlen, hget⟩ := hcomp.slices γ hγ
  have hγ_st : γ < (s.arrs aCompSt).length := by rw [hcomp.len_st]; omega
  have hγ_en : γ < (s.arrs aCompEn).length := by rw [hcomp.len_en]; omega
  refine ⟨st, en, hγ_st, hγ_en, by rw [hq.1]; omega, by simp; omega,
    by simpa [List.getElem?_eq_getElem hγ_st] using hst,
    by simpa [List.getElem?_eq_getElem hγ_en] using hen,
    by omega, fun k hk => ?_⟩
  simp only [List.length_map] at hk
  have hget_k := hget k hk
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hget_k
  rw [List.getElem_map, ← hget_k]
  exact hq.2.2.2.2.2 (st + k) (by omega)

/-- For any off-cycle vertex `u ∉ T`, there is a unique component `γ₀ < segs.length` such that
`(s.arrs aCompOf)[u.1]? = some γ₀`, and for every `γ < segs.length`,
`(s.arrs aCompOf)[u.1]? = some γ ↔ u ∈ segs[γ]`. -/
theorem CompSegsOK.compOf_spec {H : SimpleGraph (Fin n)} {T : List (Fin n)}
    {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hcomp : CompSegsOK H T segs items s)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items)
    {u : Fin n} (huT : u ∉ T) :
    ∃ (γ₀ : ℕ) (hγ₀ : γ₀ < segs.length),
      (s.arrs aCompOf)[u.1]? = some γ₀ ∧
      u ∈ segs[γ₀]'hγ₀ ∧
      ∀ (γ : ℕ) (hγ : γ < segs.length),
        γ = γ₀ ↔ u ∈ segs[γ]'hγ := by
  obtain ⟨γ₀, hγ₀, hu₀⟩ := (hcomp.mem_items_iff u).mp (hall u huT)
  have heq₀ := hcomp.compOf_eq γ₀ hγ₀ u hu₀
  refine ⟨γ₀, hγ₀, heq₀, hu₀, fun γ hγ => ?_⟩
  constructor
  · rintro rfl; exact hu₀
  · intro hu_γ
    by_contra hne
    exact hcomp.disjoint_segs γ γ₀ hγ hγ₀ hne u hu_γ hu₀

/-! ### Part 2: Chord Bridge Enumeration (`chordEnumProg`) -/

/-- Condition for a chord `(D[rI2], rY)` with `rI2 + 1 < rQ` and `Apart rk rQ (rI2 + 1)`. -/
def chordEnumCond : Expr :=
  .op .mul (.op .lt (.op .add (.reg rI2) (.const 1)) (.reg rQ))
    (apartE (.op .add (.reg rI2) (.const 1)) (.reg rQ))

/-- Check one neighbour `rY` of `D[rI2]` and append `(rI2, rQ - 1)` to `(aChordI, aChordJ)` when
`chordEnumCond` holds. -/
def chordEnumBody : Cmd :=
  .seq (.assign rQ (.read aPos (.reg rY)))
    (.ite chordEnumCond
      (.seq (.write aChordI (.reg rNumChords) (.reg rI2))
        (.seq (.write aChordJ (.reg rNumChords) (.op .sub (.reg rQ) (.const 1)))
          (.assign rNumChords (.op .add (.reg rNumChords) (.const 1)))))
      .skip)

/-- Scan all neighbours of `D[rI2]`. -/
def chordEnumOuter : Cmd :=
  .seq (.assign rX2 (.read aCyc (.reg rI2)))
    (forList aStart aEnd aEnt rX2 rK2 rHi2 rY chordEnumBody)

/-- Enumerate all chord bridges of `D` in `G` into `(aChordI, aChordJ)` with count `rNumChords`. -/
def chordEnumProg : Cmd :=
  .seq (.alloc aChordI (.len aEnt))
    (.seq (.alloc aChordJ (.len aEnt))
      (.seq (.assign rNumChords (.const 0))
        (.seq (.assign rI2 (.const 0))
          (forUp rI2 (.reg rk) chordEnumOuter))))

/-- Registers written by `chordEnumProg`. -/
def chordEnumRegs : List ℕ := [rI2, rX2, rK2, rHi2, rY, rQ, rNumChords]

/-- Arrays written by `chordEnumProg`. -/
def chordEnumArrs : List ℕ := [aChordI, aChordJ]

/-- Pure specification of whether neighbour `y` of `T[i]` gives a chord `(i, j)` with `i < j`. -/
def chordPairOf (T : List (Fin n)) (i y : ℕ) : Option (ℕ × ℕ) :=
  if hy : y < n then
    let yFin : Fin n := ⟨y, hy⟩
    if yFin ∈ T then
      let j := T.idxOf yFin
      if i < j ∧ Apart T.length (j + 1) (i + 1) then
        some (i, j)
      else none
    else none
  else none

/-- Chords found among the first `j` neighbours of `T[i]`. -/
def chordsAt (lists : Fin n → List ℕ) (T : List (Fin n)) (i j : ℕ) : List (ℕ × ℕ) :=
  if hi : i < T.length then
    ((lists (T[i]'hi)).take j).filterMap (chordPairOf T i)
  else []

/-- Chords found among the first `i` vertices of `T`. -/
def chordsUpTo (lists : Fin n → List ℕ) (T : List (Fin n)) (i : ℕ) : List (ℕ × ℕ) :=
  (List.range i).flatMap (fun i' =>
    if hi' : i' < T.length then
      (lists (T[i']'hi')).filterMap (chordPairOf T i')
      else [])

theorem chordsAt_zero (lists : Fin n → List ℕ) (T : List (Fin n)) (i : ℕ) :
    chordsAt lists T i 0 = [] := by
  simp [chordsAt]

theorem chordsUpTo_zero (lists : Fin n → List ℕ) (T : List (Fin n)) :
    chordsUpTo lists T 0 = [] := by
  simp [chordsUpTo]

theorem chordsAt_succ (lists : Fin n → List ℕ) (T : List (Fin n)) {i j : ℕ}
    (hi : i < T.length) (hj : j < (lists (T[i]'hi)).length) :
    chordsAt lists T i (j + 1) =
      chordsAt lists T i j ++
        (match chordPairOf T i ((lists (T[i]'hi))[j]'hj) with
         | some p => [p]
         | none => []) := by
  simp only [chordsAt, hi, ↓reduceDIte, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases chordPairOf T i ((lists (T[i]'hi))[j]'hj) <;> rfl

theorem chordsUpTo_succ (lists : Fin n → List ℕ) (T : List (Fin n)) {i : ℕ}
    (hi : i < T.length) :
    chordsUpTo lists T (i + 1) =
      chordsUpTo lists T i ++ chordsAt lists T i (lists (T[i]'hi)).length := by
  simp [chordsUpTo, chordsAt, List.range_succ, hi]

theorem length_chordsAt_le (lists : Fin n → List ℕ) (T : List (Fin n)) {i : ℕ}
    (hi : i < T.length) (j : ℕ) (hj : j ≤ (lists (T[i]'hi)).length) :
    (chordsAt lists T i j).length ≤ j := by
  simp only [chordsAt, hi, ↓reduceDIte]
  exact le_trans (List.length_filterMap_le _ _) (by simp [hj])

theorem length_chordsUpTo_le_sum (lists : Fin n → List ℕ) (T : List (Fin n)) :
    ∀ i ≤ T.length,
      (chordsUpTo lists T i).length ≤
        ∑ i' ∈ Finset.range i, degOf lists ((T.map Fin.val).getD i' 0)
  | 0, _ => by simp [chordsUpTo]
  | i + 1, hi => by
    have hi' : i < T.length := by omega
    rw [chordsUpTo_succ lists T hi', List.length_append, Finset.sum_range_succ]
    have ih := length_chordsUpTo_le_sum lists T i (by omega)
    have hcur := length_chordsAt_le lists T hi' (lists (T[i]'hi')).length le_rfl
    have hdeg : degOf lists ((T.map Fin.val).getD i 0) = (lists (T[i]'hi')).length := by
      simp [degOf, List.getD_eq_getElem?_getD, hi']
    omega

theorem sum_range_le_sum_range {f : ℕ → ℕ} {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.range a, f i ≤ ∑ i ∈ Finset.range b, f i :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem length_chordsUpTo_add_chordsAt_lt (lists : Fin n → List ℕ) {T : List (Fin n)}
    (hT : T.Nodup) {i : ℕ} (hi : i < T.length) {j : ℕ} (hj : j < (lists (T[i]'hi)).length) :
    (chordsUpTo lists T i).length + (chordsAt lists T i j).length < totalAdjEntries lists := by
  have h1 := length_chordsUpTo_le_sum lists T i (by omega)
  have h2 := length_chordsAt_le lists T hi j (by omega)
  have hdeg : degOf lists ((T.map Fin.val).getD i 0) = (lists (T[i]'hi)).length := by
    simp [degOf, List.getD_eq_getElem?_getD, hi]
  have h3 : ∑ i' ∈ Finset.range (i + 1), degOf lists ((T.map Fin.val).getD i' 0) ≤
      totalAdjEntries lists := by
    refine le_trans (sum_range_le_sum_range (b := T.length) (by omega)) (sum_deg_cycle_le lists hT)
  rw [Finset.sum_range_succ, hdeg] at h3
  omega

/-- State predicate stating that `(aChordI, aChordJ)` with counter `rNumChords` holds `pairs`. -/
structure ChordsArrOK (M : ℕ) (pairs : List (ℕ × ℕ)) (s : State) : Prop where
  numChords : s.regs rNumChords = pairs.length
  pairs_le_M : pairs.length ≤ M
  len_I : (s.arrs aChordI).length = M
  len_J : (s.arrs aChordJ).length = M
  get_I : ∀ (m : ℕ) (hm : m < pairs.length),
    (s.arrs aChordI)[m]? = some (pairs[m]'hm).1
  get_J : ∀ (m : ℕ) (hm : m < pairs.length),
    (s.arrs aChordJ)[m]? = some (pairs[m]'hm).2

theorem ChordsArrOK.of_state {M : ℕ} {pairs : List (ℕ × ℕ)} {s s' : State}
    (h : ChordsArrOK M pairs s)
    (hr : s'.regs rNumChords = s.regs rNumChords)
    (hI : s'.arrs aChordI = s.arrs aChordI)
    (hJ : s'.arrs aChordJ = s.arrs aChordJ) :
    ChordsArrOK M pairs s' where
  numChords := by rw [hr, h.numChords]
  pairs_le_M := h.pairs_le_M
  len_I := by rw [hI, h.len_I]
  len_J := by rw [hJ, h.len_J]
  get_I := fun m hm => by rw [hI]; exact h.get_I m hm
  get_J := fun m hm => by rw [hJ]; exact h.get_J m hm

/-- Execution of `chordEnumBody` for one neighbour `y` of `T[i]`. -/
theorem chordEnumBody_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀)
    (M : ℕ) (hM_w : M < 2 ^ w)
    (i : ℕ) (hi : i < T.length) (y : Fin n)
    (pairs : List (ℕ × ℕ))
    (hpairs_lt : pairs.length < M)
    (s : State) (hk : Keeps chordEnumRegs chordEnumArrs s₀ s)
    (hri : s.regs rI2 = i) (hrx : s.regs rX2 = T[i].1) (hry : s.regs rY = y.1)
    (hch : ChordsArrOK M pairs s) :
    ∃ s' t, Exec w chordEnumBody s s' t ∧ t ≤ 50 ∧
      Keeps chordEnumRegs chordEnumArrs s₀ s' ∧
      s'.regs rI2 = i ∧ s'.regs rX2 = T[i].1 ∧
      s'.regs rK2 = s.regs rK2 ∧ s'.regs rHi2 = s.regs rHi2 ∧
      ChordsArrOK M (pairs ++ (match chordPairOf T i y.1 with | some p => [p] | none => [])) s' := by
  have hpre' : ChordPre H lists T s := by
    refine ⟨hpre.adj.of_arrs_eq (hk.2 _ (by decide)) (hk.2 _ (by decide)) (hk.2 _ (by decide)),
      by rw [hk.2 _ (by decide)]; exact hpre.cyc,
      by rw [hk.2 _ (by decide)]; exact hpre.pos,
      by rw [hk.1 _ (by decide)]; exact hpre.k,
      by rw [hk.1 _ (by decide)]; exact hpre.n⟩
  have hw1 : 1 < 2 ^ w := by omega
  have hyw : y.1 < 2 ^ w := by have := y.2; omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  obtain ⟨q, hq⟩ : ∃ q, (if y ∈ T then T.idxOf y + 1 else 0) = q := ⟨_, rfl⟩
  have hqk : q ≤ T.length := by
    rw [← hq]; split_ifs with h
    · exact pos_le h
    · omega
  have hqw : q < 2 ^ w := by omega
  have hiw : i + 1 < 2 ^ w := by omega
  have hread : (Expr.read aPos (.reg rY)).eval w s = some q := by
    simp [Expr.eval, checkWord, hry, hyw, hpre'.pos, posArr, hq, hqw]
  set s₁ := s.setReg rQ q
  have hex₁ : Exec w (.assign rQ (.read aPos (.reg rY))) s s₁ 3 := .assign hread
  have hk₁ : Keeps chordEnumRegs chordEnumArrs s₀ s₁ :=
    hk.setReg (by simp [chordEnumRegs]) _
  have hie : (Expr.op .add (.reg rI2) (.const 1)).eval w s₁ = some (i + 1) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hri, hiw, show i < 2 ^ w by omega, hw1]
  have hqe : (Expr.reg rQ).eval w s₁ = some q := by simp [checkWord, s₁, hqw]
  have hcond : chordEnumCond.eval w s₁ =
      some (if i + 1 < q ∧ Apart T.length q (i + 1) then 1 else 0) :=
    mul_eval (lt_eval hie hqe hw1)
      (apartE_eval hie hqe (by simp [s₁, hpre'.k]) (by omega) (by omega) hw1) hw1
  by_cases hc : i + 1 < q ∧ Apart T.length q (i + 1)
  · have hyT : y ∈ T := by
      by_contra h; simp [← hq, h] at hc
    have hqy : q = T.idxOf y + 1 := by simp [← hq, hyT]
    have hij : i < T.idxOf y := by omega
    have hap : Apart T.length (T.idxOf y + 1) (i + 1) := by rw [← hqy]; exact hc.2
    have hpair_eq : chordPairOf T i y.1 = some (i, T.idxOf y) := by
      simp [chordPairOf, y.2, Fin.eta, hyT, hij, hap]
    set m := pairs.length
    have hm_w : m < 2 ^ w := lt_trans hpairs_lt hM_w
    set s₂ := s₁.writeArr aChordI m i
    have hex₂ : Exec w (.write aChordI (.reg rNumChords) (.reg rI2)) s₁ s₂ 3 :=
      .write (reg_eval (by simp [s₁, hch.numChords, m]) hm_w)
        (reg_eval (by simp [s₁, hri]) (by omega))
        (by simp [s₁, hch.len_I]; exact hpairs_lt)
    set s₃ := s₂.writeArr aChordJ m (q - 1)
    have hex₃ : Exec w (.write aChordJ (.reg rNumChords) (.op .sub (.reg rQ) (.const 1))) s₂ s₃ 5 :=
      .write (reg_eval (by simp [s₂, s₁, hch.numChords, m]) hm_w)
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hqw, hw1,
          show q - 1 < 2 ^ w by omega])
        (by simp [s₂, s₁, hch.len_J]; exact hpairs_lt)
    set s₄ := s₃.setReg rNumChords (m + 1)
    have hex₄ : Exec w (.assign rNumChords (.op .add (.reg rNumChords) (.const 1))) s₃ s₄ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, s₂, s₁, hch.numChords, m,
        hm_w, hw1, show m + 1 < 2 ^ w by omega])
    have hex : Exec w chordEnumBody s s₄ (3 + (chordEnumCond.cost + (3 + (5 + 4)))) :=
      .seq hex₁ (.ite_true (by rw [hcond]; simp [hc]) one_ne_zero (.seq hex₂ (.seq hex₃ hex₄)))
    refine ⟨s₄, _, hex, by simp [chordEnumCond, apartE, distE, Expr.cost],
      (((hk₁.writeArr (by simp [chordEnumArrs]) _ _).writeArr
        (by simp [chordEnumArrs]) _ _).setReg (by simp [chordEnumRegs]) _),
      by simp [s₄, s₃, s₂, s₁, hri], by simp [s₄, s₃, s₂, s₁, hrx],
      by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂, s₁], ?_⟩
    rw [hpair_eq]
    refine ⟨by simp [s₄, m], by simp; omega,
      by simp [s₄, s₃, s₂, s₁, hch.len_I], by simp [s₄, s₃, s₂, s₁, hch.len_J],
      fun idx hidx => ?_, fun idx hidx => ?_⟩
    · simp only [List.length_append, List.length_singleton] at hidx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · have hne : m ≠ idx := Nat.ne_of_gt hlt
        simp [s₄, s₃, s₂, s₁, List.getElem?_set_ne hne, List.getElem_append_left hlt,
          hch.get_I idx hlt]
      · simp [s₄, s₃, s₂, s₁, m, hch.len_I, hpairs_lt]
    · simp only [List.length_append, List.length_singleton] at hidx
      rcases Nat.lt_succ_iff_lt_or_eq.mp hidx with hlt | rfl
      · have hne : m ≠ idx := Nat.ne_of_gt hlt
        simp [s₄, s₃, s₂, s₁, List.getElem?_set_ne hne, List.getElem_append_left hlt,
          hch.get_J idx hlt]
      · simp [s₄, s₃, s₂, s₁, m, hch.len_J, hpairs_lt, hqy]
  · have hpair_eq : chordPairOf T i y.1 = none := by
      simp only [chordPairOf, y.2, ↓reduceDIte, Fin.eta]
      split_ifs with hyT hcond'
      · exfalso
        apply hc
        have hqy : q = T.idxOf y + 1 := by simp [← hq, hyT]
        rw [hqy]
        exact ⟨by omega, hcond'.2⟩
      · rfl
      · rfl
    have hex : Exec w chordEnumBody s s₁ (3 + (chordEnumCond.cost + 1)) :=
      .seq hex₁ (.ite_false (by rw [hcond]; simp [hc]) (.skip _))
    refine ⟨s₁, _, hex, by simp [chordEnumCond, apartE, distE, Expr.cost], hk₁,
      by simp [s₁, hri], by simp [s₁, hrx], by simp [s₁], by simp [s₁], ?_⟩
    rw [hpair_eq]
    simpa using hch.of_state (by simp [s₁]) (by simp [s₁]) (by simp [s₁])

/-- Execution of `chordEnumOuter` for cycle index `i < T.length`. -/
theorem chordEnumOuter_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (M : ℕ) (hM_le : totalAdjEntries lists ≤ M) (hM_w : M < 2 ^ w)
    (i : ℕ) (hi : i < T.length)
    (s : State) (hk : Keeps chordEnumRegs chordEnumArrs s₀ s)
    (hri : s.regs rI2 = i)
    (hch : ChordsArrOK M (chordsUpTo lists T i) s) :
    ∃ s' t, Exec w chordEnumOuter s s' t ∧
      t ≤ 12 + 60 * (lists T[i]).length ∧
      Keeps chordEnumRegs chordEnumArrs s₀ s' ∧
      s'.regs rI2 = i ∧
      ChordsArrOK M (chordsUpTo lists T (i + 1)) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set x := T[i] with hx
  have hxw : x.1 < 2 ^ w := by have := x.2; omega
  have hcyc_s : s.arrs aCyc = T.map Fin.val := by
    rw [hk.2 aCyc (by decide)]; exact hpre.cyc
  have hread : (Expr.read aCyc (.reg rI2)).eval w s = some x.1 := by
    simp [Expr.eval, checkWord, hri, hcyc_s, hi, x, hxw, show i < 2 ^ w by omega]
  set s₁ := s.setReg rX2 x.1
  have hex₁ : Exec w (.assign rX2 (.read aCyc (.reg rI2))) s s₁ 3 := .assign hread
  have hk₁ : Keeps chordEnumRegs chordEnumArrs s₀ s₁ :=
    hk.setReg (by simp [chordEnumRegs]) _
  obtain ⟨st, en, hlist₀⟩ := hpre.adj.1.2.2 x
  obtain ⟨hmem_lt, -, -, _⟩ := hpre.adj.2 x
  have hlistOf : ∀ st' : State, Keeps chordEnumRegs chordEnumArrs s₀ st' →
      IsListAt aStart aEnd aEnt x.1 st en (lists x) st' := fun st' hk' =>
    hlist₀.of_arrs_eq (hk'.2 _ (by decide)) (hk'.2 _ (by decide)) (hk'.2 _ (by decide))
  have hen_w : en < 2 ^ w := by
    obtain ⟨_, _, hle, _⟩ := hlist₀
    omega
  let II : ℕ → State → Prop := fun j st' =>
    Keeps chordEnumRegs chordEnumArrs s₀ st' ∧
    st'.regs rI2 = i ∧
    st'.regs rX2 = x.1 ∧
    ChordsArrOK M (chordsUpTo lists T i ++ chordsAt lists T i j) st'
  have hI0 : II 0 s₁ := by
    refine ⟨hk₁, by simp [s₁, hri], by simp [s₁], ?_⟩
    rw [chordsAt_zero, List.append_nil]
    exact hch.of_state (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
  have hinit : ∀ st', II 0 st' → IsListAt aStart aEnd aEnt x.1 st en (lists x) st' ∧
      st'.regs rX2 = x.1 ∧ II 0 ((st'.setReg rK2 st).setReg rHi2 en) := by
    intro st' ⟨hk', hri', hrx', hch'⟩
    refine ⟨hlistOf st' hk', hrx',
      (hk'.setReg (by simp [chordEnumRegs]) st).setReg (by simp [chordEnumRegs]) en,
      by simp [hri'], by simp [hrx'],
      hch'.of_state (by simp) (by simp) (by simp)⟩
  have hfor := Triple.forList_const aStart aEnd aEnt rX2 rK2 rHi2 rY x.1 st en (lists x) II 50
    chordEnumBody (by decide) (by decide) hw1 hxw hen_w
    (fun z hz => by have := hmem_lt z hz; omega) hinit
    (fun j _ st' hst' => hlistOf st' hst'.1)
    (fun j hj sv ⟨st', ⟨hk', hri', hrx', hch'⟩, hsv, hrk, hrhi⟩ => by
      subst hsv
      have hyn : (lists x)[j] < n := hmem_lt _ (List.getElem_mem hj)
      have hpairs_lt : (chordsUpTo lists T i ++ chordsAt lists T i j).length < M := by
        have hlt := length_chordsUpTo_add_chordsAt_lt lists hT hi hj
        rw [List.length_append]
        omega
      obtain ⟨s', t, hex, ht, hk'', hri'', hrx'', hrk'', hrhi'', hch''⟩ :=
        chordEnumBody_exec H lists T hT hn s₀ hpre M hM_w i hi ⟨(lists x)[j], hyn⟩
          (chordsUpTo lists T i ++ chordsAt lists T i j) hpairs_lt
          (st'.setReg rY (lists x)[j]) (hk'.setReg (by simp [chordEnumRegs]) _)
          (by simp [hri']) (by simp [hrx', hx]) (by simp)
          (hch'.of_state (by simp) (by simp) (by simp))
      have hII : II (j + 1) (s'.setReg rK2 (st + (j + 1))) := by
        refine ⟨hk''.setReg (by simp [chordEnumRegs]) _, by simp [hri''], by simp [hrx'', hx], ?_⟩
        rw [chordsAt_succ lists T hi hj, ← List.append_assoc]
        exact hch''.of_state (by simp) (by simp) (by simp)
      exact ⟨s', t, hex, ht, hII, by rw [hrk'']; simpa using hrk, by rw [hrhi'']; simpa using hrhi⟩)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hri₂, -, hch₂⟩ := hfor s₁ hI0
  refine ⟨s₂, _, .seq hex₁ hex₂, by dsimp only at ht₂; omega, hk₂, hri₂, ?_⟩
  rw [chordsUpTo_succ lists T hi]
  exact hch₂

/-- **Execution of `chordEnumProg`.** Enumerates all chord bridges of `T` in `H` into
`(aChordI, aChordJ)` with count `rNumChords` in at most
`10 + 19 * |T| + 2 * |(s₀.arrs aEnt)| + 60 * totalAdjEntries lists` steps. -/
theorem chordEnumProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hM_le : totalAdjEntries lists ≤ (s₀.arrs aEnt).length) :
    ∃ s' t, Exec w chordEnumProg s₀ s' t ∧
      t ≤ 10 + 19 * T.length + 2 * (s₀.arrs aEnt).length + 60 * totalAdjEntries lists ∧
      Keeps chordEnumRegs chordEnumArrs s₀ s' ∧
      ChordsArrOK (s₀.arrs aEnt).length (chordsUpTo lists T T.length) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set M := (s₀.arrs aEnt).length with hM_def
  set s₁ := s₀.setArr aChordI (List.replicate M 0)
  have hex₁ : Exec w (.alloc aChordI (.len aEnt)) s₀ s₁ (1 + M) :=
    .alloc (by simp [Expr.eval, checkWord, ← hM_def, hent])
  set s₂ := s₁.setArr aChordJ (List.replicate M 0)
  have hex₂ : Exec w (.alloc aChordJ (.len aEnt)) s₁ s₂ (1 + M) :=
    .alloc (by simp [Expr.eval, checkWord, s₁, ← hM_def, hent])
  set s₃ := s₂.setReg rNumChords 0
  have hex₃ : Exec w (.assign rNumChords (.const 0)) s₂ s₃ 2 := .assign (by simp [checkWord])
  set s₄ := s₃.setReg rI2 0
  have hex₄ : Exec w (.assign rI2 (.const 0)) s₃ s₄ 2 := .assign (by simp [checkWord])
  let OI : ℕ → State → Prop := fun i st =>
    Keeps chordEnumRegs chordEnumArrs s₀ st ∧
    st.regs rI2 = i ∧
    ChordsArrOK M (chordsUpTo lists T i) st
  have hI0 : OI 0 s₄ := by
    refine ⟨((((Keeps.refl _ _ s₀).setArr (by simp [chordEnumArrs]) _).setArr
      (by simp [chordEnumArrs]) _).setReg (by simp [chordEnumRegs]) _).setReg
      (by simp [chordEnumRegs]) _, by simp [s₄], ?_⟩
    rw [chordsUpTo_zero]
    exact ⟨by simp [s₄, s₃], Nat.zero_le _, by simp [s₄, s₃, s₂, s₁], by simp [s₄, s₃, s₂],
      fun _ h => by simp at h, fun _ h => by simp at h⟩
  have hloop := Triple.forUp_sum OI T.length
    (fun i => 12 + 60 * degOf lists ((T.map Fin.val).getD i 0))
    (r_i := rI2) (hi := .reg rk) (body := chordEnumOuter) hw1 (by omega)
    (fun i _ st hst => ⟨hst.2.1,
      reg_eval (by rw [hst.1.1 rk (by decide), hpre.k]) (by omega)⟩)
    (fun i hi st ⟨hk, hri, hch⟩ => by
      obtain ⟨s', t, hex, ht, hk', hri', hch'⟩ :=
        chordEnumOuter_exec H lists T hT hn s₀ hpre hent M hM_le hent i hi st hk hri hch
      refine ⟨s', t, hex, ?_, ⟨hk'.setReg (by simp [chordEnumRegs]) _, by simp,
        hch'.of_state (by simp) (by simp) (by simp)⟩, hri'⟩
      have hd : degOf lists ((T.map Fin.val).getD i 0) = (lists T[i]).length := by
        simp [degOf, List.getD_eq_getElem?_getD, hi]
      show t ≤ 12 + 60 * degOf lists ((T.map Fin.val).getD i 0)
      rw [hd]; exact ht)
  obtain ⟨s₅, t₅, hex₅, ht₅, hk₅, -, hch₅⟩ := hloop s₄ hI0
  refine ⟨s₅, _, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, hk₅, hch₅⟩
  have hsum := sum_deg_cycle_le lists hT
  simp only [Expr.cost] at ht₅
  have e : ∑ j ∈ Finset.range T.length,
      (1 + 6 + (12 + 60 * degOf lists ((T.map Fin.val).getD j 0))) =
      19 * T.length + 60 * ∑ j ∈ Finset.range T.length,
        degOf lists ((T.map Fin.val).getD j 0) := by
    rw [Finset.mul_sum, show 19 * T.length = ∑ _j ∈ Finset.range T.length, 19 by simp [mul_comm],
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e] at ht₅
  omega

/-! ### Part 3: Mathematical Properties of `chordsUpTo` and `ValidBridgeList` -/

/-- For `i < j < T.length` and `T.Nodup`, `Apart T.length (j + 1) (i + 1)` holds if and only if
`D[i]` and `D[j]` do not form a cycle edge of `T`. -/
theorem apart_iff_not_isCycleEdge {T : List (Fin n)} (hT : T.Nodup) {i j : ℕ}
    (hij : i < j) (hj : j < T.length) :
    Apart T.length (j + 1) (i + 1) ↔ ¬ PlaneEmbedding.IsCycleEdge T T[i] T[j] := by
  have hi : i < T.length := lt_trans hij hj
  have hii : T.idxOf T[i] = i := hT.idxOf_getElem i hi
  have hjj : T.idxOf T[j] = j := hT.idxOf_getElem j hj
  rw [isCycleEdge_iff_idxOf hT]
  simp only [List.getElem_mem, true_and, hii, hjj]
  unfold Apart
  rw [cdist_eq ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  simp only [show ¬(j + 1 < i + 1) by omega, ↓reduceIte, show j + 1 - (i + 1) = j - i by omega]
  have hmod_i : (i + 1) % T.length = i + 1 := Nat.mod_eq_of_lt (by omega)
  have hmod_j : (j + 1) % T.length = if j + 1 = T.length then 0 else j + 1 := by
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [hmod_i, hmod_j]
  split_ifs <;> omega

/-- Membership characterization of `chordsUpTo lists T T.length`. -/
theorem mem_chordsUpTo_iff {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hadj : IsAdjListFamily H lists) {T : List (Fin n)} (hT : T.Nodup) {p : ℕ × ℕ} :
    p ∈ chordsUpTo lists T T.length ↔
      ∃ (hi : p.1 < T.length) (hj : p.2 < T.length),
        p.1 < p.2 ∧ H.Adj (T[p.1]'hi) (T[p.2]'hj) ∧
        ¬ PlaneEmbedding.IsCycleEdge T (T[p.1]'hi) (T[p.2]'hj) := by
  rcases p with ⟨i, j⟩
  simp only [chordsUpTo, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨i', hi', h⟩
    simp only [hi', ↓reduceDIte, List.mem_filterMap] at h
    obtain ⟨y, hy_mem, hpair⟩ := h
    simp only [chordPairOf] at hpair
    split_ifs at hpair with hy_n hyT hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hpair
    rcases hpair with ⟨rfl, rfl⟩
    set yFin : Fin n := ⟨y, hy_n⟩
    have hj_lt : T.idxOf yFin < T.length := List.idxOf_lt_length_of_mem hyT
    have hget_j : T[T.idxOf yFin]'hj_lt = yFin := List.getElem_idxOf hj_lt
    have hadj_ij : H.Adj T[i'] (T[T.idxOf yFin]'hj_lt) := by
      rw [hget_j]
      exact ((hadj T[i']).2.2.2 yFin).mp hy_mem
    refine ⟨hi', hj_lt, hcond.1, hadj_ij, ?_⟩
    exact (apart_iff_not_isCycleEdge hT hcond.1 hj_lt).mp hcond.2
  · rintro ⟨hi, hj, hij, hadj_ij, hnot_cyc⟩
    refine ⟨i, hi, ?_⟩
    simp only [hi, ↓reduceDIte, List.mem_filterMap]
    refine ⟨(T[j]'hj).1, ((hadj T[i]).2.2.2 T[j]).mpr hadj_ij, ?_⟩
    have hjj : T.idxOf (T[j]'hj) = j := hT.idxOf_getElem j hj
    have hap : Apart T.length (j + 1) (i + 1) :=
      (apart_iff_not_isCycleEdge hT hij hj).mpr hnot_cyc
    simp [chordPairOf, (T[j]'hj).2, Fin.eta, List.getElem_mem hj, hjj, hij, hap]

theorem fst_lt_of_mem_chordsUpTo {lists : Fin n → List ℕ} {T : List (Fin n)} {k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ chordsUpTo lists T k) : p.1 < k := by
  simp only [chordsUpTo, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨i', hi', h⟩ := hp
  split_ifs at h with hi_T
  · simp only [List.mem_filterMap, chordPairOf] at h
    obtain ⟨y, _, hy⟩ := h
    split_ifs at hy
    simp only [Option.some.injEq] at hy
    rw [← hy]
    exact hi'
  · simp at h

theorem nodup_chordsUpTo_aux {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hadj : IsAdjListFamily H lists) {T : List (Fin n)} :
    ∀ k ≤ T.length, (chordsUpTo lists T k).Nodup
  | 0, _ => by simp [chordsUpTo]
  | k + 1, hk => by
    have hk' : k < T.length := by omega
    rw [chordsUpTo_succ lists T hk', List.nodup_append]
    refine ⟨nodup_chordsUpTo_aux hadj k (by omega), ?_, ?_⟩
    · simp only [chordsAt, hk', ↓reduceDIte, List.take_length]
      refine ((hadj T[k]).2.1).filterMap ?_
      intro y₁ y₂ p hp₁ hp₂
      simp only [Option.mem_def, chordPairOf] at hp₁ hp₂
      split_ifs at hp₁ with h1_n h1_T h1_c
      split_ifs at hp₂ with h2_n h2_T h2_c
      rw [Option.some.injEq] at hp₁ hp₂
      subst hp₁
      have hj_eq : T.idxOf ⟨y₁, h1_n⟩ = T.idxOf ⟨y₂, h2_n⟩ := (Prod.mk.injEq ..).mp hp₂.symm |>.2
      have hfin_eq : (⟨y₁, h1_n⟩ : Fin n) = ⟨y₂, h2_n⟩ := by
        have h1_lt := List.idxOf_lt_length_of_mem h1_T
        have h2_lt := List.idxOf_lt_length_of_mem h2_T
        rw [← List.getElem_idxOf h1_lt, ← List.getElem_idxOf h2_lt]
        congr 1
      exact congrArg Fin.val hfin_eq
    · intro p₁ hp₁ p₂ hp₂ heq
      subst heq
      have hlt : p₁.1 < k := fst_lt_of_mem_chordsUpTo hp₁
      simp only [chordsAt, hk', ↓reduceDIte, List.take_length, List.mem_filterMap,
        chordPairOf] at hp₂
      obtain ⟨y, _, hy⟩ := hp₂
      split_ifs at hy
      rw [Option.some.injEq] at hy
      have heq_k : p₁.1 = k := by rw [← hy]
      omega

/-- `chordsUpTo lists T T.length` has no duplicate pairs. -/
theorem nodup_chordsUpTo {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hadj : IsAdjListFamily H lists) {T : List (Fin n)} (_hT : T.Nodup) :
    (chordsUpTo lists T T.length).Nodup :=
  nodup_chordsUpTo_aux hadj T.length le_rfl

/-- Convert a list of index pairs `(i, j)` into chord `BridgeData` on `T`. -/
def chordBridgesOfPairs (T : List (Fin n)) (pairs : List (ℕ × ℕ)) : List (BridgeData (Fin n)) :=
  pairs.map (fun p =>
    if h : p.1 < T.length ∧ p.2 < T.length then
      BridgeData.chord (T[p.1]'h.1) (T[p.2]'h.2)
    else
      BridgeData.comp [])

/-- Build the full list of bridges `compBridges ++ chordBridges` from `segs` and `chordPairs`. -/
def bridgesOfSegsAndChords (T : List (Fin n)) (segs : List (List (Fin n)))
    (chordPairs : List (ℕ × ℕ)) : List (BridgeData (Fin n)) :=
  segs.map BridgeData.comp ++ chordBridgesOfPairs T chordPairs

/-- **`bridgesOfSegsAndChords` is a `ValidBridgeList`.** -/
theorem validBridgeList_bridgesOfSegsAndChords {H : SimpleGraph (Fin n)} [DecidableRel H.Adj]
    {lists : Fin n → List ℕ}
    (hadj : IsAdjListFamily H lists) {T : List (Fin n)} (hT : T.Nodup)
    {segs : List (List (Fin n))} {items : List ℕ} {s : State}
    (hcomp : CompSegsOK H T segs items s)
    (hall : ∀ x : Fin n, x ∉ T → x.1 ∈ items) :
    ValidBridgeList H (List.finRange n) T
      (bridgesOfSegsAndChords T segs (chordsUpTo lists T T.length)) := by
  have hmem_verts : ∀ x : Fin n, x ∈ List.finRange n := List.mem_finRange
  refine ⟨?_, ?_, ?_⟩
  · -- 1. pairwise_ne
    rw [bridgesOfSegsAndChords, List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · -- compBridges pairwise distinct
      rw [List.pairwise_iff_getElem]
      intro γ₁ γ₂ h₁ h₂ hlt heq
      simp only [List.length_map, List.getElem_map, BridgeData.toBridge,
        Bridge.comp.injEq, Set.ext_iff] at h₁ h₂ heq
      have hne_seg := hcomp.nonempty (segs[γ₁]'h₁) (List.getElem_mem h₁)
      obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hne_seg
      have hu₂ : u ∈ segs[γ₂]'h₂ := (heq u).mp hu
      exact hcomp.disjoint_segs γ₁ γ₂ h₁ h₂ (Nat.ne_of_lt hlt) u hu hu₂
    · -- chordBridges pairwise distinct
      rw [List.pairwise_iff_getElem]
      intro m₁ m₂ hm₁ hm₂ hlt heq
      simp only [chordBridgesOfPairs, List.length_map, List.getElem_map] at hm₁ hm₂ heq
      have hp₁ := (mem_chordsUpTo_iff hadj hT).mp (List.getElem_mem hm₁)
      have hp₂ := (mem_chordsUpTo_iff hadj hT).mp (List.getElem_mem hm₂)
      obtain ⟨hi₁, hj₁, hlt₁, _, _⟩ := hp₁
      obtain ⟨hi₂, hj₂, hlt₂, _, _⟩ := hp₂
      simp only [hi₁, hj₁, hi₂, hj₂, and_self, ↓reduceDIte, BridgeData.toBridge,
        Bridge.chord.injEq, Sym2.eq_iff] at heq
      have hnd_pairs := nodup_chordsUpTo hadj hT
      have hne_m : m₁ ≠ m₂ := Nat.ne_of_lt hlt
      rcases heq with ⟨hA, hB⟩ | ⟨hA, hB⟩
      · have heq_i := (hT.getElem_inj_iff).mp hA
        have heq_j := (hT.getElem_inj_iff).mp hB
        have hp_eq : (chordsUpTo lists T T.length)[m₁] = (chordsUpTo lists T T.length)[m₂] :=
          Prod.ext heq_i heq_j
        exact hne_m ((hnd_pairs.getElem_inj_iff).mp hp_eq)
      · have heq_i := (hT.getElem_inj_iff).mp hA
        have heq_j := (hT.getElem_inj_iff).mp hB
        omega
    · -- compBridge ≠ chordBridge
      intro b₁ hb₁ b₂ hb₂ heq
      simp only [List.mem_map] at hb₁
      obtain ⟨seg, _, rfl⟩ := hb₁
      simp only [chordBridgesOfPairs, List.mem_map] at hb₂
      obtain ⟨p, hp, rfl⟩ := hb₂
      obtain ⟨hi, hj, _⟩ := (mem_chordsUpTo_iff hadj hT).mp hp
      simp [hi, hj, BridgeData.toBridge] at heq
  · -- 2. valid_mem
    intro bd hbd
    rw [bridgesOfSegsAndChords, List.mem_append] at hbd
    rcases hbd with hcomp_mem | hchord_mem
    · simp only [List.mem_map] at hcomp_mem
      obtain ⟨seg, hseg, rfl⟩ := hcomp_mem
      obtain ⟨γ, hγ, rfl⟩ := List.getElem_of_mem hseg
      have hne_seg := hcomp.nonempty (segs[γ]'hγ) hseg
      obtain ⟨v₀, hv₀⟩ := List.exists_mem_of_ne_nil _ hne_seg
      refine ⟨?_, fun A hA => ?_⟩
      · simp only [BridgeData.toBridge, Crossing.IsBridge, IsOffCycleComp]
        refine ⟨v₀, hmem_verts v₀, hcomp.off_cyc _ hseg v₀ hv₀, ?_⟩
        ext v
        exact hcomp.comp_reach γ hγ v₀ hv₀ v
      · cases hA
        exact ⟨hcomp.nodup_seg _ hseg, hcomp.off_cyc _ hseg⟩
    · simp only [chordBridgesOfPairs, List.mem_map] at hchord_mem
      obtain ⟨p, hp, rfl⟩ := hchord_mem
      obtain ⟨hi, hj, _, hadj_p, hnot_cyc⟩ := (mem_chordsUpTo_iff hadj hT).mp hp
      simp only [hi, hj, and_self, ↓reduceDIte]
      refine ⟨?_, fun A hA => by cases hA⟩
      simp only [BridgeData.toBridge, Crossing.IsBridge]
      exact ⟨T[p.1], T[p.2], rfl, List.getElem_mem hi, List.getElem_mem hj, hadj_p, hnot_cyc⟩
  · -- 3. complete
    intro B hB
    cases B with
    | comp A =>
      obtain ⟨v₀, _, hv₀_T, rfl⟩ := hB
      obtain ⟨γ, hγ, hv₀_seg⟩ := (hcomp.mem_items_iff v₀).mp (hall v₀ hv₀_T)
      refine ⟨γ, ?_, ?_⟩
      · rw [bridgesOfSegsAndChords, List.length_append, List.length_map]; omega
      · have hlt_comp : γ < (segs.map BridgeData.comp).length := by simp [hγ]
        simp only [bridgesOfSegsAndChords, List.getElem_append_left hlt_comp,
          List.getElem_map, BridgeData.toBridge, Bridge.comp.injEq]
        ext v
        exact hcomp.comp_reach γ hγ v₀ hv₀_seg v
    | chord e =>
      obtain ⟨u, v, rfl, huT, hvT, hadj_uv, hnot_cyc⟩ := hB
      have huv : u ≠ v := H.ne_of_adj hadj_uv
      obtain ⟨i₀, hi₀, rfl⟩ := List.getElem_of_mem huT
      obtain ⟨j₀, hj₀, rfl⟩ := List.getElem_of_mem hvT
      have hij_ne : i₀ ≠ j₀ := fun h => huv (by subst h; rfl)
      have hex_pair : ∃ p ∈ chordsUpTo lists T T.length,
          ∃ (hi : p.1 < T.length) (hj : p.2 < T.length),
            s(T[p.1]'hi, T[p.2]'hj) = s(T[i₀], T[j₀]) := by
        rcases lt_trichotomy i₀ j₀ with hlt | rfl | hgt
        · refine ⟨(i₀, j₀), (mem_chordsUpTo_iff hadj hT).mpr ⟨hi₀, hj₀, hlt, hadj_uv, hnot_cyc⟩,
            hi₀, hj₀, rfl⟩
        · exact absurd rfl hij_ne
        · have hnot_cyc' : ¬ PlaneEmbedding.IsCycleEdge T T[j₀] T[i₀] := by
            unfold PlaneEmbedding.IsCycleEdge
            rw [Sym2.eq_swap]; exact hnot_cyc
          refine ⟨(j₀, i₀),
            (mem_chordsUpTo_iff hadj hT).mpr ⟨hj₀, hi₀, hgt, hadj_uv.symm, hnot_cyc'⟩,
            hj₀, hi₀, Sym2.eq_swap⟩
      obtain ⟨p, hp_mem, hi, hj, hsym⟩ := hex_pair
      obtain ⟨m, hm, hp_eq⟩ := List.getElem_of_mem hp_mem
      refine ⟨segs.length + m, ?_, ?_⟩
      · rw [bridgesOfSegsAndChords, List.length_append, List.length_map,
          chordBridgesOfPairs, List.length_map]
        omega
      · simp only [bridgesOfSegsAndChords]
        rw [List.getElem_append_right (by simp)]
        simp only [List.length_map, Nat.add_sub_cancel_left, chordBridgesOfPairs, List.getElem_map]
        have hi_m : (chordsUpTo lists T T.length)[m].1 < T.length := by rw [hp_eq]; exact hi
        have hj_m : (chordsUpTo lists T T.length)[m].2 < T.length := by rw [hp_eq]; exact hj
        simp only [hi_m, hj_m, and_self, ↓reduceDIte, BridgeData.toBridge, Bridge.chord.injEq]
        convert hsym using 2 <;> simp [hp_eq]

end GraphMinor.Compute
