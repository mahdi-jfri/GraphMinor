module

public import GraphMinor.Compute.GM06DartPairKeysProgram
public import GraphMinor.Compute.GM06CandidateEdgeProgram
public import GraphMinor.Compute.CrossingOpsEmit

/-!
# Materializing the directed edge row of a BFS path

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) return
actual directed edges for the successful vertex path. The RAM BFS
stores all but its last vertex in 634 and its last vertex in register
645. This program reads each consecutive pair, computes its positive
key, searches the retained-dart key row, and emits that permanent
dart label. No predecessor edge or replacement row is supplied.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- There is one recovered dart per vertex preceding the final target. -/
theorem gm06PathDarts_append_target_length (n : ℕ) (origins active before : List ℕ) (target : ℕ) :
    (gm06PathDarts n origins active (before ++ [target])).length = before.length := by
  simp only [gm06PathDarts, List.length_map, List.length_zip, List.length_append,
    List.length_singleton, List.length_tail, Nat.add_sub_cancel, Nat.min_eq_right (by omega : before.length ≤ before.length + 1)]

/-- The i-th emitted dart joins the i-th BFS vertex to the next vertex. -/
theorem gm06PathDarts_append_target_get {n i : ℕ} (origins active before : List ℕ) (target : ℕ)
    (hi : i < before.length) :
    (gm06PathDarts n origins active (before ++ [target]))[i]'(by
      rw [gm06PathDarts_append_target_length]; exact hi) =
      gm06PathDart n origins active before[i] ((before ++ [target])[i + 1]?.getD 0) := by
  have hnext : i + 1 < (before ++ [target]).length := by simp only [List.length_append, List.length_singleton]; omega
  simp only [gm06PathDarts, List.getElem_map, List.getElem_zip, List.getElem_tail,
    List.getElem_append_left hi, List.getElem?_eq_getElem hnext, Option.getD_some]

/-- Read the next pair, using target 645 only after the last stored vertex. -/
def gm06ReadBfsPairProg : Cmd :=
  .seq (.assign 674 (.read 634 (.reg 675)))
    (.ite (exprLt (.op .add (.reg 675) (.const 1)) (.len 634))
      (.assign 679 (.read 634 (.op .add (.reg 675) (.const 1)))) (.assign 679 (.reg 645)))

/-- Reading a consecutive pair preserves the complete stored vertex row. -/
theorem gm06ReadBfsPairProg_exec {w n i : ℕ} (before : List ℕ) (target : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : before.length < 2 ^ w) (hi : i < before.length)
    (hvalues : ∀ v ∈ before, v < n) (htarget : target < n)
    (h634 : s.arrs 634 = before) (h645 : s.regs 645 = target) (h675 : s.regs 675 = i) :
    ∃ sf t, Exec w gm06ReadBfsPairProg s sf t ∧ t ≤ 13 ∧ Keeps [674, 679] [] s sf ∧
      sf.regs 674 = before[i] ∧ sf.regs 679 = (before ++ [target])[i + 1]?.getD 0 ∧
      (before ++ [target])[i + 1]?.getD 0 < n := by
  let u := before[i]
  let s₁ := s.setReg 674 u
  have hu : u < n := hvalues _ (List.getElem_mem hi)
  have he₁ : Exec w (.assign 674 (.read 634 (.reg 675))) s s₁ 3 := by
    apply Exec.assign
    have he := GraphMinor.Compute.Crossing.eval_read (a := 634)
      (GraphMinor.Compute.Crossing.eval_reg h675 (hi.trans hlen))
      (by simpa only [h634] using hi) (by simpa only [h634] using hu.trans hn)
    simpa only [h634] using he
  have hiNext : i + 1 < 2 ^ w := by omega
  have hnext : (Expr.op .add (.reg 675) (.const 1)).eval w s₁ = some (i + 1) :=
    GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h675) (hi.trans hlen))
      (GraphMinor.Compute.Crossing.eval_const hw) hiNext
  have hcond := eval_exprLt hw hnext
    (GraphMinor.Compute.Crossing.eval_len (by simpa [s₁] using h634) hlen)
  by_cases hmore : i + 1 < before.length
  · let sf := s₁.setReg 679 before[i + 1]
    have hv : before[i + 1] < n := hvalues _ (List.getElem_mem hmore)
    have he₂ : Exec w (.assign 679 (.read 634 (.op .add (.reg 675) (.const 1)))) s₁ sf 5 := by
      apply Exec.assign
      have he := GraphMinor.Compute.Crossing.eval_read (a := 634) hnext
        (by simpa [s₁, h634] using hmore) (by simpa [s₁, h634] using hv.trans hn)
      simpa [s₁, h634] using he
    have harrival : (before ++ [target])[i + 1]?.getD 0 = before[i + 1] := by
      rw [List.getElem?_append_left hmore, List.getElem?_eq_getElem hmore, Option.getD_some]
    refine ⟨sf, 13, .seq he₁ (.ite_true (by simpa only [hmore, ↓reduceIte] using hcond) (by decide) he₂),
      le_rfl, ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _,
      by simp [sf, s₁, u], by simp [sf, harrival], by rw [harrival]; exact hv⟩
  · have hlast : i + 1 = before.length := by omega
    have harrival : (before ++ [target])[i + 1]?.getD 0 = target := by
      rw [hlast, List.getElem?_append_right (by omega : before.length ≤ before.length), Nat.sub_self]
      rfl
    let sf := s₁.setReg 679 target
    have he₂ : Exec w (.assign 679 (.reg 645)) s₁ sf 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h645) (htarget.trans hn))
    refine ⟨sf, 10, .seq he₁ (.ite_false (by simpa only [hmore, ↓reduceIte] using hcond) he₂),
      by decide, ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _,
      by simp [sf, s₁, u], by simp [sf, harrival], by rw [harrival]; exact htarget⟩

/-- Compute one pair key, find its permanent dart index and emit it. -/
def gm06RecoverDartStep : Cmd :=
  .seq gm06ReadBfsPairProg
    (.seq (.assign 652 (gm06PairKeyExpr (.reg 674) (.reg 679)))
      (.seq (gm06FindLabelProg 616 652 650 651)
        (GraphMinor.Compute.Crossing.emitProg 635 655 (.reg 651))))

/-- Recover the entire directed row into 635 from BFS vertex storage. -/
def gm06RecoverDartsProg : Cmd :=
  .seq (.alloc 635 (.len 634))
    (.seq (.assign 655 (.const 0))
      (.seq (.assign 675 (.const 0)) (forUp 675 (.len 634) gm06RecoverDartStep)))

/-- The RAM computes exactly the pure directed dart row, in polynomial
time even with parallel edge labels. Missing matches yield the same
sentinel as the pure function; candidate-walk correctness excludes them. -/
theorem gm06RecoverDartsProg_exec {w n m : ℕ} (origins active before : List ℕ) (target : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : 1 + n * n < 2 ^ w) (hlen : before.length + 2 < 2 ^ w)
    (horg : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hbefore : ∀ v ∈ before, v < n) (htarget : target < n)
    (h616 : s.arrs 616 = gm06DartPairKeys n origins active) (h634 : s.arrs 634 = before)
    (h620 : s.regs 620 = n) (h645 : s.regs 645 = target) :
    ∃ sf t, Exec w gm06RecoverDartsProg s sf t ∧
      t ≤ 8 + before.length * (70 + 13 * (2 * m)) ∧
      Keeps [650, 651, 652, 655, 674, 675, 679] [635] s sf ∧
      sf.arrs 635 = gm06PathDarts n origins active (before ++ [target]) := by
  have hw1 : 1 < 2 ^ w := by omega
  let keys := gm06DartPairKeys n origins active
  let out := gm06PathDarts n origins active (before ++ [target])
  have hkeysLen : keys.length = 2 * m := (gm06DartPairKeys_length n origins active).trans horg
  have houtlen : out.length = before.length := gm06PathDarts_append_target_length n origins active before target
  have hkeysWords : ∀ key ∈ keys, key < 2 ^ w := fun key hk =>
    (gm06DartPairKeys_bounds origins active horg hvalues key hk).trans hfit
  let s₀ := s.setArr 635 (List.replicate before.length 0)
  let s₁ := s₀.setReg 655 0
  let s₂ := s₁.setReg 675 0
  have he₀ : Exec w (.alloc 635 (.len 634)) s s₀ (1 + before.length) :=
    .alloc (GraphMinor.Compute.Crossing.eval_len h634 (by omega))
  have he₁ : Exec w (.assign 655 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 675 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  let Inv := fun i st => st.regs 675 = i ∧
    Keeps [650, 651, 652, 655, 674, 675, 679] [635] s st ∧
    GraphMinor.Compute.Crossing.IsBuf 635 655 (out.take i) (before.length - i) st
  have hinit : Inv 0 s₂ := ⟨by simp [s₂],
    (((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _).setReg (by simp) _,
    by simp [GraphMinor.Compute.Crossing.IsBuf, s₂, s₁, s₀]⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 675) (hi := .len 634) (body := gm06RecoverDartStep) Inv before.length
    (60 + 13 * (2 * m)) hw1 (by omega)
    (fun _ _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 634 (by decide)).trans h634) (by omega)⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, hb⟩ := h
      obtain ⟨st₁, t₁, he₁, ht₁, hk₁, hu₁, hv₁, hvBound⟩ := gm06ReadBfsPairProg_exec
        before target st hw1 hn (by omega) hi hbefore htarget
        ((hk.2 634 (by decide)).trans h634) ((hk.1 645 (by decide)).trans h645) hidx
      let v := (before ++ [target])[i + 1]?.getD 0
      let key := gm06PairKey n before[i] v
      let st₂ := st₁.setReg 652 key
      have hkey := gm06PairKeyExpr_eval (.reg 674) (.reg 679) st₁ hw1 hfit
        (hbefore _ (List.getElem_mem hi)) hvBound
        (GraphMinor.Compute.Crossing.eval_reg hu₁ ((hbefore _ (List.getElem_mem hi)).trans hn))
        (GraphMinor.Compute.Crossing.eval_reg hv₁ (hvBound.trans hn))
        ((hk₁.1 620 (by decide)).trans ((hk.1 620 (by decide)).trans h620))
      have he₂ : Exec w (.assign 652 (gm06PairKeyExpr (.reg 674) (.reg 679))) st₁ st₂
          ((gm06PairKeyExpr (.reg 674) (.reg 679)).cost + 1) := .assign hkey
      have hk₁₂ : Keeps [652, 674, 679] [] st st₂ :=
        (hk₁.mono (by simp) (fun _ h => h)).setReg (by simp) _
      obtain ⟨st₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06FindLabelProg_exec_exact
        616 652 650 651 (by decide) (by decide) (by decide) keys key st₂ hw1
        (hkeysLen ▸ hm) hkeysWords ((gm06PairKey_lt (hbefore _ (List.getElem_mem hi)) hvBound).trans hfit)
        ((hk₁₂.2 616 (by simp)).trans ((hk.2 616 (by decide)).trans h616)) (by simp [st₂])
      have hk₁₃ : Keeps [650, 651, 652, 674, 679] [] st st₃ :=
        (hk₁₂.mono (by simp) (fun _ h => h)).trans hk₃ (by simp) (fun _ h => h)
      have hbuf₃ : GraphMinor.Compute.Crossing.IsBuf 635 655 (out.take i) (before.length - i) st₃ :=
        ⟨(hk₁₃.2 635 (by simp)).trans hb.1, (hk₁₃.1 655 (by decide)).trans hb.2⟩
      have hdword : gm06LabelIndex keys key < 2 ^ w := by
        rcases gm06LabelIndexPrefix_spec keys key keys.length le_rfl with hz | ⟨q, _, hq, heq, _⟩
        · simpa only [gm06LabelIndex, hz.1] using hkeysLen ▸ hm
        · change gm06LabelIndexPrefix keys key keys.length < 2 ^ w
          rw [heq]
          exact hq.trans (hkeysLen ▸ hm)
      have hcapEq : before.length - i = (before.length - i - 1) + 1 := by omega
      obtain ⟨he₄, hb₄⟩ := GraphMinor.Compute.Crossing.emitProg_exec 635 655 (.reg 651)
        (k := before.length - i - 1) (hcapEq ▸ hbuf₃)
        (GraphMinor.Compute.Crossing.eval_reg hd₃ hdword)
        (by rw [List.length_take, houtlen]; omega)
      let st₄ := (st₃.writeArr 635 (out.take i).length (gm06LabelIndex keys key)).setReg 655 ((out.take i).length + 1)
      have hk₄ : Keeps [655] [635] st₃ st₄ :=
        ((Keeps.refl _ _ st₃).writeArr (by simp) _ _).setReg (by simp) _
      refine ⟨st₄, t₁ + ((gm06PairKeyExpr (.reg 674) (.reg 679)).cost + 1 + (t₃ + 7)),
        .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, ⟨by simp, ?_, ?_⟩, ?_⟩
      · rw [hkeysLen] at ht₃
        have hc : (gm06PairKeyExpr (.reg 674) (.reg 679)).cost = 7 := by decide
        omega
      · exact (((hk.trans hk₁₃ (by simp) (by simp)).trans hk₄ (by simp) (by simp)).setReg (by simp) _)
      · have hout : out[i]'(houtlen ▸ hi) = gm06LabelIndex keys key :=
          gm06PathDarts_append_target_get origins active before target hi
        have htake : out.take (i + 1) = out.take i ++ [gm06LabelIndex keys key] := by
          rw [List.take_succ_eq_append_getElem (houtlen ▸ hi), hout]
        have hcap : before.length - (i + 1) = before.length - i - 1 := by omega
        simpa only [GraphMinor.Compute.Crossing.IsBuf, st₄, State.setReg_arrs,
          State.setReg_regs_ne _ _ (by decide : 655 ≠ 675), htake, hcap] using hb₄
      · exact (hk₄.1 675 (by decide)).trans ((hk₁₃.1 675 (by decide)).trans hidx)) s₂ hinit
  refine ⟨sf, (1 + before.length) + (2 + (2 + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), ?_, hIf.2.1, ?_⟩
  · simp only [Expr.cost] at htf
    nlinarith only [htf]
  · have hbuf := hIf.2.2.1
    simpa only [← houtlen, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil] using hbuf

/-- Build the directed pair keys and recover the stored BFS path. -/
def gm06RecoverPathProg : Cmd := .seq gm06DartPairKeysProg gm06RecoverDartsProg

/-- Full directed-path recovery reads graph origins and activity bits,
not a supplied key or edge row, and returns exactly the pure dart row. -/
theorem gm06RecoverPathProg_exec {w n m : ℕ} (origins active before : List ℕ) (target : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : 1 + n * n < 2 ^ w) (hlen : before.length + 2 < 2 ^ w)
    (horg : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hbefore : ∀ v ∈ before, v < n) (htarget : target < n)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h634 : s.arrs 634 = before) (h620 : s.regs 620 = n) (h645 : s.regs 645 = target) :
    ∃ sf t, Exec w gm06RecoverPathProg s sf t ∧
      t ≤ 14 + 100 * (2 * m) + before.length * (70 + 13 * (2 * m)) ∧
      Keeps [650, 651, 652, 655, 674, 675, 679] [616, 635] s sf ∧
      sf.arrs 635 = gm06PathDarts n origins active (before ++ [target]) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06DartPairKeysProg_exec origins active s
    hw hn hm hfit horg hvalues h626 h627 h620
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06RecoverDartsProg_exec origins active before target s₁
    hw hn hm hfit hlen horg hvalues hbefore htarget hd₁
    ((hk₁.2 634 (by decide)).trans h634) ((hk₁.1 620 (by decide)).trans h620)
    ((hk₁.1 645 (by decide)).trans h645)
  exact ⟨sf, t₁ + tf, .seq he₁ hef, by omega,
    (hk₁.mono (by simp) (by simp)).trans hkf (fun _ h => h) (by simp), hdf⟩

/-- Rebuild the selected contact's retained edges before recovering its
BFS row. The saved successful contact is read from register 678. -/
def gm06Find4RecoverProg : Cmd :=
  .seq (.assign 673 (.reg 678))
    (.seq gm06CandidateVerticesProg (.seq gm06CandidateEdgeBitsProg gm06RecoverPathProg))

/-- Writes of the directed continuation after a successful FIND_4. -/
def gm06Find4RecoverRegs : List ℕ := [673, 650, 610, 611, 612, 651, 652, 655, 674, 675, 679]

/-- Scratch and output arrays of the directed continuation. -/
def gm06Find4RecoverArrs : List ℕ := [611, 615, 623, 619, 627, 616, 635]

/-- The continuation computes its candidate restriction again from the
saved index and input lists, then returns the exact directed path row.
Thus no property of leftover search scratch is a precondition. -/
theorem gm06Find4RecoverProg_exec {w n m j : ℕ} (origins : List ℕ) (ordinary : List Bool)
    (incV incE upper path before : List ℕ) (target : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : 1 + n * n < 2 ^ w) (horg : origins.length = 2 * m)
    (hvalues : ∀ v ∈ origins, v < n) (hordinary : ordinary.length = m)
    (hVlen : incV.length = n) (hElen : incE.length = m)
    (hVwords : ∀ x ∈ incV, x < 2 ^ w) (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (hpathLen : path.length < 2 ^ w) (hupperLen : upper.length < 2 ^ w)
    (hj : j < path.length) (hpath : ∀ x ∈ path, x < n) (hupper : ∀ x ∈ upper, x < n)
    (hbeforeLen : before.length + 2 < 2 ^ w) (hbefore : ∀ v ∈ before, v < n) (htarget : target < n)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE) (h608 : s.arrs 608 = upper)
    (h609 : s.arrs 609 = path) (h624 : s.arrs 624 = ordinary.map Bool.toNat)
    (h626 : s.arrs 626 = origins) (h634 : s.arrs 634 = before) (h620 : s.regs 620 = n)
    (h645 : s.regs 645 = target) (h649 : s.regs 649 = m) (h678 : s.regs 678 = j) :
    ∃ sf t, Exec w gm06Find4RecoverProg s sf t ∧
      t ≤ 126 + 100 * n + 350 * m + 100 * path.length + 100 * upper.length +
        before.length * (70 + 13 * (2 * m)) ∧
      Keeps gm06Find4RecoverRegs gm06Find4RecoverArrs s sf ∧ sf.arrs 635 =
        gm06PathDarts n origins (gm06CandidateDarts m origins ordinary incV incE upper path j)
          (before ++ [target]) := by
  let s₀ := s.setReg 673 j
  have he₀ : Exec w (.assign 673 (.reg 678)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h678 (hj.trans hpathLen))
  have hk₀ : Keeps gm06Find4RecoverRegs gm06Find4RecoverArrs s s₀ :=
    (Keeps.refl _ _ s).setReg (by simp [gm06Find4RecoverRegs]) _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06CandidateVerticesProg_exec incV upper path s₀
    (by omega) hn hpathLen hupperLen hj hVlen hVwords hpath hupper
    h606 h608 h609 h620 (by simp [s₀])
  have hk₀₁ : Keeps gm06Find4RecoverRegs gm06Find4RecoverArrs s s₁ :=
    hk₀.trans hk₁ (by simp [gm06Find4RecoverRegs]) (by simp [gm06Find4RecoverArrs])
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06CandidateEdgeBitsProg_exec origins ordinary
    incV incE upper path s₁ hw hn hm horg hvalues hordinary hElen hEwords
    ((hk₀₁.2 624 (by decide)).trans h624) ((hk₀₁.2 607 (by decide)).trans h607)
    ((hk₀₁.2 626 (by decide)).trans h626) hd₁ ((hk₀₁.1 649 (by decide)).trans h649)
  have hk₀₂ : Keeps gm06Find4RecoverRegs gm06Find4RecoverArrs s s₂ :=
    hk₀₁.trans hk₂ (by simp [gm06Find4RecoverRegs]) (by simp [gm06Find4RecoverArrs])
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06RecoverPathProg_exec origins
    (gm06CandidateDarts m origins ordinary incV incE upper path j) before target s₂
    hw hn hm hfit hbeforeLen horg hvalues hbefore htarget
    ((hk₀₂.2 626 (by decide)).trans h626) hd₂ ((hk₀₂.2 634 (by decide)).trans h634)
    ((hk₀₂.1 620 (by decide)).trans h620) ((hk₀₂.1 645 (by decide)).trans h645)
  exact ⟨sf, 2 + (t₁ + (t₂ + tf)), .seq he₀ (.seq he₁ (.seq he₂ hef)), by omega,
    hk₀₂.trans hkf (by simp [gm06Find4RecoverRegs]) (by simp [gm06Find4RecoverArrs]), hdf⟩

end GraphMinor.Compute
