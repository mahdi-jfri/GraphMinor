module

public import GraphMinor.Compute.CrossingClassScan
public import GraphMinor.Compute.CrossingClassPathMath
public import GraphMinor.Compute.BitSet

/-!
# Preserving the component-search data

The two searches of Section 5.2 of `docs/crossing/crossing_extractor.tex` reuse their queue. This
file saves
the component enumeration before those searches. It copies only the used prefix, so entries
outside that prefix need no word-size bound.
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.Compute.TwoPaths

/-- Saved off-cycle component enumeration, preserved by both path searches. -/
abbrev aBridgeQueue : Arr := 127
/-- Scratch registers for copying a component slice. -/
abbrev rBridgeCopy : Reg := 150

/-- Save only the initialized prefix of the component queue. -/
def saveBridgeQueueProg : Cmd :=
  readSliceProg aQue (.const 0) aBridgeQueue (.reg rTail) rBridgeCopy

/-- Save the component queue in linear time. The hypotheses give its used prefix, its bound,
and the word bounds. -/
theorem saveBridgeQueueProg_exec {w n : ℕ} (items : List ℕ) (s : State)
    (hq : IsQueueHistory aQue rHead rTail n items items.length s)
    (hitems : ∀ v ∈ items, v < n) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ s' t, Exec w saveBridgeQueueProg s s' t ∧ t ≤ 16 * items.length + 9 ∧
      s'.arrs aBridgeQueue = items ∧
      (∀ a ≠ aBridgeQueue, s'.arrs a = s.arrs a) ∧
      (∀ r < 150, s'.regs r = s.regs r) := by
  obtain ⟨hlen, hcap, _, htail, _, hget⟩ := hq
  have htake : (s.arrs aQue).take items.length = items := by
    apply List.ext_getElem
    · simp only [List.length_take, hlen, Nat.min_eq_left hcap]
    · intro i hi hj
      rw [List.getElem_take]
      exact hget i hj
  have hsrc : s.arrs aQue = [] ++ items ++ (s.arrs aQue).drop items.length := by
    simpa only [List.nil_append, htake] using
      (List.take_append_drop items.length (s.arrs aQue)).symm
  obtain ⟨s', t, hex, ht, hout, ha, hr⟩ :=
    readSliceProg_exec (w := w) (n := items.length) (off := 0) (s := s) aQue aBridgeQueue (.const 0) rTail rBridgeCopy
      (by decide) (by decide) [] items ((s.arrs aQue).drop items.length) rfl rfl
      (fun v hv => lt_trans (hitems v hv) hn) hw (by simpa only [Nat.zero_add] using Nat.lt_of_le_of_lt hcap hn)
      (by simp [checkWord]) hsrc htail
  exact ⟨s', t, hex, ht, hout, ha, hr⟩

/-- Selected bridge index and the start and length of its component slice. -/
abbrev rBridgeColor : Reg := 143
abbrev rBridgeOff : Reg := 144
abbrev rBridgeLen : Reg := 145

/-- Copy one component from the saved enumeration to the allowed-vertex array. -/
def readBridgeComponentProg : Cmd :=
  .seq (.assign rBridgeOff (.read aCompSt (.reg rBridgeColor)))
    (.seq (.assign rBridgeLen (.op .sub (.read aCompEn (.reg rBridgeColor)) (.reg rBridgeOff)))
      (readSliceProg aBridgeQueue (.reg rBridgeOff) aBridgeAllowed (.reg rBridgeLen) rBridgeCopy))

/-- Read a component slice, without reading the unused part of any array. -/
theorem readBridgeComponentProg_exec {w n : ℕ} {H : SimpleGraph (Fin n)}
    {T : List (Fin n)} {segs : List (List (Fin n))} {items : List ℕ} (s : State)
    (hcomp : CompSegsOK H T segs items s) (hsaved : s.arrs aBridgeQueue = items)
    (γ : ℕ) (hγ : γ < segs.length) (hrγ : s.regs rBridgeColor = γ)
    (hitems : items.length ≤ n) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ s' t, Exec w readBridgeComponentProg s s' t ∧
      t ≤ 17 + 16 * (segs[γ]'hγ).length ∧
      s'.arrs aBridgeAllowed = (segs[γ]'hγ).map Fin.val ∧
      (∀ a ≠ aBridgeAllowed, s'.arrs a = s.arrs a) ∧
      (∀ r < 144, s'.regs r = s.regs r) := by
  obtain ⟨st, en, hst, hen, henle, hlength, hget⟩ := hcomp.slices γ hγ
  let A := segs[γ]'hγ
  change st + A.length = en at hlength
  have hγw : γ < 2 ^ w := lt_trans (lt_of_lt_of_le hγ hcomp.segs_le_n) hn
  have hstw : st < 2 ^ w := by omega
  have henw : en < 2 ^ w := by omega
  let s₁ := s.setReg rBridgeOff st
  have hex₁ : Exec w (.assign rBridgeOff (.read aCompSt (.reg rBridgeColor))) s s₁ 3 :=
    .assign (read_reg_eval hrγ hγw hst hstw)
  let s₂ := s₁.setReg rBridgeLen A.length
  have hex₂ : Exec w
      (.assign rBridgeLen (.op .sub (.read aCompEn (.reg rBridgeColor)) (.reg rBridgeOff)))
      s₁ s₂ 5 := by
    apply Exec.assign
    have hend : (Expr.read aCompEn (.reg rBridgeColor)).eval w s₁ = some en :=
      read_reg_eval (by simp [s₁, hrγ]) hγw hen henw
    have hoff : (Expr.reg rBridgeOff).eval w s₁ = some st :=
      reg_eval (by simp [s₁]) hstw
    have hd : en - st = A.length := by omega
    have hAw : A.length < 2 ^ w := by omega
    change (match (Expr.read aCompEn (.reg rBridgeColor)).eval w s₁,
        (Expr.reg rBridgeOff).eval w s₁ with
      | some a, some b => BinOp.sub.eval w a b
      | _, _ => none) = some A.length
    rw [hend, hoff]
    simp [BinOp.eval, BinOp.raw, checkWord, hd, hAw]
  have hslice : (items.drop st).take A.length = A.map Fin.val := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_map]
      omega
    · intro i hi hj
      have hiA : i < A.length := by simpa using hj
      have hg := hget i hiA
      rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hg
      simpa only [List.getElem_take, List.getElem_drop, List.getElem_map] using hg
  have hsplit : items = items.take st ++ A.map Fin.val ++ items.drop en := by
    calc
      items = items.take st ++ items.drop st := (List.take_append_drop st items).symm
      _ = items.take st ++ ((items.drop st).take A.length ++
          (items.drop st).drop A.length) := by
        exact congrArg (fun xs => items.take st ++ xs)
          (List.take_append_drop A.length (items.drop st)).symm
      _ = items.take st ++ A.map Fin.val ++ items.drop en := by
        rw [hslice, List.drop_drop, hlength, List.append_assoc]
  have hpre : (items.take st).length = st := by simp; omega
  obtain ⟨s₃, t₃, hex₃, ht₃, hout, ha₃, hr₃⟩ :=
    readSliceProg_exec (w := w) (n := A.length) (off := st) (s := s₂) aBridgeQueue aBridgeAllowed (.reg rBridgeOff)
      rBridgeLen rBridgeCopy (by decide) (by decide) (items.take st) (A.map Fin.val)
      (items.drop en) hpre (by simp) (by intro v hv; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv; exact lt_trans u.2 hn)
      hw (by omega) (reg_eval (by simp [s₂, s₁]) hstw)
      (by change s.arrs aBridgeQueue = _; exact hsaved.trans hsplit) (by simp [s₂])
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), by
      change 3 + (5 + t₃) ≤ 17 + 16 * A.length
      dsimp [Expr.cost] at ht₃
      omega,
    hout, ?_, ?_⟩
  · intro a ha
    exact ha₃ a ha
  · intro r hr
    dsimp only [Reg] at hr
    rw [hr₃ r (Nat.lt_trans hr (by decide))]
    have h1 : r ≠ rBridgeOff := by dsimp only [rBridgeOff, Reg]; omega
    have h2 : r ≠ rBridgeLen := by dsimp only [rBridgeLen, Reg]; omega
    simp [s₂, s₁, h1, h2]

/-- Use the selected component's vertices, or no inner vertices for a chord index. -/
def selectBridgeInnerProg : Cmd :=
  .ite (.op .lt (.reg rBridgeColor) (.reg rNumComp)) readBridgeComponentProg
    (.alloc aBridgeAllowed (.const 0))

/-- Select the allowed inner vertices of a component or chord bridge in linear time. -/
theorem selectBridgeInnerProg_exec {w n : ℕ} {H : SimpleGraph (Fin n)}
    {T : List (Fin n)} {segs : List (List (Fin n))} {items : List ℕ} (s : State)
    (hcomp : CompSegsOK H T segs items s) (hsaved : s.arrs aBridgeQueue = items)
    (γ : ℕ) (hrγ : s.regs rBridgeColor = γ) (hγw : γ < 2 ^ w)
    (hitems : items.length ≤ n) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ s' t, Exec w selectBridgeInnerProg s s' t ∧ t ≤ 21 + 16 * n ∧
      s'.arrs aBridgeAllowed =
        (if h : γ < segs.length then segs[γ]'h else []).map Fin.val ∧
      (∀ a ≠ aBridgeAllowed, s'.arrs a = s.arrs a) ∧
      (∀ r < 144, s'.regs r = s.regs r) := by
  have hKw : segs.length < 2 ^ w := lt_of_le_of_lt hcomp.segs_le_n hn
  by_cases hγ : γ < segs.length
  · have hc : (Expr.op .lt (.reg rBridgeColor) (.reg rNumComp)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrγ, hcomp.numComp, hγw, hKw, hγ, hw]
    obtain ⟨s', t, hex, ht, hout, ha, hr⟩ :=
      readBridgeComponentProg_exec s hcomp hsaved γ hγ hrγ hitems hw hn
    have hAn : (segs[γ]'hγ).length ≤ n := by
      simpa using (hcomp.nodup_seg _ (List.getElem_mem hγ)).length_le_card
    refine ⟨s', _, .ite_true hc (by decide) hex, by dsimp [Expr.cost]; omega, ?_, ha, hr⟩
    simpa only [hγ, ↓reduceDIte] using hout
  · have hc : (Expr.op .lt (.reg rBridgeColor) (.reg rNumComp)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrγ, hcomp.numComp, hγw, hKw, hγ]
    have he : (Expr.const 0).eval w s = some 0 := by simp [checkWord]
    refine ⟨s.setArr aBridgeAllowed [], _, .ite_false hc (.alloc (m := 0) he), ?_, ?_, ?_, ?_⟩
    · dsimp [Expr.cost]; omega
    · simp [hγ]
    · intro a ha; simp [ha]
    · intro r _; rfl

/-- The component part of an enumerated bridge has the stored slice, and the chord part has
no allowed inner vertices. -/
theorem bridgeInnerVertices_bridgesOfSegsAndChords {n : ℕ} (T : List (Fin n))
    (segs : List (List (Fin n))) (pairs : List (ℕ × ℕ)) {γ : ℕ}
    (hγ : γ < (bridgesOfSegsAndChords T segs pairs).length) :
    bridgeInnerVertices ((bridgesOfSegsAndChords T segs pairs)[γ]'hγ) =
      if h : γ < segs.length then segs[γ]'h else [] := by
  dsimp only [bridgesOfSegsAndChords] at hγ ⊢
  by_cases h : γ < segs.length
  · rw [List.getElem_append_left (show γ < (segs.map GraphMinor.Crossing.BridgeData.comp).length by simpa using h)]
    simp only [List.getElem_map, bridgeInnerVertices, h, ↓reduceDIte]
  · have hright : (segs.map GraphMinor.Crossing.BridgeData.comp).length ≤ γ := by simpa using Nat.le_of_not_gt h
    simp only [List.getElem_append_right hright,
      chordBridgesOfPairs, List.getElem_map, h, ↓reduceDIte]
    split_ifs <;> rfl

end GraphMinor.Compute
