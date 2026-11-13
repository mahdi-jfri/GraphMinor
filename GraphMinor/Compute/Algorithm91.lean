module

public import GraphMinor.Compute.Algorithm91Parse

/-!
# Graph Minors XIII, (9.1): Word RAM Algorithm (`Algorithm91.lean`)

This file completes the Word RAM algorithm of **Graph Minors XIII, (9.1)** (Section 9, page 98):
> "Moreover, a model of $K_p$ in $G$ can be found in time $\le C\varepsilon(G)$, where $C$ depends
> only on $p$ and the height of $H$."

Building on the parsing and slice-marking primitives in `Algorithm91Parse.lean` and the pure math
bridge `recOfCfg` in `Algorithm91Eye.lean`, this file defines `alg91Prog p h` and proves
`algorithm_9_1 : Algorithm91Statement`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators

namespace Alg91

/-! ### Section 1: Parsed Input State Invariant and Full Input Parser -/

/-- State invariant after parsing `encAlg91In x`:
- `inArr` holds `encAlg91In x`,
- `reg 1 = x.n`,
- `reg 3 = x.G.enc.length` (the start offset of `x.W.encList`),
- for each `e : Fin (elemWallEdges h).length`, `(rWStart e, rWLen e)` record the slice of
  `(x.W.internalVerts e).map Fin.val` in `encAlg91In x`,
- for each `a : Fin k`, `rHSub h a = x.h_sub a` and `(rPStart h a, rPLen h a)`,
  `(rQStart h a, rQLen h a)` record the slices of `(x.P a).map Fin.val` and `(x.Q a).map Fin.val`
  in `encAlg91In x`. -/
def ParsedAlg91State {p h k r : ℕ} (x : Alg91Input p h k r) (s : State) : Prop :=
  s.arrs inArr = encAlg91In x ∧
  s.regs 1 = x.n ∧
  s.regs 3 = x.G.enc.length ∧
  (∀ e : Fin (elemWallEdges h).length,
    ∃ pre suf : List ℕ,
      encAlg91In x = pre ++ (x.W.internalVerts e).map Fin.val ++ suf ∧
      s.regs (rWStart e) = pre.length ∧
      s.regs (rWLen e) = (x.W.internalVerts e).length) ∧
  (∀ a : Fin k,
    s.regs (rHSub h a) = x.h_sub a ∧
    (∃ pre suf : List ℕ,
      encAlg91In x = pre ++ (x.P a).map Fin.val ++ suf ∧
      s.regs (rPStart h a) = pre.length ∧
      s.regs (rPLen h a) = (x.P a).length) ∧
    (∃ pre suf : List ℕ,
      encAlg91In x = pre ++ (x.Q a).map Fin.val ++ suf ∧
      s.regs (rQStart h a) = pre.length ∧
      s.regs (rQLen h a) = (x.Q a).length))

theorem ParsedAlg91State.of_eq {p h k r : ℕ} {x : Alg91Input p h k r} {s s' : State}
    (hp : ParsedAlg91State x s)
    (hin : s'.arrs inArr = s.arrs inArr)
    (hreg : ∀ reg : ℕ, reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → s'.regs reg = s.regs reg) :
    ParsedAlg91State x s' := by
  rcases hp with ⟨hin₀, hr1, hr3, hW, hsub⟩
  refine ⟨hin.trans hin₀,
    (hreg 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr1,
    (hreg 3 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr3,
    fun e => ?_, fun a => ?_⟩
  · rcases hW e with ⟨pre, suf, hsplit, hstart, hlen⟩
    refine ⟨pre, suf, hsplit, ?_, ?_⟩
    · rw [hreg (rWStart e) (by unfold rWStart; omega) (by unfold rWStart; omega)
        (by unfold rWStart; omega) (by unfold rWStart; omega) (by unfold rWStart; omega)]
      exact hstart
    · rw [hreg (rWLen e) (by unfold rWLen; omega) (by unfold rWLen; omega)
        (by unfold rWLen; omega) (by unfold rWLen; omega) (by unfold rWLen; omega)]
      exact hlen
  · rcases hsub a with ⟨hhsub, ⟨preP, sufP, hsplitP, hstartP, hlenP⟩,
      ⟨preQ, sufQ, hsplitQ, hstartQ, hlenQ⟩⟩
    refine ⟨?_, ⟨preP, sufP, hsplitP, ?_, ?_⟩, ⟨preQ, sufQ, hsplitQ, ?_, ?_⟩⟩
    · rw [hreg (rHSub h a) (by unfold rHSub baseSubReg; omega)
        (by unfold rHSub baseSubReg; omega) (by unfold rHSub baseSubReg; omega)
        (by unfold rHSub baseSubReg; omega) (by unfold rHSub baseSubReg; omega)]
      exact hhsub
    · rw [hreg (rPStart h a) (by unfold rPStart baseSubReg; omega)
        (by unfold rPStart baseSubReg; omega) (by unfold rPStart baseSubReg; omega)
        (by unfold rPStart baseSubReg; omega) (by unfold rPStart baseSubReg; omega)]
      exact hstartP
    · rw [hreg (rPLen h a) (by unfold rPLen baseSubReg; omega)
        (by unfold rPLen baseSubReg; omega) (by unfold rPLen baseSubReg; omega)
        (by unfold rPLen baseSubReg; omega) (by unfold rPLen baseSubReg; omega)]
      exact hlenP
    · rw [hreg (rQStart h a) (by unfold rQStart baseSubReg; omega)
        (by unfold rQStart baseSubReg; omega) (by unfold rQStart baseSubReg; omega)
        (by unfold rQStart baseSubReg; omega) (by unfold rQStart baseSubReg; omega)]
      exact hstartQ
    · rw [hreg (rQLen h a) (by unfold rQLen baseSubReg; omega)
        (by unfold rQLen baseSubReg; omega) (by unfold rQLen baseSubReg; omega)
        (by unfold rQLen baseSubReg; omega) (by unfold rQLen baseSubReg; omega)]
      exact hlenQ

/-- Full linear-time parser for `encAlg91In x`. -/
def parseAlg91Prog (h k : ℕ) : Cmd :=
  .seq (.assign 1 (.read inArr (.const 0)))
    (.seq (.assign 2 (.read inArr (.const 1)))
      (.seq (.assign 3 (.op .add (.const 2) (.op .mul (.const 3) (.reg 2))))
        (.seq (.assign 4 (.op .add (.reg 3) (.const (3 + elemWallNumVerts h))))
          (.seq (parseWEdgesUpTo h (elemWallEdges h).length)
            (parseSubwallsUpTo h k k)))))

theorem parseAlg91Prog_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (hw2 : 3 < 2 ^ w)
    (hh_w : h < 2 ^ w)
    (hn_w : x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (hE_w : 2 * elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hin : s.arrs inArr = encAlg91In x) :
    ∃ s' t,
      Exec w (parseAlg91Prog h k) s s' t ∧
      t ≤ 18 + 22 * elemWallNumVerts h + k * (46 + 28 * elemWallNumVerts h) ∧
      ParsedAlg91State x s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hV_w : elemWallNumVerts h < 2 ^ w := by omega
  have hG_len_eq : x.G.enc.length = 2 + 3 * x.G.numActivePairs :=
    MultiDigraph.length_enc x.G
  have hG_le_tot : x.G.enc.length ≤ (encAlg91In x).length := by
    unfold encAlg91In
    simp [List.length_append]
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have h3m_w : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hG_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  let rest_G :=
    x.G.flatTriples x.G.activePairsList ++
      x.W.encList ++
      (List.finRange k).flatMap (fun a =>
        (x.W_sub a).encList ++
        ((x.P a).length :: (x.P a).map Fin.val) ++
        ((x.Q a).length :: (x.Q a).map Fin.val))
  have hin_split : s.arrs inArr = x.n :: x.G.numActivePairs :: rest_G := by
    rw [hin]
    unfold encAlg91In MultiDigraph.enc
    simp [rest_G, List.append_assoc]
  have hin_len0 : 0 < (s.arrs inArr).length := by
    rw [hin_split]; simp
  have hin_len1 : 1 < (s.arrs inArr).length := by
    rw [hin_split]; simp
  have hread0 : (s.arrs inArr)[0]'hin_len0 = x.n := by
    apply getElem_of_eq hin_split rfl (h₂ := by simp)
    rfl
  have hread1 : (s.arrs inArr)[1]'hin_len1 = x.G.numActivePairs := by
    apply getElem_of_eq hin_split rfl (h₂ := by simp)
    rfl
  let s₁ := s.setReg 1 x.n
  have hex₁ : Exec w (.assign 1 (.read inArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, hin_len0, hread0, hn_w])
  let s₂ := s₁.setReg 2 x.G.numActivePairs
  have hex₂ : Exec w (.assign 2 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw1, hin_len1, hread1, hm_w])
  let s₃ := s₂.setReg 3 x.G.enc.length
  have hex₃ : Exec w (.assign 3 (.op .add (.const 2) (.op .mul (.const 3) (.reg 2)))) s₂ s₃ 6 :=
    .assign (by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        h2_w, hw2, hm_w, h3m_w, hG_w, hG_len_eq])
  let pre_W := x.G.enc ++ [h, elemWallNumVerts h, (elemWallEdges h).length] ++
    (List.finRange (elemWallNumVerts h)).map (fun u => (x.W.branchVert u).1)
  have hpre_W_len : pre_W.length = x.G.enc.length + (3 + elemWallNumVerts h) := by
    simp [pre_W]
    omega
  let fW : Fin (elemWallEdges h).length → List ℕ :=
    fun e => (x.W.internalVerts e).length :: (x.W.internalVerts e).map Fin.val
  let blk : Fin k → List ℕ := fun a =>
    (x.W_sub a).encList ++
    ((x.P a).length :: (x.P a).map Fin.val) ++
    ((x.Q a).length :: (x.Q a).map Fin.val)
  have hW_eq : x.G.enc ++ x.W.encList = pre_W ++ (List.finRange (elemWallEdges h).length).flatMap fW := by
    unfold WallOfHeight.encList
    simp [pre_W, fW, List.append_assoc]
  have hGW_le_tot : (x.G.enc ++ x.W.encList).length ≤ (encAlg91In x).length := by
    unfold encAlg91In
    simp [List.length_append]
  have hGW_w : (pre_W ++ (List.finRange (elemWallEdges h).length).flatMap fW).length < 2 ^ w := by
    rw [← hW_eq]
    exact Nat.lt_of_le_of_lt hGW_le_tot htot_w
  have hpre_W_w : 2 + 3 * x.G.numActivePairs + (3 + elemWallNumVerts h) < 2 ^ w := by
    have : x.G.enc.length + (3 + elemWallNumVerts h) < 2 ^ w := by
      rw [← hpre_W_len]
      simp [List.length_append] at hGW_w
      omega
    omega
  let s₄ := s₃.setReg 4 pre_W.length
  have hex₄ : Exec w (.assign 4 (.op .add (.reg 3) (.const (3 + elemWallNumVerts h)))) s₃ s₄ 4 :=
    .assign (by
      simp [s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hG_w, hc_w, hpre_W_w, hpre_W_len])
  have hin₄ :
      s₄.arrs inArr =
        pre_W ++ (List.finRange (elemWallEdges h).length).flatMap fW ++
          (List.finRange k).flatMap blk := by
    change s.arrs inArr = _
    rw [hin]
    unfold encAlg91In
    rw [hW_eq]
  rcases parseWEdgesUpTo_exec x.W pre_W ((List.finRange k).flatMap blk)
      hw1 hGW_w (elemWallEdges h).length le_rfl hin₄ (by simp [s₄]) with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, hpos₅, hW₅, harr₅, hreg₅⟩
  have htake_W :
      (List.finRange (elemWallEdges h).length).take (elemWallEdges h).length =
        List.finRange (elemWallEdges h).length :=
    List.take_of_length_le (by simp)
  have hpos₅' : s₅.regs 4 = (x.G.enc ++ x.W.encList).length := by
    rw [hpos₅, htake_W, ← hW_eq]
  have hin₅' : s₅.arrs inArr = encAlg91In x := by
    rw [harr₅ inArr]
    exact hin
  rcases parseSubwallsUpTo_exec x hw2 hh_w hV_w hE_w htot_w k le_rfl hin₅' hpos₅' with
    ⟨s₆, t₆, hex₆, ht₆, hin₆, _, hsub₆, harr₆, hreg₆⟩
  have ht₅_le : t₅ ≤ 1 + 22 * elemWallNumVerts h := by
    have := length_elemWallEdges_le h
    omega
  refine ⟨s₆, 3 + (3 + (6 + (4 + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hin₆.trans hin₅', ?_, ?_, fun e => ?_, fun a => ?_⟩
  · rw [hreg₆ 1 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by unfold baseSubReg; omega)),
      hreg₅ 1 (by decide) (Or.inl (by decide))]
    simp [s₄, s₃, s₂, s₁]
  · rw [hreg₆ 3 (by decide) (by decide) (by decide) (by decide)
      (Or.inl (by unfold baseSubReg; omega)),
      hreg₅ 3 (by decide) (Or.inl (by decide))]
    simp [s₄, s₃]
  · obtain ⟨hstart_e, hlen_e⟩ := hW₅ e e.2
    let pre_e :=
      pre_W ++ ((List.finRange (elemWallEdges h).length).take e.1).flatMap fW ++
        [(x.W.internalVerts e).length]
    let suf_e :=
      ((List.finRange (elemWallEdges h).length).drop (e.1 + 1)).flatMap fW ++
        (List.finRange k).flatMap blk
    refine ⟨pre_e, suf_e, ?_, ?_, ?_⟩
    · unfold encAlg91In
      rw [hW_eq, flatMap_finRange_eq_take_append_drop fW e.1,
        flatMap_drop_eq_cons fW e.2]
      simp [pre_e, suf_e, fW, blk, List.append_assoc]
    · rw [hreg₆ (rWStart e) (by unfold rWStart; omega) (by unfold rWStart; omega)
        (by unfold rWStart; omega) (by unfold rWStart; omega)
        (Or.inl (by unfold rWStart baseSubReg; have := e.2; omega))]
      rw [hstart_e]
      simp [pre_e, fW]
      omega
    · rw [hreg₆ (rWLen e) (by unfold rWLen; omega) (by unfold rWLen; omega)
        (by unfold rWLen; omega) (by unfold rWLen; omega)
        (Or.inl (by unfold rWLen baseSubReg; have := e.2; omega))]
      exact hlen_e
  · obtain ⟨hhsub_a, hPstart_a, hPlen_a, hQstart_a, hQlen_a⟩ := hsub₆ a a.2
    let pre_a :=
      (x.G.enc ++ x.W.encList) ++ ((List.finRange k).take a.1).flatMap blk
    let suf_a := ((List.finRange k).drop (a.1 + 1)).flatMap blk
    have hsplit_a : encAlg91In x = pre_a ++ blk a ++ suf_a := by
      unfold encAlg91In
      rw [flatMap_finRange_eq_take_append_drop blk a.1, flatMap_drop_eq_cons blk a.2]
      simp [pre_a, suf_a, List.append_assoc]
    refine ⟨hhsub_a, ?_, ?_⟩
    · refine ⟨pre_a ++ (x.W_sub a).encList ++ [(x.P a).length],
        ((x.Q a).length :: (x.Q a).map Fin.val) ++ suf_a,
        by rw [hsplit_a]; simp [blk, List.append_assoc],
        by rw [hPstart_a]; simp [pre_a, blk]; omega,
        hPlen_a⟩
    · refine ⟨pre_a ++ (x.W_sub a).encList ++ ((x.P a).length :: (x.P a).map Fin.val) ++ [(x.Q a).length],
        suf_a,
        by rw [hsplit_a]; simp [blk, List.append_assoc],
        by rw [hQstart_a]; simp [pre_a, blk]; omega,
        hQlen_a⟩

/-! ### Section 2: Execution of Wall-Edge and Cross-Path Slice Marking -/

theorem markWallEdgeProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (e : Fin (elemWallEdges h).length) (S : Finset (Fin x.n))
    (hw1 : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w) (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s)
    (harr2 : s.arrs 2 = bitSetList S) :
    ∃ s' t,
      Exec w (markWallEdgeProg e) s s' t ∧
      t ≤ 9 + 14 * x.n ∧
      ParsedAlg91State x s' ∧
      s'.arrs 2 = bitSetList (S ∪ (x.W.internalVerts e).toFinset) ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s'.regs reg = s.regs reg) := by
  obtain ⟨pre, suf, hsplit, hstart, hlen⟩ := hp.2.2.2.1 e
  have hpre_L_le : (pre ++ (x.W.internalVerts e).map Fin.val).length ≤ (encAlg91In x).length := by
    rw [hsplit]
    simp [List.length_append]
  have hpre_L_w : (pre ++ (x.W.internalVerts e).map Fin.val).length < 2 ^ w :=
    Nat.lt_of_le_of_lt hpre_L_le htot_w
  have hpre_w : pre.length < 2 ^ w := by
    simp [List.length_append] at hpre_L_w; omega
  have hlen_w : (x.W.internalVerts e).length < 2 ^ w := by
    simp [List.length_append] at hpre_L_w; omega
  let s₁ := s.setReg 6 pre.length
  have hex₁ : Exec w (.assign 6 (.reg (rWStart e))) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hstart, hpre_w])
  let s₂ := s₁.setReg 7 (x.W.internalVerts e).length
  have hex₂ : Exec w (.assign 7 (.reg (rWLen e))) s₁ s₂ 2 :=
    .assign (by
      have hr : s₁.regs (rWLen e) = (x.W.internalVerts e).length := by
        rw [State.setReg_regs_ne _ _ (show (rWLen e : ℕ) ≠ 6 by unfold rWLen; omega), hlen]
      simp [s₁, Expr.eval, checkWord, hr, hlen_w])
  have hin₂ : s₂.arrs inArr = pre ++ (x.W.internalVerts e).map Fin.val ++ suf := by
    change s.arrs inArr = _
    rw [hp.1, hsplit]
  rcases markSliceProg_exec pre (x.W.internalVerts e) suf S hw1 hn_w hpre_L_w
      hin₂ (by simp [s₂, s₁]) (by simp [s₂]) harr2 with
    ⟨s₃, t₃, hex₃, ht₃, harr2_3, harrs₃, hregs₃⟩
  have hlen_le_n : (x.W.internalVerts e).length ≤ x.n :=
    length_internalVerts_le_of_isValid x.hW_valid.2.2 e
  have hreg_final : ∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s₃.regs reg = s.regs reg := by
    intro reg hr5 hr6 hr7
    rw [hregs₃ reg hr5]
    simp [s₂, s₁, State.setReg_regs_ne _ _ hr6, State.setReg_regs_ne _ _ hr7]
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hp.of_eq (harrs₃ inArr (by decide)) (fun reg _ hr5 hr6 hr7 _ => hreg_final reg hr5 hr6 hr7),
    harr2_3, harrs₃, hreg_final⟩

theorem markWallEdgeListProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (hw1 : 1 < 2 ^ w) (hn_w : x.n < 2 ^ w) (htot_w : (encAlg91In x).length < 2 ^ w) :
    ∀ (es : List (Fin (elemWallEdges h).length)) (S : Finset (Fin x.n)) {s : State}
      (_hp : ParsedAlg91State x s)
      (_harr2 : s.arrs 2 = bitSetList S),
      ∃ s' t,
        Exec w (markWallEdgeListProg es) s s' t ∧
        t ≤ 1 + es.length * (9 + 14 * x.n) ∧
        ParsedAlg91State x s' ∧
        s'.arrs 2 = bitSetList (S ∪ es.toFinset.biUnion (fun e => (x.W.internalVerts e).toFinset)) ∧
        (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
        (∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s'.regs reg = s.regs reg)
  | [], S, s, hp, harr2 => by
    exact ⟨s, 1, .skip s, by omega, hp, by simpa using harr2, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | e :: es, S, s, hp, harr2 => by
    rcases markWallEdgeProg_exec x e S hw1 hn_w htot_w hp harr2 with
      ⟨s₁, t₁, hex₁, ht₁, hp₁, harr2_1, harrs₁, hregs₁⟩
    rcases markWallEdgeListProg_exec x hw1 hn_w htot_w es
        (S ∪ (x.W.internalVerts e).toFinset) hp₁ harr2_1 with
      ⟨s₂, t₂, hex₂, ht₂, hp₂, harr2_2, harrs₂, hregs₂⟩
    have hset_eq :
        (S ∪ (x.W.internalVerts e).toFinset) ∪
            es.toFinset.biUnion (fun d => (x.W.internalVerts d).toFinset) =
          S ∪ (e :: es).toFinset.biUnion (fun d => (x.W.internalVerts d).toFinset) := by
      ext v
      simp [Finset.mem_biUnion]
    rw [hset_eq] at harr2_2
    have ht_tot : t₁ + t₂ ≤ 1 + (e :: es).length * (9 + 14 * x.n) := by
      simp only [List.length_cons]
      calc t₁ + t₂ ≤ (9 + 14 * x.n) + (1 + es.length * (9 + 14 * x.n)) := Nat.add_le_add ht₁ ht₂
        _ = 1 + (es.length + 1) * (9 + 14 * x.n) := by ring
    exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ht_tot, hp₂, harr2_2,
      fun a ha => (harrs₂ a ha).trans (harrs₁ a ha),
      fun reg hr5 hr6 hr7 => (hregs₂ reg hr5 hr6 hr7).trans (hregs₁ reg hr5 hr6 hr7)⟩

theorem markCrossPathProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    {r_start r_len : ℕ} (_hr_start : 10 ≤ r_start) (hr_len : 10 ≤ r_len)
    (L : List (Fin x.n))
    (hne : L ≠ []) (hdiff : L.head hne ≠ L.getLast hne) (hnd : L.Nodup)
    (pre suf : List ℕ) (S : Finset (Fin x.n))
    (hw1 : 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s)
    (hsplit : encAlg91In x = pre ++ L.map Fin.val ++ suf)
    (hstart : s.regs r_start = pre.length)
    (hlen : s.regs r_len = L.length)
    (harr2 : s.arrs 2 = bitSetList S) :
    ∃ s' t,
      Exec w (markCrossPathProg r_start r_len) s s' t ∧
      t ≤ 13 + 14 * x.n ∧
      ParsedAlg91State x s' ∧
      s'.arrs 2 = bitSetList (S ∪ ((L.drop 1).dropLast).toFinset) ∧
      (∀ a : ℕ, a ≠ 2 → s'.arrs a = s.arrs a) ∧
      (∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s'.regs reg = s.regs reg) := by
  let L_int := (L.drop 1).dropLast
  have hL_eq : L = L.head hne :: (L_int ++ [L.getLast hne]) :=
    list_eq_head_cons_drop_one_dropLast_append_getLast hne hdiff
  have hL_len : L.length = L_int.length + 2 := by
    conv_lhs => rw [hL_eq]
    simp
  have hL_le_n : L.length ≤ x.n := by
    have hcard := Finset.card_le_univ L.toFinset
    rw [List.toFinset_card_of_nodup hnd, Fintype.card_fin] at hcard
    exact hcard
  have hint_le_n : L_int.length ≤ x.n := by omega
  let pre' := pre ++ [(L.head hne).1]
  let suf' := [(L.getLast hne).1] ++ suf
  have hsplit' : encAlg91In x = pre' ++ L_int.map Fin.val ++ suf' := by
    rw [hsplit]
    conv_lhs => rw [hL_eq]
    simp [pre', suf', List.append_assoc]
  have hpre'_len : pre'.length = pre.length + 1 := by simp [pre']
  have hpre'_L_le : (pre' ++ L_int.map Fin.val).length ≤ (encAlg91In x).length := by
    rw [hsplit']
    simp [List.length_append]
  have hpre'_L_w : (pre' ++ L_int.map Fin.val).length < 2 ^ w :=
    Nat.lt_of_le_of_lt hpre'_L_le htot_w
  have hpre_w : pre.length < 2 ^ w := by
    simp [pre', List.length_append] at hpre'_L_w; omega
  have hpre'_w : pre.length + 1 < 2 ^ w := by
    simp [pre', List.length_append] at hpre'_L_w; omega
  have hL_len_w : L.length < 2 ^ w := by omega
  have hint_len_w : L_int.length < 2 ^ w := by omega
  let s₁ := s.setReg 6 (pre.length + 1)
  have hex₁ : Exec w (.assign 6 (.op .add (.reg r_start) (.const 1))) s s₁ 4 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hstart, hpre_w, hw1, hpre'_w])
  let s₂ := s₁.setReg 7 L_int.length
  have hex₂ : Exec w (.assign 7 (.op .sub (.reg r_len) (.const 2))) s₁ s₂ 4 :=
    .assign (by
      have hr : s₁.regs r_len = L.length := by
        rw [State.setReg_regs_ne _ _ (show r_len ≠ 6 by omega), hlen]
      have hsub_eq : L.length - 2 = L_int.length := by omega
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hL_len_w, hw2,
        hint_len_w, hsub_eq])
  have hin₂ : s₂.arrs inArr = pre' ++ L_int.map Fin.val ++ suf' := by
    change s.arrs inArr = _
    rw [hp.1, hsplit']
  rcases markSliceProg_exec pre' L_int suf' S hw1 hn_w hpre'_L_w
      hin₂ (by simp [s₂, s₁, hpre'_len]) (by simp [s₂]) harr2 with
    ⟨s₃, t₃, hex₃, ht₃, harr2_3, harrs₃, hregs₃⟩
  have hreg_final : ∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s₃.regs reg = s.regs reg := by
    intro reg hr5 hr6 hr7
    rw [hregs₃ reg hr5]
    simp [s₂, s₁, State.setReg_regs_ne _ _ hr6, State.setReg_regs_ne _ _ hr7]
  refine ⟨s₃, 4 + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hp.of_eq (harrs₃ inArr (by decide)) (fun reg _ hr5 hr6 hr7 _ => hreg_final reg hr5 hr6 hr7),
    harr2_3, harrs₃, hreg_final⟩

theorem Alg91Input.P_head_ne_getLast {p h k r : ℕ} (x : Alg91Input p h k r) (a : Fin k) :
    (x.P a).head (x.hcross a).ne_nil₁ ≠ (x.P a).getLast (x.hcross a).ne_nil₁ := by
  obtain ⟨sa, hsa⟩ := SubwallParam.exists_matchesSubwall_of_isSubwallOf (x.hsub a)
  have hhead : (x.P a).head (x.hcross a).ne_nil₁ = x.W.branchVert (sa.cornerIdx 0) := by
    rw [(x.hcross a).head₁, hsa.cornerVert_eq (x.hsub a).1 0]
  have hlast : (x.P a).getLast (x.hcross a).ne_nil₁ = x.W.branchVert (sa.cornerIdx 2) := by
    rw [(x.hcross a).getLast₁, hsa.cornerVert_eq (x.hsub a).1 2]
  rw [hhead, hlast]
  exact fun heq => absurd (sa.cornerIdx_injective (x.hW_valid.2.2.1 heq)) (by decide)

theorem Alg91Input.Q_head_ne_getLast {p h k r : ℕ} (x : Alg91Input p h k r) (a : Fin k) :
    (x.Q a).head (x.hcross a).ne_nil₂ ≠ (x.Q a).getLast (x.hcross a).ne_nil₂ := by
  obtain ⟨sa, hsa⟩ := SubwallParam.exists_matchesSubwall_of_isSubwallOf (x.hsub a)
  have hhead : (x.Q a).head (x.hcross a).ne_nil₂ = x.W.branchVert (sa.cornerIdx 1) := by
    rw [(x.hcross a).head₂, hsa.cornerVert_eq (x.hsub a).1 1]
  have hlast : (x.Q a).getLast (x.hcross a).ne_nil₂ = x.W.branchVert (sa.cornerIdx 3) := by
    rw [(x.hcross a).getLast₂, hsa.cornerVert_eq (x.hsub a).1 3]
  rw [hhead, hlast]
  exact fun heq => absurd (sa.cornerIdx_injective (x.hW_valid.2.2.1 heq)) (by decide)

theorem markCrossPListProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (hw1 : 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w) :
    ∀ (as : List (Fin k)) (S : Finset (Fin x.n)) {s : State}
      (_hp : ParsedAlg91State x s)
      (_harr2 : s.arrs 2 = bitSetList S),
      ∃ s' t,
        Exec w (markCrossPListProg h as) s s' t ∧
        t ≤ 1 + as.length * (13 + 14 * x.n) ∧
        ParsedAlg91State x s' ∧
        s'.arrs 2 = bitSetList (S ∪ as.toFinset.biUnion (fun a => (((x.P a).drop 1).dropLast).toFinset)) ∧
        (∀ arr : ℕ, arr ≠ 2 → s'.arrs arr = s.arrs arr) ∧
        (∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s'.regs reg = s.regs reg)
  | [], S, s, hp, harr2 => by
    exact ⟨s, 1, .skip s, by omega, hp, by simpa using harr2, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | a :: as, S, s, hp, harr2 => by
    obtain ⟨_, ⟨pre, suf, hsplit, hstart, hlen⟩, _⟩ := hp.2.2.2.2 a
    rcases markCrossPathProg_exec x
        (r_start := rPStart h a) (r_len := rPLen h a)
        (by unfold rPStart baseSubReg; omega) (by unfold rPLen baseSubReg; omega)
        (x.P a) (x.hcross a).ne_nil₁ (Alg91Input.P_head_ne_getLast x a) (x.hcross a).nodup₁
        pre suf S hw1 hw2 hn_w htot_w hp hsplit hstart hlen harr2 with
      ⟨s₁, t₁, hex₁, ht₁, hp₁, harr2_1, harrs₁, hregs₁⟩
    rcases markCrossPListProg_exec x hw1 hw2 hn_w htot_w as
        (S ∪ (((x.P a).drop 1).dropLast).toFinset) hp₁ harr2_1 with
      ⟨s₂, t₂, hex₂, ht₂, hp₂, harr2_2, harrs₂, hregs₂⟩
    have hset_eq :
        (S ∪ (((x.P a).drop 1).dropLast).toFinset) ∪
            as.toFinset.biUnion (fun b => (((x.P b).drop 1).dropLast).toFinset) =
          S ∪ (a :: as).toFinset.biUnion (fun b => (((x.P b).drop 1).dropLast).toFinset) := by
      ext v
      simp [Finset.mem_biUnion]
    rw [hset_eq] at harr2_2
    have ht_tot : t₁ + t₂ ≤ 1 + (a :: as).length * (13 + 14 * x.n) := by
      simp only [List.length_cons]
      calc t₁ + t₂ ≤ (13 + 14 * x.n) + (1 + as.length * (13 + 14 * x.n)) := Nat.add_le_add ht₁ ht₂
        _ = 1 + (as.length + 1) * (13 + 14 * x.n) := by ring
    exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ht_tot, hp₂, harr2_2,
      fun arr ha => (harrs₂ arr ha).trans (harrs₁ arr ha),
      fun reg hr5 hr6 hr7 => (hregs₂ reg hr5 hr6 hr7).trans (hregs₁ reg hr5 hr6 hr7)⟩

theorem markCrossQListProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (hw1 : 1 < 2 ^ w) (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w) :
    ∀ (as : List (Fin k)) (S : Finset (Fin x.n)) {s : State}
      (_hp : ParsedAlg91State x s)
      (_harr2 : s.arrs 2 = bitSetList S),
      ∃ s' t,
        Exec w (markCrossQListProg h as) s s' t ∧
        t ≤ 1 + as.length * (13 + 14 * x.n) ∧
        ParsedAlg91State x s' ∧
        s'.arrs 2 = bitSetList (S ∪ as.toFinset.biUnion (fun a => (((x.Q a).drop 1).dropLast).toFinset)) ∧
        (∀ arr : ℕ, arr ≠ 2 → s'.arrs arr = s.arrs arr) ∧
        (∀ reg : ℕ, reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → s'.regs reg = s.regs reg)
  | [], S, s, hp, harr2 => by
    exact ⟨s, 1, .skip s, by omega, hp, by simpa using harr2, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | a :: as, S, s, hp, harr2 => by
    obtain ⟨_, _, ⟨pre, suf, hsplit, hstart, hlen⟩⟩ := hp.2.2.2.2 a
    rcases markCrossPathProg_exec x
        (r_start := rQStart h a) (r_len := rQLen h a)
        (by unfold rQStart baseSubReg; omega) (by unfold rQLen baseSubReg; omega)
        (x.Q a) (x.hcross a).ne_nil₂ (Alg91Input.Q_head_ne_getLast x a) (x.hcross a).nodup₂
        pre suf S hw1 hw2 hn_w htot_w hp hsplit hstart hlen harr2 with
      ⟨s₁, t₁, hex₁, ht₁, hp₁, harr2_1, harrs₁, hregs₁⟩
    rcases markCrossQListProg_exec x hw1 hw2 hn_w htot_w as
        (S ∪ (((x.Q a).drop 1).dropLast).toFinset) hp₁ harr2_1 with
      ⟨s₂, t₂, hex₂, ht₂, hp₂, harr2_2, harrs₂, hregs₂⟩
    have hset_eq :
        (S ∪ (((x.Q a).drop 1).dropLast).toFinset) ∪
            as.toFinset.biUnion (fun b => (((x.Q b).drop 1).dropLast).toFinset) =
          S ∪ (a :: as).toFinset.biUnion (fun b => (((x.Q b).drop 1).dropLast).toFinset) := by
      ext v
      simp [Finset.mem_biUnion]
    rw [hset_eq] at harr2_2
    have ht_tot : t₁ + t₂ ≤ 1 + (a :: as).length * (13 + 14 * x.n) := by
      simp only [List.length_cons]
      calc t₁ + t₂ ≤ (13 + 14 * x.n) + (1 + as.length * (13 + 14 * x.n)) := Nat.add_le_add ht₁ ht₂
        _ = 1 + (as.length + 1) * (13 + 14 * x.n) := by ring
    exact ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ht_tot, hp₂, harr2_2,
      fun arr ha => (harrs₂ arr ha).trans (harrs₁ arr ha),
      fun reg hr5 hr6 hr7 => (hregs₂ reg hr5 hr6 hr7).trans (hregs₁ reg hr5 hr6 hr7)⟩

/-! ### Section 3: Materializing a `Recipe p h k` into `outArr` -/

theorem filter_finRange_toFinset {m : ℕ} (F : Finset (Fin m)) :
    ((List.finRange m).filter (fun u => decide (u ∈ F))).toFinset = F := by
  ext u
  simp

theorem length_filter_finRange_le {m : ℕ} (F : Finset (Fin m)) :
    ((List.finRange m).filter (fun u => decide (u ∈ F))).length ≤ m :=
  (List.length_filter_le _ _).trans (by simp)

/-- Build branch set `idx : Fin p` of `evalRecipe x rec` in array `2` and append it to `outArr`
at offset `reg 8 = idx.1 * x.n`. -/
noncomputable def buildBranchSetProg {p : ℕ} (h k : ℕ) (rec : Recipe p h k) (idx : Fin p) : Cmd :=
  .seq (.alloc 2 (.reg 1))
    (.seq (markBranchVertListProg
        ((List.finRange (elemWallNumVerts h)).filter (fun u => decide (u ∈ rec.branchCoords idx))))
      (.seq (markWallEdgeListProg
          ((List.finRange (elemWallEdges h).length).filter (fun e => decide (e ∈ rec.wallEdges idx))))
        (.seq (markCrossPListProg h
            ((List.finRange k).filter (fun a => decide (a ∈ rec.crossP idx))))
          (.seq (markCrossQListProg h
              ((List.finRange k).filter (fun a => decide (a ∈ rec.crossQ idx))))
            appendArr2ToOutProg))))

/-- Upper bound on the step count of `buildBranchSetProg h k rec idx`. -/
def buildBranchSetCost (h k n : ℕ) : ℕ :=
  14 + 24 * elemWallNumVerts h + 26 * k +
    (15 + 28 * elemWallNumVerts h + 28 * k) * n

theorem buildBranchSetProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (rec : Recipe p h k) (j : ℕ) (hj : j < p)
    (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w) (hpn_w : p * x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s)
    (hr8 : s.regs 8 = j * x.n)
    (hout : s.arrs outArr = encBitSetsUpTo (evalRecipe x rec) j ++ List.replicate ((p - j) * x.n) 0) :
    ∃ s' t,
      Exec w (buildBranchSetProg h k rec ⟨j, hj⟩) s s' t ∧
      t ≤ buildBranchSetCost h k x.n ∧
      ParsedAlg91State x s' ∧
      s'.regs 8 = (j + 1) * x.n ∧
      s'.arrs outArr =
        encBitSetsUpTo (evalRecipe x rec) (j + 1) ++ List.replicate ((p - (j + 1)) * x.n) 0 := by
  have hw1 : 1 < 2 ^ w := by omega
  let idx : Fin p := ⟨j, hj⟩
  -- Step 1: `.alloc 2 (.reg 1)`
  let s₁ := s.setArr 2 (List.replicate x.n 0)
  have hex₁ : Exec w (.alloc 2 (.reg 1)) s s₁ (1 + x.n) :=
    .alloc (by simp [Expr.eval, checkWord, hp.2.1, hn_w])
  have hp₁ : ParsedAlg91State x s₁ :=
    hp.of_eq (State.setArr_arrs_ne _ _ (by decide)) (fun _ _ _ _ _ _ => rfl)
  have harr2_1 : s₁.arrs 2 = bitSetList (∅ : Finset (Fin x.n)) := by
    simp [s₁, bitSetList_empty]
  -- Step 2: `markBranchVertListProg`
  let us := (List.finRange (elemWallNumVerts h)).filter (fun u => decide (u ∈ rec.branchCoords idx))
  let suf_W :=
    (List.finRange k).flatMap (fun a =>
      (x.W_sub a).encList ++
      ((x.P a).length :: (x.P a).map Fin.val) ++
      ((x.Q a).length :: (x.Q a).map Fin.val))
  have hGW_w : (x.G.enc ++ x.W.encList).length < 2 ^ w := by
    have hle : (x.G.enc ++ x.W.encList).length ≤ (encAlg91In x).length := by
      unfold encAlg91In; simp [List.length_append]
    exact Nat.lt_of_le_of_lt hle htot_w
  rcases markBranchVertListProg_exec x.W x.G.enc suf_W hw1 hn_w hc_w hGW_w
      us ∅ hp₁.1 hp₁.2.2.1 harr2_1 with
    ⟨s₂, t₂, hex₂, ht₂, harr2_2, harrs₂, hregs₂⟩
  have hp₂ : ParsedAlg91State x s₂ :=
    hp₁.of_eq (harrs₂ inArr (by decide)) (fun reg _ _ _ _ _ => hregs₂ reg)
  have hus_fin : us.toFinset = rec.branchCoords idx := filter_finRange_toFinset _
  have hus_len : us.length ≤ elemWallNumVerts h := length_filter_finRange_le _
  rw [Finset.empty_union, hus_fin] at harr2_2
  -- Step 3: `markWallEdgeListProg`
  let es := (List.finRange (elemWallEdges h).length).filter (fun e => decide (e ∈ rec.wallEdges idx))
  rcases markWallEdgeListProg_exec x hw1 hn_w htot_w es
      ((rec.branchCoords idx).image x.W.branchVert) hp₂ harr2_2 with
    ⟨s₃, t₃, hex₃, ht₃, hp₃, harr2_3, harrs₃, hregs₃⟩
  have hes_fin : es.toFinset = rec.wallEdges idx := filter_finRange_toFinset _
  have hes_len : es.length ≤ 2 * elemWallNumVerts h :=
    (length_filter_finRange_le _).trans (length_elemWallEdges_le h)
  rw [hes_fin] at harr2_3
  -- Step 4: `markCrossPListProg`
  let asP := (List.finRange k).filter (fun a => decide (a ∈ rec.crossP idx))
  rcases markCrossPListProg_exec x hw1 hw2 hn_w htot_w asP _ hp₃ harr2_3 with
    ⟨s₄, t₄, hex₄, ht₄, hp₄, harr2_4, harrs₄, hregs₄⟩
  have hasP_fin : asP.toFinset = rec.crossP idx := filter_finRange_toFinset _
  have hasP_len : asP.length ≤ k := length_filter_finRange_le _
  rw [hasP_fin] at harr2_4
  -- Step 5: `markCrossQListProg`
  let asQ := (List.finRange k).filter (fun a => decide (a ∈ rec.crossQ idx))
  rcases markCrossQListProg_exec x hw1 hw2 hn_w htot_w asQ _ hp₄ harr2_4 with
    ⟨s₅, t₅, hex₅, ht₅, hp₅, harr2_5, harrs₅, hregs₅⟩
  have hasQ_fin : asQ.toFinset = rec.crossQ idx := filter_finRange_toFinset _
  have hasQ_len : asQ.length ≤ k := length_filter_finRange_le _
  rw [hasQ_fin] at harr2_5
  have harr2_eval : s₅.arrs 2 = bitSetList (evalRecipe x rec idx) := harr2_5
  -- Step 6: `appendArr2ToOutProg`
  have hr8_5 : s₅.regs 8 = j * x.n := by
    rw [hregs₅ 8 (by decide) (by decide) (by decide),
      hregs₄ 8 (by decide) (by decide) (by decide),
      hregs₃ 8 (by decide) (by decide) (by decide),
      hregs₂ 8]
    exact hr8
  have hout_5 : s₅.arrs outArr =
      encBitSetsUpTo (evalRecipe x rec) j ++ List.replicate ((p - j) * x.n) 0 := by
    rw [harrs₅ outArr (by decide), harrs₄ outArr (by decide),
      harrs₃ outArr (by decide), harrs₂ outArr (by decide),
      State.setArr_arrs_ne _ _ (by decide)]
    exact hout
  rcases appendArr2ToOutProg_exec (evalRecipe x rec) j hj hw1 hn_w hpn_w
      hp₅.2.1 hr8_5 harr2_eval hout_5 with
    ⟨s₆, t₆, hex₆, ht₆, hout₆, hr8_6, harrs₆, hregs₆⟩
  have hp₆ : ParsedAlg91State x s₆ :=
    hp₅.of_eq (harrs₆ inArr (by decide)) (fun reg _ hr5 _ _ hr8 => hregs₆ reg hr5 hr8)
  have ht₃_le : t₃ ≤ 1 + 2 * elemWallNumVerts h * (9 + 14 * x.n) := by
    calc t₃ ≤ 1 + es.length * (9 + 14 * x.n) := ht₃
      _ ≤ 1 + 2 * elemWallNumVerts h * (9 + 14 * x.n) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hes_len) 1
  have ht₄_le : t₄ ≤ 1 + k * (13 + 14 * x.n) := by
    calc t₄ ≤ 1 + asP.length * (13 + 14 * x.n) := ht₄
      _ ≤ 1 + k * (13 + 14 * x.n) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hasP_len) 1
  have ht₅_le : t₅ ≤ 1 + k * (13 + 14 * x.n) := by
    calc t₅ ≤ 1 + asQ.length * (13 + 14 * x.n) := ht₅
      _ ≤ 1 + k * (13 + 14 * x.n) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hasQ_len) 1
  have ht_tot : (1 + x.n) + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))) ≤ buildBranchSetCost h k x.n := by
    unfold buildBranchSetCost
    nlinarith
  exact ⟨s₆, (1 + x.n) + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    ht_tot, hp₆, hr8_6, hout₆⟩

/-- Build the first `j` branch sets (`j ≤ p`) of `evalRecipe x rec` into `outArr`. -/
noncomputable def materializeRecipeUpTo (p h k : ℕ) (rec : Recipe p h k) : ℕ → Cmd
  | 0 => .skip
  | j + 1 =>
    .seq (materializeRecipeUpTo p h k rec j)
      (if hj : j < p then buildBranchSetProg h k rec ⟨j, hj⟩ else .skip)

theorem materializeRecipeUpTo_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (rec : Recipe p h k)
    (hw2 : 2 < 2 ^ w) (hn_w : x.n < 2 ^ w) (hpn_w : p * x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w) :
    ∀ j (_hj : j ≤ p) {s : State}
      (_hp : ParsedAlg91State x s)
      (_hr8 : s.regs 8 = 0)
      (_hout : s.arrs outArr = List.replicate (p * x.n) 0),
      ∃ s' t,
        Exec w (materializeRecipeUpTo p h k rec j) s s' t ∧
        t ≤ 1 + j * buildBranchSetCost h k x.n ∧
        ParsedAlg91State x s' ∧
        s'.regs 8 = j * x.n ∧
        s'.arrs outArr =
          encBitSetsUpTo (evalRecipe x rec) j ++ List.replicate ((p - j) * x.n) 0
  | 0, _, s, hp, hr8, hout => by
    exact ⟨s, 1, .skip s, by omega, hp, by simpa using hr8, by simpa [encBitSetsUpTo] using hout⟩
  | j + 1, hj, s, hp, hr8, hout => by
    have hj_lt : j < p := by omega
    rcases materializeRecipeUpTo_exec x rec hw2 hn_w hpn_w hc_w htot_w j (by omega) hp hr8 hout with
      ⟨s₁, t₁, hex₁, ht₁, hp₁, hr8_1, hout₁⟩
    rcases buildBranchSetProg_exec x rec j hj_lt hw2 hn_w hpn_w hc_w htot_w hp₁ hr8_1 hout₁ with
      ⟨s₂, t₂, hex₂, ht₂, hp₂, hr8_2, hout₂⟩
    have ht_tot : t₁ + t₂ ≤ 1 + (j + 1) * buildBranchSetCost h k x.n := by
      calc t₁ + t₂ ≤ (1 + j * buildBranchSetCost h k x.n) + buildBranchSetCost h k x.n :=
            Nat.add_le_add ht₁ ht₂
        _ = 1 + (j + 1) * buildBranchSetCost h k x.n := by ring
    exact ⟨s₂, t₁ + t₂,
      by simpa [materializeRecipeUpTo, hj_lt] using Exec.seq hex₁ hex₂,
      ht_tot, hp₂, hr8_2, hout₂⟩

/-- Materialize all `p` branch sets of `evalRecipe x rec` into `outArr`. -/
noncomputable def materializeRecipeProg (p h k : ℕ) (rec : Recipe p h k) : Cmd :=
  .seq (.alloc outArr (.op .mul (.const p) (.reg 1)))
    (.seq (.assign 8 (.const 0))
      (materializeRecipeUpTo p h k rec p))

theorem materializeRecipeProg_exec {w p h k r : ℕ} (x : Alg91Input p h k r)
    (rec : Recipe p h k)
    (hw2 : 2 < 2 ^ w) (hp_w : p < 2 ^ w) (hn_w : x.n < 2 ^ w) (hpn_w : p * x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s) :
    ∃ s' t,
      Exec w (materializeRecipeProg p h k rec) s s' t ∧
      t ≤ 6 + p * x.n + p * buildBranchSetCost h k x.n ∧
      s'.arrs outArr = encBitSetsUpTo (evalRecipe x rec) p := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr outArr (List.replicate (p * x.n) 0)
  have hex₁ : Exec w (.alloc outArr (.op .mul (.const p) (.reg 1))) s s₁ (3 + p * x.n) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp.2.1, hp_w, hn_w, hpn_w])
  let s₂ := s₁.setReg 8 0
  have hex₂ : Exec w (.assign 8 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hp₂ : ParsedAlg91State x s₂ :=
    hp.of_eq (by simp [s₂, s₁])
      (fun reg _ _ _ _ hr8 => State.setReg_regs_ne _ _ hr8)
  rcases materializeRecipeUpTo_exec x rec hw2 hn_w hpn_w hc_w htot_w p le_rfl
      hp₂ (by simp [s₂]) (by simp [s₂, s₁]) with
    ⟨s₃, t₃, hex₃, ht₃, _, _, hout₃⟩
  rw [Nat.sub_self, Nat.zero_mul, List.replicate_zero, List.append_nil] at hout₃
  exact ⟨s₃, (3 + p * x.n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hout₃⟩

/-! ### Section 4: Subwall Configuration Matching and Dispatch -/

/-- Expression testing whether subwall `a : Fin k` has height `sa.h'` and top-left corner
`x.W.branchVert (sa.cornerIdx 0)`. -/
def testOneSubwallExpr (h : ℕ) {k : ℕ} (a : Fin k) (sa : SubwallParam h) : Expr :=
  .op .mul
    (.op .eq (.reg (rHSub h a)) (.const sa.h'))
    (.op .eq
      (.read inArr (.reg (rPStart h a)))
      (.read inArr (.op .add (.reg 3) (.const (3 + (sa.cornerIdx 0).1)))))

@[simp]
theorem cost_testOneSubwallExpr (h : ℕ) {k : ℕ} (a : Fin k) (sa : SubwallParam h) :
    (testOneSubwallExpr h a sa).cost = 11 := rfl

theorem testOneSubwallExpr_eval {w p h k r : ℕ} (x : Alg91Input p h k r)
    (cfg : Fin k → SubwallParam h)
    (hmatch : ∀ b : Fin k, (cfg b).MatchesSubwall x.W (x.W_sub b))
    (a : Fin k) (sa : SubwallParam h)
    (hw1 : 1 < 2 ^ w) (hh_w : h < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s) :
    (testOneSubwallExpr h a sa).eval w s = some (if sa = cfg a then 1 else 0) := by
  obtain ⟨hhsub_a, ⟨preP, sufP, hsplitP, hstartP, _⟩, _⟩ := hp.2.2.2.2 a
  have hh_sub_le : x.h_sub a ≤ h := (x.hsub a).2.2.1
  have hh_sub_w : x.h_sub a < 2 ^ w := by omega
  have hsa_h_w : sa.h' < 2 ^ w := Nat.lt_of_le_of_lt sa.hle hh_w
  -- Evaluate `inArr[rPStart h a]`
  have hne_P : x.P a ≠ [] := (x.hcross a).ne_nil₁
  have hP_cons : (x.P a).map Fin.val = ((x.P a).head hne_P).1 :: ((x.P a).tail.map Fin.val) := by
    conv_lhs => rw [← List.cons_head_tail hne_P]
    rfl
  have hsplitP' :
      s.arrs inArr =
        preP ++ (((x.P a).head hne_P).1 :: ((x.P a).tail.map Fin.val) ++ sufP) := by
    rw [hp.1, hsplitP, hP_cons]
    simp [List.append_assoc]
  have hpreP_w : preP.length < 2 ^ w := by
    have hle : preP.length ≤ (encAlg91In x).length := by
      rw [hsplitP]; simp [List.length_append]
    exact Nat.lt_of_le_of_lt hle htot_w
  have hin_lenP : preP.length < (s.arrs inArr).length := by
    rw [hsplitP']; simp
  have hreadP : (s.arrs inArr)[preP.length]'hin_lenP = ((x.P a).head hne_P).1 := by
    have hlen2 : preP.length <
        (preP ++ (((x.P a).head hne_P).1 :: ((x.P a).tail.map Fin.val) ++ sufP)).length := by
      simp
    apply getElem_of_eq hsplitP' rfl (h₂ := hlen2)
    rw [List.getElem_append_right (le_refl preP.length)]
    simp
  have hheadP_eq : (x.P a).head hne_P = x.W.branchVert ((cfg a).cornerIdx 0) := by
    rw [(x.hcross a).head₁, (hmatch a).cornerVert_eq (x.hsub a).1 0]
  have hheadP_w : ((x.P a).head hne_P).1 < 2 ^ w :=
    Nat.lt_of_lt_of_le ((x.P a).head hne_P).2 (by omega)
  -- Evaluate `inArr[reg 3 + (3 + (sa.cornerIdx 0).1)]`
  let u_sa := sa.cornerIdx 0
  have hu_sa_lt : u_sa.1 < elemWallNumVerts h := u_sa.2
  have hc_sa_w : 3 + u_sa.1 < 2 ^ w := by omega
  let hdr_W := x.G.enc ++ [h, elemWallNumVerts h, (elemWallEdges h).length]
  let bvs_W := (List.finRange (elemWallNumVerts h)).map (fun u' => (x.W.branchVert u').1)
  let rest_W :=
    (List.finRange (elemWallEdges h).length).flatMap
      (fun e => (x.W.internalVerts e).length :: (x.W.internalVerts e).map Fin.val) ++
    (List.finRange k).flatMap (fun b =>
      (x.W_sub b).encList ++
      ((x.P b).length :: (x.P b).map Fin.val) ++
      ((x.Q b).length :: (x.Q b).map Fin.val))
  have hsplitW : s.arrs inArr = hdr_W ++ (bvs_W ++ rest_W) := by
    rw [hp.1, encAlg91In, WallOfHeight.encList]
    simp [hdr_W, bvs_W, rest_W, List.append_assoc]
  have hidx_eq : x.G.enc.length + (3 + u_sa.1) = hdr_W.length + u_sa.1 := by
    simp [hdr_W]; omega
  have hG_w : x.G.enc.length < 2 ^ w := by
    have hle : x.G.enc.length ≤ (encAlg91In x).length := by
      unfold encAlg91In; simp [List.length_append]
    exact Nat.lt_of_le_of_lt hle htot_w
  have hidxW_w : x.G.enc.length + (3 + u_sa.1) < 2 ^ w := by
    have hle : hdr_W.length + u_sa.1 < (encAlg91In x).length := by
      have : (encAlg91In x).length = (hdr_W ++ (bvs_W ++ rest_W)).length := by
        rw [← hp.1, hsplitW]
      rw [this]
      simp [hdr_W, bvs_W, List.length_append]
      omega
    omega
  have hin_lenW : x.G.enc.length + (3 + u_sa.1) < (s.arrs inArr).length := by
    rw [hsplitW, hidx_eq]
    simp [bvs_W, List.length_append]
    omega
  have hreadW :
      (s.arrs inArr)[x.G.enc.length + (3 + u_sa.1)]'hin_lenW = (x.W.branchVert u_sa).1 := by
    have hlen2 : hdr_W.length + u_sa.1 < (hdr_W ++ (bvs_W ++ rest_W)).length := by
      simp [bvs_W, List.length_append]; omega
    apply getElem_of_eq hsplitW hidx_eq (h₂ := hlen2)
    rw [List.getElem_append_right (Nat.le_add_right _ _)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem_append_left (by simp [bvs_W, hu_sa_lt])]
    simp [bvs_W]
  have hbv_sa_w : (x.W.branchVert u_sa).1 < 2 ^ w :=
    Nat.lt_of_lt_of_le (x.W.branchVert u_sa).2 (by omega)
  have h0_w : 0 < 2 ^ w := by omega
  have heq_iff :
      (x.h_sub a = sa.h' ∧ ((x.P a).head hne_P).1 = (x.W.branchVert u_sa).1) ↔ sa = cfg a := by
    rw [hheadP_eq, (hmatch a).1]
    constructor
    · rintro ⟨hh', hval⟩
      have hbv_eq : x.W.branchVert ((cfg a).cornerIdx 0) = x.W.branchVert (sa.cornerIdx 0) :=
        Fin.ext hval
      have hc_eq : (cfg a).cornerIdx 0 = sa.cornerIdx 0 :=
        x.hW_valid.2.2.1 hbv_eq
      exact (SubwallParam.eq_of_h'_eq_of_cornerIdx_zero_eq hh' hc_eq).symm
    · rintro rfl
      exact ⟨rfl, rfl⟩
  have he1 :
      (Expr.op .eq (.reg (rHSub h a)) (.const sa.h')).eval w s =
        some (if x.h_sub a = sa.h' then 1 else 0) := by
    by_cases h1 : x.h_sub a = sa.h' <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hhsub_a, hh_sub_w, hsa_h_w, h1, hw1, h0_w]
  have hread_lhs :
      (Expr.read inArr (.reg (rPStart h a))).eval w s = some ((x.P a).head hne_P).1 := by
    simp [Expr.eval, checkWord, hstartP, hpreP_w, hin_lenP, hreadP, hheadP_w]
  have hread_rhs :
      (Expr.read inArr (.op .add (.reg 3) (.const (3 + u_sa.1)))).eval w s =
        some (x.W.branchVert u_sa).1 := by
    simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hp.2.2.1,
      hG_w, hc_sa_w, hidxW_w, hin_lenW, hreadW, hbv_sa_w, ↓reduceIte, ↓reduceDIte]
  have he2 :
      (Expr.op .eq
        (.read inArr (.reg (rPStart h a)))
        (.read inArr (.op .add (.reg 3) (.const (3 + u_sa.1))))).eval w s =
        some (if ((x.P a).head hne_P).1 = (x.W.branchVert u_sa).1 then 1 else 0) := by
    rw [Expr.eval, hread_lhs, hread_rhs]
    by_cases h2 : ((x.P a).head hne_P).1 = (x.W.branchVert u_sa).1
    · simp [BinOp.eval, BinOp.raw, checkWord, h2, hw1]
    · simp [BinOp.eval, BinOp.raw, checkWord, h2, h0_w]
  unfold testOneSubwallExpr
  rw [Expr.eval, he1, he2]
  by_cases h1 : x.h_sub a = sa.h' <;>
    by_cases h2 : ((x.P a).head hne_P).1 = (x.W.branchVert u_sa).1
  · have hsa : sa = cfg a := heq_iff.mp ⟨h1, h2⟩
    simp [h1, h2, hsa, BinOp.eval, BinOp.raw, checkWord, hw1]
  · have hsa : sa ≠ cfg a := fun h => h2 (heq_iff.mpr h).2
    simp [h1, h2, hsa, BinOp.eval, BinOp.raw, checkWord, h0_w]
  · have hsa : sa ≠ cfg a := fun h => h1 (heq_iff.mpr h).1
    simp [h1, h2, hsa, BinOp.eval, BinOp.raw, checkWord, h0_w]
  · have hsa : sa ≠ cfg a := fun h => h1 (heq_iff.mpr h).1
    simp [h1, h2, hsa, BinOp.eval, BinOp.raw, checkWord, h0_w]

/-- Conjunction over `as : List (Fin k)` of `testOneSubwallExpr h a (cfg' a)`. -/
def testCfgListExpr (h : ℕ) {k : ℕ} (cfg' : Fin k → SubwallParam h) : List (Fin k) → Expr
  | [] => .const 1
  | a :: as => .op .mul (testOneSubwallExpr h a (cfg' a)) (testCfgListExpr h cfg' as)

theorem cost_testCfgListExpr (h : ℕ) {k : ℕ} (cfg' : Fin k → SubwallParam h) :
    ∀ as : List (Fin k), (testCfgListExpr h cfg' as).cost = 1 + 12 * as.length
  | [] => rfl
  | a :: as => by
    simp only [testCfgListExpr, Expr.cost_op, cost_testOneSubwallExpr,
      cost_testCfgListExpr h cfg' as, List.length_cons]
    ring

theorem testCfgListExpr_eval {w p h k r : ℕ} (x : Alg91Input p h k r)
    (cfg cfg' : Fin k → SubwallParam h)
    (hmatch : ∀ b : Fin k, (cfg b).MatchesSubwall x.W (x.W_sub b))
    (hw1 : 1 < 2 ^ w) (hh_w : h < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s) :
    ∀ as : List (Fin k),
      (testCfgListExpr h cfg' as).eval w s =
        some (if ∀ b ∈ as, cfg' b = cfg b then 1 else 0)
  | [] => by simp [testCfgListExpr, checkWord, hw1]
  | a :: as => by
    have h0_w : 0 < 2 ^ w := by omega
    have he1 := testOneSubwallExpr_eval x cfg hmatch a (cfg' a) hw1 hh_w hn_w hc_w htot_w hp
    have he2 := testCfgListExpr_eval x cfg cfg' hmatch hw1 hh_w hn_w hc_w htot_w hp as
    unfold testCfgListExpr
    rw [Expr.eval, he1, he2]
    by_cases h1 : cfg' a = cfg a <;> by_cases h2 : ∀ b ∈ as, cfg' b = cfg b
    · simp [h1, eq_true h2, BinOp.eval, BinOp.raw, checkWord, hw1]
    · simp [h1, eq_false h2, BinOp.eval, BinOp.raw, checkWord, h0_w]
    · simp [h1, eq_true h2, BinOp.eval, BinOp.raw, checkWord, h0_w]
    · simp [h1, eq_false h2, BinOp.eval, BinOp.raw, checkWord, h0_w]

/-- Dispatch over a list of candidate subwall configurations `cfgs`, materializing `recOfCfg p h cfg'`
for the matching configuration `cfg'`. -/
noncomputable def dispatchConfigs (p h : ℕ) :
    List (Fin (alg91K p) → SubwallParam h) → Cmd
  | [] => .skip
  | cfg' :: cfgs =>
    .ite (testCfgListExpr h cfg' (List.finRange (alg91K p)))
      (materializeRecipeProg p h (alg91K p) (recOfCfg p h cfg'))
      (dispatchConfigs p h cfgs)

theorem dispatchConfigs_exec {w p h r : ℕ} (x : Alg91Input p h (alg91K p) r)
    (cfg : Fin (alg91K p) → SubwallParam h)
    (hmatch : ∀ b : Fin (alg91K p), (cfg b).MatchesSubwall x.W (x.W_sub b))
    (hw2 : 2 < 2 ^ w) (hp_w : p < 2 ^ w) (hh_w : h < 2 ^ w) (hn_w : x.n < 2 ^ w)
    (hpn_w : p * x.n < 2 ^ w) (hc_w : 3 + elemWallNumVerts h < 2 ^ w)
    (htot_w : (encAlg91In x).length < 2 ^ w)
    {s : State}
    (hp : ParsedAlg91State x s) :
    ∀ (cfgs : List (Fin (alg91K p) → SubwallParam h)),
      cfg ∈ cfgs →
      ∃ s' t,
        Exec w (dispatchConfigs p h cfgs) s s' t ∧
        t ≤ cfgs.length * (1 + 14 * alg91K p) +
          (6 + p * x.n + p * buildBranchSetCost h (alg91K p) x.n) ∧
        s'.arrs outArr = encBitSetsUpTo (evalRecipe x (recOfCfg p h cfg)) p
  | [], hmem => False.elim (List.not_mem_nil hmem)
  | cfg' :: cfgs, hmem => by
    have hw1 : 1 < 2 ^ w := by omega
    have heval := testCfgListExpr_eval x cfg cfg' hmatch hw1 hh_w hn_w hc_w htot_w hp
      (List.finRange (alg91K p))
    have hcost : (testCfgListExpr h cfg' (List.finRange (alg91K p))).cost ≤ 1 + 14 * alg91K p := by
      rw [cost_testCfgListExpr, List.length_finRange]
      omega
    by_cases heq : cfg' = cfg
    · subst heq
      have heval1 : (testCfgListExpr h cfg' (List.finRange (alg91K p))).eval w s = some 1 := by
        simpa using heval
      rcases materializeRecipeProg_exec x (recOfCfg p h cfg')
          hw2 hp_w hn_w hpn_w hc_w htot_w hp with
        ⟨s', t_mat, hex_mat, ht_mat, hout⟩
      have hex_ite : Exec w (dispatchConfigs p h (cfg' :: cfgs)) s s'
          ((testCfgListExpr h cfg' (List.finRange (alg91K p))).cost + t_mat) :=
        .ite_true heval1 (by decide) hex_mat
      refine ⟨s', _, hex_ite, ?_, hout⟩
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · have hmem_tail : cfg ∈ cfgs := by
        rcases List.mem_cons.mp hmem with h | h
        · exact False.elim (heq h.symm)
        · exact h
      have hcond : ¬ (∀ b : Fin (alg91K p), cfg' b = cfg b) :=
        fun h => heq (funext h)
      have heval0 : (testCfgListExpr h cfg' (List.finRange (alg91K p))).eval w s = some 0 := by
        simpa [eq_false hcond] using heval
      rcases dispatchConfigs_exec x cfg hmatch hw2 hp_w hh_w hn_w hpn_w hc_w htot_w hp
          cfgs hmem_tail with
        ⟨s', t_rec, hex_rec, ht_rec, hout⟩
      have hex_ite : Exec w (dispatchConfigs p h (cfg' :: cfgs)) s s'
          ((testCfgListExpr h cfg' (List.finRange (alg91K p))).cost + t_rec) :=
        .ite_false heval0 hex_rec
      refine ⟨s', _, hex_ite, ?_, hout⟩
      rw [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-! ### Section 5: Complete Word RAM Program `alg91Prog` and `gm13_algorithm_9_1` -/

theorem const_mul_lt_two_pow_wordSize {K c S : ℕ} (hc : K + 1 ≤ c) :
    K * (S + 1) < 2 ^ wordSize c S := by
  have h1 : K ≤ (S + 2) ^ K :=
    (Nat.le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left (by omega) K)
  have h2 : K * (S + 1) ≤ (S + 2) ^ (K + 1) := by
    rw [Nat.pow_succ]
    exact Nat.mul_le_mul h1 (by omega)
  have h3 : (S + 2) ^ (K + 1) ≤ (S + 2) ^ c := Nat.pow_le_pow_right (by omega) hc
  exact Nat.lt_of_le_of_lt (h2.trans h3) (pow_lt_two_pow_wordSize (by omega) S)

/-- Complete Word RAM program for **Graph Minors XIII, (9.1)** (page 98) for target
clique size `p` and wall height `h`. -/
noncomputable def alg91Prog (p h : ℕ) : Cmd :=
  .seq (parseAlg91Prog h (alg91K p))
    (dispatchConfigs p h (allSubwallConfigs h (alg91K p)))

/-- **Graph Minors XIII, (9.1), Algorithmic Theorem (Section 9, page 98):**
For every integer `p ≥ 0`, there exist `k, r ≥ 0` (`alg91K p` and `alg91R p`) such that for every
even height `h ≥ 2`, `alg91Prog p h` computes a valid model of $K_p$ in `G` in time `O(ε(G))`. -/
theorem gm13_algorithm_9_1 : Algorithm91Statement := by
  intro p
  refine ⟨alg91K p, alg91R p, fun h h2 he => ?_⟩
  let k := alg91K p
  let r := alg91R p
  let cfgs := allSubwallConfigs h k
  let C_parse := 18 + 22 * elemWallNumVerts h + k * (46 + 28 * elemWallNumVerts h)
  let C_disp := cfgs.length * (1 + 14 * k) + 6 +
    p * (14 + 24 * elemWallNumVerts h + 26 * k) +
    p * (16 + 28 * elemWallNumVerts h + 28 * k)
  let C := C_parse + C_disp + 1
  let K := 4 + p + h + 3 * elemWallNumVerts h + encAlg91LenFactor h k
  let c := K + 1
  refine ⟨alg91Prog p h, C, c, by omega, by omega, fun x s hs => ?_⟩
  let S := alg91Size x
  have hS_pos : 1 ≤ S := by unfold S alg91Size; omega
  have hn_le_S : x.n ≤ S := by unfold S alg91Size; omega
  let w := wordSize c S
  have hKS_w : K * (S + 1) < 2 ^ w := const_mul_lt_two_pow_wordSize le_rfl
  have hK_w : K < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right K (by omega)) hKS_w
  have hw3 : 3 < 2 ^ w := by dsimp [K] at hK_w; omega
  have hw2 : 2 < 2 ^ w := by omega
  have hp_w : p < 2 ^ w := by dsimp [K] at hK_w; omega
  have hh_w : h < 2 ^ w := by dsimp [K] at hK_w; omega
  have hc_w : 3 + elemWallNumVerts h < 2 ^ w := by dsimp [K] at hK_w; omega
  have hE_w : 2 * elemWallNumVerts h < 2 ^ w := by dsimp [K] at hK_w; omega
  have hn_w : x.n < 2 ^ w := by
    have : x.n ≤ K * (S + 1) := by
      have : 1 * x.n ≤ K * (S + 1) := Nat.mul_le_mul (by dsimp [K]; omega) (by omega)
      omega
    omega
  have hpn_w : p * x.n < 2 ^ w := by
    have : p * x.n ≤ K * (S + 1) := Nat.mul_le_mul (by dsimp [K]; omega) (by omega)
    omega
  have htot_w : (encAlg91In x).length < 2 ^ w := by
    have h1 := length_encAlg91In_le x
    have h2 : encAlg91LenFactor h k * S ≤ K * (S + 1) :=
      Nat.mul_le_mul (by dsimp [K]; omega) (by omega)
    exact Nat.lt_of_le_of_lt (h1.trans h2) hKS_w
  -- Step 1: Parse `encAlg91In x`
  rcases parseAlg91Prog_exec x hw3 hh_w hn_w hc_w hE_w htot_w hs with
    ⟨s₁, t₁, hex₁, ht₁, hp₁⟩
  -- Step 2: Obtain the subwall configuration `cfg` matching `x.W_sub`
  have hex_cfg : ∀ b : Fin k, ∃ sb : SubwallParam h, sb.MatchesSubwall x.W (x.W_sub b) :=
    fun b => SubwallParam.exists_matchesSubwall_of_isSubwallOf (x.hsub b)
  let cfg : Fin k → SubwallParam h := fun b => (hex_cfg b).choose
  have hmatch : ∀ b : Fin k, (cfg b).MatchesSubwall x.W (x.W_sub b) :=
    fun b => (hex_cfg b).choose_spec
  have hcfg_mem : cfg ∈ cfgs := mem_allSubwallConfigs h k cfg
  -- Step 3: Dispatch over `cfgs`
  rcases dispatchConfigs_exec x cfg hmatch hw2 hp_w hh_w hn_w hpn_w hc_w htot_w hp₁ cfgs hcfg_mem with
    ⟨s₂, t₂, hex₂, ht₂, hout₂⟩
  have ht_tot : t₁ + t₂ ≤ C * S := by
    have ht₁_le : t₁ ≤ C_parse * S := by
      calc t₁ ≤ C_parse := ht₁
        _ ≤ C_parse * S := Nat.le_mul_of_pos_right _ hS_pos
    have ht₂_le : t₂ ≤ C_disp * S := by
      have hcost :
          6 + p * x.n + p * buildBranchSetCost h k x.n =
            6 + p * (14 + 24 * elemWallNumVerts h + 26 * k) +
              p * (16 + 28 * elemWallNumVerts h + 28 * k) * x.n := by
        unfold buildBranchSetCost
        ring
      change t₂ ≤ cfgs.length * (1 + 14 * k) + (6 + p * x.n + p * buildBranchSetCost h k x.n) at ht₂
      rw [hcost] at ht₂
      have hconst_le :
          cfgs.length * (1 + 14 * k) + 6 + p * (14 + 24 * elemWallNumVerts h + 26 * k) ≤
            (cfgs.length * (1 + 14 * k) + 6 + p * (14 + 24 * elemWallNumVerts h + 26 * k)) * S :=
        Nat.le_mul_of_pos_right _ hS_pos
      have hlin_le :
          p * (16 + 28 * elemWallNumVerts h + 28 * k) * x.n ≤
            p * (16 + 28 * elemWallNumVerts h + 28 * k) * S :=
        Nat.mul_le_mul_left _ hn_le_S
      have hsum_eq :
          (cfgs.length * (1 + 14 * k) + 6 + p * (14 + 24 * elemWallNumVerts h + 26 * k)) * S +
            p * (16 + 28 * elemWallNumVerts h + 28 * k) * S = C_disp * S := by
        dsimp [C_disp]
        ring
      omega
    have hCS : C_parse * S + C_disp * S ≤ C * S := by
      dsimp [C]
      have : C_parse * S + C_disp * S = (C_parse + C_disp) * S := (Nat.add_mul _ _ _).symm
      rw [this]
      exact Nat.mul_le_mul_right S (by omega)
    omega
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ht_tot, evalRecipe x (recOfCfg p h cfg), hout₂,
    isCliqueModel_evalRecipe_recOfCfg p h h2 he x cfg hmatch⟩

end Alg91

export Alg91 (alg91Prog gm13_algorithm_9_1)

end GraphMinor.Compute
