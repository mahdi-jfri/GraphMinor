module

public import GraphMinor.Compute.TwoPathsCyc

/-!
# Chords of the cycle that join two vertices that are apart

Line 2 of Algorithm 5.1 (Humeau and Pous, page 22) needs a `C`-path between two vertices of `C`
that are not consecutive. The shortest such paths are *chords*: edges `x y` of `H` with `x, y ∈ C`
apart on `C`. The program `chordScan` looks at every edge at every vertex of the cycle and stops
looking once it has found such a chord; it writes the chord into registers `rPx`, `rPy`, writes
`n` into `rPu0` (to say that the path is a single edge) and sets `rFound` to `1`
(`chordScan_exec`). Otherwise `rFound` stays `0` and no edge of `H` joins two vertices of `C` that
are apart.

`PairOK` is the result shared with the search of components (`TwoPathsSweep.lean`): either a
chord, or two vertices `u₀, u₁` off the cycle, joined in `H - C`, with `x u₀` and `u₁ y` edges.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### Registers -/

/-- Whether a pair was found. -/
abbrev rFound : Reg := 77
/-- First end of the pair. -/
abbrev rPx : Reg := 78
/-- Second end of the pair. -/
abbrev rPy : Reg := 79
/-- Neighbour of `rPx` off the cycle, or `n` for a chord. -/
abbrev rPu0 : Reg := 80
/-- Neighbour of `rPy` off the cycle. -/
abbrev rPu1 : Reg := 81
/-- A position just read. -/
abbrev rQ : Reg := 90
/-- Cursor of an adjacency list. -/
abbrev rK2 : Reg := 92
/-- End of an adjacency list. -/
abbrev rHi2 : Reg := 93
/-- A neighbour. -/
abbrev rY : Reg := 94

variable {n : ℕ}

/-! ### Conditions as expressions -/

theorem lt_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .lt A B).eval w s = some (if a < b then 1 else 0) := by
  by_cases h : a < b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw, show 0 < 2 ^ w by omega]

theorem eq_eval {w : ℕ} {s : State} {A B : Expr} {a b : ℕ} (hA : A.eval w s = some a)
    (hB : B.eval w s = some b) (hw : 1 < 2 ^ w) :
    (Expr.op .eq A B).eval w s = some (if a = b then 1 else 0) := by
  by_cases h : a = b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, h, hw, show 0 < 2 ^ w by omega]

theorem mul_eval {w : ℕ} {s : State} {A B : Expr} {a b : Prop} [Decidable a] [Decidable b]
    (hA : A.eval w s = some (if a then 1 else 0)) (hB : B.eval w s = some (if b then 1 else 0))
    (hw : 1 < 2 ^ w) :
    (Expr.op .mul A B).eval w s = some (if a ∧ b then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;>
    simp [Expr.eval, hA, hB, BinOp.eval, BinOp.raw, checkWord, ha, hb, hw,
      show 0 < 2 ^ w by omega]

/-- The distance from position `P` to position `Q` around the cycle of length `rk`. -/
def distE (P Q : Expr) : Expr := .op .mod (.op .sub (.op .add Q (.reg rk)) P) (.reg rk)

/-- `1` when position `Q` and position `P` are apart, else `0`. -/
def apartE (P Q : Expr) : Expr :=
  .op .mul (.op .lt (.const 1) (distE P Q)) (.op .lt (distE P Q) (.op .sub (.reg rk) (.const 1)))

theorem apartE_eval {w : ℕ} {s : State} {P Q : Expr} {p q k : ℕ} (hP : P.eval w s = some p)
    (hQ : Q.eval w s = some q) (hk : s.regs rk = k) (hk0 : 0 < k) (hqk : q + k < 2 ^ w)
    (hw : 1 < 2 ^ w) :
    (apartE P Q).eval w s = some (if Apart k q p then 1 else 0) := by
  have hkw' : k < 2 ^ w := by omega
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  have hkw : (Expr.reg rk).eval w s = some k := by simp [checkWord, hk, hkw']
  have hadd : (Expr.op .add Q (.reg rk)).eval w s = some (q + k) := by
    simp [Expr.eval, hQ, hk, hkw', BinOp.eval, BinOp.raw, checkWord, hqk]
  have hsub : (Expr.op .sub (.op .add Q (.reg rk)) P).eval w s = some (q + k - p) := by
    simp [Expr.eval, hQ, hk, hkw', hqk, hP, BinOp.eval, BinOp.raw, checkWord,
      show q + k - p < 2 ^ w by omega]
  have hd : (distE P Q).eval w s = some (cdist k q p) := by
    have hm : (q + k - p) % k < 2 ^ w := lt_trans (Nat.mod_lt _ hk0) hkw'
    simp [distE, Expr.eval, hQ, hk, hkw', hqk, hP, BinOp.eval, BinOp.raw, checkWord, cdist,
      Nat.ne_of_gt hk0, hm, show q + k - p < 2 ^ w by omega]
  have h1 : (Expr.const 1).eval w s = some 1 := by simp [checkWord, hw]
  have hk1 : (Expr.op .sub (.reg rk) (.const 1)).eval w s = some (k - 1) := by
    simp [Expr.eval, hk, hkw', hw0, hw, BinOp.eval, BinOp.raw, checkWord,
      show k - 1 < 2 ^ w by omega]
  exact mul_eval (lt_eval h1 hd hw) (lt_eval hd hk1 hw) hw

/-! ### The pair -/

/-- The pair found by line 2 of Algorithm 5.1: vertices `x, y` of `T` that are apart, joined by a
chord (`rPu0 = n`) or by edges `x u₀`, `u₁ y` to vertices `u₀, u₁` off `T` that are joined in
`H - T`. -/
def PairOK (H : SimpleGraph (Fin n)) (T : List (Fin n)) (s : State) : Prop :=
  ∃ x y : Fin n, x ∈ T ∧ y ∈ T ∧ s.regs rPx = x.1 ∧ s.regs rPy = y.1 ∧
    Apart T.length (T.idxOf y + 1) (T.idxOf x + 1) ∧
    ((s.regs rPu0 = n ∧ H.Adj x y) ∨
      ∃ u₀ u₁ : Fin n, s.regs rPu0 = u₀.1 ∧ s.regs rPu1 = u₁.1 ∧ u₀ ∉ T ∧ u₁ ∉ T ∧
        H.Adj x u₀ ∧ H.Adj u₁ y ∧ (restrict H {v | v ∉ T}).Reachable u₀ u₁)

theorem PairOK.of_regs {H : SimpleGraph (Fin n)} {T : List (Fin n)} {s s' : State}
    (h : PairOK H T s) (h1 : s'.regs rPx = s.regs rPx) (h2 : s'.regs rPy = s.regs rPy)
    (h3 : s'.regs rPu0 = s.regs rPu0) (h4 : s'.regs rPu1 = s.regs rPu1) : PairOK H T s' := by
  rw [PairOK, h1, h2, h3, h4]; exact h

/-- No edge in the scanned set `S` is a chord between vertices that are apart. -/
def NoChord (H : SimpleGraph (Fin n)) (T : List (Fin n)) (S : Fin n → Fin n → Prop) : Prop :=
  ∀ x y, S x y → H.Adj x y → y ∈ T → ¬ Apart T.length (T.idxOf y + 1) (T.idxOf x + 1)

/-- The result of a scan: no chord found in `S`, or a pair found. -/
def ChordRes (H : SimpleGraph (Fin n)) (T : List (Fin n)) (S : Fin n → Fin n → Prop)
    (s : State) : Prop :=
  (s.regs rFound = 0 ∧ NoChord H T S) ∨ (s.regs rFound = 1 ∧ PairOK H T s)

/-! ### The program -/

/-- The condition of a new chord: the neighbour is on the cycle, nothing was found yet, and the
two positions are apart. -/
def chordCond : Expr :=
  .op .mul (.op .mul (.op .lt (.const 0) (.reg rQ)) (.op .eq (.reg rFound) (.const 0)))
    (apartE (.op .add (.reg rI2) (.const 1)) (.reg rQ))

/-- Look at the neighbour `rY` of the cycle vertex `rX2`. -/
def chordBody : Cmd :=
  .seq (.assign rQ (.read aPos (.reg rY)))
    (.ite chordCond
      (.seq (.assign rPx (.reg rX2)) (.seq (.assign rPy (.reg rY))
        (.seq (.assign rPu0 (.reg 40)) (.assign rFound (.const 1)))))
      .skip)

/-- Look at all neighbours of the cycle vertex at index `rI2`. -/
def chordOuter : Cmd :=
  .seq (.assign rX2 (.read aCyc (.reg rI2)))
    (forList aStart aEnd aEnt rX2 rK2 rHi2 rY chordBody)

/-- Look at all edges at the cycle. -/
def chordScan : Cmd :=
  .seq (.assign rFound (.const 0)) (.seq (.assign rI2 (.const 0)) (forUp rI2 (.reg rk) chordOuter))

/-- The registers that `chordScan` writes. -/
def chordRegs : List ℕ := [rI2, rX2, rK2, rHi2, rY, rQ, rPx, rPy, rPu0, rFound]

/-- The array of positions of `T`. -/
def posArr (T : List (Fin n)) : List ℕ :=
  List.ofFn (fun x : Fin n => if x ∈ T then T.idxOf x + 1 else 0)

/-- What the chord scan needs of the state it starts from. -/
structure ChordPre (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) (T : List (Fin n))
    (s : State) : Prop where
  adj : IsAdjList H aStart aEnd aEnt lists s
  cyc : s.arrs aCyc = T.map Fin.val
  pos : s.arrs aPos = posArr T
  k : s.regs rk = T.length
  n : s.regs 40 = n

theorem ChordPre.keeps {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {T : List (Fin n)}
    {s₀ s : State} (h : ChordPre H lists T s₀) (hk : Keeps chordRegs [] s₀ s) :
    ChordPre H lists T s := by
  refine ⟨h.adj.of_arrs_eq (hk.2 _ (by simp)) (hk.2 _ (by simp)) (hk.2 _ (by simp)), ?_, ?_, ?_,
    ?_⟩
  · rw [hk.2 _ (by simp)]; exact h.cyc
  · rw [hk.2 _ (by simp)]; exact h.pos
  · rw [hk.1 _ (by simp [chordRegs])]; exact h.k
  · rw [hk.1 _ (by simp [chordRegs])]; exact h.n

theorem pos_le {T : List (Fin n)} {y : Fin n} (hy : y ∈ T) : T.idxOf y + 1 ≤ T.length := by
  have := List.idxOf_lt_length_iff.mpr hy
  omega

/-- **One neighbour.** -/
theorem chordBody_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (i : ℕ) (hi : i < T.length) (y : Fin n)
    (hy : H.Adj T[i] y) (S S' : Fin n → Fin n → Prop)
    (hS' : ∀ a b, S' a b → S a b ∨ (a = T[i] ∧ b = y)) (s : State)
    (hk : Keeps chordRegs [] s₀ s) (hri : s.regs rI2 = i) (hrx : s.regs rX2 = T[i].1)
    (hry : s.regs rY = y.1) (hres : ChordRes H T S s) :
    ∃ s' t, Exec w chordBody s s' t ∧ t ≤ 50 ∧ Keeps chordRegs [] s₀ s' ∧
      s'.regs rI2 = i ∧ s'.regs rX2 = T[i].1 ∧ s'.regs rK2 = s.regs rK2 ∧
      s'.regs rHi2 = s.regs rHi2 ∧ ChordRes H T S' s' := by
  have hpre' := hpre.keeps hk
  have hyw : y.1 < 2 ^ w := by have := y.2; omega
  obtain ⟨q, hq⟩ : ∃ q, (if y ∈ T then T.idxOf y + 1 else 0) = q := ⟨_, rfl⟩
  have hqk : q ≤ T.length := by
    rw [← hq]; split_ifs with h
    · exact pos_le h
    · omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  have hread : (Expr.read aPos (.reg rY)).eval w s = some q := by
    simp [Expr.eval, checkWord, hry, hyw, hpre'.pos, posArr, hq, show q < 2 ^ w by omega]
  set s₁ := s.setReg rQ q with hs₁
  have hex₁ : Exec w (.assign rQ (.read aPos (.reg rY))) s s₁ (1 + 1 + 1) := .assign hread
  have hk₁ : Keeps chordRegs [] s₀ s₁ := hk.setReg (by simp [chordRegs]) _
  have hw1 : 1 < 2 ^ w := by omega
  have hiw : i + 1 < 2 ^ w := by omega
  have hqw : q < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set f := s.regs rFound with hf
  have hfw : f ≤ 1 := by
    rcases hres with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hcond : chordCond.eval w s₁ =
      some (if (0 < q ∧ f = 0) ∧ Apart T.length q (i + 1) then 1 else 0) := by
    have h0 : (Expr.const 0).eval w s₁ = some 0 := by simp [checkWord, hw1]
    have hqe : (Expr.reg rQ).eval w s₁ = some q := by simp [checkWord, s₁, hqw]
    have hfe : (Expr.reg rFound).eval w s₁ = some f := by
      simp [checkWord, s₁, f, show f < 2 ^ w by omega]
    have hie : (Expr.op .add (.reg rI2) (.const 1)).eval w s₁ = some (i + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hri, hiw, show i < 2 ^ w by omega,
        hw1]
    exact mul_eval (mul_eval (lt_eval h0 hqe hw1) (eq_eval hfe h0 hw1) hw1)
      (apartE_eval hie hqe (by simp [s₁, hpre'.k]) (by omega) (by omega) hw1) hw1
  by_cases hc : (0 < q ∧ f = 0) ∧ Apart T.length q (i + 1)
  · -- a new chord
    have hyT : y ∈ T := by
      by_contra h; simp [← hq, h] at hc
    set s₂ := s₁.setReg rPx T[i].1 with hs₂
    set s₃ := s₂.setReg rPy y.1 with hs₃
    set s₄ := s₃.setReg rPu0 n with hs₄
    set s₅ := s₄.setReg rFound 1 with hs₅
    have hTiw : T[i].1 < 2 ^ w := by have := T[i].2; omega
    have hex : Exec w chordBody s s₅ (3 + (chordCond.cost + (2 + (2 + (2 + 2))))) :=
      .seq hex₁ (.ite_true hcond (by simp [hc])
        (.seq (.assign (by simp [checkWord, s₁, hrx, hTiw]))
          (.seq (.assign (by simp [checkWord, s₂, s₁, hry, hyw]))
            (.seq (.assign (by simp [checkWord, s₃, s₂, s₁, hpre'.n, hnw]))
              (.assign (by simp [checkWord, hw1]))))))
    refine ⟨s₅, _, hex, by simp [chordCond, apartE, distE, Expr.cost], ?_, by simp [s₅, s₄, s₃,
      s₂, s₁, hri], by simp [s₅, s₄, s₃, s₂, s₁, hrx], by simp [s₅, s₄, s₃, s₂, s₁],
      by simp [s₅, s₄, s₃, s₂, s₁], Or.inr ⟨by simp [s₅], T[i], y, List.getElem_mem hi, hyT,
        by simp [s₅, s₄, s₃, s₂], by simp [s₅, s₄, s₃], ?_, Or.inl ⟨by simp [s₅, s₄], hy⟩⟩⟩
    · exact (((hk₁.setReg (by simp [chordRegs]) _).setReg (by simp [chordRegs]) _).setReg
        (by simp [chordRegs]) _).setReg (by simp [chordRegs]) _
    · have hqy : q = T.idxOf y + 1 := by rw [← hq]; simp [hyT]
      rw [← hqy, idxOf_getElem_of_nodup hT hi]
      exact hc.2
  · have hcond' : chordCond.eval w s₁ = some 0 := by rw [hcond]; simp [hc]
    have hex : Exec w chordBody s s₁ (3 + (chordCond.cost + 1)) :=
      .seq hex₁ (.ite_false hcond' (.skip _))
    refine ⟨s₁, _, hex, by simp [chordCond, apartE, distE, Expr.cost], hk₁, by simp [s₁, hri],
      by simp [s₁, hrx], by simp [s₁], by simp [s₁], ?_⟩
    rcases hres with ⟨h0, hno⟩ | ⟨h1, hp⟩
    · refine Or.inl ⟨by simp [s₁, ← h0], fun a b hab hadj hb => ?_⟩
      rcases hS' a b hab with hab | ⟨rfl, rfl⟩
      · exact hno a b hab hadj hb
      · intro hap
        apply hc
        have hqy : q = T.idxOf b + 1 := by rw [← hq]; simp [hb]
        refine ⟨⟨by omega, by simp [f, h0]⟩, ?_⟩
        rw [hqy, ← idxOf_getElem_of_nodup hT hi]
        exact hap
    · exact Or.inr ⟨by simp [s₁, h1], hp.of_regs (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
        (by simp [s₁])⟩


theorem ChordRes.of_regs {H : SimpleGraph (Fin n)} {T : List (Fin n)} {S S' : Fin n → Fin n → Prop}
    {s s' : State} (h : ChordRes H T S s) (hS : ∀ a b, S' a b → H.Adj a b → S a b)
    (h0 : s'.regs rFound = s.regs rFound) (h1 : s'.regs rPx = s.regs rPx)
    (h2 : s'.regs rPy = s.regs rPy) (h3 : s'.regs rPu0 = s.regs rPu0)
    (h4 : s'.regs rPu1 = s.regs rPu1) : ChordRes H T S' s' := by
  rcases h with ⟨hf, hno⟩ | ⟨hf, hp⟩
  · exact Or.inl ⟨by rw [h0, hf], fun a b hab hadj => hno a b (hS a b hab hadj) hadj⟩
  · exact Or.inr ⟨by rw [h0, hf], hp.of_regs h1 h2 h3 h4⟩

/-- The edges scanned when the first `i` vertices of `T` are done, and the first `j` neighbours
of `T[i]`. -/
def chordScanned (lists : Fin n → List ℕ) (T : List (Fin n)) (i j : ℕ) (x y : Fin n) : Prop :=
  x ∈ T.take i ∨ (∃ hi : i < T.length, x = T[i] ∧ y.1 ∈ (lists T[i]).take j)

/-- **All neighbours of one cycle vertex.** -/
theorem chordOuter_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (i : ℕ) (hi : i < T.length) (s : State) (hk : Keeps chordRegs [] s₀ s)
    (hri : s.regs rI2 = i) (hres : ChordRes H T (fun x _ => x ∈ T.take i) s) :
    ∃ s' t, Exec w chordOuter s s' t ∧ t ≤ 12 + 60 * (lists T[i]).length ∧
      Keeps chordRegs [] s₀ s' ∧ s'.regs rI2 = i ∧
      ChordRes H T (fun x _ => x ∈ T.take (i + 1)) s' := by
  have hpre' := hpre.keeps hk
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set x := T[i] with hx
  have hxw : x.1 < 2 ^ w := by have := x.2; omega
  have hread : (Expr.read aCyc (.reg rI2)).eval w s = some x.1 := by
    simp [Expr.eval, checkWord, hri, hpre'.cyc, show i < T.length from hi, x, hxw,
      show i < 2 ^ w by omega]
  set s₁ := s.setReg rX2 x.1 with hs₁
  have hex₁ : Exec w (.assign rX2 (.read aCyc (.reg rI2))) s s₁ (1 + 1 + 1) := .assign hread
  have hk₁ : Keeps chordRegs [] s₀ s₁ := hk.setReg (by simp [chordRegs]) _
  obtain ⟨st, en, hlist₀⟩ := hpre.adj.1.2.2 x
  obtain ⟨hmem_lt, -, -, hadj_iff⟩ := hpre.adj.2 x
  have hlistOf : ∀ st' : State, Keeps chordRegs [] s₀ st' →
      IsListAt aStart aEnd aEnt x.1 st en (lists x) st' := fun st' hk' =>
    hlist₀.of_arrs_eq (hk'.2 _ (by simp)) (hk'.2 _ (by simp)) (hk'.2 _ (by simp))
  have hen_w : en < 2 ^ w := by
    obtain ⟨_, _, hle, _⟩ := hlist₀
    omega
  let II : ℕ → State → Prop := fun j st' => Keeps chordRegs [] s₀ st' ∧ st'.regs rI2 = i ∧
    st'.regs rX2 = x.1 ∧ ChordRes H T (chordScanned lists T i j) st'
  have hI0 : II 0 s₁ := by
    refine ⟨hk₁, by simp [s₁, hri], by simp [s₁], hres.of_regs ?_ (by simp [s₁]) (by simp [s₁])
      (by simp [s₁]) (by simp [s₁]) (by simp [s₁])⟩
    rintro a b (h | ⟨_, -, h⟩) -
    · exact h
    · simp at h
  have hinit : ∀ st', II 0 st' → IsListAt aStart aEnd aEnt x.1 st en (lists x) st' ∧
      st'.regs rX2 = x.1 ∧ II 0 ((st'.setReg rK2 st).setReg rHi2 en) := by
    intro st' hst'
    obtain ⟨hk', hri', hrx', hres'⟩ := hst'
    refine ⟨hlistOf st' hk', hrx', (hk'.setReg (by simp [chordRegs]) st).setReg
      (by simp [chordRegs]) en, by simp [hri'], by simp [hrx'], ?_⟩
    exact hres'.of_regs (fun _ _ h _ => h) (by simp) (by simp) (by simp) (by simp) (by simp)
  have hfor := Triple.forList_const aStart aEnd aEnt rX2 rK2 rHi2 rY x.1 st en (lists x) II 50
    chordBody (by decide) (by decide) hw1 hxw hen_w
    (fun z hz => by have := hmem_lt z hz; omega) hinit
    (fun j _ st' hst' => hlistOf st' hst'.1)
    (fun j hj sv ⟨st', hI, hsv, hrk, hrhi⟩ => by
      subst hsv
      obtain ⟨hk', hri', hrx', hres'⟩ := hI
      have hyn : (lists x)[j] < n := hmem_lt _ (List.getElem_mem hj)
      have hy : H.Adj T[i] ⟨(lists x)[j], hyn⟩ := (hadj_iff _).1 (List.getElem_mem hj)
      have hS' : ∀ a b, chordScanned lists T i (j + 1) a b →
          chordScanned lists T i j a b ∨ (a = T[i] ∧ b = ⟨(lists x)[j], hyn⟩) := by
        intro a b hab
        rcases hab with h | ⟨hi', ha, hb⟩
        · exact Or.inl (Or.inl h)
        · rw [List.take_add_one, List.mem_append] at hb
          rcases hb with hb | hb
          · exact Or.inl (Or.inr ⟨hi', ha, hb⟩)
          · right
            refine ⟨ha, Fin.ext ?_⟩
            have he : (lists T[i])[j]? = some (lists x)[j] := List.getElem?_eq_getElem hj
            rw [he] at hb
            simpa using hb
      obtain ⟨s', t, hex, ht, hk'', hri'', hrx'', hrk'', hrhi'', hres''⟩ :=
        chordBody_exec H lists T hT hk4 hn s₀ hpre i hi ⟨(lists x)[j], hyn⟩ hy
          (chordScanned lists T i j) (chordScanned lists T i (j + 1)) hS'
          (st'.setReg rY (lists x)[j]) (hk'.setReg (by simp [chordRegs]) _) (by simp [hri'])
          (by simp [hrx', hx]) (by simp)
          (hres'.of_regs (fun _ _ h _ => h) (by simp) (by simp) (by simp) (by simp) (by simp))
      have hII : II (j + 1) (s'.setReg rK2 (st + (j + 1))) := by
        refine ⟨hk''.setReg (by simp [chordRegs]) _, by simp [hri''], by simp [hrx'', hx], ?_⟩
        exact hres''.of_regs (fun _ _ h _ => h) (by simp) (by simp) (by simp) (by simp)
          (by simp)
      exact ⟨s', t, hex, ht, hII, by rw [hrk'']; simpa using hrk, by rw [hrhi'']; simpa using hrhi⟩)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hri₂, -, hres₂⟩ := hfor s₁ hI0
  refine ⟨s₂, _, .seq hex₁ hex₂, by dsimp only at ht₂; omega, hk₂, hri₂, ?_⟩
  refine hres₂.of_regs ?_ rfl rfl rfl rfl rfl
  intro a b hab hadj
  rw [take_succ_eq hi, List.mem_append, List.mem_singleton] at hab
  rcases hab with h | h
  · exact Or.inl h
  · refine Or.inr ⟨hi, h, ?_⟩
    rw [List.take_length]
    subst h
    exact (hadj_iff b).2 hadj


theorem sum_range_getD (f : ℕ → ℕ) : ∀ l : List ℕ,
    ∑ i ∈ Finset.range l.length, f (l.getD i 0) = (l.map f).sum
  | [] => by simp
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← sum_range_getD f l]
    simp [Nat.add_comm]

/-- The degrees of the vertices of `T` add up to at most the number of adjacency entries. -/
theorem sum_deg_cycle_le (lists : Fin n → List ℕ) {T : List (Fin n)} (hT : T.Nodup) :
    ∑ i ∈ Finset.range T.length, degOf lists ((T.map Fin.val).getD i 0) ≤
      totalAdjEntries lists := by
  have h := sum_range_getD (degOf lists) (T.map Fin.val)
  rw [List.length_map] at h
  rw [h]
  exact sum_degOf_le lists (hT.map Fin.val_injective) (by simp)

/-- **The chord scan.** It ends with `rFound = 0` and no chord between vertices of `T` that are
apart, or with `rFound = 1` and a chord in `PairOK`. It takes at most `7 + 19|T| + 60 M` steps,
where `M` is the number of adjacency entries. -/
theorem chordScan_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (s₀ : State) (hpre : ChordPre H lists T s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w) :
    ∃ s' t, Exec w chordScan s₀ s' t ∧ t ≤ 7 + 19 * T.length + 60 * totalAdjEntries lists ∧
      Keeps chordRegs [] s₀ s' ∧ ChordRes H T (fun x _ => x ∈ T) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  set s₁ := s₀.setReg rFound 0 with hs₁
  have hex₁ : Exec w (.assign rFound (.const 0)) s₀ s₁ (1 + 1) := .assign (by simp [checkWord])
  set s₂ := s₁.setReg rI2 0 with hs₂
  have hex₂ : Exec w (.assign rI2 (.const 0)) s₁ s₂ (1 + 1) := .assign (by simp [checkWord])
  let OI : ℕ → State → Prop := fun i st => Keeps chordRegs [] s₀ st ∧ st.regs rI2 = i ∧
    ChordRes H T (fun x _ => x ∈ T.take i) st
  have hI0 : OI 0 s₂ := ⟨((Keeps.refl _ _ s₀).setReg (by simp [chordRegs]) _).setReg
    (by simp [chordRegs]) _, by simp [s₂], Or.inl ⟨by simp [s₂, s₁], fun a b h => by simp at h⟩⟩
  have hloop := Triple.forUp_sum OI T.length
    (fun i => 12 + 60 * degOf lists ((T.map Fin.val).getD i 0)) (r_i := rI2) (hi := .reg rk)
    (body := chordOuter) (w := w) hw1 (by omega)
    (fun i _ st hst => ⟨hst.2.1, by
      have := (hpre.keeps hst.1).k
      simp [checkWord, this]; omega⟩)
    (fun i hi st hst => by
      obtain ⟨s', t, hex, ht, hk', hri', hres'⟩ :=
        chordOuter_exec H lists T hT hk4 hn s₀ hpre hent i hi st hst.1 hst.2.1 hst.2.2
      refine ⟨s', t, hex, ?_, ⟨hk'.setReg (by simp [chordRegs]) _, by simp,
        hres'.of_regs (fun _ _ h _ => h) (by simp) (by simp) (by simp) (by simp) (by simp)⟩, hri'⟩
      have hd : degOf lists ((T.map Fin.val).getD i 0) = (lists T[i]).length := by
        simp [degOf, List.getD_eq_getElem?_getD, hi]
      show t ≤ 12 + 60 * degOf lists ((T.map Fin.val).getD i 0)
      rw [hd]; exact ht)
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, -, hres₃⟩ := hloop s₂ hI0
  refine ⟨s₃, _, .seq hex₁ (.seq hex₂ hex₃), ?_, hk₃, ?_⟩
  · have hsum := sum_deg_cycle_le lists hT
    simp only [Expr.cost] at ht₃
    have e : ∑ j ∈ Finset.range T.length, (1 + 6 + (12 + 60 * degOf lists
        ((T.map Fin.val).getD j 0))) = 19 * T.length + 60 * ∑ j ∈ Finset.range T.length,
          degOf lists ((T.map Fin.val).getD j 0) := by
      rw [Finset.mul_sum, show 19 * T.length = ∑ _j ∈ Finset.range T.length, 19 by simp [mul_comm],
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e] at ht₃
    omega
  · rw [List.take_length] at hres₃
    exact hres₃

end GraphMinor.Compute.TwoPaths
