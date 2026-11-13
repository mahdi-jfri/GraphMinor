module

public import GraphMinor.Compute.TwoPathsChord

/-!
# The components of `H - C` and their attachments

The second part of line 2 of Algorithm 5.1 (Humeau and Pous, page 22): a `C`-path with inner
vertices runs inside one component `K` of `H - C` and joins two of its *attachments* (the vertices
of `C` with a neighbour in `K`). So a `C`-path between two vertices of `C` that are apart exists
exactly when there is a chord between such vertices (`TwoPathsChord.lean`) or a component with two
attachments that are apart.

The program `sweep` runs the search of `TwoPathsSearch.lean` once more for each vertex `v` that is
not yet reached, with the vertices of `C` forbidden. Each such run reaches exactly the component
of `v` (it is the last part of the queue, the *segment*). Then `segScan` looks at the attachments
of the segment: it keeps the position `F` of the first attachment and the position `S` of a
second one that is next to `F`; any other attachment is apart from `F` or from `S`
(`apart_of_cons`), and gives a pair.

This file has the steps: `pushV_exec` (push a new source and keep the invariant of the search).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

variable {n : ℕ}

/-! ### Registers -/

/-- Outer counter of the sweep. -/
abbrev rV2 : Reg := 95
/-- A vertex of the segment. -/
abbrev rU2 : Reg := 96
/-- Start of the segment. -/
abbrev rSt : Reg := 88
/-- Index into the segment. -/
abbrev rJ : Reg := 89
/-- Position of the first attachment (`0`: none yet). -/
abbrev rFp : Reg := 82
/-- First attachment. -/
abbrev rFx : Reg := 83
/-- Neighbour of the first attachment in the segment. -/
abbrev rFu : Reg := 84
/-- Position of the second attachment (`0`: none yet). -/
abbrev rSp : Reg := 85
/-- Second attachment. -/
abbrev rSx : Reg := 86
/-- Neighbour of the second attachment in the segment. -/
abbrev rSu : Reg := 87

/-! ### Pushing a new source -/

/-- Push the vertex in register `rV2` into the queue when its label is `0`. -/
def pushV : Cmd :=
  .seq (.assign rX (.reg rV2))
    (.seq (.assign rL (.read aLab (.reg rX)))
      (.ite (.op .eq (.reg rL) (.const 0))
        (.seq (.write aLab (.reg rX) (.const 1))
          (.seq (.write aPar (.reg rX) (.reg 40)) (queuePush aQue rTail (.reg rX))))
        .skip))

theorem SInv.rebase {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s₁ s : State}
    {items : List ℕ} {h : ℕ} (hs : SInv G L0 src s₁ items h s) (hf : SFrame s₀ s) :
    SInv G L0 src s₀ items h s :=
  { hs with frame := hf }

/-- **Pushing a source.** From the invariant with an empty queue, `pushV` pushes the vertex `v` of
register `rV2` when it is free and not reached; otherwise it changes nothing that the invariant
sees. -/
theorem pushV_exec {w : ℕ} (G : SimpleGraph (Fin n)) (L0 : Fin n → ℕ) (hL0 : ∀ x, L0 x ≤ 3)
    (src : List ℕ) (s₀ : State) (hrn : s₀.regs 40 = n) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (items : List ℕ) (s : State) (hs : SInv G L0 src s₀ items items.length s) (v : Fin n)
    (hv : s.regs rV2 = v.1) :
    ∃ s' t, Exec w pushV s s' t ∧ t ≤ 22 ∧
      ((v.1 ∉ items ∧ L0 v = 0 ∧ SInv G L0 (src ++ [v.1]) s₀ (items ++ [v.1]) items.length s') ∨
        ((v.1 ∈ items ∨ L0 v ≠ 0) ∧ SInv G L0 src s₀ items items.length s')) := by
  obtain ⟨hfr, hq, hnd, hlt, hfree, hlab, ⟨p, hpar, hpok⟩, hcl, hhit, hsrcs⟩ := hs
  set x := v with hx_def
  have hxw : x.1 < 2 ^ w := lt_trans x.2 hn
  have hrnS : s.regs 40 = n := by rw [hfr.1 40 (Or.inl (by decide)), hrn]
  set s₁ := s.setReg rX x.1 with hs₁
  have hex₁ : Exec w (.assign rX (.reg rV2)) s s₁ (1 + 1) := .assign (by simp [checkWord, hv, hxw])
  set lx : ℕ := if x.1 ∈ items then 1 else L0 x with hlx
  have hlxw : lx < 2 ^ w := by
    simp only [lx]; split_ifs
    · omega
    · have := hL0 x; omega
  have hread₂ : (Expr.read aLab (.reg rX)).eval w s₁ = some lx := by
    simp only [Expr.eval, s₁, State.setReg_regs_self, checkWord, hxw, ↓reduceIte,
      State.setReg_arrs]
    simp [hlab, lx, hlxw, x]
  set s₂ := s₁.setReg rL lx with hs₂
  have hex₂ : Exec w (.assign rL (.read aLab (.reg rX))) s₁ s₂ 3 := .assign hread₂
  have hrl : s₂.regs rL = lx := by simp [s₂]
  have hcond := eval_eq_const s₂ rL 0 (by rw [hrl]; exact hlxw) (by omega) (by omega)
  rw [hrl] at hcond
  have hfr₂ : SFrame s₀ s₂ := (hfr.setReg (by decide) _).setReg (by decide) _
  by_cases hnew : x.1 ∉ items ∧ L0 x = 0
  · have hlx0 : lx = 0 := by simp [lx, hnew.1, hnew.2]
    rw [hlx0] at hcond
    set s₃ := s₂.writeArr aLab x.1 1 with hs₃
    have hex₃ : Exec w (.write aLab (.reg rX) (.const 1)) s₂ s₃ 3 :=
      .write (by simp [Expr.eval, checkWord, s₂, s₁, hxw])
        (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega]) (by simp [s₂, s₁, hlab])
    set s₄ := s₃.writeArr aPar x.1 n with hs₄
    have hex₄ : Exec w (.write aPar (.reg rX) (.reg 40)) s₃ s₄ 3 :=
      .write (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hxw])
        (by simp [Expr.eval, checkWord, s₃, s₂, s₁, hrnS, hn]) (by simp [s₃, s₂, s₁, hpar])
    have hlen : items.length < n := length_lt_of_nodup_lt_not_mem hnd hlt x.2 hnew.1
    have hq₄ : IsQueueHistory aQue rHead rTail n items items.length s₄ :=
      hq.of_eq (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁])
    obtain ⟨s₅, t₅, hex₅, ht₅, hq₅⟩ := Triple.queuePush_spec aQue rHead rTail (.reg rX) n items
      items.length x.1 (by decide) (by omega) hn hlen s₄
      ⟨hq₄, by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hxw]⟩
    simp only [Expr.cost] at ht₅
    have hR : ∀ r, r ≠ rTail → s₅.regs r = s₄.regs r := fun r hr =>
      Exec.regs_eq_of_not_mem_writtenRegs hex₅ (by simp [queuePush, Cmd.writtenRegs, hr])
    have hA : ∀ a, a ≠ aQue → s₅.arrs a = s₄.arrs a := fun a ha =>
      Exec.arrs_eq_of_not_mem_writtenArrs hex₅ (by simp [queuePush, Cmd.writtenArrs, ha])
    have hex : Exec w pushV s s₅ (2 + (3 + (3 + (3 + (3 + t₅))))) :=
      .seq hex₁ (.seq hex₂ (.ite_true (by simpa using hcond) (by omega)
        (.seq hex₃ (.seq hex₄ hex₅))))
    refine ⟨s₅, _, hex, by omega, Or.inl ⟨hnew.1, hnew.2, ?_⟩⟩
    have hmem : ∀ y : ℕ, y ∈ items ++ [x.1] ↔ y ∈ items ∨ y = x.1 := by simp
    have htake : (items ++ [x.1]).take items.length = items := by simp
    refine ⟨?_, hq₅.of_eq rfl (by simp) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun r (hr : r < 60 ∨ 71 ≤ r) => ?_, fun a h1 h2 h3 => ?_⟩
      · have hne : r ≠ 61 := by
          rcases hr with hh | hh
          · exact Nat.ne_of_lt (Nat.lt_trans hh (by decide))
          · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by decide) hh)
        rw [hR r hne]
        exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).1 r hr
      · rw [hA a h3]
        exact ((hfr₂.writeArr (Or.inl rfl) _ _).writeArr (Or.inr (Or.inl rfl)) _ _).2 a h1 h2 h3
    · rw [List.nodup_append]
      exact ⟨hnd, List.nodup_singleton _, fun a ha b hb hab => by
        simp at hb; subst hb; subst hab; exact hnew.1 ha⟩
    · intro y hy
      rcases (hmem y).1 hy with hy | rfl
      · exact hlt y hy
      · exact x.2
    · intro y hy
      rcases (hmem y.1).1 hy with hy | hy
      · exact hfree y hy
      · rw [show y = x from Fin.ext hy]; exact hnew.2
    · rw [hA _ (by decide)]
      simp only [s₄, s₃, State.writeArr_arrs_ne _ _ _ (show (60 : ℕ) ≠ 61 by decide),
        State.writeArr_arrs_self, s₂, s₁, State.setReg_arrs, hlab]
      rw [ofFn_set x]
      congr 1
      funext y
      simp only [Function.update_apply, hmem]
      by_cases hyx : y = x
      · rw [hyx]; simp
      · have : y.1 ≠ x.1 := fun e => hyx (Fin.ext e)
        simp [hyx, this]
    · refine ⟨Function.update p x n, ?_, ?_⟩
      · rw [hA _ (by decide)]
        simp only [s₄, State.writeArr_arrs_self, s₃,
          State.writeArr_arrs_ne _ _ _ (show (61 : ℕ) ≠ 60 by decide), s₂, s₁,
          State.setReg_arrs, hpar]
        exact ofFn_set x _
      · intro y hy
        rcases (hmem y.1).1 hy with hy' | hy'
        · have hyx : y ≠ x := fun e => hnew.1 (e ▸ hy')
          rw [Function.update_of_ne hyx]
          obtain ⟨h0, hrest⟩ := hpok y hy'
          refine ⟨fun hys => h0 (by
            rw [List.mem_append, List.mem_singleton] at hys
            rcases hys with h | h
            · exact h
            · exact absurd (Fin.ext h) hyx), ?_⟩
          rcases hrest with ⟨h1, h2⟩ | ⟨u', h1, h2, h3, h4⟩
          · exact Or.inl ⟨h1, List.mem_append_left _ h2⟩
          · refine Or.inr ⟨u', h1, List.mem_append_left _ h2, ?_, h4⟩
            rw [idxOf_append_mem h2, idxOf_append_mem hy']
            exact h3
        · rw [show y = x from Fin.ext hy', Function.update_self]
          exact ⟨fun _ => rfl, Or.inl ⟨rfl, by simp⟩⟩
    · intro u hu v' hv'
      rw [htake] at hu
      rcases hcl u (by simpa using hu) v' hv' with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_append_left _ h)
    · have h67 : s₅.regs rHit = s.regs rHit := by rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁]
      have h68 : s₅.regs rHitPar = s.regs rHitPar := by
        rw [hR _ (by decide)]; simp [s₄, s₃, s₂, s₁]
      rw [h67, h68]
      refine hhit.mono_items fun v' hv' => ?_
      obtain ⟨u, hu, hadj⟩ := hv'
      rw [htake] at hu
      exact ⟨u, by simpa using hu, hadj⟩
    · intro y hy hy0
      rw [List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | hy
      · exact List.mem_append_left _ (hsrcs y hy hy0)
      · exact (hmem y.1).2 (Or.inr hy)
  · have hlx : lx ≠ 0 := by
      simp only [lx]
      split_ifs with h
      · omega
      · intro h0; exact hnew ⟨h, h0⟩
    have hcond' : (Expr.op .eq (.reg rL) (.const 0)).eval w s₂ = some 0 := by
      rw [hcond]; simp [hlx]
    have hex : Exec w pushV s s₂ (2 + (3 + (3 + 1))) :=
      .seq hex₁ (.seq hex₂ (.ite_false hcond' (.skip _)))
    refine ⟨s₂, _, hex, by omega, Or.inr ⟨?_, ?_⟩⟩
    · by_contra hc
      exact hnew ⟨fun h => hc (Or.inl h), by by_contra h; exact hc (Or.inr h)⟩
    · exact ⟨hfr₂, hq.of_eq rfl (by simp [s₂, s₁]) (by simp [s₂, s₁]), hnd, hlt, hfree,
        by simp [s₂, s₁, hlab], ⟨p, by simp [s₂, s₁, hpar], hpok⟩, hcl,
        by simpa [s₂, s₁] using hhit, hsrcs⟩


/-! ### The attachments of a segment -/

/-- The position of a vertex of `T`. -/
def tpos (T : List (Fin n)) (x : Fin n) : ℕ := T.idxOf x + 1

/-- What the registers `rFp, rFx, rFu, rSp, rSx, rSu` say about the attachments `seen` so far:
none yet, or all at the position `F` of `rFx`, or all at `F` or at the position `S` of `rSx`, with
`S ≠ F` and `S`, `F` not apart. -/
def AttOK (H : SimpleGraph (Fin n)) (T : List (Fin n)) (seg : List ℕ)
    (seen : Fin n → Fin n → Prop) (s : State) : Prop :=
  (s.regs rFp = 0 → s.regs rSp = 0 ∧ ∀ u y, seen u y → H.Adj u y → y ∉ T) ∧
  (s.regs rFp ≠ 0 → ∃ fx fu : Fin n, fx ∈ T ∧ fu.1 ∈ seg ∧ H.Adj fu fx ∧
    s.regs rFp = tpos T fx ∧ s.regs rFx = fx.1 ∧ s.regs rFu = fu.1 ∧
    ((s.regs rSp = 0 ∧ ∀ u y, seen u y → H.Adj u y → y ∈ T → tpos T y = tpos T fx) ∨
     (∃ sx su : Fin n, sx ∈ T ∧ su.1 ∈ seg ∧ H.Adj su sx ∧ s.regs rSp = tpos T sx ∧
        s.regs rSx = sx.1 ∧ s.regs rSu = su.1 ∧ tpos T sx ≠ tpos T fx ∧
        ¬ Apart T.length (tpos T sx) (tpos T fx) ∧
        ∀ u y, seen u y → H.Adj u y → y ∈ T → tpos T y = tpos T fx ∨ tpos T y = tpos T sx)))

/-- The result of the scan of a segment so far. -/
def SegRes (H : SimpleGraph (Fin n)) (T : List (Fin n)) (seg : List ℕ)
    (seen : Fin n → Fin n → Prop) (s : State) : Prop :=
  (s.regs rFound = 0 ∧ AttOK H T seg seen s) ∨ (s.regs rFound = 1 ∧ PairOK H T s)

theorem AttOK.of_regs {H : SimpleGraph (Fin n)} {T : List (Fin n)} {seg : List ℕ}
    {seen seen' : Fin n → Fin n → Prop} {s s' : State} (h : AttOK H T seg seen s)
    (hseen : ∀ a b, seen' a b → H.Adj a b → seen a b)
    (h1 : s'.regs rFp = s.regs rFp) (h2 : s'.regs rFx = s.regs rFx)
    (h3 : s'.regs rFu = s.regs rFu) (h4 : s'.regs rSp = s.regs rSp)
    (h5 : s'.regs rSx = s.regs rSx) (h6 : s'.regs rSu = s.regs rSu) :
    AttOK H T seg seen' s' := by
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun hf => ?_, fun hf => ?_⟩
  · obtain ⟨hs, hno⟩ := hA (by rw [← h1]; exact hf)
    exact ⟨by rw [h4]; exact hs, fun u y hs' hadj => hno u y (hseen u y hs' hadj) hadj⟩
  · obtain ⟨fx, fu, a1, a2, a3, a4, a5, a6, a7⟩ := hB (by rw [← h1]; exact hf)
    refine ⟨fx, fu, a1, a2, a3, by rw [h1]; exact a4, by rw [h2]; exact a5, by rw [h3]; exact a6,
      ?_⟩
    rcases a7 with ⟨b1, b2⟩ | ⟨sx, su, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
    · exact Or.inl ⟨by rw [h4]; exact b1, fun u y hs' hadj => b2 u y (hseen u y hs' hadj) hadj⟩
    · exact Or.inr ⟨sx, su, b1, b2, b3, by rw [h4]; exact b4, by rw [h5]; exact b5,
        by rw [h6]; exact b6, b7, b8, fun u y hs' hadj => b9 u y (hseen u y hs' hadj) hadj⟩

/-- Record a new first attachment. -/
def setF : Cmd :=
  .seq (.assign rFp (.reg rQ)) (.seq (.assign rFx (.reg rY)) (.assign rFu (.reg rU2)))

/-- Record a new second attachment. -/
def setS : Cmd :=
  .seq (.assign rSp (.reg rQ)) (.seq (.assign rSx (.reg rY)) (.assign rSu (.reg rU2)))

/-- Record the pair of the attachment in registers `rx, ru` and the current one. -/
def foundP (rx ru : Reg) : Cmd :=
  .seq (.assign rPx (.reg rx)) (.seq (.assign rPu0 (.reg ru))
    (.seq (.assign rPy (.reg rY)) (.seq (.assign rPu1 (.reg rU2)) (.assign rFound (.const 1)))))

/-- The decision for an attachment at position `rQ`. -/
def attachBody : Cmd :=
  .ite (.op .eq (.reg rFp) (.const 0)) setF
    (.ite (.op .eq (.reg rQ) (.reg rFp)) .skip
      (.ite (apartE (.reg rFp) (.reg rQ)) (foundP rFx rFu)
        (.ite (.op .eq (.reg rSp) (.const 0)) setS
          (.ite (.op .eq (.reg rQ) (.reg rSp)) .skip (foundP rSx rSu)))))

/-- Look at the neighbour `rY` of the segment vertex `rU2`. -/
def attach : Cmd :=
  .seq (.assign rQ (.read aPos (.reg rY)))
    (.ite (.op .mul (.op .lt (.const 0) (.reg rQ)) (.op .eq (.reg rFound) (.const 0)))
      attachBody .skip)

/-- The registers that `attach` writes. -/
def attRegs : List ℕ := [rQ, rFp, rFx, rFu, rSp, rSx, rSu, rPx, rPy, rPu0, rPu1, rFound]

theorem reg_eval {w : ℕ} {s : State} {r : Reg} {v : ℕ} (h : s.regs r = v) (hv : v < 2 ^ w) :
    (Expr.reg r).eval w s = some v := by simp [checkWord, h, hv]

theorem tpos_le {T : List (Fin n)} {x : Fin n} (hx : x ∈ T) : tpos T x ≤ T.length :=
  pos_le hx

theorem tpos_pos {T : List (Fin n)} {x : Fin n} : 1 ≤ tpos T x := by simp [tpos]

theorem tpos_inj {T : List (Fin n)} {x y : Fin n} (hx : x ∈ T) (hy : y ∈ T)
    (h : tpos T x = tpos T y) : x = y := by
  unfold tpos at h
  have h' : T.idxOf x = T.idxOf y := by omega
  rw [← List.idxOf_get (List.idxOf_lt_length_iff.mpr hx),
    ← List.idxOf_get (List.idxOf_lt_length_iff.mpr hy)]
  simp [h']


theorem foundP_exec {w : ℕ} {s : State} {rx ru : Reg} {x u0 u1 y : ℕ} (hx : s.regs rx = x)
    (hu0 : s.regs ru = u0) (hy : s.regs rY = y) (hu1 : s.regs rU2 = u1) (hxw : x < 2 ^ w)
    (hu0w : u0 < 2 ^ w) (hyw : y < 2 ^ w) (hu1w : u1 < 2 ^ w) (hw : 1 < 2 ^ w)
    (hrx : rx ≠ rPx) (hru : ru ≠ rPx ∧ ru ≠ rPu0) :
    Exec w (foundP rx ru) s ((((((s.setReg rPx x).setReg rPu0 u0).setReg rPy y).setReg rPu1
      u1).setReg rFound 1)) 10 := by
  have e1 : (Expr.reg rx).eval w s = some x := reg_eval hx hxw
  have e2 : (Expr.reg ru).eval w (s.setReg rPx x) = some u0 :=
    reg_eval (by rw [State.setReg_regs_ne _ _ hru.1]; exact hu0) hu0w
  have e3 : (Expr.reg rY).eval w ((s.setReg rPx x).setReg rPu0 u0) = some y :=
    reg_eval (by simp [hy]) hyw
  have e4 : (Expr.reg rU2).eval w (((s.setReg rPx x).setReg rPu0 u0).setReg rPy y) = some u1 :=
    reg_eval (by simp [hu1]) hu1w
  have e5 : (Expr.const 1).eval w ((((s.setReg rPx x).setReg rPu0 u0).setReg rPy y).setReg rPu1
      u1) = some 1 := by simp [checkWord, hw]
  exact .seq (.assign e1) (.seq (.assign e2) (.seq (.assign e3) (.seq (.assign e4) (.assign e5))))

/-- **One attachment.** -/
theorem attach_exec {w : ℕ} (H : SimpleGraph (Fin n)) (T : List (Fin n)) (hT : T.Nodup)
    (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w) (seg : List ℕ)
    (hoff : ∀ a : Fin n, a.1 ∈ seg → a ∉ T)
    (hR : ∀ a b : Fin n, a.1 ∈ seg → b.1 ∈ seg → (restrict H {v | v ∉ T}).Reachable a b)
    (seen : Fin n → Fin n → Prop) (s : State) (hpos : s.arrs aPos = posArr T)
    (hk : s.regs rk = T.length) (u y : Fin n) (hu : s.regs rU2 = u.1) (hy : s.regs rY = y.1)
    (huseg : u.1 ∈ seg) (hadj : H.Adj u y) (hres : SegRes H T seg seen s) :
    ∃ s' t, Exec w attach s s' t ∧ t ≤ 80 ∧ (∀ r, r ∉ attRegs → s'.regs r = s.regs r) ∧
      s'.arrs = s.arrs ∧ SegRes H T seg (fun a b => seen a b ∨ (a = u ∧ b = y)) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkn : T.length ≤ n := by have := hT.length_le_card; simpa using this
  have hkw : T.length < 2 ^ w := by omega
  have hyw : y.1 < 2 ^ w := by have := y.2; omega
  have huw : u.1 < 2 ^ w := by have := u.2; omega
  have hnw : n < 2 ^ w := by omega
  obtain ⟨q, hq⟩ : ∃ q, (if y ∈ T then tpos T y else 0) = q := ⟨_, rfl⟩
  have hqk : q ≤ T.length := by
    rw [← hq]; split_ifs with h
    · exact tpos_le h
    · omega
  have hqw : q < 2 ^ w := by omega
  have hq' : (if y ∈ T then T.idxOf y + 1 else 0) = q := hq
  have hread : (Expr.read aPos (.reg rY)).eval w s = some q := by
    simp [Expr.eval, checkWord, hy, hyw, hpos, posArr, hq', hqw]
  set s₁ := s.setReg rQ q with hs₁
  have hex₁ : Exec w (.assign rQ (.read aPos (.reg rY))) s s₁ (1 + 1 + 1) := .assign hread
  have hfv : s.regs rFound ≤ 1 := by rcases hres with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hcond : (Expr.op .mul (.op .lt (.const 0) (.reg rQ)) (.op .eq (.reg rFound)
      (.const 0))).eval w s₁ = some (if 0 < q ∧ s.regs rFound = 0 then 1 else 0) :=
    mul_eval (lt_eval (by simp [checkWord, hw1]) (reg_eval (by simp [s₁]) hqw) hw1)
      (eq_eval (reg_eval (by simp [s₁]) (by omega)) (by simp [checkWord, hw1]) hw1) hw1
  have hcost : (Expr.op .mul (.op .lt (.const 0) (.reg rQ)) (.op .eq (.reg rFound)
      (.const 0))).cost = 7 := rfl
  have hR₁ : ∀ r, r ∉ attRegs → s₁.regs r = s.regs r := fun r hr =>
    State.setReg_regs_ne _ _ (fun e => hr (by rw [e]; simp [attRegs]))
  by_cases hc : 0 < q ∧ s.regs rFound = 0
  swap
  · -- not an attachment, or a pair was found already
    have hex : Exec w attach s s₁ (3 + (7 + 1)) :=
      .seq hex₁ (.ite_false (by rw [hcond]; simp [hc]) (.skip _))
    refine ⟨s₁, _, hex, by omega, hR₁, by simp [s₁], ?_⟩
    rcases hres with ⟨h0, hatt⟩ | ⟨h1, hp⟩
    · have hyT : y ∉ T := by
        intro hyT
        apply hc
        refine ⟨?_, h0⟩
        rw [← hq, if_pos hyT]; exact tpos_pos
      refine Or.inl ⟨by simp [s₁, h0], ?_⟩
      obtain ⟨hA, hB⟩ := hatt
      refine ⟨fun hf => ?_, fun hf => ?_⟩
      · obtain ⟨hs, hno⟩ := hA (by simpa [s₁] using hf)
        refine ⟨by simp [s₁, hs], fun a b hab hab' => ?_⟩
        rcases hab with hab | ⟨rfl, rfl⟩
        · exact hno a b hab hab'
        · exact hyT
      · obtain ⟨fx, fu, a1, a2, a3, a4, a5, a6, a7⟩ := hB (by simpa [s₁] using hf)
        refine ⟨fx, fu, a1, a2, a3, by simp [s₁, a4], by simp [s₁, a5], by simp [s₁, a6], ?_⟩
        rcases a7 with ⟨b1, b2⟩ | ⟨sx, su, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
        · refine Or.inl ⟨by simp [s₁, b1], fun a b hab hab' hb => ?_⟩
          rcases hab with hab | ⟨rfl, rfl⟩
          · exact b2 a b hab hab' hb
          · exact absurd hb hyT
        · refine Or.inr ⟨sx, su, b1, b2, b3, by simp [s₁, b4], by simp [s₁, b5], by simp [s₁, b6],
            b7, b8, fun a b hab hab' hb => ?_⟩
          rcases hab with hab | ⟨rfl, rfl⟩
          · exact b9 a b hab hab' hb
          · exact absurd hb hyT
    · exact Or.inr ⟨by simp [s₁, h1], hp.of_regs (by simp [s₁]) (by simp [s₁]) (by simp [s₁])
        (by simp [s₁])⟩
  -- an attachment, and nothing found yet
  obtain ⟨hq0, hf0⟩ := hc
  have hyT : y ∈ T := by
    by_contra h; rw [← hq, if_neg h] at hq0; omega
  have hqy : q = tpos T y := by rw [← hq, if_pos hyT]
  rcases hres with ⟨-, hatt⟩ | ⟨h1, -⟩
  swap
  · omega
  obtain ⟨hA, hB⟩ := hatt
  have hcond₁ : (Expr.op .mul (.op .lt (.const 0) (.reg rQ)) (.op .eq (.reg rFound)
      (.const 0))).eval w s₁ = some 1 := by rw [hcond]; simp [hq0, hf0]
  have hAttach : ∀ s₂ t₂, Exec w attachBody s₁ s₂ t₂ → t₂ ≤ 70 →
      (∀ r, r ∉ attRegs → s₂.regs r = s₁.regs r) → s₂.arrs = s₁.arrs →
      SegRes H T seg (fun a b => seen a b ∨ (a = u ∧ b = y)) s₂ →
      ∃ s' t, Exec w attach s s' t ∧ t ≤ 80 ∧ (∀ r, r ∉ attRegs → s'.regs r = s.regs r) ∧
        s'.arrs = s.arrs ∧ SegRes H T seg (fun a b => seen a b ∨ (a = u ∧ b = y)) s' :=
    fun s₂ t₂ hex₂ ht₂ hr₂ ha₂ hres₂ =>
      ⟨s₂, _, .seq hex₁ (.ite_true hcond₁ one_ne_zero hex₂), by rw [hcost]; omega,
        fun r hr => by rw [hr₂ r hr, hR₁ r hr], by rw [ha₂]; simp [s₁], hres₂⟩
  have hFv : s₁.regs rFp = s.regs rFp := by simp [s₁]
  have hSv : s₁.regs rSp = s.regs rSp := by simp [s₁]
  have hfpw : s.regs rFp < 2 ^ w := by
    by_cases hF : s.regs rFp = 0
    · omega
    · obtain ⟨fx, -, a1, -, -, a4, -⟩ := hB hF
      have := tpos_le a1; omega
  have hspw : s.regs rSp < 2 ^ w := by
    by_cases hF : s.regs rFp = 0
    · have := (hA hF).1; omega
    · obtain ⟨fx, -, -, -, -, -, -, -, a7⟩ := hB hF
      rcases a7 with ⟨b1, -⟩ | ⟨sx, -, b1, -, -, b4, -⟩
      · omega
      · have := tpos_le b1; omega
  have eF : (Expr.op .eq (.reg rFp) (.const 0)).eval w s₁ =
      some (if s.regs rFp = 0 then 1 else 0) :=
    eq_eval (reg_eval hFv hfpw) (by simp [checkWord, hw1]) hw1
  have hQ : s₁.regs rQ = q := by simp [s₁]
  by_cases hF : s.regs rFp = 0
  · -- the first attachment
    obtain ⟨hS0, hno⟩ := hA hF
    set s₂ := ((s₁.setReg rFp q).setReg rFx y.1).setReg rFu u.1 with hs₂
    have hex₂ : Exec w setF s₁ s₂ 6 :=
      .seq (.assign (reg_eval hQ hqw)) (.seq (.assign (reg_eval (by simp [s₁, hy]) hyw))
        (.assign (reg_eval (by simp [s₁, hu]) huw)))
    refine hAttach s₂ _ (.ite_true (by rw [eF, if_pos hF]) one_ne_zero hex₂) (by
      simp only [Expr.cost]; omega) (fun r hr => ?_) (by simp [s₂]) (Or.inl ⟨by simp [s₂, s₁, hf0],
        fun h => absurd h (by simp [s₂]; omega), fun _ => ⟨y, u, hyT, huseg, hadj,
          by simp [s₂, hqy], by simp [s₂], by simp [s₂], Or.inl ⟨by simp [s₂, s₁, hS0],
            fun a b hab hab' hb => ?_⟩⟩⟩)
    · have : r ≠ rFp ∧ r ≠ rFx ∧ r ≠ rFu := by
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [attRegs] at hr
      simp [s₂, this.1, this.2.1, this.2.2]
    · rcases hab with hab | ⟨rfl, rfl⟩
      · exact absurd hb (hno a b hab hab')
      · rfl
  obtain ⟨fx, fu, a1, a2, a3, a4, a5, a6, a7⟩ := hB hF
  have eQF : (Expr.op .eq (.reg rQ) (.reg rFp)).eval w s₁ =
      some (if q = s.regs rFp then 1 else 0) :=
    eq_eval (reg_eval hQ hqw) (reg_eval hFv hfpw) hw1
  have hF' : (Expr.op .eq (.reg rFp) (.const 0)).eval w s₁ = some 0 := by rw [eF, if_neg hF]
  by_cases hQF : q = s.regs rFp
  · -- the same position as the first attachment
    refine hAttach s₁ _ (.ite_false hF' (.ite_true (by rw [eQF, if_pos hQF]) one_ne_zero
      (.skip _))) (by simp only [Expr.cost]; omega) (fun _ _ => rfl) rfl (Or.inl ⟨by
        simp [s₁, hf0], fun h => absurd (by simpa [s₁] using h) hF, fun _ => ⟨fx, fu, a1, a2, a3,
          by simp [s₁, a4], by simp [s₁, a5], by simp [s₁, a6], ?_⟩⟩)
    rcases a7 with ⟨b1, b2⟩ | ⟨sx, su, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
    · refine Or.inl ⟨by simp [s₁, b1], fun a b hab hab' hb => ?_⟩
      rcases hab with hab | ⟨rfl, rfl⟩
      · exact b2 a b hab hab' hb
      · rw [← hqy, hQF, a4]
    · refine Or.inr ⟨sx, su, b1, b2, b3, by simp [s₁, b4], by simp [s₁, b5], by simp [s₁, b6],
        b7, b8, fun a b hab hab' hb => ?_⟩
      rcases hab with hab | ⟨rfl, rfl⟩
      · exact b9 a b hab hab' hb
      · left; rw [← hqy, hQF, a4]
  have eQF' : (Expr.op .eq (.reg rQ) (.reg rFp)).eval w s₁ = some 0 := by rw [eQF, if_neg hQF]
  have eAp : (apartE (.reg rFp) (.reg rQ)).eval w s₁ =
      some (if Apart T.length q (s.regs rFp) then 1 else 0) :=
    apartE_eval (reg_eval hFv hfpw) (reg_eval hQ hqw) (by simp [s₁, hk]) (by omega) (by omega) hw1
  have hfxw : fx.1 < 2 ^ w := by have := fx.2; omega
  have hfuw : fu.1 < 2 ^ w := by have := fu.2; omega
  have hcostAp : (apartE (.reg rFp) (.reg rQ)).cost = 21 := rfl
  by_cases hAp : Apart T.length q (s.regs rFp)
  · -- apart from the first attachment: a pair
    have hex₂ := foundP_exec (w := w) (s := s₁) (rx := rFx) (ru := rFu) (y := y.1)
      (by simp [s₁, a5]) (by simp [s₁, a6]) (by simp [s₁, hy]) (by simp [s₁, hu]) hfxw hfuw hyw huw
      hw1 (by decide) ⟨by decide, by decide⟩
    refine hAttach _ _ (.ite_false hF' (.ite_false eQF' (.ite_true (by rw [eAp, if_pos hAp])
      one_ne_zero hex₂))) (by simp only [Expr.cost] at hcostAp ⊢; omega) (fun r hr => ?_)
      (by simp) (Or.inr ⟨by simp, fx, y, a1, hyT, by simp, by simp, ?_, Or.inr ⟨fu, u, by simp,
        by simp, hoff fu a2, hoff u huseg, a3.symm, hadj, hR fu u a2 huseg⟩⟩)
    · have : r ≠ rPx ∧ r ≠ rPu0 ∧ r ≠ rPy ∧ r ≠ rPu1 ∧ r ≠ rFound := by
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp [attRegs] at hr
      simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]
    · change Apart T.length (tpos T y) (tpos T fx)
      rw [← hqy, ← a4]; exact hAp
  have eAp' : (apartE (.reg rFp) (.reg rQ)).eval w s₁ = some 0 := by rw [eAp, if_neg hAp]
  have eS : (Expr.op .eq (.reg rSp) (.const 0)).eval w s₁ =
      some (if s.regs rSp = 0 then 1 else 0) :=
    eq_eval (reg_eval hSv hspw) (by simp [checkWord, hw1]) hw1
  rcases a7 with ⟨b1, b2⟩ | ⟨sx, su, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩
  · -- the second attachment
    set s₂ := ((s₁.setReg rSp q).setReg rSx y.1).setReg rSu u.1 with hs₂
    have hex₂ : Exec w setS s₁ s₂ 6 :=
      .seq (.assign (reg_eval hQ hqw)) (.seq (.assign (reg_eval (by simp [s₁, hy]) hyw))
        (.assign (reg_eval (by simp [s₁, hu]) huw)))
    refine hAttach s₂ _ (.ite_false hF' (.ite_false eQF' (.ite_false eAp'
      (.ite_true (by rw [eS, if_pos b1]) one_ne_zero hex₂)))) (by
      simp only [Expr.cost] at hcostAp ⊢; omega) (fun r hr => ?_) (by simp [s₂])
      (Or.inl ⟨by simp [s₂, s₁, hf0], fun h => absurd (by simpa [s₂, s₁] using h) hF,
        fun _ => ⟨fx, fu, a1, a2, a3, by simp [s₂, s₁, a4], by simp [s₂, s₁, a5],
          by simp [s₂, s₁, a6], Or.inr ⟨y, u, hyT, huseg, hadj, by simp [s₂, hqy],
            by simp [s₂], by simp [s₂], by rw [← hqy, ← a4]; exact hQF,
            by rw [← hqy, ← a4]; exact hAp, fun a b hab hab' hb => ?_⟩⟩⟩)
    · have : r ≠ rSp ∧ r ≠ rSx ∧ r ≠ rSu := by
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp [attRegs] at hr
      simp [s₂, this.1, this.2.1, this.2.2]
    · rcases hab with hab | ⟨rfl, rfl⟩
      · exact Or.inl (b2 a b hab hab' hb)
      · exact Or.inr rfl
  have hS0 : s.regs rSp ≠ 0 := by rw [b4]; have := tpos_pos (T := T) (x := sx); omega
  have eS' : (Expr.op .eq (.reg rSp) (.const 0)).eval w s₁ = some 0 := by rw [eS, if_neg hS0]
  have eQS : (Expr.op .eq (.reg rQ) (.reg rSp)).eval w s₁ =
      some (if q = s.regs rSp then 1 else 0) :=
    eq_eval (reg_eval hQ hqw) (reg_eval hSv hspw) hw1
  by_cases hQS : q = s.regs rSp
  · -- the same position as the second attachment
    refine hAttach s₁ _ (.ite_false hF' (.ite_false eQF' (.ite_false eAp' (.ite_false eS'
      (.ite_true (by rw [eQS, if_pos hQS]) one_ne_zero (.skip _)))))) (by
      simp only [Expr.cost] at hcostAp ⊢; omega) (fun _ _ => rfl) rfl
      (Or.inl ⟨by simp [s₁, hf0], fun h => absurd (by simpa [s₁] using h) hF,
        fun _ => ⟨fx, fu, a1, a2, a3, by simp [s₁, a4], by simp [s₁, a5], by simp [s₁, a6],
          Or.inr ⟨sx, su, b1, b2, b3, by simp [s₁, b4], by simp [s₁, b5], by simp [s₁, b6], b7, b8,
            fun a b hab hab' hb => ?_⟩⟩⟩)
    rcases hab with hab | ⟨rfl, rfl⟩
    · exact b9 a b hab hab' hb
    · right; rw [← hqy, hQS, b4]
  -- a third position: apart from the second attachment
  have eQS' : (Expr.op .eq (.reg rQ) (.reg rSp)).eval w s₁ = some 0 := by rw [eQS, if_neg hQS]
  have hsxw : sx.1 < 2 ^ w := by have := sx.2; omega
  have hsuw : su.1 < 2 ^ w := by have := su.2; omega
  have hex₂ := foundP_exec (w := w) (s := s₁) (rx := rSx) (ru := rSu) (y := y.1)
    (by simp [s₁, b5]) (by simp [s₁, b6]) (by simp [s₁, hy]) (by simp [s₁, hu]) hsxw hsuw hyw huw
    hw1 (by decide) ⟨by decide, by decide⟩
  have hp : 1 ≤ tpos T fx ∧ tpos T fx ≤ T.length := ⟨tpos_pos, tpos_le a1⟩
  have hps : 1 ≤ tpos T sx ∧ tpos T sx ≤ T.length := ⟨tpos_pos, tpos_le b1⟩
  have hpy : 1 ≤ tpos T y ∧ tpos T y ≤ T.length := ⟨tpos_pos, tpos_le hyT⟩
  have hap : Apart T.length (tpos T y) (tpos T sx) := by
    rw [apart_symm hpy hps]
    refine apart_of_cons hk4 hp hps hpy b7 (by rw [← hqy, ← a4]; exact hQF)
      (by rw [← hqy, ← b4]; exact Ne.symm hQS) ?_ ?_
    · rw [apart_symm hp hps]; exact b8
    · rw [apart_symm hp hpy, ← hqy, ← a4]; exact hAp
  refine hAttach _ _ (.ite_false hF' (.ite_false eQF' (.ite_false eAp' (.ite_false eS'
    (.ite_false eQS' hex₂))))) (by simp only [Expr.cost] at hcostAp ⊢; omega) (fun r hr => ?_)
    (by simp) (Or.inr ⟨by simp, sx, y, b1, hyT, by simp, by simp, (hap : _), Or.inr ⟨su, u, by simp,
      by simp, hoff su b2, hoff u huseg, b3.symm, hadj, hR su u b2 huseg⟩⟩)
  have : r ≠ rPx ∧ r ≠ rPu0 ∧ r ≠ rPy ∧ r ≠ rPu1 ∧ r ≠ rFound := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> simp [attRegs] at hr
  simp [this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2]


/-! ### The scan of a segment -/

/-- Look at all neighbours of the segment vertex at index `rJ` of the queue. -/
def segOuter : Cmd :=
  .seq (.assign rU2 (.read aQue (.reg rJ)))
    (forList aStart aEnd aEnt rU2 rK2 rHi2 rY attach)

/-- Look at all attachments of the segment from index `rSt` to the end of the queue. -/
def segScan : Cmd :=
  .seq (.assign rFp (.const 0)) (.seq (.assign rSp (.const 0))
    (.seq (.assign rJ (.reg rSt)) (forUp rJ (.reg rTail) segOuter)))

/-- The registers that `segScan` writes. -/
def segRegs : List ℕ :=
  [rQ, rFp, rFx, rFu, rSp, rSx, rSu, rPx, rPy, rPu0, rPu1, rFound, rJ, rU2, rK2, rHi2, rY]

theorem SegRes.of_regs {H : SimpleGraph (Fin n)} {T : List (Fin n)} {seg : List ℕ}
    {seen seen' : Fin n → Fin n → Prop} {s s' : State} (h : SegRes H T seg seen s)
    (hseen : ∀ a b, seen' a b → H.Adj a b → seen a b)
    (hr : ∀ r ∈ attRegs, s'.regs r = s.regs r) : SegRes H T seg seen' s' := by
  rcases h with ⟨h0, ha⟩ | ⟨h1, hp⟩
  · exact Or.inl ⟨by rw [hr _ (by simp [attRegs]), h0], ha.of_regs hseen (hr _ (by simp [attRegs]))
      (hr _ (by simp [attRegs])) (hr _ (by simp [attRegs])) (hr _ (by simp [attRegs]))
      (hr _ (by simp [attRegs])) (hr _ (by simp [attRegs]))⟩
  · exact Or.inr ⟨by rw [hr _ (by simp [attRegs]), h1], hp.of_regs (hr _ (by simp [attRegs]))
      (hr _ (by simp [attRegs])) (hr _ (by simp [attRegs])) (hr _ (by simp [attRegs]))⟩

theorem attRegs_sub : ∀ r ∈ attRegs, r ∈ segRegs := by decide

/-- What the scan of a segment needs of the state it starts from. -/
structure SegPre (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ) (T : List (Fin n))
    (items : List ℕ) (st : ℕ) (s : State) : Prop where
  adj : IsAdjList H aStart aEnd aEnt lists s
  pos : s.arrs aPos = posArr T
  k : s.regs rk = T.length
  que : ∀ m (hm : m < items.length), ∃ hm' : m < (s.arrs aQue).length, (s.arrs aQue)[m] = items[m]
  tail : s.regs rTail = items.length
  lt : ∀ x ∈ items, x < n
  st : st ≤ items.length
  nodup : items.Nodup

theorem SegPre.keeps {H : SimpleGraph (Fin n)} {lists : Fin n → List ℕ} {T : List (Fin n)}
    {items : List ℕ} {st : ℕ} {s₀ s : State} (h : SegPre H lists T items st s₀)
    (hk : Keeps segRegs [] s₀ s) : SegPre H lists T items st s := by
  refine ⟨h.adj.of_arrs_eq (hk.2 _ (by simp)) (hk.2 _ (by simp)) (hk.2 _ (by simp)), ?_, ?_,
    ?_, ?_, h.lt, h.st, h.nodup⟩
  · rw [hk.2 _ (by simp)]; exact h.pos
  · rw [hk.1 _ (by simp [segRegs])]; exact h.k
  · rw [hk.2 _ (by simp)]; exact h.que
  · rw [hk.1 _ (by simp [segRegs])]; exact h.tail

/-- The vertices whose attachments were looked at, before index `j` of the queue. -/
def segSeen (items : List ℕ) (st j : ℕ) (a _b : Fin n) : Prop := a.1 ∈ (items.take j).drop st

/-- **One segment vertex.** -/
theorem segOuter_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (items : List ℕ) (st : ℕ) (hoff : ∀ a : Fin n, a.1 ∈ items.drop st → a ∉ T)
    (hR : ∀ a b : Fin n, a.1 ∈ items.drop st → b.1 ∈ items.drop st →
      (restrict H {v | v ∉ T}).Reachable a b)
    (s₀ : State) (hpre : SegPre H lists T items st s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (j : ℕ) (hj : st ≤ j) (hjl : j < items.length) (s : State) (hk : Keeps segRegs [] s₀ s)
    (hrj : s.regs rJ = j) (hres : SegRes H T (items.drop st) (segSeen items st j) s) :
    ∃ s' t, Exec w segOuter s s' t ∧ t ≤ 12 + 90 * degOf lists (items.getD j 0) ∧
      Keeps segRegs [] s₀ s' ∧ s'.regs rJ = j ∧
      SegRes H T (items.drop st) (segSeen items st (j + 1)) s' := by
  have hpre' := hpre.keeps hk
  have hw1 : 1 < 2 ^ w := by omega
  have hun : items[j] < n := hpre.lt _ (List.getElem_mem hjl)
  set u : Fin n := ⟨items[j], hun⟩ with hu_def
  have huw : u.1 < 2 ^ w := by have := u.2; omega
  have hlen : items.length ≤ n := length_le_of_nodup_lt hpre.nodup hpre.lt
  have hjw : j < 2 ^ w := by omega
  obtain ⟨hm', hqm⟩ := hpre'.que j hjl
  have hread : (Expr.read aQue (.reg rJ)).eval w s = some u.1 := by
    simp [Expr.eval, checkWord, hrj, hm', hqm, u, huw, hjw]
  set s₁ := s.setReg rU2 u.1 with hs₁
  have hex₁ : Exec w (.assign rU2 (.read aQue (.reg rJ))) s s₁ (1 + 1 + 1) := .assign hread
  have hk₁ : Keeps segRegs [] s₀ s₁ := hk.setReg (by simp [segRegs]) _
  have huseg : u.1 ∈ items.drop st := by
    rw [List.mem_drop_iff_getElem]
    exact ⟨j - st, by omega, by simp [u, Nat.add_sub_cancel' hj]⟩
  obtain ⟨stl, en, hlist₀⟩ := hpre.adj.1.2.2 u
  obtain ⟨hmem_lt, -, -, hadj_iff⟩ := hpre.adj.2 u
  have hlistOf : ∀ st' : State, Keeps segRegs [] s₀ st' →
      IsListAt aStart aEnd aEnt u.1 stl en (lists u) st' := fun st' hk' =>
    hlist₀.of_arrs_eq (hk'.2 _ (by simp)) (hk'.2 _ (by simp)) (hk'.2 _ (by simp))
  have hen_w : en < 2 ^ w := by
    obtain ⟨_, _, hle, _⟩ := hlist₀
    omega
  let seenIn : ℕ → Fin n → Fin n → Prop := fun jj a b =>
    segSeen items st j a b ∨ (a = u ∧ b.1 ∈ (lists u).take jj)
  let II : ℕ → State → Prop := fun jj st' => Keeps segRegs [] s₀ st' ∧ st'.regs rJ = j ∧
    st'.regs rU2 = u.1 ∧ SegRes H T (items.drop st) (seenIn jj) st'
  have hI0 : II 0 s₁ := by
    refine ⟨hk₁, by simp [s₁, hrj], by simp [s₁], hres.of_regs ?_ (fun r hr => ?_)⟩
    · rintro a b (h | ⟨-, h⟩) -
      · exact h
      · simp at h
    · have : r ≠ rU2 := by rintro rfl; simp [attRegs] at hr
      simp [s₁, this]
  have hinit : ∀ st', II 0 st' → IsListAt aStart aEnd aEnt u.1 stl en (lists u) st' ∧
      st'.regs rU2 = u.1 ∧ II 0 ((st'.setReg rK2 stl).setReg rHi2 en) := by
    intro st' hst'
    obtain ⟨hk', hrj', hru', hres'⟩ := hst'
    refine ⟨hlistOf st' hk', hru', (hk'.setReg (by simp [segRegs]) stl).setReg
      (by simp [segRegs]) en, by simp [hrj'], by simp [hru'], ?_⟩
    refine hres'.of_regs (fun _ _ h _ => h) (fun r hr => ?_)
    have h1 : r ≠ rK2 := by rintro rfl; simp [attRegs] at hr
    have h2 : r ≠ rHi2 := by rintro rfl; simp [attRegs] at hr
    simp [h1, h2]
  have hfor := Triple.forList_const aStart aEnd aEnt rU2 rK2 rHi2 rY u.1 stl en (lists u) II 80
    attach (by decide) (by decide) hw1 huw hen_w
    (fun z hz => by have := hmem_lt z hz; omega) hinit
    (fun jj _ st' hst' => hlistOf st' hst'.1)
    (fun jj hjj sv ⟨st', hI, hsv, hrk, hrhi⟩ => by
      subst hsv
      obtain ⟨hk', hrj', hru', hres'⟩ := hI
      have hyn : (lists u)[jj] < n := hmem_lt _ (List.getElem_mem hjj)
      set y : Fin n := ⟨(lists u)[jj], hyn⟩ with hy_def
      have hy : H.Adj u y := (hadj_iff _).1 (List.getElem_mem hjj)
      have hpre'' := hpre.keeps (hk'.setReg (r := rY) (by simp [segRegs]) (lists u)[jj])
      obtain ⟨s', t, hex, ht, hregs, harrs, hres''⟩ :=
        attach_exec H T hT hk4 hn (items.drop st) hoff hR (seenIn jj)
          (st'.setReg rY (lists u)[jj]) hpre''.pos hpre''.k u y (by simp [hru']) (by simp [y])
          huseg hy (hres'.of_regs (fun _ _ h _ => h) (fun r hr => by
            have : r ≠ rY := by rintro rfl; simp [attRegs] at hr
            simp [this]))
      have hk'' : Keeps segRegs [] s₀ s' := by
        refine ⟨fun r hr => ?_, fun a _ => ?_⟩
        · have hr' : r ∉ attRegs := fun h => hr (attRegs_sub r h)
          rw [hregs r hr']
          have : r ≠ rY := by rintro rfl; simp [segRegs] at hr
          simp only [State.setReg_regs_ne _ _ this]
          exact hk'.1 r hr
        · rw [harrs]; simp only [State.setReg_arrs]; exact hk'.2 a (by simp)
      have hnot : ∀ r, r = rJ ∨ r = rU2 ∨ r = rK2 ∨ r = rHi2 → r ∉ attRegs := by
        rintro r (rfl | rfl | rfl | rfl) <;> simp [attRegs]
      refine ⟨s', t, hex, ht, ⟨hk''.setReg (by simp [segRegs]) _, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [State.setReg_regs_ne _ _ (show rJ ≠ rK2 by decide)]
        rw [hregs _ (hnot _ (Or.inl rfl))]; simp [hrj']
      · simp only [State.setReg_regs_ne _ _ (show rU2 ≠ rK2 by decide)]
        rw [hregs _ (hnot _ (Or.inr (Or.inl rfl)))]; simp [hru']
      · refine hres''.of_regs ?_ (fun r hr => ?_)
        · rintro a b (h | ⟨ha, hb⟩) -
          · exact Or.inl (Or.inl h)
          · rw [List.take_add_one, List.mem_append] at hb
            rcases hb with hb | hb
            · exact Or.inl (Or.inr ⟨ha, hb⟩)
            · right
              refine ⟨ha, Fin.ext ?_⟩
              have he : (lists u)[jj]? = some (lists u)[jj] := List.getElem?_eq_getElem hjj
              rw [he] at hb
              simpa using hb
        · have : r ≠ rK2 := by rintro rfl; simp [attRegs] at hr
          simp [this]
      · rw [hregs _ (hnot _ (Or.inr (Or.inr (Or.inl rfl))))]; simpa using hrk
      · rw [hregs _ (hnot _ (Or.inr (Or.inr (Or.inr rfl))))]; simpa using hrhi)
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hrj₂, -, hres₂⟩ := hfor s₁ hI0
  have hdeg : degOf lists (items.getD j 0) = (lists u).length := by
    simp [degOf, List.getD_eq_getElem?_getD, hjl, hun, u]
  refine ⟨s₂, _, .seq hex₁ hex₂, by rw [hdeg]; dsimp only at ht₂; omega, hk₂, hrj₂, ?_⟩
  refine hres₂.of_regs ?_ (fun _ _ => rfl)
  intro a b hab hadj
  unfold segSeen at hab
  rw [take_succ_eq hjl, List.drop_append_of_le_length (by simp; omega), List.mem_append,
    List.mem_singleton] at hab
  rcases hab with h | h
  · exact Or.inl h
  · have ha : a = u := Fin.ext h
    subst ha
    exact Or.inr ⟨rfl, by rw [List.take_length]; exact (hadj_iff b).2 hadj⟩


theorem popDeg_add (lists : Fin n → List ℕ) (items : List ℕ) (a : ℕ) :
    ∀ d, a + d ≤ items.length → popDeg lists items (a + d) =
      popDeg lists items a + ∑ j ∈ Finset.range d, degOf lists (items.getD (a + j) 0)
  | 0, _ => by simp
  | d + 1, h => by
    have ih := popDeg_add lists items a d (by omega)
    have hstep : popDeg lists items (a + (d + 1)) = popDeg lists items (a + d) +
        degOf lists (items.getD (a + d) 0) := by
      rw [← Nat.add_assoc, popDeg, popDeg, take_succ_eq (by omega), List.map_append,
        List.sum_append]
      simp [List.getD_eq_getElem?_getD, show a + d < items.length by omega]
    rw [hstep, ih, Finset.sum_range_succ]
    ring

/-- **The scan of a segment.** From `rFound = 0`, the scan looks at all attachments of the
segment `items.drop st`, in at most `9 + 19|seg| + 90 (sum of degrees in seg)` steps. -/
theorem segScan_exec {w : ℕ} (H : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (T : List (Fin n)) (hT : T.Nodup) (hk4 : 4 ≤ T.length) (hn : 4 * n + 4 < 2 ^ w)
    (items : List ℕ) (st : ℕ) (hoff : ∀ a : Fin n, a.1 ∈ items.drop st → a ∉ T)
    (hR : ∀ a b : Fin n, a.1 ∈ items.drop st → b.1 ∈ items.drop st →
      (restrict H {v | v ∉ T}).Reachable a b)
    (s₀ : State) (hpre : SegPre H lists T items st s₀) (hent : (s₀.arrs aEnt).length < 2 ^ w)
    (hst : s₀.regs rSt = st) (hf0 : s₀.regs rFound = 0) :
    ∃ s' t, Exec w segScan s₀ s' t ∧
      t ≤ 9 + 19 * (items.length - st) +
        90 * (popDeg lists items items.length - popDeg lists items st) ∧
      Keeps segRegs [] s₀ s' ∧ SegRes H T (items.drop st) (fun a _ => a.1 ∈ items.drop st) s' := by
  have hw1 : 1 < 2 ^ w := by omega
  have hlen : items.length ≤ n := length_le_of_nodup_lt hpre.nodup hpre.lt
  have hlw : items.length < 2 ^ w := by omega
  have hstl := hpre.st
  set s₁ := s₀.setReg rFp 0 with hs₁
  set s₂ := s₁.setReg rSp 0 with hs₂
  set s₃ := s₂.setReg rJ st with hs₃
  have hex : Exec w (.seq (.assign rFp (.const 0)) (.seq (.assign rSp (.const 0))
      (.assign rJ (.reg rSt)))) s₀ s₃ (2 + (2 + 2)) :=
    .seq (.assign (by simp [checkWord])) (.seq (.assign (by simp [checkWord]))
      (.assign (reg_eval (by simp [s₂, s₁, hst]) (by omega))))
  have hk₃ : Keeps segRegs [] s₀ s₃ :=
    (((Keeps.refl _ _ s₀).setReg (by simp [segRegs]) _).setReg (by simp [segRegs]) _).setReg
      (by simp [segRegs]) _
  let SO : ℕ → State → Prop := fun j st' => st ≤ j ∧ Keeps segRegs [] s₀ st' ∧ st'.regs rJ = j ∧
    SegRes H T (items.drop st) (segSeen items st j) st'
  have hI0 : SO st s₃ := by
    refine ⟨le_rfl, hk₃, by simp [s₃], Or.inl ⟨by simp [s₃, s₂, s₁, hf0], fun _ =>
      ⟨by simp [s₃, s₂], fun a b hab => ?_⟩, fun h => absurd (by simp [s₃, s₂, s₁]) h⟩⟩
    simp [segSeen] at hab
  have hloop := Triple.forUp_sum_from SO items.length
    (fun j => 12 + 90 * degOf lists (items.getD j 0)) (r_i := rJ) (hi := .reg rTail)
    (body := segOuter) (w := w) hw1 hlw
    (fun i _ st' hst' => ⟨hst'.2.2.1, reg_eval (by
      rw [(hpre.keeps hst'.2.1).tail]) hlw⟩)
    (fun i hi st' hst' => by
      obtain ⟨hsi, hk', hrj', hres'⟩ := hst'
      obtain ⟨s', t, hex', ht', hk'', hrj'', hres''⟩ :=
        segOuter_exec H lists T hT hk4 hn items st hoff hR s₀ hpre hent i hsi hi st' hk' hrj' hres'
      refine ⟨s', t, hex', ht', ⟨by omega, hk''.setReg (by simp [segRegs]) _, by simp,
        hres''.of_regs (fun _ _ h _ => h) (fun r hr => ?_)⟩, hrj''⟩
      have : r ≠ rJ := by rintro rfl; simp [attRegs] at hr
      simp [this])
    st hstl
  obtain ⟨s₄, t₄, hex₄, ht₄, -, hk₄, -, hres₄⟩ := hloop s₃ hI0
  refine ⟨s₄, _, .seq (.assign (by simp [checkWord])) (.seq (.assign (by simp [checkWord]))
    (.seq (.assign (reg_eval (by simp [s₂, s₁, hst]) (by omega))) hex₄)), ?_, hk₄, ?_⟩
  · have hpd := popDeg_add lists items st (items.length - st) (by omega)
    rw [Nat.add_sub_cancel' hstl] at hpd
    simp only [Expr.cost] at ht₄
    have e : ∑ j ∈ Finset.range (items.length - st), (1 + 6 + (12 + 90 * degOf lists
        (items.getD (st + j) 0))) = 19 * (items.length - st) + 90 * ∑ j ∈ Finset.range
          (items.length - st), degOf lists (items.getD (st + j) 0) := by
      rw [Finset.mul_sum, show 19 * (items.length - st) = ∑ _j ∈ Finset.range
        (items.length - st), 19 by simp [mul_comm], ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e] at ht₄
    simp only [Expr.cost]
    omega
  · refine hres₄.of_regs (fun a b hab _ => ?_) (fun _ _ => rfl)
    simpa [segSeen] using hab

end GraphMinor.Compute.TwoPaths
