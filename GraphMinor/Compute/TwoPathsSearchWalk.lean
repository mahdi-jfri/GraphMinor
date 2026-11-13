module

public import GraphMinor.Compute.TwoPathsSearch

/-!
# Walks from the search of `TwoPathsSearch.lean`, and a program that writes them out

The search of `TwoPathsSearch.lean` gives every reached vertex a parent: a source has parent `n`,
and any other reached vertex has as parent a neighbour that was reached before it (`ParentOK`).
Following the parents from a reached vertex `x` gives a path from a source to `x` whose vertices
were all reached (`exists_walk_of_parentOK`). The program `traceProg` follows the parents twice:
once to count the vertices of this path, and once to write them, from the source to `x`, into an
array of exactly that length (`traceProg_exec`).

The other direction is `SInv.mem_of_walk`: once the queue is empty, every vertex that a free
source reaches through free vertices was reached by the search.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph

variable {n : ℕ}

/-! ### The parent chain -/

/-- `ChainFrom p y l`: following the parents `p` from `y` visits the vertices `l` (starting with `y`)
and then reaches the value `n`. -/
inductive ChainFrom (p : Fin n → ℕ) : ℕ → List ℕ → Prop
  | stop : ChainFrom p n []
  | step {y : ℕ} (hy : y < n) {l : List ℕ} : ChainFrom p (p ⟨y, hy⟩) l → ChainFrom p y (y :: l)

/-- **The path of the parents.** Under `ParentOK`, following the parents from a reached vertex `x`
gives the reverse of a path from a source to `x` whose vertices were all reached. -/
theorem exists_walk_of_parentOK {G : SimpleGraph (Fin n)} {src items : List ℕ} {p : Fin n → ℕ}
    (hp : ParentOK G src items p) :
    ∀ (k : ℕ) (x : Fin n), x.1 ∈ items → items.idxOf x.1 < k →
      ∃ (r : Fin n) (W : G.Walk r x), W.IsPath ∧ r.1 ∈ src ∧
        (∀ y ∈ W.support, y.1 ∈ items ∧ items.idxOf y.1 ≤ items.idxOf x.1) ∧
        (∀ y ∈ W.support, y ≠ r → y.1 ∉ src) ∧
        ChainFrom p x.1 (W.support.reverse.map Fin.val) := by
  intro k
  induction k with
  | zero => intro x _ h; omega
  | succ k ih =>
    intro x hx hk
    obtain ⟨hroot, hrest⟩ := hp x hx
    rcases hrest with ⟨hpx, hsrc⟩ | ⟨u, hpu, hu, hidx, hadj⟩
    · refine ⟨x, .nil, .nil, hsrc, fun y hy => ?_, fun y hy hne => ?_, ?_⟩
      · simp only [Walk.support_nil, List.mem_singleton] at hy
        subst hy; exact ⟨hx, le_rfl⟩
      · simp only [Walk.support_nil, List.mem_singleton] at hy
        exact absurd hy hne
      · simp only [Walk.support_nil, List.reverse_singleton, List.map_cons, List.map_nil]
        exact .step x.2 (by rw [show (⟨x.1, x.2⟩ : Fin n) = x from rfl, hpx]; exact .stop)
    · obtain ⟨r, W, hW, hr, hsupp, hns, hch⟩ := ih u hu (by omega)
      have hxW : x ∉ W.support := fun h => by
        have := (hsupp x h).2
        omega
      refine ⟨r, W.concat hadj, hW.concat hxW hadj, hr, fun y hy => ?_, fun y hy hne => ?_, ?_⟩
      · rw [Walk.support_concat, List.mem_append,
          List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact ⟨(hsupp y hy).1, by have := (hsupp y hy).2; omega⟩
        · exact ⟨hx, le_rfl⟩
      · rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · exact hns y hy hne
        · intro hys
          have := hroot hys
          rw [hpu] at this
          exact absurd this (Nat.ne_of_lt u.2)
      · rw [Walk.support_concat, List.reverse_append,
          List.reverse_singleton, List.singleton_append, List.map_cons]
        exact .step x.2 (by rw [show (⟨x.1, x.2⟩ : Fin n) = x from rfl, hpu]; exact hch)

/-- Every value on a chain is a vertex. -/
theorem ChainFrom.lt {p : Fin n → ℕ} {y : ℕ} {l : List ℕ} (h : ChainFrom p y l) :
    ∀ z ∈ l, z < n := by
  induction h with
  | stop => simp
  | step hy _ ih =>
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact ih z hz

/-- The start of a chain is a vertex or `n`. -/
theorem ChainFrom.le {p : Fin n → ℕ} {y : ℕ} {l : List ℕ} (h : ChainFrom p y l) : y ≤ n := by
  cases h with
  | stop => exact le_rfl
  | step hy _ => exact hy.le

/-! ### Writing out the path -/

/-- Current vertex of the trace. -/
abbrev rCur : Reg := 72
/-- Counter of the trace. -/
abbrev rCnt : Reg := 73

theorem setReg_eq_self (s : State) (r : Reg) : s.setReg r (s.regs r) = s := by
  apply State.ext
  · funext r'
    simp only [State.setReg_regs]
    split_ifs with h
    · rw [h]
    · rfl
  · simp

/-- First loop of the trace: count the parent chain. -/
def traceCount : Cmd :=
  .while (.op .lt (.reg rCur) (.reg 40))
    (.seq (.assign rCur (.read aPar (.reg rCur)))
      (.assign rCnt (.op .add (.reg rCnt) (.const 1))))

/-- Second loop of the trace: write the chain into `out` from the back. -/
def traceWrite (out : Arr) : Cmd :=
  .while (.op .lt (.const 0) (.reg rCnt))
    (.seq (.assign rCnt (.op .sub (.reg rCnt) (.const 1)))
      (.seq (.write out (.reg rCnt) (.reg rCur))
        (.assign rCur (.read aPar (.reg rCur)))))

/-- The trace: write into `out` the parent chain from the vertex in register `rx`, in reverse, so
that `out` runs from a source to that vertex. -/
def traceProg (out : Arr) (rx : Reg) : Cmd :=
  .seq (.assign rCur (.reg rx))
    (.seq (.assign rCnt (.const 0))
      (.seq traceCount
        (.seq (.alloc out (.reg rCnt))
          (.seq (.assign rCur (.reg rx)) (traceWrite out)))))

theorem traceCount_exec {w : ℕ} (p : Fin n → ℕ) (hn : n < 2 ^ w) :
    ∀ (l : List ℕ) (y : ℕ), ChainFrom p y l → ∀ (s : State), s.regs rCur = y →
      s.regs 40 = n → s.arrs aPar = List.ofFn p → s.regs rCnt + l.length < 2 ^ w →
      Exec w traceCount s ((s.setReg rCur n).setReg rCnt (s.regs rCnt + l.length))
        (3 + 10 * l.length) := by
  intro l y hch
  induction hch with
  | stop =>
    intro s hy h40 _ _
    have hcond : (Expr.op .lt (.reg rCur) (.reg 40)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hy, h40, hn, show 0 < 2 ^ w by omega]
    have hs : (s.setReg rCur n).setReg rCnt (s.regs rCnt + ([] : List ℕ).length) = s := by
      rw [List.length_nil, Nat.add_zero, ← hy, setReg_eq_self]
      exact setReg_eq_self s rCnt ▸ (by simp [State.setReg_regs])
    rw [hs]
    exact Exec.while_false hcond
  | @step y hy l hch ih =>
    intro s hys h40 hpar hlen
    simp only [List.length_cons] at hlen
    have hyw : y < 2 ^ w := lt_trans hy hn
    have hcond : (Expr.op .lt (.reg rCur) (.reg 40)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hys, h40, hn, hy, hyw,
        show 1 < 2 ^ w by omega]
    have hpy : p ⟨y, hy⟩ ≤ n := hch.le
    have hread : (Expr.read aPar (.reg rCur)).eval w s = some (p ⟨y, hy⟩) := by
      simp [Expr.eval, checkWord, hys, hyw, hpar, hy, show p ⟨y, hy⟩ < 2 ^ w by omega]
    set s₁ := s.setReg rCur (p ⟨y, hy⟩) with hs₁
    have hadd : (Expr.op .add (.reg rCnt) (.const 1)).eval w s₁ = some (s.regs rCnt + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁,
        show s.regs rCnt < 2 ^ w by omega, show s.regs rCnt + 1 < 2 ^ w by omega,
        show 1 < 2 ^ w by omega]
    set s₂ := s₁.setReg rCnt (s.regs rCnt + 1) with hs₂
    have hbody : Exec w (.seq (.assign rCur (.read aPar (.reg rCur)))
        (.assign rCnt (.op .add (.reg rCnt) (.const 1)))) s s₂ ((1 + 1 + 1) + (1 + 1 + 1 + 1)) :=
      .seq (.assign hread) (.assign hadd)
    have hrest := ih s₂ (by simp [s₂, s₁]) (by simp [s₂, s₁, h40]) (by simp [s₂, s₁, hpar])
      (by simp [s₂]; omega)
    have hfin : (s₂.setReg rCur n).setReg rCnt (s₂.regs rCnt + l.length) =
        (s.setReg rCur n).setReg rCnt (s.regs rCnt + (l.length + 1)) := by
      simp only [s₂, s₁, State.setReg_regs_self]
      apply State.ext
      · funext r
        simp only [State.setReg_regs]
        split_ifs <;> omega
      · simp
    rw [hfin] at hrest
    have := Exec.while_true hcond one_ne_zero hbody hrest
    simp only [Expr.cost] at this
    rw [List.length_cons, show 3 + 10 * (l.length + 1) = 1 + 1 + 1 + (1 + 1 + 1 + (1 + 1 + 1 + 1))
      + (3 + 10 * l.length) by omega]
    exact this


theorem traceWrite_exec {w : ℕ} (p : Fin n → ℕ) (hn : n < 2 ^ w) (out : Arr) (hout : out ≠ aPar) :
    ∀ (l : List ℕ) (y : ℕ), ChainFrom p y l → ∀ (done : List ℕ) (s : State), s.regs rCur = y →
      s.regs rCnt = l.length → s.arrs out = List.replicate l.length 0 ++ done →
      s.arrs aPar = List.ofFn p → l.length < 2 ^ w →
      ∃ s', Exec w (traceWrite out) s s' (3 + 13 * l.length) ∧
        s'.arrs out = l.reverse ++ done ∧ s'.regs rCur = n ∧ s'.regs rCnt = 0 ∧
        (∀ r, r ≠ rCur → r ≠ rCnt → s'.regs r = s.regs r) ∧
        (∀ a, a ≠ out → s'.arrs a = s.arrs a) := by
  intro l y hch
  induction hch with
  | stop =>
    intro done s hy hc hout' _ _
    have hcond : (Expr.op .lt (.const 0) (.reg rCnt)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, show 0 < 2 ^ w by omega]
    exact ⟨s, .while_false hcond, by simpa using hout', hy, by simpa using hc,
      fun _ _ _ => rfl, fun _ _ => rfl⟩
  | @step y hy l hch ih =>
    intro done s hys hc hout' hpar hlen
    simp only [List.length_cons] at hc hout' hlen
    have hyw : y < 2 ^ w := lt_trans hy hn
    have hcond : (Expr.op .lt (.const 0) (.reg rCnt)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, show 0 < 2 ^ w by omega,
        show 1 < 2 ^ w by omega, show l.length + 1 < 2 ^ w by omega]
    have hsub : (Expr.op .sub (.reg rCnt) (.const 1)).eval w s = some l.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc, show 1 < 2 ^ w by omega,
        show l.length + 1 < 2 ^ w by omega, show l.length < 2 ^ w by omega]
    set s₁ := s.setReg rCnt l.length with hs₁
    have hidx : (Expr.reg rCnt).eval w s₁ = some l.length := by
      simp [checkWord, s₁, show l.length < 2 ^ w by omega]
    have hval : (Expr.reg rCur).eval w s₁ = some y := by
      simp [checkWord, s₁, hys, hyw]
    have hbound : l.length < (s₁.arrs out).length := by simp [s₁, hout']; omega
    set s₂ := s₁.writeArr out l.length y with hs₂
    have hpy : p ⟨y, hy⟩ ≤ n := hch.le
    have hread : (Expr.read aPar (.reg rCur)).eval w s₂ = some (p ⟨y, hy⟩) := by
      simp [Expr.eval, checkWord, s₂, s₁, hys, hyw, State.writeArr_arrs_ne _ _ _ hout.symm, hpar,
        hy, show p ⟨y, hy⟩ < 2 ^ w by omega]
    set s₃ := s₂.setReg rCur (p ⟨y, hy⟩) with hs₃
    have hbody : Exec w (.seq (.assign rCnt (.op .sub (.reg rCnt) (.const 1)))
        (.seq (.write out (.reg rCnt) (.reg rCur)) (.assign rCur (.read aPar (.reg rCur)))))
        s s₃ ((1 + 1 + 1 + 1) + ((1 + 1 + 1) + (1 + 1 + 1))) :=
      .seq (.assign hsub) (.seq (.write hidx hval hbound) (.assign hread))
    have hout₃ : s₃.arrs out = List.replicate l.length 0 ++ (y :: done) := by
      simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self, hout']
      rw [List.replicate_succ', List.append_assoc, List.set_append_right _ _ (by simp)]
      simp
    obtain ⟨s', hex, h1, h2, h3, h4, h5⟩ := ih (y :: done) s₃ (by simp [s₃])
      (by simp [s₃, s₂, s₁]) hout₃
      (by simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hout.symm, hpar]) (by omega)
    refine ⟨s', ?_, by rw [h1]; simp, h2, h3, fun r hr1 hr2 => ?_, fun a ha => ?_⟩
    · have := Exec.while_true hcond one_ne_zero hbody hex
      simp only [Expr.cost] at this
      rw [List.length_cons, show 3 + 13 * (l.length + 1) = 1 + 1 + 1 + (1 + 1 + 1 + 1 +
        (1 + 1 + 1 + (1 + 1 + 1))) + (3 + 13 * l.length) by omega]
      exact this
    · rw [h4 r hr1 hr2]
      simp [s₃, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2]
    · rw [h5 a ha]
      simp [s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ ha]

/-- **The trace.** For a reached vertex `x` in register `rx`, `traceProg out rx` writes into `out`
the vertex list of a path from a source to `x` whose vertices were all reached. It changes only
registers `rCur`, `rCnt` and array `out`, and takes at most `13 + 24 n` steps. -/
theorem traceProg_exec {w : ℕ} {G : SimpleGraph (Fin n)} {src items : List ℕ} {p : Fin n → ℕ}
    (hp : ParentOK G src items p) (hn : n < 2 ^ w) (out : Arr) (hout : out ≠ aPar) (rx : Reg)
    (hrx₁ : rx ≠ rCur) (hrx₂ : rx ≠ rCnt) (s : State) (x : Fin n) (hx : x.1 ∈ items)
    (hsx : s.regs rx = x.1) (h40 : s.regs 40 = n) (hpar : s.arrs aPar = List.ofFn p) :
    ∃ (s' : State) (t : ℕ) (r : Fin n) (W : G.Walk r x), Exec w (traceProg out rx) s s' t ∧
      t ≤ 13 + 24 * n ∧ W.IsPath ∧ r.1 ∈ src ∧ (∀ y ∈ W.support, y.1 ∈ items) ∧
      (∀ y ∈ W.support, y ≠ r → y.1 ∉ src) ∧
      s'.arrs out = W.support.map Fin.val ∧
      (∀ r', r' ≠ rCur → r' ≠ rCnt → s'.regs r' = s.regs r') ∧
      (∀ a, a ≠ out → s'.arrs a = s.arrs a) := by
  obtain ⟨r, W, hW, hr, hsupp, hns, hch⟩ :=
    exists_walk_of_parentOK hp (items.idxOf x.1 + 1) x hx (by omega)
  set L := W.support.reverse.map Fin.val with hL
  have hLn : L.length ≤ n := by
    have := hW.support_nodup.length_le_card
    simp only [Fintype.card_fin] at this
    simpa [L] using this
  have hxw : x.1 < 2 ^ w := lt_trans x.2 hn
  set s₁ := s.setReg rCur x.1 with hs₁
  have hex₁ : Exec w (.assign rCur (.reg rx)) s s₁ (1 + 1) :=
    .assign (by simp [checkWord, hsx, hxw])
  set s₂ := s₁.setReg rCnt 0 with hs₂
  have hex₂ : Exec w (.assign rCnt (.const 0)) s₁ s₂ (1 + 1) :=
    .assign (by simp [checkWord, show 0 < 2 ^ w by omega])
  have hex₃ := traceCount_exec p hn L x.1 hch s₂ (by simp [s₂, s₁])
    (by simp [s₂, s₁, h40]) (by simp [s₂, s₁, hpar]) (by simp [s₂]; omega)
  set s₃ := (s₂.setReg rCur n).setReg rCnt (s₂.regs rCnt + L.length) with hs₃
  have hc₃ : s₃.regs rCnt = L.length := by simp [s₃, s₂]
  set s₄ := s₃.setArr out (List.replicate L.length 0) with hs₄
  have hex₄ : Exec w (.alloc out (.reg rCnt)) s₃ s₄ (1 + L.length) :=
    .alloc (by simp [checkWord, hc₃, show L.length < 2 ^ w by omega])
  set s₅ := s₄.setReg rCur x.1 with hs₅
  have hex₅ : Exec w (.assign rCur (.reg rx)) s₄ s₅ (1 + 1) :=
    .assign (by simp [checkWord, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hrx₁,
      State.setReg_regs_ne _ _ hrx₂, hsx, hxw])
  obtain ⟨s₆, hex₆, h1, h2, h3, h4, h5⟩ := traceWrite_exec p hn out hout L x.1 hch [] s₅
    (by simp [s₅]) (by simp [s₅, s₄, hc₃]) (by simp [s₅, s₄])
    (by simp [s₅, s₄, State.setArr_arrs_ne _ _ hout.symm, s₃, s₂, s₁, hpar]) (by omega)
  refine ⟨s₆, _, r, W, .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hW, hr, fun y hy => (hsupp y hy).1, hns, ?_, fun r' hr1 hr2 => ?_, fun a ha => ?_⟩
  · rw [h1]; simp [L, List.map_reverse]
  · rw [h4 r' hr1 hr2]
    simp [s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2]
  · rw [h5 a ha]
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr_arrs_ne _ _ ha]


/-! ### What the search reached -/

/-- A walk through free vertices that starts at a reached vertex ends at a reached vertex, when
the reached set is closed. -/
theorem mem_of_walk_closed {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {items : List ℕ}
    (hcl : ∀ u : Fin n, u.1 ∈ items → ∀ v, G.Adj u v → L0 v ≠ 0 ∨ v.1 ∈ items) :
    ∀ {u v : Fin n} (W : G.Walk u v), u.1 ∈ items → (∀ y ∈ W.support, L0 y = 0) → v.1 ∈ items
  | _, _, .nil, hu, _ => hu
  | _, _, .cons hadj W, hu, hW => by
    refine mem_of_walk_closed hcl W ?_ (fun y hy => hW y (List.mem_cons_of_mem _ hy))
    rcases hcl _ hu _ hadj with h | h
    · exact absurd (hW _ (List.mem_cons_of_mem _ W.start_mem_support)) h
    · exact h

/-- **The reached set.** When the queue is empty, every vertex that a source reaches through free
vertices was reached. -/
theorem SInv.mem_of_walk {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s : State}
    {items : List ℕ} (hs : SInv G L0 src s₀ items items.length s) {u v : Fin n} (hu : u.1 ∈ src)
    (W : G.Walk u v) (hW : ∀ y ∈ W.support, L0 y = 0) : v.1 ∈ items :=
  mem_of_walk_closed (fun u hu v hv => hs.closed u (by simpa using hu) v hv) W
    (hs.srcs u hu (hW u W.start_mem_support)) hW

/-- When the queue is empty and register `rHit` holds `n`, no reached vertex has a target as
neighbour. -/
theorem SInv.noHit {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s : State}
    {items : List ℕ} (hs : SInv G L0 src s₀ items items.length s) (h : s.regs rHit = n)
    {u v : Fin n} (hu : u.1 ∈ items) (hadj : G.Adj u v) : L0 v ≠ 3 := by
  rcases hs.hit with ⟨-, h2⟩ | ⟨v', u', h1, -, -, -, -⟩
  · exact h2 v ⟨u, by simpa using hu, hadj⟩
  · have := v'.2; omega

/-- When the queue is empty and register `rHit` does not hold `n`, it holds a target, and register
`rHitPar` a reached neighbour of it. -/
theorem SInv.hit_of_ne {G : SimpleGraph (Fin n)} {L0 : Fin n → ℕ} {src : List ℕ} {s₀ s : State}
    {items : List ℕ} {h : ℕ} (hs : SInv G L0 src s₀ items h s) (hne : s.regs rHit ≠ n) :
    ∃ v u : Fin n, s.regs rHit = v.1 ∧ s.regs rHitPar = u.1 ∧ L0 v = 3 ∧ u.1 ∈ items ∧
      G.Adj u v := by
  rcases hs.hit with ⟨h1, -⟩ | h
  · exact absurd h1 hne
  · exact h

end GraphMinor.Compute.TwoPaths
