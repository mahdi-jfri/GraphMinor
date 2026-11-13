module

public import GraphMinor.Compute.F92Search

/-!
# Writing a parent path and its target

The search stores the reached neighbour of a target and the target in separate registers.
Count the neighbour's parent chain, allocate one extra entry, store the target there, and
write the parent chain backwards into the preceding entries. The result includes both ends.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

open SimpleGraph TwoPaths

/-- Trace from the hit's parent, including the target as the final vertex. -/
def f92TraceTargetProg (out : Arr) : Cmd :=
  .seq (.assign rCur (.reg rHitPar))
    (.seq (.assign rCnt (.const 0))
      (.seq traceCount
        (.seq (.alloc out (.op .add (.reg rCnt) (.const 1)))
          (.seq (.write out (.reg rCnt) (.reg rHit))
            (.seq (.assign rCur (.reg rHitPar)) (traceWrite out))))))

/-- The trace writes exactly the reversed parent chain followed by the target, preserving
all other arrays and registers except its two cursors. -/
theorem f92TraceTargetProg_exec {w n : ℕ} (par : Fin n → ℕ)
    (L : List ℕ) (z v : ℕ) (hchain : ChainFrom par z L)
    (out : ℕ) (hout : out ≠ aPar) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hz : z < n) (hv : v < n) (hlen : L.length + 1 < 2 ^ w)
    {s : State} (hpar : s.arrs aPar = List.ofFn par)
    (hrn : s.regs 40 = n) (hrz : s.regs rHitPar = z) (hrv : s.regs rHit = v) :
    ∃ s' t, Exec w (f92TraceTargetProg out) s s' t ∧
      t ≤ 19 + 24 * L.length ∧ s'.arrs out = L.reverse ++ [v] ∧
      (∀ q : ℕ, q ≠ rCur → q ≠ rCnt → s'.regs q = s.regs q) ∧
      (∀ a : ℕ, a ≠ out → s'.arrs a = s.arrs a) := by
  have hzw := hz.trans hn
  have hvw := hv.trans hn
  have hLw : L.length < 2 ^ w := by omega
  let s₁ := s.setReg rCur z
  have hex₁ : Exec w (.assign rCur (.reg rHitPar)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrz, hzw])
  let s₂ := s₁.setReg rCnt 0
  have hex₂ : Exec w (.assign rCnt (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  let s₃ := (s₂.setReg rCur n).setReg rCnt L.length
  have hex₃ : Exec w traceCount s₂ s₃ (3 + 10 * L.length) := by
    simpa [s₂, s₃] using traceCount_exec par hn L z hchain s₂
      (by simp [s₂, s₁]) (by simp [s₂, s₁, hrn]) hpar (by simpa [s₂] using hLw)
  let s₄ := s₃.setArr out (List.replicate (L.length + 1) 0)
  have hex₄ : Exec w (.alloc out (.op .add (.reg rCnt) (.const 1))) s₃ s₄
      (3 + (L.length + 1)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₃, hLw, hw, hlen])
  let s₅ := s₄.writeArr out L.length v
  have hex₅ : Exec w (.write out (.reg rCnt) (.reg rHit)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, s₄, s₃, hLw])
      (by simp [Expr.eval, checkWord, s₄, s₃, s₂, s₁, hrv, hvw])
      (by simp [s₄])
  have hout₅ : s₅.arrs out = List.replicate L.length 0 ++ [v] := by
    simp only [s₅, State.writeArr_arrs_self, s₄, State.setArr_arrs_self]
    rw [List.replicate_add, List.replicate_one, List.set_append_right _ _ (by simp)]
    simp
  let s₆ := s₅.setReg rCur z
  have hex₆ : Exec w (.assign rCur (.reg rHitPar)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₅, s₄, s₃, s₂, s₁, hrz, hzw])
  obtain ⟨s₇, hex₇, hout₇, _, _, _, _⟩ := traceWrite_exec par hn out hout L z hchain [v] s₆
    (by simp [s₆]) (by simp [s₆, s₅, s₄, s₃]) hout₅
    (by simp [s₆, s₅, s₄, hout.symm, s₃, s₂, s₁, hpar]) hLw
  have hex : Exec w (f92TraceTargetProg out) s s₇
      (2 + (2 + ((3 + 10 * L.length) + ((3 + (L.length + 1)) + (3 + (2 + (3 + 13 * L.length))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
  refine ⟨s₇, _, hex, by omega, hout₇, ?_, ?_⟩
  · intro q hcur hcnt
    exact hex.regs_eq_of_not_mem_writtenRegs (by
      simp [f92TraceTargetProg, traceCount, traceWrite, Cmd.writtenRegs, hcur, hcnt])
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by
      simp [f92TraceTargetProg, traceCount, traceWrite, Cmd.writtenArrs, ha])

/-- Search in the canonical layout, then write the full path into array 64. -/
def f92SearchTraceProg : Cmd :=
  .seq (searchProg 40 41 42) (f92TraceTargetProg 64)

/-- A prepared canonical search writes a subwall `H`-path. Non-dividing ensures that a
hit exists. Parent tracing writes the path itself, including its target. -/
theorem f92SearchTraceProg_exec {w l m p h k r : ℕ}
    (x : Alg92Input l m p h k r) (a : Fin k) (lists : Fin x.n → List ℕ)
    (src : List ℕ) (hsrc : ∀ v : Fin x.n, v.val ∈ src ↔ v ∈ (x.W_sub a).insideFinset)
    (hsrcLt : ∀ v ∈ src, v < x.n) (s : State)
    (hadj : IsAdjList x.G.toSimpleGraph 40 41 42 lists s)
    (hent : (s.arrs 42).length < 2 ^ w) (hrn : s.regs 40 = x.n)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hlen : src.length < 2 ^ w)
    (hlab : s.arrs aLab = List.ofFn (f92SearchLabel x.W (x.W_sub a)))
    (hsrcArr : s.arrs aSrc = src) :
    ∃ s' t, ∃ P : List (Fin x.n), Exec w f92SearchTraceProg s s' t ∧
      t ≤ 35 + 45 * x.n + 29 * src.length + 29 * totalAdjEntries lists ∧
      IsSubwallHPath x.W (x.W_sub a) P ∧ s'.arrs 64 = P.map Fin.val ∧
      (∀ q : ℕ, q < 60 ∨ 74 ≤ q → s'.regs q = s.regs q) ∧
      (∀ b : ℕ, b ≠ 60 → b ≠ 61 → b ≠ 62 → b ≠ 64 → s'.arrs b = s.arrs b) := by
  have hn' : x.n < 2 ^ w := by omega
  obtain ⟨s₁, t₁, items, hex₁, ht₁, hinv, hhit, _⟩ :=
    f92SearchProg_exec x a lists 40 41 42 (by decide) (by decide) (by decide)
      src hsrc hsrcLt s hadj hent hrn hw hn' hlen hlab hsrcArr
  obtain ⟨v, z, hv, hzreg, hvlabel, hz, hadjz⟩ := hinv.hit_of_ne hhit
  obtain ⟨par, hparArr, hpar⟩ := hinv.par
  obtain ⟨u, q, hq, hu, hsupp, hns, hchain⟩ :=
    exists_walk_of_parentOK hpar (items.idxOf z.val + 1) z hz (by omega)
  have htarget : v ∈ x.W.vertexFinset \ (x.W_sub a).vertexFinset :=
    (f92SearchLabel_three x.W (x.W_sub a) v).mp hvlabel
  have hvnot : v ∉ q.support := by
    intro hmem
    have hf := hinv.free v (hsupp v hmem).1
    omega
  have hpath : IsSubwallHPath x.W (x.W_sub a) (q.concat hadjz).support := by
    apply f92_isSubwallHPath_of_walk x.hW_valid.1 x.hW_valid.2.1 x.hW_valid.2.2
      (x.hnondiv a).1 _ (hq.concat hvnot hadjz) ((hsrc u).mp hu) htarget
    intro y hy hyW
    rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · left
      by_contra hyu
      have hfree := (f92SearchLabel_zero x.W (x.W_sub a) y).mp
        (hinv.free y (hsupp y hy).1)
      rcases hfree with hyS | hyout
      · exact hns y hy hyu ((hsrc y).mpr hyS)
      · exact hyout hyW
    · exact Or.inr rfl
  let L := q.support.reverse.map Fin.val
  have hLlen : L.length = q.support.length := by simp [L]
  have hqlen : q.support.length ≤ x.n := by
    simpa using hq.support_nodup.length_le_card
  have hrn₁ : s₁.regs 40 = x.n :=
    (hinv.frame.1 40 (Or.inl (by decide))).trans hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hout₂, hreg₂, harr₂⟩ :=
    f92TraceTargetProg_exec par L z.val v.val hchain 64 (by decide) (by omega) hn'
      z.isLt v.isLt (by omega) hparArr hrn₁ hzreg hv
  refine ⟨s₂, t₁ + t₂, (q.concat hadjz).support, .seq hex₁ hex₂,
    by omega, hpath, ?_, ?_, ?_⟩
  · simpa [L, Walk.support_concat, List.map_reverse] using hout₂
  · intro b hb
    exact (hreg₂ b (show b ≠ (72 : ℕ) by omega) (show b ≠ (73 : ℕ) by omega)).trans
      (hinv.frame.1 b (show (b : ℕ) < 60 ∨ 71 ≤ b by omega))
  · intro b hbL hbP hbQ hbO
    exact (harr₂ b hbO).trans (hinv.frame.2 b hbL hbP hbQ)

end GraphMinor.Compute.Alg92
