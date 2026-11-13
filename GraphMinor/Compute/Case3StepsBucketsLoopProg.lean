module

public import GraphMinor.Compute.Case3StepsBucketPairProg

/-!
# Reverse insertion of all stored pair indices

The scan decreases the pair index before reading it. The bucket tables at
index `k` describe exactly the suffix beginning at `k`, so the last iteration
produces the complete ordered buckets. Each positive pair costs at most
forty-two steps, regardless of its multiplicity.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Visit positive pair indices in decreasing order. -/
def case3BucketsLoopProg : Cmd :=
  .while (.reg 65)
    (.seq (.assign 65 (.op .sub (.reg 65) (.const 1))) case3BucketPairProg)

/-- Reverse insertion computes the complete head, next, and count tables. -/
theorem case3BucketsLoopProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w)
    (hL : x.n + (case3InputEdges x).length < 2 ^ w)
    (k : ℕ) (hk : k ≤ D.numActivePairs) {s : State}
    (hD : s.arrs 3 = D.enc) (hloop : s.arrs 33 = List.ofFn (case3OrderedLoopLabel x Z))
    (hmat : s.arrs 34 = case3EdgeMatrixPrefix x Z (case3InputEdges x).length)
    (hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z)
      (x.n + (case3InputEdges x).length) k)
    (hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) k)
    (hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z)
      (x.n + (case3InputEdges x).length) k)
    (hrn : s.regs 14 = x.n) (hrk : s.regs 65 = k) :
    ∃ s' t, Exec w case3BucketsLoopProg s s' t ∧ t ≤ 42 * k + 1 ∧
      s'.arrs 35 = case3BucketHeads (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      s'.arrs 36 = case3BucketNext (case3ActivePairOwner x D Z) 0 ∧
      s'.arrs 37 = case3BucketCounts (case3ActivePairOwner x D Z)
        (x.n + (case3InputEdges x).length) 0 ∧
      (∀ a, a ≠ 35 → a ≠ 36 → a ≠ 37 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 65 → r ≠ 66 → r ≠ 67 → r ≠ 68 → r ≠ 69 → s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  induction k generalizing s with
  | zero =>
    have hc : (Expr.reg 65).eval w s = some 0 := by
      simp only [Expr.eval, checkWord, hrk, h0, ↓reduceIte]
    exact ⟨s, 1, .while_false hc, by omega, hheads, hnext, hcounts,
      fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    have hkA : k < D.numActivePairs := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    have hc : (Expr.reg 65).eval w s = some (k + 1) := by
      simp only [Expr.eval, checkWord, hrk, hkpw, ↓reduceIte]
    let sD := s.setReg 65 k
    have hexD : Exec w (.assign 65 (.op .sub (.reg 65) (.const 1))) s sD 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hkpw, h1, hkw])
    obtain ⟨sB, tB, hexB, htB, hheadsB, hnextB, hcountsB, harrB, hregB⟩ :=
      case3BucketPairProg_exec x D hG Z hdiv ⟨k, hkA⟩ hw hn hsquare hA hL
        (s := sD) hD hloop hmat hheads hnext hcounts
        (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hrn) (State.setReg_regs_self ..)
    obtain ⟨s', t, hex, ht, hheads', hnext', hcounts', harr, hreg⟩ := ih (by omega) (s := sB)
      ((harrB 3 (by decide) (by decide) (by decide)).trans hD)
      ((harrB 33 (by decide) (by decide) (by decide)).trans hloop)
      ((harrB 34 (by decide) (by decide) (by decide)).trans hmat)
      hheadsB hnextB hcountsB
      (by rw [hregB 14 (by decide) (by decide) (by decide) (by decide),
        State.setReg_regs_ne _ _ (by decide)]; exact hrn)
      (by rw [hregB 65 (by decide) (by decide) (by decide) (by decide)]; exact State.setReg_regs_self ..)
    refine ⟨s', 1 + (4 + tB) + t, .while_true hc (by omega) (.seq hexD hexB) hex,
      by omega, hheads', hnext', hcounts', ?_, ?_⟩
    · intro a h35 h36 h37
      exact (harr a h35 h36 h37).trans (harrB a h35 h36 h37)
    · intro r h65 h66 h67 h68 h69
      rw [hreg r h65 h66 h67 h68 h69, hregB r h66 h67 h68 h69,
        State.setReg_regs_ne _ _ h65]

end GraphMinor.Compute
