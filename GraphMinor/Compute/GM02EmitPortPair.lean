module

public import GraphMinor.Compute.GM02PortAdjProg
public import GraphMinor.Compute.GM02AppendPortEdge
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Conditionally emitting a numeric split edge

Ignore a pair that is not increasing. Otherwise compute split adjacency
and append exactly when the resulting bit is one. The original arrays
survive except for the edge buffer, whose exact prefix and unused suffix
are recorded. Both pair counters are preserved for the scan.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Append the pair in registers 60 and 61 exactly when it is increasing and adjacent. -/
@[expose] def gm02EmitPortPairProg (src : Arr) : Cmd :=
  .ite (.op .lt (.reg 60) (.reg 61))
    (.seq (gm02PortAdjProg src) (.ite (.reg 63) gm02AppendPortEdgeProg .skip)) .skip

/-- The guarded emission command appends exactly the next canonical edge in at most 87 steps. -/
theorem gm02EmitPortPairProg_exec {w K code rem m : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (u v : Fin (gm02FullPortSize x K)) (pre : List ℕ)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hu : s.regs 60 = u.val) (hv : s.regs 61 = v.val)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hbuf : s.arrs 24 = pre ++ List.replicate (rem + 2) 0)
    (hpos : s.regs 67 = pre.length) (hcount : s.regs 68 = m)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w)
    (hposw : pre.length + 2 < 2 ^ w) (hcountw : m + 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02EmitPortPairProg src) s s' t ∧ t ≤ 87 ∧
      (if u.val < v.val ∧ (gm02FullPortGraph x gflags hflags code K).Adj u v then
        s'.arrs 24 = (pre ++ [u.val, v.val]) ++ List.replicate rem 0 ∧
          s'.regs 67 = (pre ++ [u.val, v.val]).length ∧ s'.regs 68 = m + 1
       else s'.arrs 24 = s.arrs 24 ∧ s'.regs 67 = pre.length ∧ s'.regs 68 = m) ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 46 →
        r ≠ 62 → r ≠ 63 → r ≠ 67 → r ≠ 68 → s'.regs r = s.regs r) := by
  have huw : u.val < 2 ^ w := u.isLt.trans hN
  have hvw : v.val < 2 ^ w := v.isLt.trans hN
  have hw1 : 1 < 2 ^ w := by omega
  have hguard := eval_lt (eval_reg hu huw) (eval_reg hv hvw) hw1
  by_cases huv : u.val < v.val
  · have hg : (Expr.op .lt (.reg 60) (.reg 61)).eval w s = some 1 := by
      simpa only [huv, ↓reduceIte] using hguard
    obtain ⟨s₀, t₀, he₀, ht₀, hadj, harr, hr⟩ := gm02PortAdjProg_exec x s src gflags hflags u v huv
      hsrc hG hGlen hGbits hH hHlen hHbits hmask hslots hu hv hn hm hf hw hN hfw henc
    by_cases hAdj : (gm02FullPortGraph x gflags hflags code K).Adj u v
    · have hbit : (Expr.reg 63).eval w s₀ = some 1 :=
        eval_reg (by simpa only [hAdj, ite_true] using hadj) hw1
      obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hpos₁, hcount₁, ha₁, hr₁⟩ :=
        gm02AppendPortEdgeProg_exec pre s₀ ((congrFun harr 24).trans hbuf)
          ((hr 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpos)
          ((hr 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hu)
          ((hr 61 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hv)
          ((hr 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount)
          hw hposw huw hvw hcountw
      refine ⟨s₁, 3 + (t₀ + (1 + t₁)), .ite_true hg (by decide)
        (.seq he₀ (.ite_true hbit (by decide) he₁)), by omega, ?_, ?_, ?_⟩
      · simp only [huv, hAdj, true_and, ite_true]
        exact ⟨hbuf₁, hpos₁, hcount₁⟩
      · intro a ha24
        exact (ha₁ a ha24).trans (congrFun harr a)
      · intro r h32 h42 h43 h44 h45 h46 h62 h63 h67 h68
        exact (hr₁ r h67 h68).trans (hr r h32 h42 h43 h44 h45 h46 h62 h63)
    · have hbit : (Expr.reg 63).eval w s₀ = some 0 :=
        eval_reg (by simpa only [hAdj, ite_false] using hadj) (by omega)
      refine ⟨s₀, 3 + (t₀ + 2), .ite_true hg (by decide) (.seq he₀ (.ite_false hbit (.skip s₀))),
        by omega, ?_, fun a _ => congrFun harr a, ?_⟩
      · simp only [hAdj, and_false, ite_false]
        exact ⟨congrFun harr 24,
          (hr 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpos,
          (hr 68 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hcount⟩
      · intro r h32 h42 h43 h44 h45 h46 h62 h63 _ _
        exact hr r h32 h42 h43 h44 h45 h46 h62 h63
  · have hg : (Expr.op .lt (.reg 60) (.reg 61)).eval w s = some 0 := by
      simpa only [huv, ↓reduceIte] using hguard
    refine ⟨s, 4, .ite_false hg (.skip s), by decide, ?_, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    simp only [huv, false_and, ite_false]
    exact ⟨trivial, hpos, hcount⟩

end GraphMinor.Compute
