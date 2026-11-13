module

public import GraphMinor.Compute.GM13SocietyCrossEdges
public import GraphMinor.Compute.GM13SocietyCorrectness
import GraphMinor.Compute.Algorithm74Scan

/-!
# Restoring a cross in the original society

The simple record stays in array 65. For a cross, arrays 10 and 11 contain
the actual tails and heads of its first path, and arrays 12 and 13 those of
its second path. The parallel-edge index is zero for every output edge.
The correctness predicate refers to path graphs in the original multigraph
society and ties their edges to these written arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GM09

/-- Full (8.1) output. The four edge arrays give the actual edges of the two
paths, in order, with parallel-edge index zero. -/
def GM13ActualCrossOutput (x : GM13SocietyInput) (s : State) : Prop :=
  (s.arrs 65 = [0] ∧ ¬ GM13.HasCross x.society) ∨
  ∃ c : CrossWitness x.G.toSimpleGraph x.omega,
    c.IsValid ∧ s.arrs 65 = gm13CrossCode c ∧
    s.arrs 10 = gm13PathEdgeEnds x.G c.P.support false ∧
    s.arrs 11 = gm13PathEdgeEnds x.G c.P.support true ∧
    s.arrs 12 = gm13PathEdgeEnds x.G c.Q.support false ∧
    s.arrs 13 = gm13PathEdgeEnds x.G c.Q.support true ∧
    x.society.IsCross (walkSubgraph (gm13LiftWalk x c.P))
      (walkSubgraph (gm13LiftWalk x c.Q))

/-- The nonzero-tag branch restores both actual path-edge lists. -/
def gm13CrossRestoreBody : Cmd :=
  .seq gm13SocietyEdgeMatrixProg
    (.seq gm13CrossListsProg
      (.seq (gm13PathEdgesProg 8 10 11) (gm13PathEdgesProg 9 12 13)))

/-- Restore a cross if the simple program found one. -/
def gm13CrossRestoreProg : Cmd :=
  .ite (.read 65 (.const 0)) gm13CrossRestoreBody .skip

private theorem gm13_counts (x : GM13SocietyInput) :
    x.G.numEdges + x.n + 1 ≤ x.size ∧ x.n * x.n ≤ x.size ∧
      x.G.numActivePairs ≤ x.G.numEdges := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.one_mul _).symm.trans_le
      (Nat.mul_le_mul_right _ (show 1 ≤ x.n + 1 by omega))
  · exact Nat.mul_le_mul (show x.n ≤ x.n + 1 by omega)
      (show x.n ≤ x.G.numEdges + x.n + 1 by omega)
  · exact numActivePairs_le_numEdges x.G

/-- Restore both edge lists and retain their cross record in O(vε) time. -/
theorem gm13CrossRestoreBody_exec {w : ℕ} (x : GM13SocietyInput)
    (c : CrossWitness x.G.toSimpleGraph x.omega) (hc : c.IsValid)
    (hw : 16 * (x.size + 2) < 2 ^ w)
    {s : State} (hin : s.arrs 0 = x.enc) (hcode : s.arrs 65 = gm13CrossCode c) :
    ∃ s' t, Exec w gm13CrossRestoreBody s s' t ∧
      t ≤ 1000 * x.size ∧ GM13ActualCrossOutput x s' ∧ s'.arrs 0 = x.enc := by
  obtain ⟨hsize, hsq, hact⟩ := gm13_counts x
  have hp : c.P.support.length ≤ x.n := by
    simpa using hc.1.support_nodup.length_le_card
  have hq : c.Q.support.length ≤ x.n := by
    simpa using hc.2.1.support_nodup.length_le_card
  obtain ⟨s₁, t₁, he₁, ht₁, hm₁, ha₁, hn₁⟩ :=
    gm13SocietyEdgeMatrixProg_exec (w := w) x (by omega) hin
  have hcode₁ : s₁.arrs 65 = gm13CrossCode c :=
    (ha₁ 65 (by decide) (by decide)).trans hcode
  obtain ⟨s₂, t₂, he₂, ht₂, hP₂, hQ₂, ha₂, hr₂⟩ :=
    gm13CrossListsProg_exec (w := w) c.P.support c.Q.support (by omega) hcode₁
  have hm₂ : GM13DirectionMatrix x.G (s₂.arrs 5) := by
    rw [ha₂ 5 (by decide) (by decide)]
    exact hm₁
  have hn₂ : s₂.regs 0 = x.n := hr₂.trans hn₁
  obtain ⟨s₃, t₃, he₃, ht₃, hPT₃, hPH₃, ha₃, hr₃⟩ :=
    gm13PathEdgesProg_exec (w := w) x.G c.P.support 8 10 11 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) hP₂ hm₂ hn₂
  have hQ₃ : s₃.arrs 9 = c.Q.support.map Fin.val :=
    (ha₃ 9 (by decide) (by decide)).trans hQ₂
  have hm₃ : GM13DirectionMatrix x.G (s₃.arrs 5) := by
    rw [ha₃ 5 (by decide) (by decide)]
    exact hm₂
  have hn₃ : s₃.regs 0 = x.n := hr₃.trans hn₂
  obtain ⟨s₄, t₄, he₄, ht₄, hQT₄, hQH₄, ha₄, _⟩ :=
    gm13PathEdgesProg_exec (w := w) x.G c.Q.support 9 12 13 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) hQ₃ hm₃ hn₃
  have hcode₄ : s₄.arrs 65 = gm13CrossCode c := by
    rw [ha₄ 65 (by decide) (by decide), ha₃ 65 (by decide) (by decide),
      ha₂ 65 (by decide) (by decide)]
    exact hcode₁
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)),
    .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega, Or.inr ?_, ?_⟩
  · exact ⟨c, hc, hcode₄, (ha₄ 10 (by decide) (by decide)).trans hPT₃,
    (ha₄ 11 (by decide) (by decide)).trans hPH₃, hQT₄, hQH₄,
      gm13LiftWalk_cross x c hc⟩
  · rw [ha₄ 0 (by decide) (by decide), ha₃ 0 (by decide) (by decide),
      ha₂ 0 (by decide) (by decide), ha₁ 0 (by decide) (by decide)]
    exact hin

/-- The output restoration stage is a timed RAM program. The input relation
is the already computed simple cross record and the original plain input. -/
theorem gm13CrossRestoreProg_computes :
    ComputesRelInTime GM13SocietyInput.size
      (fun x s => GM13SimpleCrossOutput x.simple (s.arrs 65) ∧ s.arrs 0 = x.enc)
      (fun x s => GM13ActualCrossOutput x s ∧ s.arrs 0 = x.enc) gm13CrossRestoreProg (fun s => s) := by
  refine ⟨1004, 4, by decide, by decide, ?_⟩
  intro x s hin
  dsimp only
  obtain ⟨hsize, _, _⟩ := gm13_counts x
  have hwords : 16 * (x.size + 2) < 2 ^ wordSize 4 x.size := by
    have hbase : 3 ≤ x.size + 2 := by omega
    have hc : 16 ≤ (x.size + 2) ^ 3 :=
      (by decide : 16 ≤ 3 ^ 3).trans (Nat.pow_le_pow_left hbase 3)
    have hm := Nat.mul_le_mul_right (x.size + 2) hc
    have hp := pow_lt_two_pow_wordSize (c := 4) (by decide) x.size
    rw [pow_succ] at hp
    exact hm.trans_lt hp
  have h0 : 0 < 2 ^ wordSize 4 x.size := by omega
  have h1 : 1 < 2 ^ wordSize 4 x.size := by omega
  rcases hin.1 with ⟨c, hc, hcode⟩ | ⟨hcode, hno⟩
  · obtain ⟨s', t, he, ht, hout, horig⟩ := gm13CrossRestoreBody_exec x c hc hwords hin.2 hcode
    have htag : (Expr.read 65 (.const 0)).eval (wordSize 4 x.size) s = some 1 := by
      apply gm13_read_eval (Crossing.eval_const h0)
      · simp [hcode, gm13CrossCode]
      · exact h1
    exact ⟨s', 2 + t, .ite_true htag (by decide) he, by omega, hout, horig⟩
  · have htag : (Expr.read 65 (.const 0)).eval (wordSize 4 x.size) s = some 0 := by
      apply gm13_read_eval (Crossing.eval_const h0)
      · simp [hcode]
      · exact h0
    refine ⟨s, 2 + 1, .ite_false htag (.skip s), by omega, Or.inl ⟨hcode, ?_⟩, hin.2⟩
    intro hcross
    exact hno ((hasCrossInSociety_iff_hasCross x.simple).mpr (x.hasCross_iff.mpr hcross))

end GraphMinor.Compute
