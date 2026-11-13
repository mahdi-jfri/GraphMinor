module

public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.Compute.GM06Alg34Layout
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Writing the supplied dual cuff labels

There is one cuff in the disc. Its dual vertex list is exactly the
supplied gap region array, so write the cuff count and that array as a
length-prefixed field. This phase copies only supplied finite words.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit the single dual cuff from the supplied gap array 47. -/
def gm06DualCuffProg : Cmd :=
  .seq (appendWordProg 55 7804 (.const 1))
    (appendLengthPrefixedProg 47 55 105 7804 8030)

/-- The finite dual cuff section is its one supplied gap-region list. -/
theorem gm06DualCuffWords_eq (x : GM06DrawingData) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).cuffWords = 1 :: L.length :: List.ofFn (fun i => (g i).val) := by
  simp only [GM06DrawingData.cuffWords, GM06DrawingData.dualData, GM06DrawingData.listsWords,
    List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.flatMap_cons,
    List.flatMap_nil, GM06DrawingData.listWords, List.map_ofFn, List.length_ofFn,
    List.append_nil]
  rfl

/-- The single cuff is appended exactly, in time linear in its supplied
length, while retaining the other arrays and lower outer registers. -/
theorem gm06DualCuffProg_exec {w k n cap : ℕ} (g : Fin k → Fin n)
    {pre : List ℕ} {s : State} (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hsource : s.arrs 47 = List.ofFn (fun i => (g i).val)) (hcount : s.regs 105 = k)
    (hbuf : IsPrefixBuffer 55 pre (2 + k + cap) s) (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + 2 + k < 2 ^ w) :
    ∃ s' t, Exec w gm06DualCuffProg s s' t ∧ t ≤ 30 * (k + 1) ∧
      IsPrefixBuffer 55 (pre ++ (1 :: k :: List.ofFn (fun i => (g i).val))) cap s' ∧
      s'.regs 7804 = (pre ++ (1 :: k :: List.ofFn (fun i => (g i).val))).length ∧
      (∀ A : ℕ, A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 8030 → q ≠ 7804 → s'.regs q = s.regs q) := by
  have hwords : ∀ y ∈ List.ofFn (fun i => (g i).val), y < 2 ^ w := by
    intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (g i).isLt.trans hn
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    appendWordProg_exec (cap := 1 + k + cap) (val := 1) 55 7804 (.const 1) hw (by omega)
      (by
        have heq : 2 + k + cap = (1 + k + cap) + 1 := by omega
        exact heq ▸ hbuf)
      hpos (GraphMinor.Compute.Crossing.eval_const hw)
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, _, ha₂, hg₂⟩ :=
    appendLengthPrefixedProg_exec 47 55 105 7804 8030 (by decide) (by decide) (by decide) (by decide)
      hwords hw (by simp only [List.length_append, List.length_singleton, List.length_ofFn]; omega)
      ((ha₁ 47 (by decide)).trans hsource)
      (by simpa only [List.length_ofFn] using hb₁)
      (by simpa only [List.length_ofFn] using (hg₁ 105 (by decide)).trans hcount) hp₁
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₁
    simp only [List.length_ofFn] at ht₂
    omega
  · simpa only [List.length_ofFn, List.append_assoc, List.singleton_append] using hb₂
  · simpa only [List.length_ofFn, List.append_assoc, List.singleton_append] using hp₂
  · intro A hA
    exact (ha₂ A hA).trans (ha₁ A hA)
  · intro q hq h7804
    exact (hg₂ q hq h7804).trans (hg₁ q h7804)

end GraphMinor.Compute
