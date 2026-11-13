module

public import GraphMinor.Compute.GM06PuncturedMatrix
public import GraphMinor.Compute.GM06Alg34VertexBfs
import GraphMinor.Compute.Algorithm81
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing a component after removing an initial vertex

For Reduction 2 in VI (5.7), page 133, build the active punctured
graph from the supplied endpoints and activity bits. Convert its
matrix to adjacency lists and use the verified breadth-first search.
The result is the exact component of the source label, computed
from the finite instance rather than supplied as extra input.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Mark the source component after removing vertex 135, with source in 187. -/
def gm06PuncturedComponentProg (ends active : Arr) : Cmd :=
  .seq (gm06PuncturedMatrixProg ends active)
    (.seq (.assign 4 (.reg 100))
      (.seq (matToAdjListRegProg 4 28 30 31 32 5 6 7 8) gm06VertexBfsProg))

/-- The component query computes the actual reachability bits in the
active punctured graph and preserves all instance arrays below 28. -/
theorem gm06PuncturedComponentProg_exec {w n : ℕ} (ends active : Arr)
    (he28 : ends < 28) (ha28 : active < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) (hsource : s.regs 187 = source.val) :
    ∃ s' t, Exec w (gm06PuncturedComponentProg ends active) s s' t ∧
      t ≤ 53 * (n * n) + 47 * n + 48 * tagged.length + 48 ∧
      s'.arrs 33 = gm06VertexReachData (gm06PuncturedGraphData tagged cut) source ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧
      s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧ s'.regs 187 = source.val := by
  let x := gm06PuncturedGraphData tagged cut
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, _, hmat₁⟩ := gm06PuncturedMatrixProg_exec (w := w) (n := n) (s := s) ends active
    (Nat.ne_of_lt he28) (Nat.ne_of_lt ha28) tagged cut hw hn hsquare hm hbits ha hb hN hcut
  let s₂ := s₁.setReg 4 n
  have hN₁ : s₁.regs 100 = n := (hk₁.1 100 (by decide)).trans hN
  have he₂ : Exec w (.assign 4 (.reg 100)) s₁ s₂ 2 := .assign (eval_reg hN₁ hn)
  have hmat₂ : IsAdjMatrix x.vertexGraph 28 s₂ := hmat₁
  obtain ⟨s₃, t₃, he₃, ht₃, hlists₃, hlen₃, hg₃, ha₃⟩ :=
    matToAdjListRegProg_exec (n := n) x.vertexGraph hw1 hsquare hmat₂ (by simp [s₂])
  have hcsr (q : ℕ) (hq : q ≠ 5 ∧ q ≠ 6 ∧ q ≠ 7 ∧ q ≠ 8) : s₃.regs q = s₂.regs q := by
    apply he₃.regs_eq_of_not_mem_writtenRegs
    have hwr : (matToAdjListRegProg 4 28 30 31 32 5 6 7 8).writtenRegs = {5, 6, 7, 8} := by decide
    simpa only [hwr, Finset.mem_insert, Finset.mem_singleton, not_or] using hq
  have h4₃ : s₃.regs 4 = n := (hg₃ 4 (by decide)).trans (by simp [s₂])
  have hsource₃ : s₃.regs 187 = source.val := by
    rw [hcsr 187 (by decide)]
    exact (hk₁.1 187 (by decide)).trans hsource
  obtain ⟨s₄, t₄, he₄, ht₄, hreach, ha₄, hg₄⟩ :=
    gm06VertexBfsProg_exec x source hw1 hn hsquare h4₃ hsource₃ hlists₃ hlen₃
  change t₃ ≤ 26 * (n * n) + 24 * n + 12 at ht₃
  change t₄ ≤ 26 * (n * n) + 23 * n + 26 at ht₄
  refine ⟨s₄, t₁ + (2 + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
    hreach, ?_, ?_, ?_, ?_⟩
  · intro a ha'
    rw [ha₄ a (by omega) (by omega), ha₃ a (by omega)]
    exact hk₁.2 a (by simp; omega)
  · rw [hg₄ 100 (by decide), hcsr 100 (by decide)]
    exact hN₁
  · rw [hg₄ 135 (by decide), hcsr 135 (by decide)]
    exact (hk₁.1 135 (by decide)).trans hcut
  · rw [hg₄ 187 (by decide)]
    exact hsource₃

end GraphMinor.Compute
