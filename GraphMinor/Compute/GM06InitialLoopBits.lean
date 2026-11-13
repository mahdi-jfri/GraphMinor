module

public import GraphMinor.Compute.GM06InducedEdgeBits
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the loops at an initial vertex

The punctured component search misses loops whose only vertex is
the removed initial vertex. Build that vertex's singleton mask,
then use the induced-edge scan to mark exactly its active loops.
This supplies the remaining edge case of Reduction 2 in VI (5.7).
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Mark the active edges having both endpoints equal to vertex 135. -/
def gm06InitialLoopBitsProg : Cmd :=
  .seq (gm13TabulateProg 180 (.reg 100) (.op .eq (.reg 180) (.reg 135)) 22)
    (gm06InducedEdgeBitsProg 3 12 22 23)

/-- The loop-mask program computes exactly the induced edge mask on
the initial vertex's singleton, preserving all ordinary input arrays. -/
theorem gm06InitialLoopBitsProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w gm06InitialLoopBitsProg s s' t ∧
      t ≤ 12 + 15 * n + 28 * tagged.length ∧ Keeps [180, 181] [22, 23] s s' ∧
      s'.arrs 23 = gm06InducedEdgeBits tagged {cut} := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hv₁⟩ := gm13TabulateProg_exec (w := w)
    180 (.reg 100) (.op .eq (.reg 180) (.reg 135)) 22 (gm02VertexBits {cut}) s (by omega)
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simpa only [gm02VertexBits, List.length_ofFn] using
        (eval_reg ((hk.1 100 (by decide)).trans hN) hn))
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      have hc : st.regs 135 = cut.val := (hk.1 135 (by decide)).trans hcut
      have heq := eval_eq (eval_reg hri (hin.trans hn)) (eval_reg hc (cut.isLt.trans hn)) (by omega)
      have hv : (⟨i, hin⟩ : Fin n) = cut ↔ i = cut.val := Fin.ext_iff
      simpa only [gm02VertexBits, List.getElem_ofFn, Finset.mem_singleton, hv] using heq)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hl₂⟩ := gm06InducedEdgeBitsProg_exec tagged {cut}
    3 12 22 23 (by decide) (by decide) (by decide) s₁ hw hn hm hbits
    ((hk₁.2 3 (by decide)).trans ha) ((hk₁.2 12 (by decide)).trans hb) hv₁
  have hk₁' : Keeps [180, 181] [22, 23] s s₁ := hk₁.mono (by simp) (by simp)
  have hk₂' : Keeps [180, 181] [22, 23] s₁ s₂ := hk₂.mono (by simp) (by simp)
  simp only [gm02VertexBits, List.length_ofFn, Expr.cost] at ht₁
  exact ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega,
    hk₁'.trans hk₂' (by simp) (by simp), hl₂⟩

/-- A loop-mask bit is one exactly for an active edge with both ends at the cut vertex. -/
theorem gm06InitialLoopBits_getElem_eq_one {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) {i : ℕ} (hi : i < tagged.length) :
    (gm06InducedEdgeBits tagged {cut})[i]'(by rw [gm06InducedEdgeBits_length]; exact hi) = 1 ↔
      tagged[i].2 = 1 ∧ tagged[i].1.1 = cut ∧ tagged[i].1.2 = cut := by
  simpa only [Finset.mem_singleton] using gm06InducedEdgeBits_getElem_eq_one tagged {cut} hi

end GraphMinor.Compute
