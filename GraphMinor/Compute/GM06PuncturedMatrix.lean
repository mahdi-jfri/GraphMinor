module

public import GraphMinor.Compute.GM06PuncturedEdgeLoop
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Building the active punctured adjacency matrix

Reduction 2 in VI (5.7), page 133, searches components after
removing an initial vertex. Allocate a fresh square matrix and
scan the supplied endpoint and activity arrays. The matrix is
proved to represent exactly the resulting finite graph.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Allocate the matrix and scan the active edges away from vertex 135. -/
def gm06PuncturedMatrixProg (ends active : Arr) : Cmd :=
  .seq (.alloc 28 (.op .mul (.reg 100) (.reg 100)))
    (gm06PuncturedEdgeLoopProg ends active)

/-- The complete matrix construction reads ordinary endpoint data,
preserves it, and takes quadratic vertex time plus linear edge time. -/
theorem gm06PuncturedMatrixProg_exec {w n : ℕ} (ends active : Arr)
    (he28 : ends ≠ 28) (ha28 : active ≠ 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w (gm06PuncturedMatrixProg ends active) s s' t ∧
      t ≤ 8 + n * n + 48 * tagged.length ∧ Keeps [136, 132, 133, 134] [28] s s' ∧
      s'.arrs 28 = gm06PuncturedMatrixData tagged cut ∧
      IsAdjMatrix (gm06PuncturedGraphData tagged cut).vertexGraph 28 s' := by
  let s₀ := s.setArr 28 (List.replicate (n * n) 0)
  have he₀ : Exec w (.alloc 28 (.op .mul (.reg 100) (.reg 100))) s s₀ (3 + n * n) :=
    .alloc (eval_mul (eval_reg hN hn) (eval_reg hN hn) hsquare)
  obtain ⟨s', t, he, ht, hk, hmat⟩ := gm06PuncturedEdgeLoopProg_exec (s := s₀) ends active he28 ha28
    tagged cut hw hn hsquare hm hbits
    (by simpa only [s₀, State.setArr_arrs_ne _ _ he28] using ha)
    (by simpa only [s₀, State.setArr_arrs_ne _ _ ha28] using hb) hN hcut
    (by simp [s₀])
  have hmat' : s'.arrs 28 = gm06PuncturedMatrixData tagged cut := hmat
  refine ⟨s', (3 + n * n) + t, .seq he₀ he, by omega, ?_, hmat', ?_⟩
  · exact ((Keeps.refl [136, 132, 133, 134] [28] s).setArr (a := 28) (by simp)
      (List.replicate (n * n) 0)).trans hk (by simp) (by simp)
  · rw [IsAdjMatrix, hmat']
    exact gm06PuncturedMatrixData_isAdjMatrixList tagged cut

end GraphMinor.Compute
