module

public import GraphMinor.Compute.GM06PuncturedProtectedCount
public import GraphMinor.Compute.GM06Alg34KeepSingleton
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Retaining a component with no linkage vertex

For Reduction 2 in VI (5.7), page 133, compute the component of
the current source and count its protected linkage vertices.
If the count is zero, offer the source to the verified first
candidate retainer. Earlier successful sources are preserved.
All source components are computed from the endpoint arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Query one source and retain it when its component has no protected vertex. -/
def gm06PuncturedCandidateProg (ends active guarded : Arr) : Cmd :=
  .seq (gm06PuncturedProtectedCountProg ends active guarded)
    (.seq (.assign 111 (.reg 187))
      (.seq (.assign 112 (.op .eq (.reg 183) (.const 0))) gm06KeepSingletonProg))

/-- The computed component test, followed by first-success retention,
returns exactly the left-biased combination of the two candidates. -/
theorem gm06PuncturedCandidateProg_exec {w n : ℕ} (ends active guarded : Arr)
    (he28 : ends < 28) (ha28 : active < 28) (hp28 : guarded < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (Q : Finset (Fin n))
    (found : Option ℕ) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (hQ : s.arrs guarded = gm02VertexBits Q)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) (hsource : s.regs 187 = source.val)
    (hfound : gm06SingletonRegs found s) :
    ∃ s' t, Exec w (gm06PuncturedCandidateProg ends active guarded) s s' t ∧
      t ≤ 53 * (n * n) + 64 * n + 48 * tagged.length + 69 ∧
      gm06SingletonRegs (found.or (if
        (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0
        then some source.val else none)) s' ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧
      s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧ s'.regs 187 = source.val := by
  classical
  let C := (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card
  let candidate : Option ℕ := if C = 0 then some source.val else none
  have hC : C ≤ n := (Finset.card_le_card Finset.inter_subset_left).trans
    (by simpa using Finset.card_le_univ Q)
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hcount₁, _, ha₁, hN₁, hcut₁, hsource₁⟩ :=
    gm06PuncturedProtectedCountProg_exec ends active guarded he28 ha28 hp28 tagged cut source Q
      hw hn hsquare hm hbits ha hb hQ hN hcut hsource
  change s₁.regs 183 = C at hcount₁
  have h113 : s₁.regs 113 = s.regs 113 :=
    he₁.regs_eq_of_not_mem_writtenRegs (by simp [gm06PuncturedProtectedCountProg, gm06PuncturedComponentProg,
      gm06PuncturedMatrixProg, gm06PuncturedEdgeLoopProg, gm06PuncturedEdgeReadProg,
      gm06PuncturedEdgeMarkProg, gm06VertexEdgeMarkProg, gm06VertexBfsProg, bfsRegProg,
      bfsLoopProg, bfsStepProg, queueInit, queuePop, queuePush, forList, forUp,
      matToAdjListRegProg, listAppend, gm02CountIntersectionProg, gm02CountBitsProg, Cmd.writtenRegs])
  have h114 : s₁.regs 114 = s.regs 114 :=
    he₁.regs_eq_of_not_mem_writtenRegs (by simp [gm06PuncturedProtectedCountProg, gm06PuncturedComponentProg,
      gm06PuncturedMatrixProg, gm06PuncturedEdgeLoopProg, gm06PuncturedEdgeReadProg,
      gm06PuncturedEdgeMarkProg, gm06VertexEdgeMarkProg, gm06VertexBfsProg, bfsRegProg,
      bfsLoopProg, bfsStepProg, queueInit, queuePop, queuePush, forList, forUp,
      matToAdjListRegProg, listAppend, gm02CountIntersectionProg, gm02CountBitsProg, Cmd.writtenRegs])
  let s₂ := s₁.setReg 111 source.val
  have he₂ : Exec w (.assign 111 (.reg 187)) s₁ s₂ 2 :=
    .assign (eval_reg hsource₁ (source.isLt.trans hn))
  let s₃ := s₂.setReg 112 (if C = 0 then 1 else 0)
  have he₃ : Exec w (.assign 112 (.op .eq (.reg 183) (.const 0))) s₂ s₃ 4 :=
    .assign (eval_eq (eval_reg (r := 183) (by simpa [s₂] using hcount₁) (hC.trans_lt hn))
      (eval_const (Nat.two_pow_pos w)) hw1)
  have hfound₃ : gm06SingletonRegs found s₃ := by
    refine ⟨?_, ?_⟩
    · simpa [s₃, s₂] using h113.trans hfound.1
    · intro v hv
      simpa [s₃, s₂] using h114.trans (hfound.2 v hv)
  have hc (v : ℕ) (hv : candidate = some v) : v = source.val := by
    by_cases h : C = 0
    · simpa [candidate, h, eq_comm] using hv
    · simp [candidate, h] at hv
  obtain ⟨s₄, t₄, he₄, ht₄, hfound₄, ha₄, hg₄⟩ := gm06KeepSingletonProg_exec found candidate hw1
    (fun v hv => (hc v hv) ▸ source.isLt.trans hn) hfound₃
    (by by_cases h : C = 0 <;> simp [s₃, candidate, h])
    (by intro v hv; rw [hc v hv]; simp [s₃, s₂])
  refine ⟨s₄, t₁ + (2 + (4 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
    hfound₄, ?_, ?_, ?_, ?_⟩
  · intro a ha'
    exact (ha₄ a).trans (ha₁ a ha')
  · exact (hg₄ 100 (by decide) (by decide)).trans hN₁
  · exact (hg₄ 135 (by decide) (by decide)).trans hcut₁
  · exact (hg₄ 187 (by decide) (by decide)).trans hsource₁

end GraphMinor.Compute
