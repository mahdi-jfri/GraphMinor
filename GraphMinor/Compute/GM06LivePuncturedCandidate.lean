module

public import GraphMinor.Compute.GM06PuncturedCandidate
import GraphMinor.Compute.GM02CopyLabelBits

/-!
# Skipping vertex labels no longer present

The reduction workspace keeps its original vertex indices. Its live
vertex mask distinguishes current vertices from labels removed by
contraction or deletion. For Reduction 2 in VI (5.7), page 133,
query only live sources and retain a source when its computed
component contains no protected linkage vertex.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test a component source only when its live-vertex bit is set. -/
def gm06LivePuncturedCandidateProg (ends active guarded live : Arr) : Cmd :=
  .ite (.read live (.reg 187)) (gm06PuncturedCandidateProg ends active guarded) .skip

/-- The guarded query retains exactly a live source with zero protected
intersection, preserving the ordinary instance arrays. -/
theorem gm06LivePuncturedCandidateProg_exec {w n : ℕ} (ends active guarded live : Arr)
    (he28 : ends < 28) (ha28 : active < 28) (hp28 : guarded < 28) (hl28 : live < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut source : Fin n) (Q A : Finset (Fin n))
    (found : Option ℕ) (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (hQ : s.arrs guarded = gm02VertexBits Q)
    (hA : s.arrs live = gm02VertexBits A)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) (hsource : s.regs 187 = source.val)
    (hfound : gm06SingletonRegs found s) :
    ∃ s' t, Exec w (gm06LivePuncturedCandidateProg ends active guarded live) s s' t ∧
      t ≤ 53 * (n * n) + 64 * n + 48 * tagged.length + 71 ∧
      gm06SingletonRegs (found.or (if source ∈ A ∧
        (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0
        then some source.val else none)) s' ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧
      s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧ s'.regs 187 = source.val := by
  have hread := gm02ReadVertexBits_eval A source live 187 s (by omega) hn hsource hA
  by_cases hlive : source ∈ A
  · obtain ⟨s', t, he, ht, hf, harrays, hN', hcut', hsource'⟩ :=
      gm06PuncturedCandidateProg_exec ends active guarded he28 ha28 hp28 tagged cut source Q
        found hw hn hsquare hm hbits ha hb hQ hN hcut hsource hfound
    refine ⟨s', 2 + t, .ite_true (by simpa only [hlive, ite_true] using hread) (by decide) he,
      by omega, ?_, harrays, hN', hcut', hsource'⟩
    simpa only [hlive, true_and] using hf
  · refine ⟨s, 3, .ite_false (by simpa only [hlive, ite_false] using hread) (.skip s),
      by omega, ?_, fun _ _ => rfl, hN, hcut, hsource⟩
    simpa only [hlive, false_and, ite_false, Option.or_none] using hfound

end GraphMinor.Compute
