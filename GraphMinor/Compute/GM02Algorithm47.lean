module

public import GraphMinor.Compute.GM02InjectionComplexity
public import GraphMinor.Compute.GM02InjectionWordBounds

/-!
# Polynomial computation for the plain-host injection search

Choose the recursive width threshold above the corrected labelled split
bound. The uniform word-size theorem and full execution theorem apply
to every host edge-list input. The fixed polynomial budget therefore
gives the three alternatives of II (4.7) from the host encoding alone.
-/

public section
namespace GraphMinor.Compute

/-- The complete injection-search program computes the printed three outcomes in polynomial time. -/
theorem gm02Algorithm47_computes (H : GM02EdgeListInput) (w : ℤ) :
    let q := max w.toNat 2 + 2 * H.edges.length + 1
    ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
      (fun G s => gm02IsomorphicTopologicalCorrect H.graph w G s)
      (gm02InjectionDecisionProg H q) (fun n => (n + 1) ^ gm02InjectionPolynomialExponent q H) := by
  dsimp only
  let q := max w.toNat 2 + 2 * H.edges.length + 1
  refine ⟨gm02InjectionPolynomialCoefficient q H, gm02InjectionWordCoefficient q H, ?_, ?_, ?_⟩
  · unfold gm02InjectionPolynomialCoefficient
    omega
  · have h := gm02InjectionWordCoefficient_ge_two q H
    omega
  · intro G s hsrc
    obtain ⟨hw, hn, hmG, hcap, hlen, hpow, hword⟩ := gm02Injection_wordBounds q G H
    obtain ⟨s', t, he, ht, hc⟩ := gm02InjectionDecisionProg_exec q G H w s
      (Nat.lt_succ_self _) hw hn hmG hcap hlen hpow hword hsrc
    exact ⟨s', t, he, ht.trans (gm02InjectionBudget_polynomial q G H), hc⟩

end GraphMinor.Compute
