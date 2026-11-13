module

public import GraphMinor.Compute.GM06Alg34GapParseFrames
public import GraphMinor.GM06.Alg34GapDisc
public import GraphMinor.GM06.Section3Reduction

/-!
# Correct parsing of every represented augmented disc instance

The geometric representation supplies the single-cuff layout. Apply
the concrete linear RAM parser and its fixed memory frames. Its outputs
are the supplied base drawing and supplied gap region labels, with
logarithmic words and no assumptions about initial scratch contents.
-/

public section
namespace GraphMinor.GM06

open Compute

universe u

/-- Every represented augmented disc input is parsed exactly in linear
RAM time with logarithmic words. The gap labels remain plain array data. -/
theorem alg34_gap_parse_exec {X : GM06GapInput} {I : DiscDivInstance.{u}}
    (h : GM06GapInputRep X I.G I.Δ) {c : ℕ} (hc : 1 ≤ c) {s : State}
    (hinput : s.arrs 0 = X.words) :
    ∃ R : List (Fin X.drawing.regions.length), X.gapRegions = [R] ∧
      ∃ s' t, Exec (wordSize c X.size) gm06GapParseProg s s' t ∧
        t ≤ 100 * (X.size + 1) ∧
        s'.arrs 0 = X.drawing.words ∧ s'.arrs 47 = R.map Fin.val ∧
        s'.arrs 49 = X.drawing.words ∧ s'.regs 6003 = R.length ∧
        (∀ A : ℕ, 50 ≤ A → s'.arrs A = s.arrs A) ∧
        (∀ q : ℕ, (q < 6000 ∨ 6303 ≤ q) → s'.regs q = s.regs q) := by
  obtain ⟨R, hR⟩ := h.disc_gapRegions_singleton I.hDisc
  obtain ⟨s', t, he, ht, hbase, hgap, hsaved, hlen, _, _⟩ :=
    gm06GapParseProg_exec X R hR
      (lt_two_pow_wordSize_of_le hc (by omega : 1 ≤ X.size + 1))
      (lt_two_pow_wordSize_of_le hc (Nat.le_succ X.size)) hinput
  refine ⟨R, hR, s', t, he, ht, hbase, hgap, hsaved, hlen, ?_, ?_⟩
  · intro A hA
    exact gm06GapParseProg_array_frame he (by omega) (by omega) (by omega)
  · intro q hq
    exact gm06GapParseProg_register_frame he hq

end GraphMinor.GM06
