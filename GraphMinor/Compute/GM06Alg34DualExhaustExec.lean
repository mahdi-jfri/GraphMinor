module

public import GraphMinor.Compute.GM06Alg34DiscDualBuild
public import GraphMinor.Compute.GM06Alg34DiscDualSize
public import GraphMinor.Compute.GM06Alg34GapSingletonComplexity
public import GraphMinor.Compute.GM06Alg34UniformWordSize
public import GraphMinor.Compute.GM06Alg34SingletonDriverFrames
public import GraphMinor.Compute.GM06Alg34DriverControlFrames

/-!
# RAM execution of the full dual branch

Construct the plain augmented dual, then exhaust its singleton blocks.
The pure uniform bounds lift both executions to the same word size
chosen from the fixed original count bound. Their composition installs
the exact finite result and retains the queue, cursors and outer controls.
-/

public section
namespace GraphMinor.Compute

/-- The dual construction followed by singleton exhaustion has a uniform
polynomial bound and preserves the complete external queue state. -/
theorem gm06DualExhaust_exec (Q : ℕ) (X : GM06GapInput)
    (hQ : X.drawing.cellCount ≤ Q)
    (hr : X.drawing.regionWords.length ≤ gm06SectionCap Q)
    (hc : X.drawing.cuffWords.length ≤ gm06SectionCap Q)
    (hd : X.drawing.divisionWords.length ≤ gm06SectionCap Q)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧
      R.length = L.length ∧ L.Nodup)
    (hR : 0 < X.drawing.regions.length) (hDiv : GM06.IsDivision X.drawing.divisionSet)
    {s : State} (hin : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    ∃ s' t, Exec (wordSize 256 Q) (.seq gm06DualBuildProg gm06GapSingletonExhaustProg) s s' t ∧
      t ≤ 8000 * (40 * (Q + 2) ^ 2 + 2) ^ 22 ∧
      s'.arrs 0 = (gm06GapReduceSingletons X.discDualData).drawing.words ∧
      s'.arrs 47 = (gm06GapReduceSingletons X.discDualData).discGapWords ∧
      s'.arrs 42 = s.arrs 42 ∧ s'.regs 7000 = s.regs 7000 ∧ s'.regs 7001 = s.regs 7001 ∧
      s'.regs 9000 = s.regs 9000 ∧ s'.regs 9001 = s.regs 9001 ∧ s'.regs 9004 = s.regs 9004 := by
  have hcounts : X.drawing.n ≤ Q ∧ X.drawing.ends.length ≤ Q := by
    unfold GM06DrawingData.cellCount at hQ
    omega
  have hsize := gm06Size_le_of_sections Q X.drawing hcounts.1 hcounts.2 hr hc hd
  have hdualSize := gm06DiscDual_size_le_uniform Q X hQ hshape hR
  obtain ⟨s₁, t₁, he₁, ht₁, hi₁, hg₁, hq₁, hp₁, hend₁, _⟩ :=
    gm06DualBuildProg_exec_input X hshape hR hDiv (c := 21) (by decide) hin hgap
  have he₁' := he₁.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  have hdualShape := X.discDualData_disc_layout
    (by obtain ⟨L, R, hL, hR', hlen, _⟩ := hshape; exact ⟨L, R, hL, hR', hlen⟩) hR
  obtain ⟨s₂, t₂, he₂, ht₂, hi₂, hg₂, _, _⟩ :=
    gm06GapSingletonExhaustProg_exec_poly X.discDualData hdualShape hi₁ hg₁
  have he₂' := he₂.mono_wordSize (gm06Uniform_wordSize Q _ hdualSize)
  have hbase : 1 ≤ 40 * (Q + 2) ^ 2 + 2 := by omega
  have hpow₁ := (Nat.pow_le_pow_left (Nat.add_le_add_right hsize 2) 4).trans
    (Nat.pow_le_pow_right hbase (by decide : 4 ≤ 22))
  have hpow₂ := Nat.pow_le_pow_left (Nat.add_le_add_right hdualSize 2) 22
  have htime₁ := ht₁.trans (Nat.mul_le_mul_left 4000 hpow₁)
  have htime₂ := ht₂.trans (Nat.mul_le_mul_left 4000 hpow₂)
  refine ⟨s₂, t₁ + t₂, .seq he₁' he₂', by omega, hi₂, hg₂,
    (gm06GapSingletonExhaust_queue_frame he₂').trans hq₁,
    (gm06GapSingletonExhaust_driver_frame he₂' 7000 (by decide)).trans hp₁,
    (gm06GapSingletonExhaust_driver_frame he₂' 7001 (by decide)).trans hend₁, ?_, ?_, ?_⟩
  · exact (gm06GapSingletonExhaust_driver_frame he₂' 9000 (by decide)).trans
      (gm06DualBuild_driver_frame he₁' 9000 (by decide))
  · exact (gm06GapSingletonExhaust_driver_frame he₂' 9001 (by decide)).trans
      (gm06DualBuild_driver_frame he₁' 9001 (by decide))
  · exact (gm06GapSingletonExhaust_driver_frame he₂' 9004 (by decide)).trans
      (gm06DualBuild_driver_frame he₁' 9004 (by decide))

end GraphMinor.Compute
