module

public import GraphMinor.Compute.GM06PhaseRows
public import GraphMinor.Compute.GM06CutFaceInput
public import GraphMinor.Compute.GM06CutOriginProgram
public import GraphMinor.Compute.GM06CutActiveProgram

/-!
# Preparing a component for the selected-face scan

Sections 9 and 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
select the face at a reverse inner cuff dart in each computed component.
This pass reads a stored component rotation record, constructs its
active darts, restores the shared permanent origin table, and runs
the complete face and incidence computation. No active list or
selected face is supplied in scratch memory.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Build active ends from component rotations, then compute incidence.
The common origin table is retained in array 641 by the enclosing phase. -/
def gm06PhaseComponentFacesProg : Cmd :=
  .seq gm06CutOriginProg
    (.seq (gm06PhaseCopyProg 641 626)
      (.seq gm06CutActiveProg
        (.seq (gm06PhaseCopyProg 628 604)
          (.seq (gm06PhaseCopyProg 625 600) gm06CutFaceIncidenceProg))))

/-- Registers used before the face scan. -/
def gm06PhaseComponentPrepRegs : List ℕ := gm06CutOriginRowsRegs ++ [650, 651, 652, 653]

/-- Register frame for component preparation and selected incidence. -/
def gm06PhaseComponentFacesRegs : List ℕ :=
  gm06PhaseComponentPrepRegs ++ (667 :: gm06SelectedIncidenceRegs)

/-- Array frame for component preparation and selected incidence. -/
def gm06PhaseComponentFacesArrs : List ℕ :=
  [611, 626, 627, 620, 621, 628, 600, 601, 602, 603, 604, 605, 606, 607]

/-- Exact component-to-incidence execution. Active ends use increasing
permanent label order, which is part of the component record format.
The other premises are the finite rotation encoding and word bounds. -/
theorem gm06PhaseComponentFacesProg_exec {w n aug base i : ℕ} (data : GM06CutData) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + 8 * aug < 2 ^ w)
    (hnd : data.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ data.rotations.flatten, d < 4 * aug)
    (hcanon : data.activeDarts = (List.range (4 * aug)).filter (fun d => decide (d ∈ data.rotations.flatten)))
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (horig : data.origins.length = 4 * aug) (hvalues : ∀ v ∈ data.origins, v < n)
    (hquery : 4 * (base + i) + 1 < 4 * aug)
    (hcode : (gm06EncodeRows data.rotations).length < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeRows data.rotations, a < 2 ^ w)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations) (h641 : s.arrs 641 = data.origins)
    (h647 : s.regs 647 = 4 * aug) (h648 : s.regs 648 = n) (h649 : s.regs 649 = 2 * aug)
    (h672 : s.regs 672 = base) (h673 : s.regs 673 = i) :
    ∃ sf t, Exec w gm06PhaseComponentFacesProg s sf t ∧
      t ≤ 300 + n + 1300 * aug + 100 * data.rotations.length +
        100 * data.rotations.flatten.length +
        data.activeDarts.length * (60 + 72 * aug) ∧
      Keeps gm06PhaseComponentFacesRegs gm06PhaseComponentFacesArrs s sf ∧
      gm06SelectedIncidenceResult sf = gm06CutFaceIncidence n (2 * aug) data (4 * (base + i) + 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have h4 : 4 * aug < 2 ^ w := by omega
  have hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten := by
    intro d
    rw [hcanon, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact and_iff_right_of_imp (hkeys d)
  have hactive : ∀ d ∈ data.activeDarts, d < 4 * aug := fun d hd => hkeys d ((hcover d).mp hd)
  have hactiveLen : data.activeDarts.length ≤ 4 * aug := by
    rw [hcanon]
    exact (List.length_filter_le _ _).trans (by simp)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, _, hb₁⟩ := gm06CutOriginProg_exec data.rotations [] s hw1 h4 hkeys
    (by simpa only [List.append_nil] using h625) (by rw [h625]; exact hcode)
    (by rw [h625]; exact hwords) h647
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, ho₂⟩ := gm06PhaseCopyProg_exec 641 626 (by decide) data.origins s₁ hw1
    (by rw [horig]; exact h4) (fun a ha => (hvalues a ha).trans hn) ((hk₁.2 641 (by decide)).trans h641)
  have hk₁₂ : Keeps gm06PhaseComponentPrepRegs gm06PhaseComponentFacesArrs s s₂ :=
    (hk₁.mono (fun _ h => List.mem_append_left _ h) (by simp [gm06PhaseComponentFacesArrs])).trans hk₂
      (by simp [gm06PhaseComponentFacesRegs, gm06PhaseComponentPrepRegs]) (by simp [gm06PhaseComponentFacesArrs])
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, ha₃⟩ := gm06CutActiveProg_exec data.rotations.flatten s₂ hw1 (by omega)
    ((hk₁₂.1 647 (by simp [gm06PhaseComponentPrepRegs, gm06CutOriginRowsRegs])).trans h647)
    ((hk₂.2 627 (by decide)).trans hb₁)
  have ha₃' : s₃.arrs 628 = data.activeDarts := ha₃.trans hcanon.symm
  have hactiveWords : ∀ a ∈ data.activeDarts, a < 2 ^ w := fun a ha => (hactive a ha).trans h4
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, ha₄⟩ := gm06PhaseCopyProg_exec 628 604 (by decide) data.activeDarts s₃ hw1
    (hactiveLen.trans_lt h4) hactiveWords ha₃'
  have h625' : s₄.arrs 625 = gm06EncodeRows data.rotations :=
    (hk₄.2 625 (by decide)).trans ((hk₃.2 625 (by decide)).trans
      ((hk₂.2 625 (by decide)).trans ((hk₁.2 625 (by decide)).trans h625)))
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hr₅⟩ := gm06PhaseCopyProg_exec 625 600 (by decide)
    (gm06EncodeRows data.rotations) s₄ hw1 hcode hwords h625'
  have hk₂₅ : Keeps gm06PhaseComponentPrepRegs gm06PhaseComponentFacesArrs s₂ s₅ :=
    ((hk₃.mono (by simp [gm06PhaseComponentFacesRegs, gm06PhaseComponentPrepRegs]) (by simp [gm06PhaseComponentFacesArrs])).trans hk₄
      (by simp [gm06PhaseComponentFacesRegs, gm06PhaseComponentPrepRegs]) (by simp [gm06PhaseComponentFacesArrs])).trans hk₅
      (by simp [gm06PhaseComponentFacesRegs, gm06PhaseComponentPrepRegs]) (by simp [gm06PhaseComponentFacesArrs])
  have hk₀₅ := hk₁₂.trans hk₂₅ (fun _ h => h) (fun _ h => h)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06CutFaceIncidenceProg_exec (n := n) (m := 2 * aug) data s₅
    hw hn (by omega) hnd (by intro d hd; have := hkeys d hd; omega)
    (by intro d hd; have := hactive d hd; omega) hcover hpair (by omega) hvalues
    (by omega) hcode hwords (hactiveLen.trans_lt h4) hr₅ ((hk₅.2 604 (by decide)).trans ha₄)
    ((hk₅.2 626 (by decide)).trans ((hk₄.2 626 (by decide)).trans ((hk₃.2 626 (by decide)).trans ho₂)))
    ((hk₀₅.1 648 (by simp [gm06PhaseComponentPrepRegs, gm06CutOriginRowsRegs])).trans h648)
    ((hk₀₅.1 649 (by simp [gm06PhaseComponentPrepRegs, gm06CutOriginRowsRegs])).trans h649)
    ((hk₀₅.1 672 (by simp [gm06PhaseComponentPrepRegs, gm06CutOriginRowsRegs])).trans h672)
    ((hk₀₅.1 673 (by simp [gm06PhaseComponentPrepRegs, gm06CutOriginRowsRegs])).trans h673)
  refine ⟨sf, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + tf)))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ hef)))), ?_, ?_, hdf⟩
  · have hlength := gm06FaceCode_length data.rotations
    rw [horig] at ht₂
    nlinarith only [ht₁, ht₂, ht₃, ht₄, ht₅, htf, hlength]
  · exact (hk₀₅.mono (fun _ h => List.mem_append_left _ h) (fun _ h => h)).trans hkf (fun _ h => List.mem_append_right _ h) (by simp [gm06PhaseComponentFacesArrs])

/-- Restoring the shared origins is an actual postcondition of the
component-face command, including when the queried face is absent. -/
theorem gm06PhaseComponentFacesProg_origins {w t : ℕ} (origins : List ℕ) (s sf : State)
    (hw : 1 < 2 ^ w) (hlen : origins.length < 2 ^ w) (hwords : ∀ a ∈ origins, a < 2 ^ w)
    (h641 : s.arrs 641 = origins) (he : Exec w gm06PhaseComponentFacesProg s sf t) :
    sf.arrs 626 = origins := by
  cases he with
  | seq hfirst hrest =>
    have hsource := (hfirst.arrs_eq_of_not_mem_writtenArrs (a := 641) (by decide)).trans h641
    cases hrest with
    | seq hcopy hafter =>
      obtain ⟨sc, tc, hc, _, _, hout⟩ := gm06PhaseCopyProg_exec 641 626 (by decide) origins _ hw hlen hwords hsource
      have hsame := (hc.deterministic hcopy).1
      rw [hsame] at hout
      exact (hafter.arrs_eq_of_not_mem_writtenArrs (a := 626) (by decide)).trans hout

end GraphMinor.Compute
