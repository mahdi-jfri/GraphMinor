module

public import GraphMinor.Compute.GM06Reduction4PhaseProgram
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Reading both path boundaries for a component search

Sections 12 and 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) use
one left path and the next right path. This pass reads both from
the saved current linkage, including the cyclic wrap when there is
one path. It computes the copied vertex rows and left edge labels
and preserves the selected face, incidence and component rotations.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Registers used while reading the two current path boundaries. -/
def gm06PhaseLoadBoundariesRegs : List ℕ :=
  [688, 695, 661, 665, 660, 662, 664, 650, 651, 652, 655]

/-- Saved path rows, append scratch and the three boundary outputs. -/
def gm06PhaseLoadBoundariesArrs : List ℕ := [645, 646, 617, 618, 609, 610, 608]

private theorem path_row_length_le_code (paths : List (List ℕ)) {i : ℕ} (hi : i < paths.length) :
    paths[i].length ≤ (gm06EncodeRows paths).length := by
  have hs : [paths[i]].Sublist paths := List.singleton_sublist.mpr (List.getElem_mem hi)
  have hl : paths[i].length ≤ paths.flatten.length := by simpa using hs.flatten.length_le
  have hc := gm06FaceCode_length paths
  omega

/-- The current linkage supplies exactly the left vertices, right
vertices and left edges used by the pure component search. Every
array and register outside the stated frame is preserved. -/
theorem gm06PhaseLoadBoundariesProg_exec {w m i : ℕ} (x : GM06SuccessorInput) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * x.vertexCount < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length) (hi : i < x.innerCuff.length)
    (hfit : (gm06EncodeRows x.linkage).length + 3 < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeRows x.linkage, a < 2 ^ w)
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h642 : s.arrs 642 = gm06EncodeRows x.linkage)
    (h681 : s.regs 681 = i) (h685 : s.regs 685 = x.innerCuff.length) :
    ∃ sf t, Exec w gm06PhaseLoadBoundariesProg s sf t ∧
      t ≤ 400 + 500 * (gm06EncodeRows x.linkage).length ∧
      Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s sf ∧
      sf.arrs 609 = gm06PhaseBoundaryVertices x i 0 ∧
      sf.arrs 608 = gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1 ∧
      sf.arrs 610 = (gm06PhaseLeftSteps x i).map Prod.fst := by
  have hk : 0 < x.innerCuff.length := by omega
  have hik : i < x.linkage.length := by omega
  have hc := gm06FaceCode_length x.linkage
  have hkw : x.innerCuff.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let next := gm06PhaseNext x i
  have hnext : next < x.innerCuff.length := Nat.mod_lt _ hk
  have hnextPath : next < x.linkage.length := by omega
  have hl := path_row_length_le_code x.linkage hik
  have hu := path_row_length_le_code x.linkage hnextPath
  have hleft : ∀ d ∈ x.linkage[i], d < 2 * m := fun d hd => hdarts d
    (List.mem_flatten.mpr ⟨x.linkage[i], List.getElem_mem hik, hd⟩)
  have hupper : ∀ d ∈ x.linkage[next], d < 2 * m := fun d hd => hdarts d
    (List.mem_flatten.mpr ⟨x.linkage[next], List.getElem_mem hnextPath, hd⟩)
  let s₀ := s.setReg 688 i
  have he₀ : Exec w (.assign 688 (.reg 681)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h681 (hi.trans hkw))
  have hk₀ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₀ :=
    (Keeps.refl _ _ s).setReg (by simp [gm06PhaseLoadBoundariesRegs]) _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hp₁⟩ := gm06PhaseSelectRowProg_exec 642 645
    (by decide) (by decide) (by decide) (by decide) (by decide) x.linkage s₀ hw1 hik
    (by simpa only [s₀, State.setReg_arrs] using h642) (by omega) hwords (by simp [s₀])
  have hk₀₁ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₁ :=
    hk₀.trans hk₁ (by simp [gm06PhaseLoadBoundariesRegs]) (by simp [gm06PhaseLoadBoundariesArrs])
  let s₂ := s₁.setReg 695 x.innerCuff[i]
  have he₂ : Exec w (.assign 695 (.read 6 (.reg 688))) s₁ s₂ 3 := .assign (by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 6)
      (GraphMinor.Compute.Crossing.eval_reg (w := w)
        ((hk₁.1 688 (by decide)).trans (by simp [s₀])) (hi.trans hkw))
      (by simpa only [hk₀₁.2 6 (by decide), h6] using hi)
      (by simpa only [hk₀₁.2 6 (by decide), h6] using
        (hinner _ (List.getElem_mem hi)).trans (by omega : x.vertexCount < 2 ^ w))
    simpa only [hk₀₁.2 6 (by decide), h6] using he)
  have hk₀₂ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₂ :=
    hk₀₁.setReg (by simp [gm06PhaseLoadBoundariesRegs]) _
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hp₃⟩ := gm06PhaseBoundaryRowProg_exec 645 609
    (by decide) (by decide) (by decide) (by decide) x.endpoints x.linkage[i] s₂ hw hn hm horig hvalues
    hleft (hinner _ (List.getElem_mem hi)) (by decide : 0 ≤ 1) (by omega)
    ((hk₀₂.2 3 (by decide)).trans h3) (by simpa only [s₂, State.setReg_arrs] using hp₁) (by simp [s₂])
  have hk₀₃ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₃ :=
    hk₀₂.trans hk₃ (by simp [gm06PhaseLoadBoundariesRegs]) (by simp [gm06PhaseLoadBoundariesArrs])
  have h645 : s₃.arrs 645 = x.linkage[i] := (hk₃.2 645 (by decide)).trans
    (by simpa only [s₂, State.setReg_arrs] using hp₁)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hp₄⟩ := gm06PhaseLeftEdgesProg_exec 645 (by decide)
    x.linkage[i] s₃ hw hm hleft (by omega) h645
  have hk₀₄ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₄ :=
    hk₀₃.trans hk₄ (by simp [gm06PhaseLoadBoundariesRegs]) (by simp [gm06PhaseLoadBoundariesArrs])
  let s₅ := s₄.setReg 688 next
  have he₅ : Exec w (.assign 688 (.op .mod (.op .add (.reg 681) (.const 1)) (.reg 685))) s₄ s₅ 6 :=
    .assign (GraphMinor.Compute.Crossing.eval_mod
      (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk₀₄.1 681 (by decide)).trans h681) (hi.trans hkw))
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega))
      (GraphMinor.Compute.Crossing.eval_reg ((hk₀₄.1 685 (by decide)).trans h685) hkw) hk)
  have hk₀₅ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₅ :=
    hk₀₄.setReg (by simp [gm06PhaseLoadBoundariesRegs]) _
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, hp₆⟩ := gm06PhaseSelectRowProg_exec 642 646
    (by decide) (by decide) (by decide) (by decide) (by decide) x.linkage s₅ hw1 hnextPath
    ((hk₀₅.2 642 (by decide)).trans h642) (by omega) hwords (by simp [s₅])
  have hk₀₆ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₆ :=
    hk₀₅.trans hk₆ (by simp [gm06PhaseLoadBoundariesRegs]) (by simp [gm06PhaseLoadBoundariesArrs])
  let s₇ := s₆.setReg 695 x.innerCuff[next]
  have he₇ : Exec w (.assign 695 (.read 6 (.reg 688))) s₆ s₇ 3 := .assign (by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 6)
      (GraphMinor.Compute.Crossing.eval_reg (w := w)
        ((hk₆.1 688 (by decide)).trans (by simp [s₅])) (hnext.trans hkw))
      (by simpa only [hk₀₆.2 6 (by decide), h6] using hnext)
      (by simpa only [hk₀₆.2 6 (by decide), h6] using
        (hinner _ (List.getElem_mem hnext)).trans (by omega : x.vertexCount < 2 ^ w))
    simpa only [hk₀₆.2 6 (by decide), h6] using he)
  have hk₀₇ : Keeps gm06PhaseLoadBoundariesRegs gm06PhaseLoadBoundariesArrs s s₇ :=
    hk₀₆.setReg (by simp [gm06PhaseLoadBoundariesRegs]) _
  obtain ⟨sf, tf, hef, htf, hkf, hpf⟩ := gm06PhaseBoundaryRowProg_exec 646 608
    (by decide) (by decide) (by decide) (by decide) x.endpoints x.linkage[next] s₇ hw hn hm horig hvalues
    hupper (hinner _ (List.getElem_mem hnext)) (by decide : 1 ≤ 1) (by omega)
    ((hk₀₇.2 3 (by decide)).trans h3) (by simpa only [s₇, State.setReg_arrs] using hp₆) (by simp [s₇])
  have hleftOut : sf.arrs 609 = gm06PhaseBoundaryRow x.endpoints x.linkage[i] x.innerCuff[i] 0 :=
    (hkf.2 609 (by decide)).trans ((hk₆.2 609 (by decide)).trans ((hk₄.2 609 (by decide)).trans hp₃))
  have hedgeOut : sf.arrs 610 = (x.linkage[i]).map (fun d => 2 * (d / 2)) :=
    (hkf.2 610 (by decide)).trans ((hk₆.2 610 (by decide)).trans hp₄)
  refine ⟨sf, 2 + (t₁ + (3 + (t₃ + (t₄ + (6 + (t₆ + (3 + tf))))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ hef))))))),
    by omega, hk₀₇.trans hkf (by simp [gm06PhaseLoadBoundariesRegs]) (by simp [gm06PhaseLoadBoundariesArrs]), ?_, ?_, ?_⟩
  · simpa only [gm06PhaseBoundaryRow, gm06PhaseBoundaryVertices, List.getElem?_eq_getElem hik,
      List.getElem?_eq_getElem hi, Option.getD_some] using hleftOut
  · simpa only [gm06PhaseBoundaryRow, gm06PhaseBoundaryVertices, next, List.getElem?_eq_getElem hnextPath,
      List.getElem?_eq_getElem hnext, Option.getD_some] using hpf
  · simpa only [gm06PhaseLeftSteps, List.getElem?_eq_getElem hik, Option.getD_some, List.map_map, Function.comp_def] using hedgeOut

end GraphMinor.Compute
