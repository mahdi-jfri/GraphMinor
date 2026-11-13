module

public import GraphMinor.Compute.GM06PhaseCore
public import GraphMinor.Compute.GM06CutAlongLinkageProgram

/-!
# Computing the cut components from the current core

Sections 9 and 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) start
with the current drawing arrays. This program loads those arrays and
runs the complete finite cut. Its output is exactly the component list
used by the pure Reduction 4 phase. Retired slots cause no problem:
their rotations are empty, and the cut retains permanent labels.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Load the current core and compute every cuff-indexed cut component. -/
def gm06PhaseCutProg : Cmd := .seq gm06PhaseLoadCoreProg gm06CutAlongLinkageProg

/-- Register frame of the complete current-core cut. -/
def gm06PhaseCutRegs : List ℕ := gm06PhaseLoadCoreRegs ++ gm06CutAlongLinkageRegs

/-- Array frame of the complete current-core cut. -/
def gm06PhaseCutArrs : List ℕ := gm06PhaseLoadCoreArrs ++ gm06CutAlongLinkageArrs

/-- Explicit cost of loading the current core and constructing its cut. -/
def gm06PhaseCutCost (x : GM06SuccessorInput) (m : ℕ) : ℕ :=
  41 + 13 * x.vertexCount + 14 *
    ((gm06EncodeRows x.rotations).length + x.endpoints.length +
      (gm06EncodeRows x.linkage).length + x.innerCuff.length + x.outerCuff.length) +
    gm06CutAlongLinkageCost x.vertexCount m (x.innerCuff.length + x.outerCuff.length)
      x.linkage.length x.linkage.flatten.length x.vertexCount
      (gm06EncodeRows x.rotations).length x.rotations.flatten.length x.innerCuff.length

/-- From the actual current-state arrays, compute the pure phase's
components with an explicit polynomial cost and the exact write frame.
Every premise concerns the input encoding or the word size. -/
theorem gm06PhaseCutProg_exec {w m : ℕ} (x : GM06SuccessorInput) (s : State)
    (hw : 4 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hsize : 4 * (m + x.innerCuff.length + x.outerCuff.length) + 3 < 2 ^ w)
    (horig : x.endpoints.length = 2 * m) (hv : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hd : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hci : ∀ v ∈ x.innerCuff, v < x.vertexCount) (hco : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hliveFit : 2 * x.vertexCount + 2 < 2 ^ w)
    (hpathCode : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (hpathWords : ∀ a ∈ gm06EncodeRows x.linkage, a < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows x.rotations).length < 2 ^ w)
    (hrotWords : ∀ a ∈ gm06EncodeRows x.rotations, a < 2 ^ w)
    (hsearchFit : (2 * x.vertexCount) * (2 * x.vertexCount) + 2 < 2 ^ w)
    (hcomponentFit : 3 + x.innerCuff.length * (2 * x.vertexCount + 1) < 2 ^ w)
    (hmaterialFit : 3 + x.innerCuff.length * (1 + 2 * (gm06EncodeRows x.rotations).length) < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount) (h12 : (s.arrs 12).length = m)
    (h4 : s.arrs 4 = gm06EncodeRows x.rotations) (h3 : s.arrs 3 = x.endpoints)
    (h8 : s.arrs 8 = gm06EncodeRows x.linkage) (h6 : s.arrs 6 = x.innerCuff) (h7 : s.arrs 7 = x.outerCuff) :
    ∃ sf t, Exec w gm06PhaseCutProg s sf t ∧ t ≤ gm06PhaseCutCost x m ∧
      Keeps gm06PhaseCutRegs gm06PhaseCutArrs s sf ∧
      gm06CutAlongLinkageResult sf = some (gm06PhaseComponents x m) := by
  have hm : m < 2 ^ w := by omega
  have hinner : x.innerCuff.length < 2 ^ w := by omega
  have houter : x.outerCuff.length < 2 ^ w := by omega
  have hfit : ∀ p ∈ gm06PhaseCoreCopies, (s.arrs p.1).length < 2 ^ w := by
    intro p hp
    simp only [gm06PhaseCoreCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · rw [h4]; omega
    · rw [h3, horig]; omega
    · rw [h8]; exact hpathCode
    · rw [h6]; exact hinner
    · rw [h7]; exact houter
  have hwords : ∀ p ∈ gm06PhaseCoreCopies, ∀ a ∈ s.arrs p.1, a < 2 ^ w := by
    intro p hp a ha
    simp only [gm06PhaseCoreCopies, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact hrotWords a (h4 ▸ ha)
    · exact (hv a (h3 ▸ ha)).trans hn
    · exact hpathWords a (h8 ▸ ha)
    · exact (hci a (h6 ▸ ha)).trans hn
    · exact (hco a (h7 ▸ ha)).trans hn
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, h600, h601, h608, h609, h610, h618, h648, h649⟩ :=
    gm06PhaseLoadCoreProg_exec x s (by omega) hn hm h100 h12 h4 h3 h8 h6 h7 hfit hwords
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06CutAlongLinkageProg_exec
    x.endpoints x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount) s₁
    hw hn hsize horig hv hd hci hco hrows hnd hkeys
    (fun _ h => List.mem_range.mp h) (by simpa only [List.length_range] using hliveFit)
    hpathCode hpathWords hrotFit hrotWords hsearchFit hcomponentFit hmaterialFit
    h600 h601 h608 h609 h610 h618 h648 h649
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_, ?_, hdf⟩
  · simpa only [gm06PhaseCutCost, List.length_range] using Nat.add_le_add ht₁ htf
  · exact (hk₁.mono (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_left _ h)).trans hkf
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_append_right _ h)

/-- A uniform cubic bound in the permanent current input sizes. -/
theorem gm06PhaseCutCost_le_polynomial (x : GM06SuccessorInput) (m : ℕ) :
    gm06PhaseCutCost x m ≤ 8100000 *
      (x.vertexCount + m + x.endpoints.length + x.innerCuff.length + x.outerCuff.length +
        x.linkage.length + x.linkage.flatten.length + (gm06EncodeRows x.rotations).length +
        x.rotations.flatten.length + 1) ^ 3 := by
  let N := x.vertexCount + m + x.endpoints.length + x.innerCuff.length + x.outerCuff.length +
    x.linkage.length + x.linkage.flatten.length + (gm06EncodeRows x.rotations).length +
    x.rotations.flatten.length + 1
  have hcut := gm06CutAlongLinkageCost_le_polynomial x.vertexCount m
    (x.innerCuff.length + x.outerCuff.length) x.linkage.length x.linkage.flatten.length
    x.vertexCount (gm06EncodeRows x.rotations).length x.rotations.flatten.length x.innerCuff.length
  have hcutSize : x.vertexCount + m + (x.innerCuff.length + x.outerCuff.length) + x.linkage.length +
      x.linkage.flatten.length + x.vertexCount + (gm06EncodeRows x.rotations).length +
      x.rotations.flatten.length + x.innerCuff.length + 1 ≤ 2 * N := by dsimp only [N]; omega
  have hcut' := hcut.trans (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hcutSize 3))
  have hpath := gm06FaceCode_length x.linkage
  have hlinear : 41 + 13 * x.vertexCount + 14 *
      ((gm06EncodeRows x.rotations).length + x.endpoints.length +
        (gm06EncodeRows x.linkage).length + x.innerCuff.length + x.outerCuff.length) ≤ 100 * N := by
    dsimp only [N]
    omega
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hcube : N ≤ N ^ 3 := by
    calc
      N = N * 1 * 1 := by omega
      _ ≤ N * N * N := Nat.mul_le_mul (Nat.mul_le_mul_left N hN) hN
      _ = N ^ 3 := by ring
  have hcube2 : (2 * N) ^ 3 = 8 * N ^ 3 := by ring
  rw [hcube2] at hcut'
  unfold gm06PhaseCutCost
  change _ ≤ 8100000 * N ^ 3
  omega

end GraphMinor.Compute
