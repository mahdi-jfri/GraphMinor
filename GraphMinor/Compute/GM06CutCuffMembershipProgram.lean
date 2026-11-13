module

public import GraphMinor.Compute.GM06CutSearchGraph
public import GraphMinor.Compute.GM06CutComponentRowProgram
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Cuff-indexed component searches from the original linkage input

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes the
copied graph and finds each component through its inner cuff edge. This file
composes all graph-data, adjacency and cuff-search passes from the
original lists. Every endpoint and root bound is derived from those
lists. The result retains the common copied graph and exact component
membership rows for the induced component graphs.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exact cuff-order membership rows of the cut along a linkage. -/
def gm06CutCuffMembership (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) : List (List ℕ) :=
  gm06CutComponentBitsFrom (2 * n) (gm06CutDataOfLinkage n m origins paths inner outer rows live) m 0 inner.length

/-- Construct the cut graph, its search arrays, and all cuff membership rows. -/
def gm06CutCuffMembershipProg : Cmd := .seq gm06CutSearchGraphProg gm06CutComponentRowsProg

/-- All registers used by the complete cuff-membership construction. -/
def gm06CutCuffMembershipRegs : List ℕ := gm06CutSearchGraphRegs ++ gm06CutComponentRowsRegs

/-- All arrays used by the complete cuff-membership construction. -/
def gm06CutCuffMembershipArrs : List ℕ := gm06CutSearchGraphArrs ++ [600, 630, 631, 632, 633]

/-- Exact original-input-to-cuff-membership execution. The bound is
cubic in the input sizes, and no copied graph, adjacency list or
component root is supplied as an additional input. -/
theorem gm06CutCuffMembershipProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 4 * (m + inner.length + outer.length) + 3 < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hrows : rows.length = n) (hnd : rows.flatten.Nodup)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length))
    (hlive : ∀ v ∈ live, v < n) (hliveFit : 2 * live.length + 2 < 2 ^ w)
    (hpathCode : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hsearchFit : (2 * n) * (2 * n) + 2 < 2 ^ w)
    (hcomponentFit : 3 + inner.length * (2 * n + 1) < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h601 : s.arrs 601 = origins)
    (h608 : s.arrs 608 = gm06EncodeRows paths) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h618 : s.arrs 618 = live) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    ∃ sf t, Exec w gm06CutCuffMembershipProg s sf t ∧
      t ≤ 206 + 172 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) + 138 * live.length + 2 * (gm06EncodeRows rows).length +
        n * (6000 + 26 * (m + inner.length + outer.length)) + 6334 * rows.flatten.length +
        268 * (m + inner.length + outer.length) + 84 * (n * n) +
        inner.length * (91 + 80 * n + 116 * (n * n)) ∧
      Keeps gm06CutCuffMembershipRegs gm06CutCuffMembershipArrs s sf ∧
      (sf.arrs 625).take (sf.regs 658) = gm06EncodeRows data.rotations ∧
      sf.arrs 626 = data.origins ∧ sf.arrs 628 = data.activeDarts ∧ sf.arrs 629 = data.vertices ∧
      gm06CutComponentRowsResult sf = gm06EncodeRows (gm06CutCuffMembership n m origins paths inner outer rows live) := by
  dsimp only
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₁, ho₁, ha₁, hv₁, hn₁, hadj₁, hent₁⟩ := gm06CutSearchGraphProg_exec
    origins paths inner outer rows live s hw hn hsize horig hv hd hci hco hrows hnd hkeys hlive hliveFit
    hpathCode hpathWords hrotFit hrotWords hsearchFit h600 h601 h608 h609 h610 h618 h648 h649
  have hNword : 2 * n + 1 < 2 ^ w := by
    have hL := gm06FaceCode_length rows
    omega
  have horgLen := (gm06CutDataOfLinkage_sizes n m origins paths inner outer rows live).2.1
  have hvalues := gm06CutDataOfLinkage_origin_bounds origins paths inner outer rows live hrows horig hv hci hco
  obtain ⟨sf, tf, hef, htf, hkf, hout⟩ := gm06CutComponentRowsProg_exec data inner s₁ hw hNword hcomponentFit
    (by change data.origins.length = _ at horgLen; rw [horgLen]; omega)
    (fun i hi => gm06CutDataOfLinkage_inner_dart_bound origins paths inner outer rows live hi) hvalues
    ((hk₁.2 609 (by decide)).trans h609) hn₁ ((hk₁.1 649 (by decide)).trans h649) ho₁ hadj₁
    (by rw [hent₁]; omega)
  have hM := totalAdjEntries_le hadj₁.2
  have hper : 91 + 40 * (2 * n) + 29 * totalAdjEntries (gm06CutAdjacencyLists (2 * n) data) ≤
      91 + 80 * n + 116 * (n * n) := by nlinarith only [hM]
  have htime : tf ≤ 18 + inner.length * (91 + 80 * n + 116 * (n * n)) :=
    htf.trans (Nat.add_le_add_left (Nat.mul_le_mul_left inner.length hper) 18)
  refine ⟨sf, t₁ + tf, .seq he₁ hef, by omega,
    (hk₁.mono
      (by intro r hr; exact List.mem_append_left _ hr)
      (by intro a ha; exact List.mem_append_left _ ha)).trans hkf
      (by intro r hr; exact List.mem_append_right _ hr)
      (by simp [gm06CutCuffMembershipArrs]), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hkf.2 625 (by decide), hkf.1 658 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])]
    exact hr₁
  · exact (hkf.2 626 (by decide)).trans ho₁
  · exact (hkf.2 628 (by decide)).trans ha₁
  · exact (hkf.2 629 (by decide)).trans hv₁
  · exact hout

/-- Interpreting the computed cuff-order membership rows gives exactly
the components selected by the positive inner cuff edges. -/
theorem gm06CutCuffMembership_components (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    gm06DecodeCutComponentBitsFrom (2 * n) data m 0
        (gm06CutCuffMembership n m origins paths inner outer rows live) =
      gm06CutComponents (2 * n) m inner.length data := by
  dsimp only [gm06CutCuffMembership]
  rw [gm06DecodeCutComponentBitsFrom_eq]
  simp only [gm06CutComponents, ← List.range_eq_range']

end GraphMinor.Compute
