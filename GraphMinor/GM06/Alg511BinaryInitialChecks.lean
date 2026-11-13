module

public import GraphMinor.Compute.GM06Alg511BinarySearchInput
public import GraphMinor.GM06.Alg511BinaryInputRep
import GraphMinor.GM06.Alg511CuffIndices
import GraphMinor.GM06.Alg511FlowLinkage
import GraphMinor.GM06.Alg511FlowOfLinkage
import GraphMinor.GM06.Section5Feasibility
import Mathlib.Tactic

/-!
# The two initial checks on actual binary cylinder input

The complete input retains the binary drawing row and repeats its
ordinary labelled graph/cuff layout for maximum flow. Equality of
these supplied words still determines feasibility. The verified
binary initial-check program returns exactly target integrality
and existence of an actual cylinder linkage. The two established
path transfers identify the finite flow family with such a linkage.
By VI (5.10), failure of either check rules out the target.

The time bound counts the complete input length, including all
integer bits and isolated vertices. This proves the first two
checks of VI (5.11), page 134, without magnitude word assumptions.
-/

@[expose] public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The search input size counts every supplied word and all
vertices, including isolated vertices not listed as edge ends. -/
def alg511BinarySearchInputSize (x : GM06Alg511BinaryInput) : ℕ :=
  x.vertexCount + (gm06Alg511BinarySearchWords x).length

/-- The repeated ordinary flow layout retains the exact answer
determined by the original binary drawing input and its labels. -/
theorem alg511_binary_search_words_feasible_iff {x y : GM06Alg511BinaryInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G)
    (rep' : GM06Alg511BinaryDrawingRep y H) (hk : 0 < x.pathCount)
    (hwords : gm06Alg511BinarySearchWords x = gm06Alg511BinarySearchWords y) :
    IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target ↔
      IsThetaFeasible y.pathCount H y.toWindingInput.drawing.target := by
  have heq := gm06Alg511BinarySearchWords_injective hwords
  subst y
  exact alg511_binary_words_feasible_iff rep rep' hk rfl

private theorem initial_time_le (C k n bits len a : ℕ)
    (hk : k ≤ n) (hbits : bits ≤ n + len)
    (ha : a ≤ 4000 + 500 * len + 2700 * (k + bits + 2) ^ 2 + C * (k + n + 1) ^ 3) :
    a ≤ (30000 + 8 * C) * (n + len + 1) ^ 3 := by
  let N := n + len + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn : n ≤ N := by dsimp only [N]; omega
  have hl : len ≤ N := by dsimp only [N]; omega
  have hsum : k + bits + 2 ≤ 2 * N := by dsimp only [N]; omega
  have hflow : k + n + 1 ≤ 2 * N := by dsimp only [N]; omega
  have hsquare := Nat.pow_le_pow_left hsum 2
  have hcube := Nat.pow_le_pow_left hflow 3
  have hp₁ : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  have hp₂ : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  have hflow' : C * (k + n + 1) ^ 3 ≤ 8 * C * N ^ 3 := by
    calc
      _ ≤ C * (2 * N) ^ 3 := Nat.mul_le_mul_left C hcube
      _ = _ := by ring
  change a ≤ (30000 + 8 * C) * N ^ 3
  nlinarith only [ha, hsquare, hflow', hp₁, hp₂, hl, hN]

/-- On every intended drawing, the actual binary checks return
exactly (5.10)(i) and (ii), retain all supplied tables and provide
an actual path-system certificate on success. Their time is cubic
in the complete input length. Every resource premise concerns
code lengths, graph counts and binary digit counts. -/
theorem alg511_binary_initialChecks_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (G : Drawing ClosedCylinder)
      (_rep : GM06Alg511BinaryDrawingRep x G), IsCylinderSection5Drawing x.pathCount G →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w →
      x.pathCount + x.numerator.digits.length + x.denominator.digits.length + 4 < 2 ^ w →
      wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ word ∈ gm06Alg511BinarySearchWords x, word < 2 ^ w) →
      ∃ t u, Exec w gm06Alg511BinaryInitialChecksProg s t u ∧
        u ≤ C * (alg511BinarySearchInputSize x + 1) ^ 3 ∧
        gm06Alg511BinaryLoadedTables x t ∧ t.regs 52 = x.pathCount ∧ t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔ (∃ m : ℤ, (x.pathCount : ℝ) * x.toWindingInput.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.pathCount G)) ∧
        (t.regs 0 = 0 → ¬ IsThetaFeasible x.pathCount G x.toWindingInput.drawing.target) ∧
        (t.regs 0 = 1 →
          IsValidPathSystem x.toWindingInput.drawing.flowGraph
            x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B
            (decUsed x.vertexCount (t.arrs outArr)) (decPred x.vertexCount (t.arrs outArr)) (decSucc x.vertexCount (t.arrs outArr)) ∧
          (pathStarts (decUsed x.vertexCount (t.arrs outArr)) (decPred x.vertexCount (t.arrs outArr))).card = x.pathCount ∧
          (t.arrs outArr).length = 1 + 3 * x.vertexCount) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := gm06Alg511BinaryInitialChecksProg_exec
  refine ⟨30000 + 8 * C, c, by omega, hc, ?_⟩
  intro x G rep hG s w hw hfit hsize hwflow hinput hwords
  obtain ⟨t, u, he, ht, htables, hk, hbit, hiff, hpath⟩ := hrun x s w rep.denominator_ne_zero hw hfit hsize hwflow hinput hwords
  have hgeom : (∃ P : Fin x.pathCount → ABWalk x.toWindingInput.drawing.flowGraph
      x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B,
        PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ↔ Nonempty (CylinderLinkage x.pathCount G) := by
    constructor
    · rintro ⟨P, hdisj, hsimple⟩
      exact alg511_exists_linkage_of_flowPaths x.toWindingInput.drawing rep.graphTurn.graph rep.graphTurn.source
        rep.graphTurn.flowA_exists_source rep.graphTurn.source_point
        (fun b hb => (rep.graphTurn.outer_mem_iff b).mp (Finset.mem_filter.mp hb).2) P hdisj hsimple
    · rintro ⟨L⟩
      exact alg511_exists_flowPaths_of_linkage x.toWindingInput.drawing rep.graphTurn.graph
        rep.graphTurn.inner_mem_iff rep.graphTurn.outer_mem_iff L
  have hpass : t.regs 0 = 1 ↔ (∃ m : ℤ, (x.pathCount : ℝ) * x.toWindingInput.drawing.target = m) ∧
      Nonempty (CylinderLinkage x.pathCount G) := by
    rw [hiff, hgeom]
    rfl
  have hkn : x.pathCount ≤ x.vertexCount := rep.graphTurn.pathCount_le_vertexCount hG.1
  have htargetBits : x.numerator.digits.length + x.denominator.digits.length ≤
      x.vertexCount + (gm06Alg511BinarySearchWords x).length := by
    have hbits := alg511_binary_target_size_le x
    have hlen := gm06Alg511BinarySearchWords_length x
    simp only [alg511BinaryInputSize, GM06Alg511BinaryInteger.words_eq, List.length_cons, List.length_map] at hbits
    omega
  refine ⟨t, u, he, initial_time_le C x.pathCount x.vertexCount
    (x.numerator.digits.length + x.denominator.digits.length) (gm06Alg511BinarySearchWords x).length u hkn htargetBits
      (by simpa only [Nat.add_assoc] using ht), htables, hk, hbit, hpass, ?_, hpath⟩
  intro hz hfeas
  have hnecessary := (theorem_5_10_proof x.pathCount G x.toWindingInput.drawing.target hG).mp hfeas
  have hone := hpass.mpr ⟨hnecessary.1, hnecessary.2.1⟩
  omega

end GraphMinor.GM06
