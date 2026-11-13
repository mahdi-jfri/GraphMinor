module

public import GraphMinor.GM06.Alg511InitializeExec
import GraphMinor.Compute.GM06Alg511InputWordBounds
import Mathlib.Tactic

/-!
# A uniform cubic time bound for initial linkage preparation

For VI (5.11), page 134, the scans and target arithmetic have degree
at most two in the vertex count and supplied word length. Maximum
flow is cubic. The supplied input representation bounds all rows
and the path count by these sizes, giving one uniform cubic bound
for the full initial phase. Word bounds for signed input values
remain explicit in this execution statement.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

private theorem initialize_time_le (C k n len base E m : ℕ)
    (hk : k ≤ n) (hb : base ≤ len) (hE : E ≤ len) (hm : m ≤ len) :
    1717 + 66 * len + 110 * base + 25 * E + 194 * m +
      n * (168 + 13 * E + 26 * k) + 32 * k + C * (k + n + 1) ^ 3 ≤
        (3000 + 8 * C) * (n + len + 1) ^ 3 := by
  let N := n + len + 1
  have hN : 1 ≤ N := by omega
  have hnN : n ≤ N := by omega
  have hkN : k ≤ N := hk.trans hnN
  have heN : E ≤ N := by omega
  have hlin : 1717 + 66 * len + 110 * base + 25 * E + 194 * m + 168 * n + 32 * k ≤
      2400 * N := by omega
  have hquad : n * (13 * E + 26 * k) ≤ 39 * N ^ 2 := by
    calc
      _ ≤ N * (13 * N + 26 * N) := Nat.mul_le_mul hnN (by omega)
      _ = _ := by ring
  have hp₁ : N ≤ N ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hN (by decide : 1 ≤ 3)
  have hp₂ : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  have hflow : C * (k + n + 1) ^ 3 ≤ 8 * C * N ^ 3 := by
    calc
      _ ≤ C * (2 * N) ^ 3 := Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (by omega : k + n + 1 ≤ 2 * N) 3)
      _ = _ := by ring
  calc
    _ = (1717 + 66 * len + 110 * base + 25 * E + 194 * m + 168 * n + 32 * k) +
        n * (13 * E + 26 * k) + C * (k + n + 1) ^ 3 := by ring
    _ ≤ 2400 * N ^ 3 + 39 * N ^ 3 + 8 * C * N ^ 3 :=
      Nat.add_le_add (Nat.add_le_add (hlin.trans (Nat.mul_le_mul_left _ hp₁))
        (hquad.trans (Nat.mul_le_mul_left _ hp₂))) hflow
    _ ≤ (3000 + 8 * C) * N ^ 3 := by
      rw [show 2400 * N ^ 3 + 39 * N ^ 3 + 8 * C * N ^ 3 =
        (2439 + 8 * C) * N ^ 3 by ring]
      exact Nat.mul_le_mul_right _ (by omega)

/-- The initial phase of VI (5.11) runs from supplied instance words.
Failure proves infeasibility. Success yields a stored actual linkage
with its winding below the target in the computed orientation. -/
theorem alg511_initialize_polynomial :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder) (rep : GM06Alg511GraphTurnRep x G)
      (hG : IsCylinderSection5Drawing x.drawing.pathCount G), x.drawing.denominator ≠ 0 →
      ∀ (s : State) (w : ℕ), 3 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      x.drawing.pathCount < 2 ^ w → x.drawing.numerator.natAbs < 2 ^ w →
      x.drawing.denominator.natAbs < 2 ^ w →
      x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w →
      1 + 3 * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w →
      x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w →
      ∃ s' t, Exec (6 * w) gm06Alg511InitializeProg s s' t ∧
        t ≤ C * (x.drawing.vertexCount + (gm06Alg511SearchWords x).length + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 90 = 0 ∨ s'.regs 90 = 1) ∧
        (s'.regs 90 = 1 ↔
          (∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) ∧
          Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        (s'.regs 90 = 0 → ¬ IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
        (s'.regs 90 = 1 → ∃ (flip : Bool) (L : CylinderLinkage x.drawing.pathCount G),
          s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
          s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
          s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
          s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
          Nonempty (GM06Alg511GraphTurnRep (if flip then x.reflected else x)
            (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)) ∧
          gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
          gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
          (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
            (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)
              (gm06Alg511TargetValue s') ↔
                IsThetaFeasible x.drawing.pathCount G x.drawing.target) ∧
          (flip = false → L.HasTheta (gm06Alg511CurrentValue s')) ∧
          (flip = true → (section5ReflectedLinkage hG.1 L).HasTheta (gm06Alg511CurrentValue s')) ∧
          ∀ i : Fin x.drawing.pathCount, ∃ (b : Fin x.drawing.vertexCount)
            (W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i) b)
            (actual : GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val),
            W.support.map (fun v => v.val) = gm06Alg511SuccVertices x.drawing.vertexCount
              (s'.arrs outArr) x.drawing.vertexCount (rep.source i).val ∧
            gm06Alg511LabelWalkDarts rep.graph.pairs W =
              gm06Alg511ChosenDarts x.drawing (s'.arrs 1300) W.support ∧
            actual.support = W.support.map (fun v => (rep.graph.vertex v).val) ∧
            actual.edges = W.edges.map (fun e => (rep.graph.edge e).val) ∧
            L.pathDrawing i = walkDrawing G actual ∧
            ParametrizesSet (L.curve i) (walkDrawing G actual).U
              (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := alg511_initialize_exec
  refine ⟨3000 + 8 * C, c, by omega, hc, ?_⟩
  intro x G rep hG hden s w hw hwflow ha hn hwords hkfit hafit hdfit hprod hword hsquare hturnprod
  obtain ⟨s', t, he, ht, hrest⟩ := hrun x G rep hG hden s w hw hwflow ha hn hwords
    hkfit hafit hdfit hprod hword hsquare hturnprod
  have hfull : (gm06Alg511WindingWords x).length ≤ (gm06Alg511SearchWords x).length :=
    gm06Alg511_encoded_row_length_le (by simp [gm06Alg511SearchRows])
  have hbase : (gm06Alg511Words x.drawing).length ≤ (gm06Alg511SearchWords x).length :=
    (gm06Alg511_encoded_row_length_le (show gm06Alg511Words x.drawing ∈
      [gm06Alg511Words x.drawing, gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)] by simp)).trans hfull
  have hends : x.drawing.endpoints.length ≤ (gm06Alg511SearchWords x).length :=
    (gm06Alg511_encoded_row_length_le (rows := gm06Alg511Rows x.drawing)
      (by simp [gm06Alg511Rows])).trans hbase
  have hturns : x.edgeTurns.length ≤ (gm06Alg511SearchWords x).length :=
    (Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans
      ((gm06Alg511TurnWordCount_le_input x).trans hfull)
  exact ⟨s', t, he, ht.trans (initialize_time_le C _ _ _ _ _ _
    (rep.pathCount_le_vertexCount hG.1) hbase hends hturns), hrest⟩

end GraphMinor.GM06
