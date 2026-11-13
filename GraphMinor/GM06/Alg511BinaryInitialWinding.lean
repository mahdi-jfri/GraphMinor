module

public import GraphMinor.GM06.Alg511BinaryStoredPaths
public import GraphMinor.GM06.Alg511BinaryFirstWinding
public import GraphMinor.GM06.Alg511BinaryInitialChecks
import Mathlib.Tactic

/-!
# The complete initial binary winding phase

Start with the raw successful maximum-flow path system and the
retained supplied binary input. Compute all selected edges, store
an actual linkage in ordinary path rows and execute its first-path
binary winding calculation. The same actual linkage is retained
throughout, and every original drawing and target row survives.

The time is cubic in the complete supplied input length. This
composition is the initial winding phase of VI (5.11), page 134.
It has no winding or turn magnitude word bound and receives no
preselected linkage or paths as part of the input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Store the initial flow linkage and compute its winding as a
signed binary numerator over the ordinary graph path count. -/
def gm06Alg511BinaryInitialWindingProg : Cmd :=
  .seq gm06Alg511BinaryStoredPathsProg gm06Alg511BinaryFirstWindingProg

end GraphMinor.Compute

namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Compute.TwoPaths GraphMinor.Surface

private theorem initial_winding_time (k n E O turn len a b : ℕ)
    (hk : k ≤ n) (hE : E ≤ len) (hO : O ≤ len) (hturn : turn ≤ len)
    (ha : a ≤ 48 + 37 * E + 12 * O + n * (38 + 13 * E) +
      k * (208 + 150 * n + 100 * (1 + k + k * n)))
    (hb : b ≤ 20000 * (k + n + turn + 5) ^ 2) :
    a + b ≤ 1000000 * (n + len + 1) ^ 3 := by
  let N := n + len + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn : n ≤ N := by dsimp only [N]; omega
  have hkN : k ≤ N := hk.trans hn
  have hEN : E ≤ N := hE.trans (by dsimp only [N]; omega)
  have hON : O ≤ N := hO.trans (by dsimp only [N]; omega)
  have ha' : a ≤ 48 + 37 * N + 12 * N + N * (38 + 13 * N) +
      N * (208 + 150 * N + 100 * (1 + N + N * N)) := by
    apply ha.trans
    gcongr
  have hsum : k + n + turn + 5 ≤ 5 * N := by dsimp only [N]; omega
  have hb' : b ≤ 500000 * N ^ 2 := by
    calc
      b ≤ 20000 * (k + n + turn + 5) ^ 2 := hb
      _ ≤ 20000 * (5 * N) ^ 2 := Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have h₁ : N ≤ N ^ 3 := Nat.le_self_pow (by decide) N
  have h₂ : N ^ 2 ≤ N ^ 3 := Nat.pow_le_pow_right hN (by decide)
  change a + b ≤ 1000000 * N ^ 3
  nlinarith only [ha', hb', hN, h₁, h₂]

/-- The raw maximum-flow output is converted to a stored actual
linkage and its exact binary winding. All drawing, target and turn
input rows survive, and the complete phase has cubic input-length
time. Its path-system premises are the certified output of the
preceding executed maximum-flow check. -/
theorem alg511_binary_initialWinding_exec {w : ℕ} (x : GM06Alg511BinaryInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511BinaryDrawingRep x G) (hk : 0 < x.pathCount)
    (out : List ℕ)
    (hsys : IsValidPathSystem x.toWindingInput.drawing.flowGraph
      x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B
      (decUsed x.vertexCount out) (decPred x.vertexCount out) (decSucc x.vertexCount out))
    (hcount : (pathStarts (decUsed x.vertexCount out) (decPred x.vertexCount out)).card = x.pathCount)
    (s : State) (hw : 3 < 2 ^ w) (hword : 1 + 3 * x.vertexCount < 2 ^ w)
    (hsquare : x.vertexCount * x.vertexCount < 2 ^ w) (hends : x.endpoints.length < 2 ^ w)
    (hcap : 1 + x.pathCount + x.pathCount * x.vertexCount < 2 ^ w)
    (hsize : 2 * x.pathCount + x.vertexCount +
      2 * (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 10 < 2 ^ w)
    (hlen : out.length = 1 + 3 * x.vertexCount) (hout : s.arrs outArr = out)
    (htables : gm06Alg511BinaryLoadedTables x s) (hkReg : s.regs 52 = x.pathCount) :
    ∃ (t : State) (u : ℕ) (L : CylinderLinkage x.pathCount G) (rows : List (List ℕ)) (digits : List ℕ) (sign : ℕ),
      Exec w gm06Alg511BinaryInitialWindingProg s t u ∧
      u ≤ 1000000 * (alg511BinarySearchInputSize x + 1) ^ 3 ∧
      gm06Alg511BinaryLoadedTables x t ∧ t.regs 52 = x.pathCount ∧ t.arrs 8 = gm06EncodeRows rows ∧
      GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows ∧
      t.arrs 2804 = sign :: digits ∧ sign < 2 ∧
      digits.length ≤ 2 * x.pathCount + x.vertexCount +
        (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 3 ∧
      (∀ d ∈ digits, d < 2) ∧ L.HasTheta ((gm06Alg511BinaryRowValue (t.arrs 2804) : ℝ) / x.pathCount) ∧ t.regs 90 = s.regs 90 := by
  obtain ⟨s₁, u₁, L, rows, b, W, actual, he₁, ht₁, htables₁, hk₁, hN₁, hout₁, houter₁, hrows₁, henc,
    hfirst, hb, hbB, hs, hturn, hparam, hsuccess₁⟩ := alg511_binary_storedPaths_exec x rep hk out hsys hcount s (by omega)
      hword hsquare hends hcap hlen hout htables hkReg
  have hinner₁ : s₁.arrs 1210 = x.toWindingInput.drawing.innerCuff := htables₁.1 ⟨3, by decide⟩
  have hturns₁ : s₁.arrs 2900 = gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words) := htables₁.1 ⟨8, by decide⟩
  obtain ⟨t, u₂, digits, sign, he₂, ht₂, hrow, hsign, hlenDigits, hbits, htheta, hk₂, harr₂, hsuccess₂⟩ :=
    alg511_binary_firstWinding_exec x.toWindingInput rep.graphTurn x.edgeTurns rfl hk out hsys hcount L rows henc
      b W actual hfirst hb hbB hs hturn hparam s₁ hw hword hcap hends hsize hlen hout₁ hinner₁ houter₁ hrows₁ hturns₁ hN₁ hk₁
  have htables₂ : gm06Alg511BinaryLoadedTables x t := htables₁.frame
    (by intro i; apply harr₂; fin_cases i <;> decide) (harr₂ 1000 (by decide)) (harr₂ 1001 (by decide))
  have hinputLen := gm06Alg511BinarySearchWords_length x
  have hE : x.endpoints.length ≤ (gm06Alg511BinarySearchWords x).length := by
    have hh := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.endpoints) (by simp [GM06Alg511BinaryInput.rows])
    change x.endpoints.length ≤ x.words.length at hh
    omega
  have hO : x.outerCuff.length ≤ (gm06Alg511BinarySearchWords x).length := by
    have hh := gm06Alg511_encoded_row_length_le (rows := x.rows) (row := x.outerCuff) (by simp [GM06Alg511BinaryInput.rows])
    change x.outerCuff.length ≤ x.words.length at hh
    omega
  have hT : (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length ≤ (gm06Alg511BinarySearchWords x).length := by
    have hh := gm06Alg511_encoded_row_length_le (rows := x.rows)
      (row := gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)) (by simp [GM06Alg511BinaryInput.rows])
    change _ ≤ x.words.length at hh
    omega
  change u₂ ≤ 20000 * (x.pathCount + x.vertexCount +
    (gm06EncodeRows (x.edgeTurns.map GM06Alg511BinaryInteger.words)).length + 5) ^ 2 at ht₂
  refine ⟨t, u₁ + u₂, L, rows, digits, sign, .seq he₁ he₂, ?_, htables₂, hk₂,
    (harr₂ 8 (by decide)).trans hrows₁, henc, hrow, hsign, hlenDigits, hbits, htheta, hsuccess₂.trans hsuccess₁⟩
  exact initial_winding_time _ _ _ _ _ _ _ _ (rep.graphTurn.pathCount_le_vertexCount hk) hE hO hT ht₁ ht₂

end GraphMinor.GM06
