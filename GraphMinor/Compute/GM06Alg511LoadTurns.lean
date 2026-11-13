module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511FlattenTurns
public import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Loading the winding accumulator from the retained drawing

Select the ordinary supplied integer edge-turn row from the full
input retained in array 1000 by the initial checks of VI (5.11),
page 134. Flatten its signed words into array 11. This phase preserves
the maximum-flow output and the vertex-path buffer.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the edge-turn row of the retained input and prepare the
signed accumulator's magnitude array. -/
def gm06Alg511LoadTurnsProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 1000 1005 1) gm06Alg511FlattenTurnsProg

/-- The supplied drawing alone determines the loaded integer turns.
The execution takes linear time in the number of supplied edges. -/
theorem gm06Alg511LoadTurnsProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hw : 3 < 2 ^ w) (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511LoadTurnsProg s s' t ∧
      t ≤ 69 + 116 * x.edgeTurns.length ∧
      s'.arrs 11 = gm06Alg511TurnWords x.edgeTurns ∧
      ∀ a, a ≠ 1005 → a ≠ 11 → s'.arrs a = s.arrs a := by
  let rows := [gm06Alg511Words x.drawing,
    gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)]
  have hrow : gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords) ∈ rows := by
    simp [rows]
  have hlen := (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
  have hvals : ∀ v ∈ gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords),
      v < 2 ^ w := fun v hv => hwords v (gm06Alg511_mem_encoded_row hrow hv)
  obtain ⟨s₁, t₁, he₁, ht₁, hturns, harr₁⟩ := gm06Alg511SelectFieldProg_exec
    1000 1005 (by decide) rows 1 (by simp [rows]) s (by omega) ha hn hwords
  change s₁.arrs 1005 = gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords) at hturns
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout⟩ :=
    gm06Alg511FlattenTurnsProg_exec x.edgeTurns s₁ hw hlen hvals hturns
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, hout, ?_⟩
  · change t₁ ≤ 18 + 17 * 1 + 22 *
      (gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)).length at ht₁
    rw [gm06Alg511TurnCode_length] at ht₁
    omega
  · intro a ha₁ ha₂
    rw [hk₂.2 a (by simp [ha₂]), harr₁ a ha₁]

end GraphMinor.Compute
