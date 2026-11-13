module

public import GraphMinor.Compute.GM06Alg511TurnSum
import Mathlib.Tactic

/-!
# Interpreting the signed-turn accumulator

Store each supplied integer edge turn in two consecutive words. The
integer difference between the word at a dart and the word at its
mate is exactly the edge turn in that traversal orientation. The
difference between the two sums computed by the RAM loop is therefore
the sum of those signed edge turns. This file supplies that arithmetic
interpretation without assuming a winding computation as a hypothesis.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Paired magnitude words for the supplied edge-turn list. -/
def gm06Alg511TurnWords (turns : List ℤ) : List ℕ :=
  turns.flatMap gm06Alg511IntegerWords

/-- There are two signed magnitude words for each edge turn. -/
theorem gm06Alg511TurnWords_length (turns : List ℤ) :
    (gm06Alg511TurnWords turns).length = 2 * turns.length := by
  induction turns with
  | nil => rfl
  | cons t ts ih =>
    simp only [gm06Alg511TurnWords, List.flatMap_cons, gm06Alg511IntegerWords,
      List.cons_append, List.nil_append, List.length_cons] at *
    omega

/-- The two words at an edge's consecutive positions are its two
nonnegative integer parts. -/
theorem gm06Alg511TurnWords_getD (turns : List ℤ) (i : ℕ) (hi : i < turns.length) :
    (gm06Alg511TurnWords turns).getD (2 * i) 0 = (turns.getD i 0).toNat ∧
    (gm06Alg511TurnWords turns).getD (2 * i + 1) 0 = (-(turns.getD i 0)).toNat := by
  induction turns generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => exact ⟨rfl, rfl⟩
    | succ i =>
      have hi' : i < ts.length := by simpa using hi
      simpa [gm06Alg511TurnWords, gm06Alg511IntegerWords, Nat.mul_succ, Nat.add_assoc]
        using ih i hi'

/-- Integer contribution of an oriented edge, read from its dart pair. -/
def gm06Alg511DartTurn (words : List ℕ) (d : ℕ) : ℤ :=
  (words.getD d 0 : ℤ) - (words.getD (gm06DartMate d) 0 : ℤ)

/-- Reversing a dart negates its integer contribution. -/
theorem gm06Alg511DartTurn_mate (words : List ℕ) (d : ℕ) :
    gm06Alg511DartTurn words (gm06DartMate d) = -gm06Alg511DartTurn words d := by
  simp only [gm06Alg511DartTurn, gm06DartMate_involutive d]
  ring

/-- A forward dart contributes precisely the supplied edge turn. -/
theorem gm06Alg511DartTurn_forward (turns : List ℤ) (i : ℕ) (hi : i < turns.length) :
    gm06Alg511DartTurn (gm06Alg511TurnWords turns) (2 * i) = turns.getD i 0 := by
  obtain ⟨hpos, hneg⟩ := gm06Alg511TurnWords_getD turns i hi
  have hmate : gm06DartMate (2 * i) = 2 * i + 1 := by simp [gm06DartMate]
  rw [gm06Alg511DartTurn, hmate, hpos, hneg]
  omega

/-- A reverse dart contributes the negative of the supplied edge turn. -/
theorem gm06Alg511DartTurn_reverse (turns : List ℤ) (i : ℕ) (hi : i < turns.length) :
    gm06Alg511DartTurn (gm06Alg511TurnWords turns) (2 * i + 1) = -turns.getD i 0 := by
  have hmate : gm06DartMate (2 * i) = 2 * i + 1 := by simp [gm06DartMate]
  rw [← hmate, gm06Alg511DartTurn_mate, gm06Alg511DartTurn_forward turns i hi]

/-- The difference between the two natural accumulators is the sum
of the integer contributions in traversal order. -/
theorem gm06Alg511TurnSum_difference (words darts : List ℕ) :
    ((darts.map (fun d => words.getD d 0)).sum : ℤ) -
      ((darts.map (fun d => words.getD (gm06DartMate d) 0)).sum : ℤ) =
      (darts.map (gm06Alg511DartTurn words)).sum := by
  induction darts with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, gm06Alg511DartTurn] at *
    omega

/-- The actual RAM program computes the signed sum of the supplied
edge turns along a dart list, in linear time. -/
theorem gm06Alg511TurnSum_exec_signed {w : ℕ} (turns : List ℤ) (darts : List ℕ)
    (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * turns.length < 2 ^ w) (hpathlen : darts.length < 2 ^ w)
    (hwords : s.arrs 11 = gm06Alg511TurnWords turns) (hpath : s.arrs 12 = darts)
    (hdarts : ∀ d ∈ darts, d < 2 * turns.length)
    (hpos : (darts.map (fun d => (gm06Alg511TurnWords turns).getD d 0)).sum < 2 ^ w)
    (hneg : (darts.map (fun d =>
      (gm06Alg511TurnWords turns).getD (gm06DartMate d) 0)).sum < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511TurnSumProg s s' t ∧
      t ≤ 9 + 29 * darts.length ∧ s'.arrs = s.arrs ∧
      (s'.regs 21 : ℤ) - (s'.regs 22 : ℤ) =
        (darts.map (gm06Alg511DartTurn (gm06Alg511TurnWords turns))).sum := by
  obtain ⟨s', t, he, ht, harr, hp, hn'⟩ := gm06Alg511TurnSumProg_exec
    (gm06Alg511TurnWords turns) darts s hw (gm06Alg511TurnWords_length turns)
    hn hpathlen hwords hpath hdarts hpos hneg
  refine ⟨s', t, he, ht, harr, ?_⟩
  rw [hp, hn']
  exact gm06Alg511TurnSum_difference _ _

end GraphMinor.Compute
