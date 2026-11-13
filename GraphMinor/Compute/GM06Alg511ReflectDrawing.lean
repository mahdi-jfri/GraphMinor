module

public import GraphMinor.Compute.GM06DartMate
import Mathlib.Tactic

/-!
# Reflection of the full drawing's directed labels

VI (5.11), page 134, reverses the plane orientation when the initial
linkage winds above the target. Original edge labels keep their
parameter directions. The prescribed cuff gaps instead have fixed
increasing angular parameters. Reflection sends gap i to gap k-1-i
and exchanges its two parameter ends. Region rows keep their first
word, which is a region label, and reverse only their directed walk.
The permutations below are involutions and preserve all valid bounds.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Reflection sends the gap following index i to the gap with
index k-1-i. This is different from the permutation of cuff vertices. -/
def gm06Alg511ReflectGapFin {k : ℕ} (i : Fin k) : Fin k :=
  ⟨k - 1 - i.val, by omega⟩

/-- Reflecting a cuff-gap index twice restores that gap. -/
theorem gm06Alg511ReflectGapFin_involutive {k : ℕ} :
    Function.Involutive (@gm06Alg511ReflectGapFin k) := by
  intro i
  apply Fin.ext
  dsimp only [gm06Alg511ReflectGapFin]
  omega

/-- Reflect a directed label of the augmented drawing. Original
labels are retained. Each cuff's gap order and parameter direction
are reversed. Labels outside the augmented edge range are retained. -/
def gm06Alg511ReflectAugmentedDart (m k d : ℕ) : ℕ :=
  let j := d / 2
  let b := d % 2
  if j < m then d
  else if j < m + k then 2 * (m + (k - 1 - (j - m))) + (1 - b)
  else if j < m + k + k then 2 * (m + k + (k - 1 - (j - (m + k)))) + (1 - b)
  else d

private theorem mate_binary (j b : ℕ) (hb : b < 2) :
    gm06DartMate (2 * j + b) = 2 * j + (1 - b) := by
  unfold gm06DartMate
  split <;> omega

/-- Reflection leaves every original directed end label unchanged. -/
theorem gm06Alg511ReflectAugmentedDart_old {m k d : ℕ} (hd : d < 2 * m) :
    gm06Alg511ReflectAugmentedDart m k d = d := by
  simp only [gm06Alg511ReflectAugmentedDart]
  rw [ite_eq_left (by omega : d / 2 < m)]

/-- The inner gap i becomes gap k-1-i and its end bit is exchanged. -/
theorem gm06Alg511ReflectAugmentedDart_inner (m k i b : ℕ) (hi : i < k) (hb : b < 2) :
    gm06Alg511ReflectAugmentedDart m k (2 * (m + i) + b) =
      2 * (m + (k - 1 - i)) + (1 - b) := by
  have hdiv : (2 * (m + i) + b) / 2 = m + i := by omega
  have hmod : (2 * (m + i) + b) % 2 = b := by omega
  simp only [gm06Alg511ReflectAugmentedDart, hdiv, hmod]
  rw [ite_eq_right (by omega : ¬ m + i < m), ite_eq_left (by omega : m + i < m + k)]
  rw [Nat.add_sub_cancel_left]

/-- The outer gap uses the same reflected gap index and exchanged
end bit, after the original and inner edge blocks. -/
theorem gm06Alg511ReflectAugmentedDart_outer (m k i b : ℕ) (hi : i < k) (hb : b < 2) :
    gm06Alg511ReflectAugmentedDart m k (2 * (m + k + i) + b) =
      2 * (m + k + (k - 1 - i)) + (1 - b) := by
  have hdiv : (2 * (m + k + i) + b) / 2 = m + k + i := by omega
  have hmod : (2 * (m + k + i) + b) % 2 = b := by omega
  simp only [gm06Alg511ReflectAugmentedDart, hdiv, hmod]
  rw [ite_eq_right (by omega : ¬ m + k + i < m),
    ite_eq_right (by omega : ¬ m + k + i < m + k),
    ite_eq_left (by omega : m + k + i < m + k + k), Nat.add_sub_cancel_left]

/-- Reflection retains labels outside the augmented directed-edge
range, so the operation is total even on unused words. -/
theorem gm06Alg511ReflectAugmentedDart_outside {m k d : ℕ} (hd : 2 * (m + k + k) ≤ d) :
    gm06Alg511ReflectAugmentedDart m k d = d := by
  simp only [gm06Alg511ReflectAugmentedDart]
  rw [ite_eq_right (by omega : ¬ d / 2 < m), ite_eq_right (by omega : ¬ d / 2 < m + k),
    ite_eq_right (by omega : ¬ d / 2 < m + k + k)]

/-- Every valid directed edge remains in the augmented edge range. -/
theorem gm06Alg511ReflectAugmentedDart_lt {m k d : ℕ} (hd : d < 2 * (m + k + k)) :
    gm06Alg511ReflectAugmentedDart m k d < 2 * (m + k + k) := by
  dsimp only [gm06Alg511ReflectAugmentedDart]
  split_ifs <;> omega

/-- Reflecting augmented directed labels twice restores every word. -/
theorem gm06Alg511ReflectAugmentedDart_involutive (m k : ℕ) :
    Function.Involutive (gm06Alg511ReflectAugmentedDart m k) := by
  intro d
  by_cases hold : d < 2 * m
  · rw [gm06Alg511ReflectAugmentedDart_old hold, gm06Alg511ReflectAugmentedDart_old hold]
  by_cases hinner : d < 2 * (m + k)
  · let i := d / 2 - m
    let b := d % 2
    have hi : i < k := by dsimp [i]; omega
    have hb : b < 2 := Nat.mod_lt _ (by decide)
    have hd : d = 2 * (m + i) + b := by dsimp [i, b]; omega
    have hi' : k - 1 - i < k := by omega
    have hb' : 1 - b < 2 := by omega
    rw [hd, gm06Alg511ReflectAugmentedDart_inner m k i b hi hb,
      gm06Alg511ReflectAugmentedDart_inner m k _ _ hi' hb']
    omega
  by_cases houter : d < 2 * (m + k + k)
  · let i := d / 2 - (m + k)
    let b := d % 2
    have hi : i < k := by dsimp [i]; omega
    have hb : b < 2 := Nat.mod_lt _ (by decide)
    have hd : d = 2 * (m + k + i) + b := by dsimp [i, b]; omega
    have hi' : k - 1 - i < k := by omega
    have hb' : 1 - b < 2 := by omega
    rw [hd, gm06Alg511ReflectAugmentedDart_outer m k i b hi hb,
      gm06Alg511ReflectAugmentedDart_outer m k _ _ hi' hb']
    omega
  · have hout : 2 * (m + k + k) ≤ d := Nat.le_of_not_gt houter
    rw [gm06Alg511ReflectAugmentedDart_outside hout, gm06Alg511ReflectAugmentedDart_outside hout]

/-- Changing the traversal direction commutes with plane reflection. -/
theorem gm06Alg511ReflectAugmentedDart_mate (m k d : ℕ) :
    gm06Alg511ReflectAugmentedDart m k (gm06DartMate d) =
      gm06DartMate (gm06Alg511ReflectAugmentedDart m k d) := by
  have hdiv := gm06DartMate_edge d
  by_cases hold : d < 2 * m
  · rw [gm06Alg511ReflectAugmentedDart_old (gm06DartMate_lt hold),
      gm06Alg511ReflectAugmentedDart_old hold]
  by_cases hinner : d < 2 * (m + k)
  · let i := d / 2 - m
    let b := d % 2
    have hi : i < k := by dsimp [i]; omega
    have hb : b < 2 := Nat.mod_lt _ (by decide)
    have hd : d = 2 * (m + i) + b := by dsimp [i, b]; omega
    rw [hd, mate_binary _ _ hb,
      gm06Alg511ReflectAugmentedDart_inner m k i (1 - b) hi (by omega),
      gm06Alg511ReflectAugmentedDart_inner m k i b hi hb, mate_binary _ _ (by omega)]
  by_cases houter : d < 2 * (m + k + k)
  · let i := d / 2 - (m + k)
    let b := d % 2
    have hi : i < k := by dsimp [i]; omega
    have hb : b < 2 := Nat.mod_lt _ (by decide)
    have hd : d = 2 * (m + k + i) + b := by dsimp [i, b]; omega
    rw [hd, mate_binary _ _ hb,
      gm06Alg511ReflectAugmentedDart_outer m k i (1 - b) hi (by omega),
      gm06Alg511ReflectAugmentedDart_outer m k i b hi hb, mate_binary _ _ (by omega)]
  · have hd : 2 * (m + k + k) ≤ d := by omega
    have hmate : 2 * (m + k + k) ≤ gm06DartMate d := by omega
    rw [gm06Alg511ReflectAugmentedDart_outside hmate, gm06Alg511ReflectAugmentedDart_outside hd]

/-- Reverse the boundary walk of a region while retaining its header.
The header is a region label and is never treated as a directed end. -/
def gm06Alg511ReflectRegionRow (m k : ℕ) : List ℕ → List ℕ
  | [] => []
  | region :: ds => region :: ds.reverse.map
      (fun d => gm06Alg511ReflectAugmentedDart m k (gm06DartMate d))

/-- Reflection preserves the explicit region header of every row. -/
theorem gm06Alg511ReflectRegionRow_head (m k : ℕ) (row : List ℕ) :
    (gm06Alg511ReflectRegionRow m k row).head? = row.head? := by
  cases row <;> rfl

/-- Reflection preserves the number of words in each boundary row. -/
theorem gm06Alg511ReflectRegionRow_length (m k : ℕ) (row : List ℕ) :
    (gm06Alg511ReflectRegionRow m k row).length = row.length := by
  cases row <;> simp [gm06Alg511ReflectRegionRow]

/-- The header-preserving boundary-row transformation is an involution. -/
theorem gm06Alg511ReflectRegionRow_involutive (m k : ℕ) :
    Function.Involutive (gm06Alg511ReflectRegionRow m k) := by
  have hstep (d : ℕ) : gm06Alg511ReflectAugmentedDart m k
      (gm06DartMate (gm06Alg511ReflectAugmentedDart m k (gm06DartMate d))) = d := by
    rw [← gm06Alg511ReflectAugmentedDart_mate,
      gm06Alg511ReflectAugmentedDart_involutive, gm06DartMate_involutive]
  intro row
  cases row with
  | nil => rfl
  | cons r ds =>
    simp only [gm06Alg511ReflectRegionRow, List.map_reverse, List.reverse_reverse, List.map_map]
    congr 1
    have heq : (fun d => gm06Alg511ReflectAugmentedDart m k
        (gm06DartMate (gm06Alg511ReflectAugmentedDart m k (gm06DartMate d)))) = id := funext hstep
    simp only [Function.comp_def]
    rw [heq, List.map_id]

end GraphMinor.Compute
