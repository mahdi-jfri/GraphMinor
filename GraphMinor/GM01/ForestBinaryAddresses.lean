module

public import GraphMinor.GM01.ForestTrees
import Mathlib.Tactic.FinCases

/-!
# Addresses for the three retained binary subtrees

In Graph Minors I, (3.3), page 51, contract the root and its two
children of `H` to one centre. Three of the four grandchild subtrees
supply the branches of `Y`. Appending distinct two-bit suffixes
places words in those three subtrees and preserves parent edges.
-/

@[expose] public section

namespace GraphMinor.GM01

/-- The three retained grandchild addresses in the proof of (3.3). -/
def forestBinarySuffix (i : Fin 3) : List Bool :=
  if i = 0 then [false, false] else if i = 1 then [false, true] else [true, false]

/-- All three addresses lie two levels below the binary root. -/
theorem forestBinarySuffix_length (i : Fin 3) : (forestBinarySuffix i).length = 2 := by
  fin_cases i <;> decide

/-- The word of an arm vertex in its retained grandchild subtree. -/
def forestBinaryAddress (p : Fin 3 × List Bool) : List Bool :=
  p.2 ++ forestBinarySuffix p.1

/-- Distinct arm vertices have distinct binary addresses. -/
theorem forestBinaryAddress_injective : Function.Injective forestBinaryAddress := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have he := congrArg List.reverse h
  change (u ++ forestBinarySuffix i).reverse = (v ++ forestBinarySuffix j).reverse at he
  fin_cases i <;> fin_cases j <;> simp [forestBinarySuffix] at he
  all_goals exact Prod.ext rfl he

/-- Each retained address adds exactly two levels to its arm word. -/
theorem forestBinaryAddress_length (p : Fin 3 × List Bool) :
    (forestBinaryAddress p).length = p.2.length + 2 := by
  simp only [forestBinaryAddress, List.length_append, forestBinarySuffix_length]

end GraphMinor.GM01
