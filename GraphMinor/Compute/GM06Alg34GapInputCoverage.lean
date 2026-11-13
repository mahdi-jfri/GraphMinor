module

public import GraphMinor.Compute.GM06Alg34GapInputArray
public import GraphMinor.GM06.Section3Reduction
import GraphMinor.GM06.Alg34GapInputExists

/-!
# Coverage of the augmented disc input relation

Every intended disc instance has finite drawing labels and explicit cuff
gap region incidence with the required geometric interpretation. Its
plain serializer therefore supplies an array in the augmented input
relation. Together with answer determination, this closes the encoding
requirements independently of the RAM reduction procedure.
-/

public section
namespace GraphMinor.Compute

open GM06

universe u

/-- Every disc instance of VI (3.4) is represented by an augmented plain
word array, with no answer, linkage, or reduction certificate in that array. -/
theorem GM06GapRepresentsArray.exists_of_disc_instance (I : DiscDivInstance.{u}) :
    ∃ w : List ℕ, GM06GapRepresentsArray w I.G I.Δ := by
  obtain ⟨X, hX⟩ := I.exists_gap_input_rep
  exact ⟨X.words, X, rfl, hX⟩

end GraphMinor.Compute
