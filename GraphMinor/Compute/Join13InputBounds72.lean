module

public import GraphMinor.Compute.Join13CoreBounds72
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.Algorithm74Scan

/-!
# Bounds for the caller's encoded inputs

A valid decomposition code has at most two tree vertices per graph edge. Its
parent and leaf words are tree indices. Together with the graph's triple
encoding, this bounds both input copies by a linear function of graph size.
-/

public section
namespace GraphMinor.Compute

/-- Both caller input encodings have linear length. -/
theorem inputLengths72_le {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    G.enc.length ≤ 3 * (G.numEdges + n + 1) ∧
      bdCode.length ≤ 3 * (G.numEdges + n + 1) := by
  have hp : G.numActivePairs ≤ G.numEdges := numActivePairs_le_numEdges G
  have ht := hbd.2.1
  have hl := hbd.2.2.1
  rw [hbd.1] at ht hl
  rw [G.length_enc]
  omega

/-- Every word in the graph encoding fits when vertex and edge counts fit. -/
theorem graphWords72_lt {w n : ℕ} (G : MultiDigraph n)
    (hn : n < 2 ^ w) (hm : G.numEdges < 2 ^ w) :
    ∀ a ∈ G.enc, a < 2 ^ w :=
  all_lt_enc_multiDigraph G hn ((numActivePairs_le_numEdges G).trans_lt hm) hm

/-- Every decomposition word is bounded by twice the graph edge count plus one. -/
theorem bdWords72_le {n B : ℕ} (G : MultiDigraph n) (bdCode : List ℕ)
    (hbd : IsValidBranchDecompCode B G bdCode) :
    ∀ a ∈ bdCode, a ≤ 2 * G.numEdges + 1 := by
  have ht : bdNumTreeVerts bdCode ≤ 2 * G.numEdges := by simpa [hbd.1] using hbd.2.1
  have hl : bdCode.length = 2 + bdNumTreeVerts bdCode + G.numEdges := by
    simpa [hbd.1] using hbd.2.2.1
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hget : bdCode.getD i 0 = bdCode[i] := List.getD_eq_getElem _ _ hi
  rw [← hget]
  by_cases hi0 : i = 0
  · subst i
    exact ht.trans (by omega)
  by_cases hi1 : i = 1
  · subst i
    change bdNumGraphEdges bdCode ≤ _
    rw [hbd.1]
    omega
  have hi2 : 2 ≤ i := by omega
  rcases hbd.2.2.2 with ⟨_, ht0, hz⟩ | ⟨_, htpos, hp0, hp, hτ, _⟩
  · have he : i - 2 < bdNumGraphEdges bdCode := by rw [hbd.1]; omega
    have hz' := hz (i - 2) he
    rw [show 2 + (i - 2) = i by omega] at hz'
    rw [hz']
    omega
  · by_cases hit : i < 2 + bdNumTreeVerts bdCode
    · by_cases hir : i = 2
      · subst i
        rw [hp0]
        omega
      · have hp' := hp (i - 2) (by omega) (by omega)
        change bdCode.getD (2 + (i - 2)) 0 < i - 2 at hp'
        rw [show 2 + (i - 2) = i by omega] at hp'
        omega
    · have hei : i - (2 + bdNumTreeVerts bdCode) < G.numEdges := by omega
      have hτ' := hτ ⟨i - (2 + bdNumTreeVerts bdCode), hei⟩
      have heq : 2 + bdNumTreeVerts bdCode + (i - (2 + bdNumTreeVerts bdCode)) = i := by omega
      simp only [heq] at hτ'
      omega

end GraphMinor.Compute
