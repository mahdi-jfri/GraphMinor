module

public import GraphMinor.Compute.GM02TerminatedInput

/-!
# Terminal support as a list of supplied endpoints

Routine A2 of II (3.2) balances the support of the current termination.
Its input already lists the terminal pairs. Flattening those pairs as
vertices therefore lists exactly the required support. Marking this list
constructs the subset bits used by the separator program.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- The supplied endpoints, as vertices rather than machine words. -/
def gm02TerminalVertices {n : ℕ} (A : Termination (Set.univ : Set (Fin n))) : List (Fin n) :=
  (edgeListOf A.pairGraph).flatMap (fun p => [p.1, p.2])

/-- Forgetting the vertex bounds gives exactly the terminal-pair words. -/
theorem gm02TerminalVertices_map_val {n : ℕ} (A : Termination (Set.univ : Set (Fin n))) :
    (gm02TerminalVertices A).map Fin.val = flatEdges (edgeListOf A.pairGraph) := by
  simp only [gm02TerminalVertices, flatEdges, List.map_flatMap, List.map_cons, List.map_nil]

/-- The endpoint list has two entries per terminal pair. -/
theorem gm02TerminalVertices_length {n : ℕ} (A : Termination (Set.univ : Set (Fin n))) :
    (gm02TerminalVertices A).length = 2 * A.index := by
  have he := congrArg List.length (gm02TerminalVertices_map_val A)
  simpa only [List.length_map, length_flatEdges, gm02Termination_pairList_length] using he

/-- Membership in the endpoint list is precisely membership in the
termination support. -/
theorem gm02TerminalVertices_mem {n : ℕ} (A : Termination (Set.univ : Set (Fin n)))
    (v : Fin n) : v ∈ gm02TerminalVertices A ↔ v ∈ A.support := by
  rw [A.mem_support_iff_exists_adj]
  constructor
  · intro hv
    obtain ⟨p, hp, hv⟩ := List.mem_flatMap.1 hv
    have hadj := (mem_edgeListOf A.pairGraph p).1 hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨p.2, hadj.2⟩
    · exact ⟨p.1, hadj.2.symm⟩
  · rintro ⟨b, hab⟩
    have hne : v ≠ b := A.pairGraph.ne_of_adj hab
    by_cases hlt : v.val < b.val
    · apply List.mem_flatMap.2
      exact ⟨(v, b), (mem_edgeListOf A.pairGraph _).2 ⟨hlt, hab⟩, by simp⟩
    · have hgt : b.val < v.val := by
        have hneval : v.val ≠ b.val := fun he => hne (Fin.ext he)
        omega
      apply List.mem_flatMap.2
      exact ⟨(b, v), (mem_edgeListOf A.pairGraph _).2 ⟨hgt, hab.symm⟩, by simp⟩

/-- The finite set obtained by marking the endpoint list is the support. -/
theorem gm02TerminalVertices_toFinset {n : ℕ} (A : Termination (Set.univ : Set (Fin n))) :
    ((gm02TerminalVertices A).toFinset : Set (Fin n)) = A.support := by
  ext v
  simp only [Finset.mem_coe, List.mem_toFinset, gm02TerminalVertices_mem]

/-- Marking the endpoint list gives the finite support set itself. -/
theorem gm02TerminalVertices_eq_support_toFinset {n : ℕ}
    (A : Termination (Set.univ : Set (Fin n))) :
    (gm02TerminalVertices A).toFinset = A.support.toFinset := by
  apply Finset.coe_injective
  rw [gm02TerminalVertices_toFinset, Set.coe_toFinset]

end GraphMinor.Compute
