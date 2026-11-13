module

public import GraphMinor.Compute.GM02TopologicalInput

/-!
# Patterns placed by a vertex injection

The proof of II (4.7), pages 319–320, tries the injections of the fixed
pattern's vertices into the host vertices. For each injection, keep every
pattern edge, including loops and parallel copies, and replace each end
by its image. This supplies an ordinary labelled input to (4.6).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Place a fixed edge-list pattern on host vertices by the chosen injection. -/
noncomputable def gm02InjectedPattern (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : GM02TopologicalInput where
  G := G
  vertices := Finset.univ.image f
  edges := H.edges.map (fun p => (f p.1, f p.2))
  ends_mem := by
    classical
    intro p hp
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hp
    exact ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩⟩

/-- Relabelling retains each pattern edge as a separate list entry. -/
theorem gm02InjectedPattern_edges_length (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : (gm02InjectedPattern G H f).edges.length = H.edges.length := by
  simp only [gm02InjectedPattern, List.length_map]

/-- Injectivity retains all pattern vertices, including isolated vertices. -/
theorem gm02InjectedPattern_vertices_card (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : (gm02InjectedPattern G H f).vertices.card = H.n := by
  classical
  change (Finset.univ.image f).card = H.n
  rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_fin]

/-- Each test has the original host size plus the fixed pattern size. -/
theorem gm02InjectedPattern_size (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) :
    gm02TopologicalSize (gm02InjectedPattern G H f) = G.size + H.size := by
  unfold gm02TopologicalSize GM02EdgeListInput.size
  rw [gm02InjectedPattern_vertices_card, gm02InjectedPattern_edges_length]
  exact Nat.add_assoc _ _ _

end GraphMinor.Compute
