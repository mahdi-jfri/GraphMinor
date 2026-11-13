module

public import GraphMinor.Compute.GM02CompactFilteredEdges
public import GraphMinor.Compute.GM02CompactTermination
public import GraphMinor.Compute.GM02TerminatedInput

/-!
# Plain compact inputs formed from a filtered child

The edge filter supplies the simple child graph on parent names. Its
termination is contained in the retained child vertices. Compact both
by the same increasing numbering. This is the plain terminated input
written by the executable child builder.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Compact a filtered side and a termination on its retained vertices. -/
noncomputable def gm02FilteredChildInput {n : ℕ} (F : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ}) :
    GM02SimpleTerminatedInput where
  n := Bᶜᶜ.card
  G := (gm02FilteredSide F A B).comap (compactEmb Bᶜ)
  decAdj := Classical.decRel _
  A := gm02CompactTermination Bᶜ T

/-- The compact child has exactly the retained number of vertices. -/
theorem gm02FilteredChildInput_size {n : ℕ} (F : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ}) :
    (gm02FilteredChildInput F A B T).n = B.card := by
  simp only [gm02FilteredChildInput, compl_compl]

/-- Compacting the prescribed pairs preserves their index. -/
theorem gm02FilteredChildInput_index {n : ℕ} (F : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ}) :
    (gm02FilteredChildInput F A B T).A.index = T.index :=
  gm02CompactTermination_index Bᶜ T

/-- The compact child edge count is exactly the side filter's returned count. -/
theorem gm02FilteredChildInput_edgeCount {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ}) :
    (edgeListOf (gm02FilteredChildInput F A B T).G).length =
      (edgeListOf (gm02FilteredSide F A B)).length := by
  have he := congrArg List.length (gm02CompactEdgeList_map (gm02FilteredSide F A B) Bᶜ)
  simp only [List.length_map, gm02FilteredSide_filter_survives] at he
  convert he using 1
  congr 2

/-- The exact input encoding consists of the compact graph and matching word arrays. -/
theorem gm02FilteredChildInput_enc {n : ℕ} (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj] (A B : Finset (Fin n)) (T : Termination {v : Fin n | v ∉ Bᶜ}) :
    (gm02FilteredChildInput F A B T).enc =
      [B.card, (edgeListOf (gm02FilteredSide F A B)).length] ++
        flatEdges (edgeListOf ((gm02FilteredSide F A B).comap (compactEmb Bᶜ))) ++
        [T.index] ++ flatEdges (edgeListOf (gm02CompactTermination Bᶜ T).pairGraph) := by
  simp only [GM02SimpleTerminatedInput.enc, encGraph, gm02FilteredChildInput_size,
    gm02FilteredChildInput_index, gm02FilteredChildInput_edgeCount]
  congr

end GraphMinor.Compute
