module

public import GraphMinor.GM05.GraphCopies
import GraphMinor.GM05.CopyIso
import GraphMinor.GM05.CopyContraction
import GraphMinor.Minor.Basic

/-!
# Copying a minor witness

Take the same subgraph and contract the same edges in every copy.
Contraction commutes with disjoint copies, and an isomorphism can be
applied separately in each copy. Thus taking disjoint copies preserves
the minor relation, as needed for Graph Minors V, (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- Disjoint copies preserve the relation of being isomorphic to a minor. -/
theorem graphCopies_minor {α β α' β' : Type*} {H : Graph α' β'} {G : Graph α β}
    (k : ℕ) (h : IsIsoMinor H G) : IsIsoMinor (graphCopies k H) (graphCopies k G) := by
  obtain ⟨K,hKG,C,hC,⟨φ⟩⟩ := h
  refine ⟨graphCopies k K,graphCopies_mono k hKG,univ ×ˢ C,?_,
    ⟨(copiesIso k φ).trans (copiesContractIso k K C)⟩⟩
  intro e he
  exact ⟨mem_univ _,hC he.2⟩

end GraphMinor.GM05
