module

public import GraphMinor.GM05.GraphCopies
public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.Minor.Model
import GraphMinor.GM05.CopyModels
import GraphMinor.GM05.EdgeSupport
import GraphMinor.Minor.Basic

/-!
# Packing expansions from a disjoint copy minor

Restrict a minor model of the graph of `k` copies to each copy's branch
union. Each restriction supplies a minor witness, hence an expansion
subgraph. The branch unions are disjoint, so the resulting expansions
are pairwise vertex-disjoint. This proves the minor-to-packing implication
used in Graph Minors V, (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- A model of disjoint copies supplies disjoint expansion witnesses.
The edge map is provided by the model itself, so no condition on ambient
edge types is required here. -/
theorem disjointExpansions_of_copy_model {α β α' β' : Type*} {k : ℕ}
    {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    {ηv : Fin k × α' → Set α} {ηe : Fin k × β' → β}
    (hm : IsMinorModel (graphCopies k H) G ηv ηe) : HasDisjointExpansions H G k := by
  classical
  let B (i : Fin k) := ⋃ v∈V(H),ηv (i,v)
  have hB (i : Fin k) : B i⊆V(G) := by
    intro x hx
    obtain ⟨v,hv,hxv⟩ := mem_iUnion₂.mp hx
    exact hm.vertex_subset (i,v) ⟨mem_univ i,hv⟩ hxv
  have hex (i : Fin k) : ∃ A, IsHExpansion H G A ∧ V(A)⊆B i := by
    have hAG : G.induce (B i)≤G := Graph.induce_le (hB i)
    have hminor : IsIsoMinor H (G.induce (B i)) :=
      isIsoMinor_of_isMinorModel H (G.induce (B i)) hVH hEH
        (hVG.subset (hB i)) (hEG.subset hAG.edgeSet_mono)
        (fun v ↦ ηv (i,v)) (fun e ↦ ηe (i,e)) (copy_model_restrict hm i)
    obtain ⟨A,hA,F,hF,hIso⟩ := hminor
    exact ⟨A,⟨hA.trans hAG,F,hF,hIso⟩,hA.vertexSet_mono⟩
  choose A hA hAB using hex
  refine ⟨A,hA,?_⟩
  intro i j hij
  exact (copy_model_branches_disjoint hm hij).mono (hAB i) (hAB j)

/-- The minor-to-packing implication when the host edge type is nonempty.
This is the direct application of the equivalence between minor models
and contraction witnesses. -/
theorem disjointExpansions_of_copy_minor_nonempty {α β α' β' : Type*} [Nonempty β] {k : ℕ}
    {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hminor : IsIsoMinor (graphCopies k H) G) : HasDisjointExpansions H G k := by
  obtain ⟨ηv,ηe,hm⟩ := exists_isMinorModel_of_isIsoMinor hVG hEG hminor
  exact disjointExpansions_of_copy_model hVH hEH hVG hEG hm

/-- A minor consisting of `k` disjoint copies of `H` gives `k`
vertex-disjoint `H`-expansions. This includes edgeless graphs and empty
ambient edge types. -/
theorem disjointExpansions_of_copy_minor {α β α' β' : Type*} {k : ℕ}
    {H : Graph α' β'} {G : Graph α β}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hminor : IsIsoMinor (graphCopies k H) G) : HasDisjointExpansions H G k := by
  classical
  by_cases hk : k=0
  · subst k
    exact ⟨Fin.elim0,fun i ↦ Fin.elim0 i,fun i ↦ Fin.elim0 i⟩
  cases isEmpty_or_nonempty β with
  | inr hβ =>
    let : Nonempty β := hβ
    exact disjointExpansions_of_copy_minor_nonempty hVH hEH hVG hEG hminor
  | inl hβ =>
    let : IsEmpty β := hβ
    have hEmpty : IsEmpty E(H) := by
      refine ⟨fun e ↦ ?_⟩
      obtain ⟨G',hG',C,hC,⟨φ⟩⟩ := hminor
      let i : Fin k := ⟨0,by omega⟩
      exact isEmptyElim ((φ.edgeEquiv ⟨(i,e.1),mem_univ i,e.2⟩).1)
    let : IsEmpty E(H) := hEmpty
    have hnorm : IsIsoMinor (graphCopies k (edgeSupportGraph H)) G :=
      (copiesEdgeSupportIso k H).symm.isIsoMinor_left hminor
    obtain ⟨ηv,ηe,hm⟩ := exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty
      hVG hEG (Or.inr (inferInstance : IsEmpty (Fin k × E(H)))) hnorm
    have hE' : E(edgeSupportGraph H).Finite := finite_univ
    obtain ⟨A,hA,hdisj⟩ := disjointExpansions_of_copy_model (H:=edgeSupportGraph H) hVH hE' hVG hEG hm
    refine ⟨A,?_,hdisj⟩
    intro i
    obtain ⟨hAG,F,hF,⟨φ⟩⟩ := hA i
    exact ⟨hAG,F,hF,⟨(edgeSupportIso H).trans φ⟩⟩

end GraphMinor.GM05
