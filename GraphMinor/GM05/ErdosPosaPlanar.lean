module

public import GraphMinor.GM05.Statements
import GraphMinor.GM05.ExpansionWidth
import GraphMinor.GM05.ConnectedFamilies
import GraphMinor.GM05.ComponentExpansions
import GraphMinor.GM05.ExpansionConnected
import GraphMinor.GM05.ExpansionIso
import GraphMinor.GM05.EmptyExpansions
import GraphMinor.GM05.EdgeSupport
import GraphMinor.Minor.Basic

/-!
# Planar graphs have the Erdős–Pósa property

This is Graph Minors V, (8.8). Excluding a packing bounds the host's
width. Apply the connected-family packing lemma to expansions of the
components. A packing of every component combines into a packing of the
whole graph. Otherwise a bounded vertex set hits one component's every
expansion, and therefore hits every expansion of the whole graph.
Unused edge labels and the empty graph are handled by isomorphism and
the empty expansion, without adding hypotheses to the result.
-/

public section

namespace GraphMinor.GM05

open Graph Set GM06

universe u v u' v'

private theorem erdosPosa_of_all_edges {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    (hH : IsPlanar H) (hEdges : E(H)=univ) : HasErdosPosaProperty.{u,v,u',v'} H := by
  classical
  by_cases hEmpty : V(H)=∅
  · intro k
    exact ⟨0,fun G _ _ ↦ Or.inl (hasDisjointExpansions_of_empty_vertices hEmpty G k)⟩
  obtain ⟨m,C,hinj,hCi,hcover⟩ := exists_component_enumeration hH.1
  have hN : V(H).Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
  obtain ⟨v₀,hv₀⟩ := hN
  obtain ⟨D,hD,hvD⟩ := exists_component_of_vertex hv₀
  obtain ⟨i₀,hi₀⟩ := hcover D hD
  intro k
  obtain ⟨w,hwidth⟩ := treeWidthLE_of_no_disjointExpansions.{u,v,u',v'} hH k
  refine ⟨(m*k-1)*(w+1),?_⟩
  intro α β G hVG hEG
  by_cases hp : HasDisjointExpansions H G k
  · exact Or.inl hp
  by_cases hSome : ∃ A,IsHExpansion H G A
  swap
  · exact Or.inr ⟨∅,empty_subset _,by simp,fun A hA ↦ (hSome ⟨A,hA⟩).elim⟩
  have hβ : Nonempty β ∨ IsEmpty β' := by
    cases isEmpty_or_nonempty β with
    | inr hβ => exact Or.inl hβ
    | inl hβ =>
      let : IsEmpty β := hβ
      refine Or.inr ⟨fun e ↦ ?_⟩
      obtain ⟨A,hAG,F,hF,⟨φ⟩⟩ := hSome
      have he : e∈E(H) := hEdges.symm ▸ mem_univ e
      exact isEmptyElim (φ.edgeEquiv ⟨e,he⟩).1
  let F (i : Fin m) : Set (Graph α β) := {A | IsHExpansion (C i) G A}
  have hF : ∀ i A,A∈F i → A≤G ∧ GraphConnected A := by
    intro i A hA
    exact ⟨hA.1,hA.graphConnected ((graphConnected_iff_isGraphConnected (C i)).mpr (hCi i).2.1)⟩
  rcases lemma_8_8_pack_families_or_hit F hF (hwidth G hVG hEG hp) with
    ⟨A,hA,hdisj⟩|⟨i,X,hX,hcard,hhit⟩
  · exact Or.inl (disjointExpansions_of_component_packings hH.1 hH.2.1 hVG hEG hβ
      C hCi hinj hcover i₀ A hA hdisj)
  · refine Or.inr ⟨X,hX,hcard,?_⟩
    intro A hA
    obtain ⟨B,hB,hBA,hconn⟩ := hA.exists_component_expansion (hCi i)
    obtain ⟨x,hxX,hxB⟩ := hhit B hB
    exact ⟨x,hxX,hBA hxB⟩

/-- Graph Minors V, (8.8), page 111:
"If $H$ is planar then $H$ has the Erdös-Pósa property."
The proof follows the paper's component-family argument using the proved
(8.6) and (8.7). Its initial width bound applies (1.5) to the planar
graph of `k` disjoint copies of `H`. -/
theorem theorem_8_8_proof {α' : Type u'} {β' : Type v'} {H : Graph α' β'}
    (hH : IsPlanar H) : HasErdosPosaProperty.{u,v,u',v'} H := by
  have hK : IsPlanar (edgeSupportGraph H) := IsPlanar.of_iso (edgeSupportIso H).symm hH
  exact erdosPosa_of_iso (edgeSupportIso H) (erdosPosa_of_all_edges hK rfl)

/-- The universally quantified positive half (8.8). -/
theorem statement88_proved : Theorem88Statement.{u,v,u',v'} := fun _ hH ↦ theorem_8_8_proof hH

end GraphMinor.GM05
