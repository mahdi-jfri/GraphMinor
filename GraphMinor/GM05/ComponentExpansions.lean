module

public import GraphMinor.GM05.ComponentIndices
import GraphMinor.GM05.ComponentModels
import GraphMinor.Minor.Basic

/-!
# Assembling expansions of all connected components

Choose a minor model inside each component expansion. The component model
lemma combines them inside their vertex union. Its contraction witness is
an expansion of the whole fixed graph. Applying this construction to each
column of a disjoint family gives a packing of whole-graph expansions,
as in Graph Minors V, proof of (8.8), page 112.
-/

public section

namespace GraphMinor.GM05

open Graph Set GM06

/-- Disjoint expansions of all components contain an expansion of the
whole graph, using only their vertices. The edge-type condition permits
representing edges to be encoded by total functions in minor models. -/
theorem expansion_of_disjoint_component_expansions {α β α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {m : ℕ}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hβ : Nonempty β ∨ IsEmpty β') (C : Fin m → Graph α' β')
    (hCi : ∀ i,IsGraphComponent (C i) H) (hinj : Function.Injective C)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m)
    (A : Fin m → Graph α β) (hA : ∀ i,IsHExpansion (C i) G (A i))
    (hdisj : Pairwise (fun i j ↦ Disjoint V(A i) V(A j))) :
    ∃ B,IsHExpansion H G B ∧ V(B)⊆⋃ i,V(A i) := by
  classical
  have hmodels (i : Fin m) : ∃ ηv ηe,IsMinorModel (C i) (A i) ηv ηe := by
    have hminor : IsIsoMinor (C i) (A i) := ⟨A i,le_rfl,(hA i).2⟩
    exact exists_isMinorModel_of_isIsoMinor_of_nonempty_or_isEmpty
      (hVG.subset (hA i).1.vertexSet_mono) (hEG.subset (hA i).1.edgeSet_mono) hβ hminor
  choose ηv ηe hm using hmodels
  obtain ⟨νv,νe,hmodel⟩ := component_models_glue C hCi hinj hcover i₀ A
    (fun i ↦ (hA i).1) hdisj ηv ηe hm
  let U := ⋃ i,V(A i)
  have hU : U⊆V(G) := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact (hA i).1.vertexSet_mono hi
  have hDG : G.induce U≤G := Graph.induce_le hU
  have hminor : IsIsoMinor H (G.induce U) :=
    isIsoMinor_of_isMinorModel H (G.induce U) hVH hEH (hVG.subset hU)
      (hEG.subset hDG.edgeSet_mono) νv νe hmodel
  obtain ⟨B,hB,F,hF,hIso⟩ := hminor
  exact ⟨B,⟨hB.trans hDG,F,hF,hIso⟩,hB.vertexSet_mono⟩

/-- Packing `k` expansions of every component, with all chosen subgraphs
disjoint, gives `k` expansions of the whole graph. -/
theorem disjointExpansions_of_component_packings {α β α' β' : Type*}
    {H : Graph α' β'} {G : Graph α β} {m k : ℕ}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hβ : Nonempty β ∨ IsEmpty β') (C : Fin m → Graph α' β')
    (hCi : ∀ i,IsGraphComponent (C i) H) (hinj : Function.Injective C)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m)
    (A : Fin m → Fin k → Graph α β) (hA : ∀ i a,IsHExpansion (C i) G (A i a))
    (hdisj : Pairwise (fun p q : (_ : Fin m) × Fin k ↦ Disjoint V(A p.1 p.2) V(A q.1 q.2))) :
    HasDisjointExpansions H G k := by
  classical
  have hex (a : Fin k) : ∃ B,IsHExpansion H G B ∧ V(B)⊆⋃ i,V(A i a) := by
    apply expansion_of_disjoint_component_expansions hVH hEH hVG hEG hβ C hCi hinj hcover i₀
      (fun i ↦ A i a) (fun i ↦ hA i a)
    intro i j hij
    exact hdisj (i:=⟨i,a⟩) (j:=⟨j,a⟩) (fun h ↦ hij (congrArg Sigma.fst h))
  choose B hB hBA using hex
  refine ⟨B,hB,?_⟩
  intro a b hab
  rw [Set.disjoint_left]
  intro x hxa hxb
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hBA a hxa)
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hBA b hxb)
  have hne : (⟨i,a⟩ : (_ : Fin m) × Fin k)≠⟨j,b⟩ :=
    fun h ↦ hab (congrArg (fun p : (_ : Fin m) × Fin k ↦ p.2) h)
  exact Set.disjoint_left.mp (hdisj hne) hi hj

end GraphMinor.GM05
