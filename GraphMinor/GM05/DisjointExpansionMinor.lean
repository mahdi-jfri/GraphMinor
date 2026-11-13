module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.GM05.GraphCopies
public import GraphMinor.Minor.Model
import GraphMinor.Minor.Basic

/-!
# Disjoint expansions give a minor of disjoint copies

For GM V, (8.14), combine the minor models in vertex-disjoint
expansions. Their branches remain disjoint and their chosen edges
cannot coincide across expansions. The connecting subgraphs avoid
all chosen edges, including those in other expansions, because their
host subgraphs have disjoint edge sets.
-/

public section
namespace GraphMinor.GM05
open Set Graph

private theorem subgraph_inc_iff {α β : Type*} {A G : Graph α β} (hA : A≤G)
    {e : β} (he : e∈E(A)) (x : α) : G.Inc e x ↔ A.Inc e x := by
  constructor
  · rintro ⟨y,hxy⟩
    exact ⟨y,(hA.isLink_iff he).mpr hxy⟩
  · rintro ⟨y,hxy⟩
    exact ⟨y,hA.isLink_mono hxy⟩

/-- Models inside vertex-disjoint subgraphs combine to a model of
pairwise disjoint copies of their common source. -/
theorem copy_model_of_disjoint_models {α β α' β' : Type*} {k : ℕ}
    {H : Graph α' β'} {G : Graph α β} (A : Fin k → Graph α β)
    (hA : ∀ i,A i≤G) (hdis : Pairwise (fun i j ↦ Disjoint V(A i) V(A j)))
    (ηv : Fin k → α' → Set α) (ηe : Fin k → β' → β)
    (hm : ∀ i,IsMinorModel H (A i) (ηv i) (ηe i)) :
    IsMinorModel (graphCopies k H) G (fun p ↦ ηv p.1 p.2) (fun p ↦ ηe p.1 p.2) := by
  have hEd : Pairwise (fun i j ↦ Disjoint E(A i) E(A j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro e hei hej
    obtain ⟨x,y,hxy⟩ := (A i).exists_isLink_of_mem_edgeSet hei
    have hxy' := ((hA j).isLink_iff hej).mpr ((hA i).isLink_mono hxy)
    exact disjoint_left.mp (hdis hij) hxy.left_mem hxy'.left_mem
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rintro ⟨i,v⟩ hv
    exact (hm i).vertex_nonempty v hv.2
  · rintro ⟨i,v⟩ hv
    exact ((hm i).vertex_subset v hv.2).trans (hA i).vertexSet_mono
  · rintro ⟨i,e⟩ he
    exact (hA i).edgeSet_mono ((hm i).edge_mem e he.2)
  · rintro ⟨i,v⟩ hv ⟨j,w⟩ hw hne
    by_cases hij : i=j
    · subst j
      exact (hm i).vertex_disjoint v hv.2 w hw.2 (fun he ↦ hne (Prod.ext rfl he))
    · exact (hdis hij).mono ((hm i).vertex_subset v hv.2) ((hm j).vertex_subset w hw.2)
  · rintro ⟨i,e⟩ he ⟨j,f⟩ hf hef
    change ηe i e=ηe j f at hef
    by_cases hij : i=j
    · subst j
      exact Prod.ext rfl ((hm i).edge_injOn he.2 hf.2 hef)
    · exact (disjoint_left.mp (hEd hij) ((hm i).edge_mem e he.2)
        (hef.symm ▸ (hm j).edge_mem f hf.2)).elim
  · rintro ⟨i,v⟩ hv ⟨j,e⟩ he
    simp only [graphCopies_inc]
    by_cases hji : j=i
    · subst j
      simp only [true_and]
      constructor
      · intro h
        obtain ⟨x,hx,hi⟩ := ((hm i).inc_iff v hv.2 e he.2).mp h
        exact ⟨x,hx,(subgraph_inc_iff (hA i) ((hm i).edge_mem e he.2) x).mpr hi⟩
      · rintro ⟨x,hx,hi⟩
        exact ((hm i).inc_iff v hv.2 e he.2).mpr
          ⟨x,hx,(subgraph_inc_iff (hA i) ((hm i).edge_mem e he.2) x).mp hi⟩
    · constructor
      · exact fun h ↦ (hji h.1).elim
      · rintro ⟨x,hx,hi⟩
        have hxj := ((subgraph_inc_iff (hA j) ((hm j).edge_mem e he.2) x).mp hi).vertex_mem
        exact (disjoint_left.mp (hdis (Ne.symm hji)) ((hm i).vertex_subset v hv.2 hx) hxj).elim
  · rintro ⟨i,v⟩ hv ⟨j,e⟩ he
    simp only [graphCopies_isLoopAt]
    by_cases hji : j=i
    · subst j
      simp only [true_and]
      exact ((hm i).isLoopAt_iff v hv.2 e he.2).trans
        (forall_congr' fun x ↦ imp_congr_left (subgraph_inc_iff (hA i) ((hm i).edge_mem e he.2) x).symm)
    · constructor
      · exact fun h ↦ (hji h.1).elim
      · intro hh
        obtain ⟨x,y,hxy⟩ := (A j).exists_isLink_of_mem_edgeSet ((hm j).edge_mem e he.2)
        have hx := hh x ((hA j).isLink_mono hxy).inc_left
        exact (disjoint_left.mp (hdis (Ne.symm hji)) ((hm i).vertex_subset v hv.2 hx) hxy.left_mem).elim
  · rintro ⟨i,v⟩ hv
    obtain ⟨K,hK,hKV,hconn⟩ := (hm i).connected v hv.2
    have hKA : K≤A i := hK.trans Graph.deleteEdges_le
    have hKG : K≤G := hKA.trans (hA i)
    refine ⟨K,⟨hKG.vertexSet_mono,?_⟩,hKV,hconn⟩
    intro f x y hxy
    refine ⟨hKG.isLink_mono hxy,?_⟩
    rintro ⟨⟨j,e⟩,he,hef⟩
    change ηe j e=f at hef
    by_cases hji : j=i
    · subst j
      exact (hK.isLink_mono hxy).2 ⟨e,he.2,hef⟩
    · exact disjoint_left.mp (hEd (Ne.symm hji)) (hKA.edgeSet_mono hxy.edge_mem)
        (hef ▸ (hm j).edge_mem e he.2)

/-- The packing-to-minor implication used in GM V, proof of (8.14).
The nonempty ambient edge type permits extending the model edge maps
to unused names, as required by the library model API. -/
theorem copy_minor_of_disjoint_expansions {α β α' β' : Type*} [Nonempty β]
    {H : Graph α' β'} {G : Graph α β} (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hVG : V(G).Finite) (hEG : E(G).Finite) {k : ℕ} (hpack : HasDisjointExpansions H G k) :
    IsIsoMinor (graphCopies k H) G := by
  classical
  obtain ⟨A,hA,hdis⟩ := hpack
  have hex : ∀ i,∃ ηv ηe,IsMinorModel H (A i) ηv ηe := by
    intro i
    obtain ⟨hAG,F,hF,φ⟩ := hA i
    exact exists_isMinorModel_of_isIsoMinor (hVG.subset hAG.vertexSet_mono)
      (hEG.subset hAG.edgeSet_mono) ⟨A i,le_rfl,F,hF,φ⟩
  choose ηv ηe hm using hex
  have hmodel := copy_model_of_disjoint_models A (fun i ↦ (hA i).1) hdis ηv ηe hm
  have hfin := graphCopies_finite k H hVH hEH
  exact isIsoMinor_of_isMinorModel _ _ hfin.1 hfin.2 hVG hEG _ _ hmodel

end GraphMinor.GM05
