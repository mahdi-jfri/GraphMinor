module

public import GraphMinor.GM05.ComponentIndices
import GraphMinor.GM06.Section3Basic

/-!
# Combining models of connected components

Assign each source vertex and edge to its component. Use that component's
branch set or representing edge. Disjoint host subgraphs give disjoint
branches and prevent a contracted edge in one component from being a
representing edge in another. Thus models of all components combine into
a model of the whole graph inside their vertex union, as used in (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set GM06

/-- Combine component models in pairwise vertex-disjoint host subgraphs.
The resulting model stays within the union of those host vertex sets. -/
theorem component_models_glue {α β α' β' : Type*} {H : Graph α' β'} {G : Graph α β}
    {m : ℕ} (C : Fin m → Graph α' β') (hCi : ∀ i,IsGraphComponent (C i) H)
    (hinj : Function.Injective C) (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D)
    (i₀ : Fin m) (A : Fin m → Graph α β) (hAG : ∀ i,A i≤G)
    (hdisj : Pairwise (fun i j ↦ Disjoint V(A i) V(A j)))
    (ηv : Fin m → α' → Set α) (ηe : Fin m → β' → β)
    (hm : ∀ i,IsMinorModel (C i) (A i) (ηv i) (ηe i)) :
    ∃ νv νe,IsMinorModel H (G.induce (⋃ i,V(A i))) νv νe := by
  classical
  let vc := componentVertexIndex C hcover i₀
  let ec := componentEdgeIndex C hcover i₀
  have hvC {v : α'} (hv : v∈V(H)) : v∈V(C (vc v)) := componentVertexIndex_mem C hcover i₀ hv
  have heC {e : β'} (he : e∈E(H)) : e∈E(C (ec e)) := componentEdgeIndex_mem C hcover i₀ he
  have hincColor {e : β'} {v : α'} (hinc : H.Inc e v) : vc v=ec e := by
    obtain ⟨w,hl⟩ := hinc
    exact (component_indices_of_link C hCi hinj hcover i₀ hl).1
  let U := ⋃ i,V(A i)
  let D := G.induce U
  have hAD (i : Fin m) : A i≤D := by
    refine ⟨subset_iUnion (fun j ↦ V(A j)) i,?_⟩
    intro e x y hxy
    exact ⟨(hAG i).isLink_mono hxy,mem_iUnion.mpr ⟨i,hxy.left_mem⟩,
      mem_iUnion.mpr ⟨i,hxy.right_mem⟩⟩
  have hedgeDisj : Pairwise (fun i j ↦ Disjoint E(A i) E(A j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    obtain ⟨x,y,hxy⟩ := exists_isLink_of_mem_edgeSet hei
    have hlG := (hAG i).isLink_mono hxy
    have hlJ := ((hAG j).isLink_iff hej).mpr hlG
    exact Set.disjoint_left.mp (hdisj hij) hxy.left_mem hlJ.left_mem
  have heA {e : β'} (he : e∈E(H)) : ηe (ec e) e∈E(A (ec e)) := (hm _).edge_mem e (heC he)
  let νv (v : α') := ηv (vc v) v
  let νe (e : β') := ηe (ec e) e
  refine ⟨νv,νe,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro v hv
    exact (hm _).vertex_nonempty v (hvC hv)
  · intro v hv x hx
    exact mem_iUnion.mpr ⟨vc v,(hm _).vertex_subset v (hvC hv) hx⟩
  · intro e he
    exact (hAD _).edgeSet_mono (heA he)
  · intro u hu v hv huv
    change Disjoint (ηv (vc u) u) (ηv (vc v) v)
    by_cases he : vc u=vc v
    · rw [←he]
      exact (hm (vc u)).vertex_disjoint u (hvC hu) v (he.symm ▸ hvC hv) huv
    · exact (hdisj he).mono ((hm _).vertex_subset u (hvC hu)) ((hm _).vertex_subset v (hvC hv))
  · intro e he f hf hef
    change ηe (ec e) e=ηe (ec f) f at hef
    by_cases hc : ec e=ec f
    · rw [←hc] at hef
      exact (hm (ec e)).edge_injOn (heC he) (hc.symm ▸ heC hf) hef
    · have hE := heA hf
      rw [←hef] at hE
      exact (Set.disjoint_left.mp (hedgeDisj hc) (heA he) hE).elim
  · intro v hv e he
    change H.Inc e v ↔ ∃ x∈ηv (vc v) v,D.Inc (ηe (ec e) e) x
    by_cases hc : vc v=ec e
    · rw [hc,←(hCi (ec e)).1.inc_congr (heC he)]
      have h := (hm (ec e)).inc_iff v (hc ▸ hvC hv) e (heC he)
      simpa only [(hAD (ec e)).inc_congr (heA he)] using h
    · constructor
      · intro h
        exact (hc (hincColor h)).elim
      · rintro ⟨x,hx,hinc⟩
        have hxV := (hm _).vertex_subset v (hvC hv) hx
        have hxE := (((hAD (ec e)).inc_congr (heA he)).mpr hinc).vertex_mem
        exact (Set.disjoint_left.mp (hdisj hc) hxV hxE).elim
  · intro v hv e he
    change H.IsLoopAt e v ↔ ∀ x,D.Inc (ηe (ec e) e) x → x∈ηv (vc v) v
    by_cases hc : vc v=ec e
    · rw [hc,←(hCi (ec e)).1.isLoopAt_congr (heC he)]
      have h := (hm (ec e)).isLoopAt_iff v (hc ▸ hvC hv) e (heC he)
      simpa only [(hAD (ec e)).inc_congr (heA he)] using h
    · constructor
      · intro h
        exact (hc (hincColor h.inc)).elim
      · intro hall
        obtain ⟨x,y,hxy⟩ := exists_isLink_of_mem_edgeSet (heA he)
        have hx := hall x (hxy.inc_left.mono (hAD (ec e)))
        exact (Set.disjoint_left.mp (hdisj hc)
          ((hm _).vertex_subset v (hvC hv) hx) hxy.left_mem).elim
  · intro v hv
    obtain ⟨K,hK,hKV,hconn⟩ := (hm (vc v)).connected v (hvC hv)
    have hKA : K≤A (vc v) := hK.trans Graph.deleteEdges_le
    have hKD : K≤D := hKA.trans (hAD (vc v))
    refine ⟨K,⟨hKD.vertexSet_mono,?_⟩,hKV,hconn⟩
    intro f x y hf
    refine ⟨hKD.isLink_mono hf,?_⟩
    rintro ⟨e,he,hef⟩
    change ηe (ec e) e=f at hef
    by_cases hc : ec e=vc v
    · have he' : e∈E(C (vc v)) := hc ▸ heC he
      have hmem : f∈ηe (vc v) '' E(C (vc v)) := ⟨e,he',by simpa only [hc] using hef⟩
      exact (hK.isLink_mono hf).2 hmem
    · have heOther : f∈E(A (ec e)) := hef ▸ heA he
      exact Set.disjoint_left.mp (hedgeDisj hc) heOther (hKA.edgeSet_mono hf.edge_mem)

end GraphMinor.GM05
