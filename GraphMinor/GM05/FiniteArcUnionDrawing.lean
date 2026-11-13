module

public import GraphMinor.Surface.Defs
public import GraphMinor.Surface.CrossCut
import GraphMinor.GM05.ArcFiniteComplement
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM19.Section6Tri

/-!
# Turning finitely many crossing arcs into a drawing

In GM V, (8.14), insert every crossing as a vertex. Start with the
prescribed finite vertex set and add the arcs one at a time. Each
meets the old graph in finitely many points, so the part off the
old graph is a finite union of connected pieces. The library arc
insertion theorem subdivides both graphs at their meetings.
-/

public section
namespace GraphMinor.GM05
open Set Surface
universe v

/-- The finite union step in GM V, proof of (8.14), page 113.
Pairwise finite arc intersections yield a drawing with exactly their
union and the prescribed vertex set as its support. -/
theorem exists_surfaceGraph_of_finite_crossing_arcs {S : Type} [TopologicalSpace S] [T2Space S]
    {ι : Type v} [Fintype ι] (a : ι → unitInterval → S)
    (ha : ∀ i, IsArcMap (a i)) {Z : Set S} (hZ : Z.Finite)
    (h0 : ∀ i,a i 0∈Z) (h1 : ∀ i,a i 1∈Z)
    (hmeet : ∀ i j,i≠j → (range (a i)∩range (a j)).Finite) :
    ∃ V E, IsGraph V E ∧ Z ⊆ V ∧ gr V E = Z ∪ ⋃ i, range (a i) := by
  classical
  have key : ∀ T : Finset ι,∃ V E,IsGraph V E ∧ Z⊆V ∧ gr V E=Z∪⋃ i∈T,range (a i) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      exact ⟨Z,∅,⟨hZ,finite_empty,by simp,by simp⟩,subset_rfl,by simp [gr]⟩
    | insert i T hi ih =>
      obtain ⟨V,E,hG,hZV,hU⟩ := ih
      have hm : (range (a i)∩gr V E).Finite := by
        rw [hU,inter_union_distrib_left]
        simp only [inter_iUnion]
        exact (hZ.subset inter_subset_right).union (T.finite_toSet.biUnion fun j hj ↦
          hmeet i j (fun he ↦ hi (he ▸ hj)))
      have hfc : FinConn (range (a i)\gr V E) := by
        have h := finConn_arc_sdiff_finite (ha i) hm
        have he : range (a i)\(range (a i)∩gr V E)=range (a i)\gr V E := by
          ext x
          constructor
          · rintro ⟨hx,hn⟩
            exact ⟨hx,fun h ↦ hn ⟨hx,h⟩⟩
          · rintro ⟨hx,hn⟩
            exact ⟨hx,fun h ↦ hn h.2⟩
        rwa [he] at h
      obtain ⟨P,hP,hconn,hcov⟩ := hfc
      obtain ⟨V',E',hVV,hG',hU',-⟩ := IsGraph.add_path (ha i) P.ncard V E P hG
        (hU.symm ▸ (.inl (h0 i) : a i 0∈Z∪⋃ j∈T,range (a j)))
        (hU.symm ▸ (.inl (h1 i) : a i 1∈Z∪⋃ j∈T,range (a j))) hP rfl hconn hcov
      refine ⟨V',E',hG',hZV.trans hVV,?_⟩
      rw [hU',hU,Finset.set_biUnion_insert,union_assoc,union_comm (⋃ j∈T,range (a j)) (range (a i))]
  obtain ⟨V,E,hG,hZV,hU⟩ := key Finset.univ
  refine ⟨V,E,hG,hZV,?_⟩
  simpa only [Finset.mem_univ,iUnion_true] using hU

/-- Turning the subdivided finite arc graph into a drawing, as in
GM V, proof of (8.14), page 113. -/
theorem exists_drawing_of_finite_crossing_arcs {S : Type} [TopologicalSpace S] [T2Space S]
    {ι : Type v} [Fintype ι] (a : ι → unitInterval → S)
    (ha : ∀ i, IsArcMap (a i)) {Z : Set S} (hZ : Z.Finite)
    (h0 : ∀ i,a i 0∈Z) (h1 : ∀ i,a i 1∈Z)
    (hmeet : ∀ i j,i≠j → (range (a i)∩range (a j)).Finite) :
    ∃ D : Drawing S,D.U=Z∪⋃ i,range (a i) ∧ Z⊆D.V := by
  obtain ⟨V,E,hG,hZV,hU⟩ := exists_surfaceGraph_of_finite_crossing_arcs a ha hZ h0 h1 hmeet
  exact ⟨hG.toDrawing,hU,hZV⟩

end GraphMinor.GM05
