module

public import GraphMinor.GM05.CopyVertexStars
public import GraphMinor.GM05.StarSupport
public import GraphMinor.Minor.Model
import GraphMinor.GM05.StarUnionDrawing
import GraphMinor.GM16.FiniteDrawingUnion
import GraphMinor.GM11.Walks
import GraphMinor.Surface.SurfaceGraph

/-!
# The drawing of all vertex stars

For GM V, (8.14), planarize all copy stars at each vertex. The
original vertex discs are disjoint, so their drawings have disjoint
supports and can be united. Every copy star remains a connected
subdrawing of the union, with its centre and ports among its vertices.
-/

public section
namespace GraphMinor.GM05
open Set Surface

/-- Unite the planarized vertex stars in GM V, (8.14), page 113,
retaining each copy's connected branch subdrawing and port vertices. -/
theorem exists_copy_star_drawings {S : Type} [TopologicalSpace S] [T2Space S]
    (D : Drawing S) (m : ℕ) (R : S → Set S)
    (hR : ∀ w ∈ D.V, ∀ z ∈ D.V, w ≠ z → Disjoint (R w) (R z))
    (u : D.E → S) (p q : Fin m × D.E → S)
    (x : D.V → Fin m → S) (L : ∀ w : D.V, Fin m × IncidentEdge D w → Set S)
    (hx : ∀ w i, x w i ∈ R w.val) (hxne : ∀ w i j, i ≠ j → x w i ≠ x w j)
    (hL : ∀ w a, IsLineWithEnds (L w a) (x w a.1) (vertexPort D u p q w a))
    (hLR : ∀ w a, L w a ⊆ R w.val)
    (hfin : ∀ w a b, a ≠ b → (L w a ∩ L w b).Finite) :
    ∃ T : Drawing S, ∃ K : Fin m × D.V → Drawing S,
      T.U = ⋃ w : D.V, ⋃ i, starSupport (x w) (L w) i ∧
      (∀ i w, (K (i,w)).IsSubdrawing T ∧ (K (i,w)).U = starSupport (x w) (L w) i ∧
        GraphConnected (K (i,w)).toGraph ∧ x w i ∈ (K (i,w)).V) ∧
      ∀ w a, vertexPort D u p q w a ∈ (K (a.1,w)).V := by
  classical
  let : Fintype D.V := D.finite_V.fintype
  let : Fintype D.E := D.finite_edges.fintype
  let : ∀ w : D.V, Fintype (IncidentEdge D w) := fun _ ↦ Fintype.ofFinite _
  choose T K hTU hTx hTp hK using fun w : D.V ↦ exists_star_union_drawing m
    (x w) (vertexPort D u p q w) (L w) (hxne w) (hL w) (hfin w)
  have hTR : ∀ w, (T w).U ⊆ R w.val := by
    intro w
    rw [hTU w]
    exact iUnion_subset fun i ↦ starSupport_subset (x w) (L w) i (hx w i)
      (fun e ↦ hLR w (i,e))
  have hTT : ∀ w z : D.V, w ≠ z → Disjoint (T w).U (T z).U := by
    intro w z hwz
    exact (hR w.val w.prop z.val z.prop (fun he ↦ hwz (Subtype.ext he))).mono (hTR w) (hTR z)
  obtain ⟨H,hHU,hHV,hHE⟩ := GM16.exists_drawing_of_finite_drawings
    (toFinite (univ : Set D.V)) (Z := ∅) finite_empty T
    (by simp) (fun w _ z _ hwz ↦ by rw [(hTT w z hwz).inter_eq])
  simp only [mem_univ,iUnion_true,empty_union] at hHU hHV hHE
  have hsub : ∀ w, (T w).IsSubdrawing H := by
    intro w
    constructor
    · intro y hy
      rw [hHV]
      exact mem_iUnion.mpr ⟨w,hy⟩
    · intro e he
      rw [hHE]
      exact mem_iUnion.mpr ⟨w,he⟩
  refine ⟨H,fun a ↦ K a.2 a.1,?_,?_,?_⟩
  · rw [hHU]
    simp_rw [hTU]
  · intro i w
    obtain ⟨hKT,hKU,hKV,hconn⟩ := hK w i
    refine ⟨hKT.trans (hsub w),hKU,hconn,?_⟩
    rw [hKV]
    exact ⟨centre_mem_starSupport (x w) (L w) i,hTx w i⟩
  · intro w a
    obtain ⟨-,hKU,hKV,-⟩ := hK w a.1
    rw [hKV]
    exact ⟨ray_subset_starSupport (x w) (L w) a.1 a.2 (hL w a).right_mem,hTp w a⟩

end GraphMinor.GM05
