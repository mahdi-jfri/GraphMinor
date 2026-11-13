module

public import GraphMinor.Surface.Defs
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryReplacement
import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.Triangulate

/-!
# A cut corner outside the marked attachment intervals

Part IV, opening and Section 7b of the planarity note chooses a cut corner
at a root. The attachment intervals are finitely many disjoint closed
pieces, and each is a proper subset of the boundary circle. Adding the
finitely many port points still leaves a point outside all pieces. A
connected set covered by finitely many disjoint closed sets would have
to lie in just one of them, which proves the required gap.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Finitely many disjoint proper closed pieces cannot cover a nonempty
connected set. -/
theorem exists_point_outside_disjoint_closed_pieces {ι : Type*} [Finite ι]
    (C : Set ℂ) (hC : IsPreconnected C) (hne : C.Nonempty) (F : ι → Set ℂ)
    (hF : ∀ i, IsClosed (F i)) (hsep : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hproper : ∀ i, ¬C ⊆ F i) : ∃ x ∈ C, ∀ i, x ∉ F i := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have cover : ∀ s : Finset ι, C ⊆ ⋃ i ∈ s, F i → ∃ i ∈ s, C ⊆ F i := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      obtain ⟨x,hx⟩ := hne
      have hm := hs hx
      simp at hm
    | @insert i s hi ih =>
      intro hs
      let U := ⋃ j ∈ s, F j
      have hU : IsClosed U := isClosed_biUnion_finset fun j _ => hF j
      have hdis : Disjoint (F i) U := by
        rw [disjoint_left]
        intro x hxi hxU
        obtain ⟨j,hj'⟩ := mem_iUnion.mp hxU
        obtain ⟨hj,hxj⟩ := mem_iUnion.mp hj'
        have hij : i ≠ j := fun he => hi (he.symm ▸ hj)
        exact disjoint_left.mp (hsep hij) hxi hxj
      have hcover : C ⊆ F i ∪ U := by
        intro x hx
        obtain ⟨j,hj'⟩ := mem_iUnion.mp (hs hx)
        obtain ⟨hj,hxj⟩ := mem_iUnion.mp hj'
        rcases Finset.mem_insert.mp hj with he | hj
        · exact Or.inl (he ▸ hxj)
        · exact Or.inr (mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨hj,hxj⟩⟩)
      have havoid : Disjoint C (F i ∩ U) := by rw [hdis.inter_eq]; exact disjoint_empty _
      rcases preconnected_subset_or_subset_of_closed_cover hC (hF i) hU hcover havoid with h | h
      · exact ⟨i,Finset.mem_insert_self _ _,h⟩
      · obtain ⟨j,hj,hCj⟩ := ih h
        exact ⟨j,Finset.mem_insert_of_mem hj,hCj⟩
  by_contra hno
  have hcover : C ⊆ ⋃ i ∈ (Finset.univ : Finset ι), F i := by
    intro x hx
    by_contra hnot
    apply hno
    refine ⟨x,hx,?_⟩
    intro i hi
    exact hnot (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  obtain ⟨i,_,hCi⟩ := cover Finset.univ hcover
  exact hproper i hCi

private theorem line_infinite {L : Set ℂ} {a b : ℂ} (hL : IsLineWithEnds L a b) : L.Infinite := by
  obtain ⟨f,hf,hrange,hzero,hone⟩ := hL.exists_arc
  have hpc : IsPreconnected L := by rw [← hrange]; exact isPreconnected_range hf.1
  have hab : a ≠ b := fun he => zero_ne_one (hf.2 (hzero.trans (he.trans hone.symm)))
  exact hpc.infinite_of_nontrivial ⟨a,hL.left_mem,b,hL.right_mem,hab⟩

/-- An attachment line on a boundary circle is a proper part of it. -/
theorem circle_not_subset_boundary_line {C L : Set ℂ} {a b : ℂ}
    (hC : IsOArc C) (hL : IsLineWithEnds L a b) (hsub : L ⊆ C) : ¬C ⊆ L := by
  intro hback
  obtain ⟨R,hR,hcover,hinter⟩ := exists_complementary_boundary_arc hC hL hsub
  have hRsub : R ⊆ ({a,b} : Set ℂ) := by
    intro x hx
    have hxC : x ∈ C := hcover ▸ Or.inr hx
    have hm : x ∈ L ∩ R := ⟨hback hxC,hx⟩
    exact hinter ▸ hm
  exact line_infinite hR ((Set.toFinite _).subset hRsub)

end GraphMinor.LRPlanarity
