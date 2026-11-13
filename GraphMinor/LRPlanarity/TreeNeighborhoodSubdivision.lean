module

public import GraphMinor.LRPlanarity.DefsGeometry
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.LRPlanarity.PolygonalizationSegmentGraph
import GraphMinor.HP25.Embedding

/-!
# Straight subdivision of a polygonal drawing

Part IV, Section 7b of the planarity note subdivides the drawn tree at
its bends. The finite straight segment arrangement of all edge images
provides a common subdivision. Insert all original vertex points as well,
including isolated vertices. The drawn set is unchanged.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

private theorem add_original_points {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b) (points : Finset ℂ) :
    ∃ V' E', V ⊆ V' ∧ (∀ x ∈ points, x ∈ V') ∧ IsGraph V' E' ∧
      gr V' E' = (points : Set ℂ) ∪ gr V E ∧
      ∀ e ∈ E', ∃ a b : ℂ, e = segment ℝ a b := by
  classical
  induction points using Finset.induction_on with
  | empty =>
    refine ⟨V, E, subset_rfl, ?_, h, ?_, hstraight⟩
    · intro x hx
      exact (Finset.notMem_empty x hx).elim
    · simp
  | @insert x points hx ih =>
    obtain ⟨V1, E1, hV1, hp1, hG1, hg1, hS1⟩ := ih
    obtain ⟨E2, hG2, hg2, hS2⟩ := segment_graph_add_point hG1 hS1 x
    refine ⟨insert x V1, E2, hV1.trans (subset_insert _ _), ?_, hG2, ?_, hS2⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Or.inl rfl
      · exact Or.inr (hp1 y hy)
    · rw [hg2, hg1, Finset.coe_insert, insert_union]

/-- Part IV, Section 7b: a polygonal plane drawing has a finite straight
segment arrangement containing every original vertex and with exactly the
same drawn set. -/
theorem exists_straight_drawing_arrangement {N : ℕ} {G : SimpleGraph (Fin N)}
    (drawing : HP25.PlaneEmbedding G univ) (hpolygonal : IsPolygonal drawing) :
    ∃ (V : Set ℂ) (E : Set (Set ℂ)), IsGraph V E ∧
      (∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b) ∧
      (∀ v, drawing.pt v ∈ V) ∧ gr V E = drawing.U := by
  classical
  let D := {e : Fin N × Fin N // G.Adj e.1 e.2}
  have hpieces : ∀ e : D, ∃ pieces : Finset (ℂ × ℂ),
      drawing.line e.val.1 e.val.2 = ⋃ p ∈ pieces, segment ℝ p.1 p.2 :=
    fun e => hpolygonal _ _ e.property
  choose pieces hpieces using hpieces
  let allpieces := Finset.univ.biUnion pieces
  obtain ⟨V0, E0, hG0, hg0, _, hS0⟩ := exists_straight_segment_arrangement allpieces
  let points := Finset.univ.image drawing.pt
  obtain ⟨V, E, hV, hpoints, hG, hgr, hS⟩ := add_original_points hG0 hS0 points
  have hvertices : ∀ v, drawing.pt v ∈ V := fun v =>
    hpoints _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩)
  have hline_sub : ∀ u v, G.Adj u v → drawing.line u v ⊆ gr V E := by
    intro u v huv x hx
    have hm : x ∈ ⋃ p ∈ pieces ⟨(u, v), huv⟩, segment ℝ p.1 p.2 :=
      hpieces ⟨(u, v), huv⟩ ▸ hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hm
    obtain ⟨hp, hxp⟩ := mem_iUnion.mp hp
    rw [hgr, hg0]
    apply Or.inr
    apply mem_iUnion.mpr
    refine ⟨p, mem_iUnion.mpr ⟨?_, hxp⟩⟩
    exact Finset.mem_biUnion.mpr ⟨⟨(u, v), huv⟩, Finset.mem_univ _, hp⟩
  refine ⟨V, E, hG, hS, hvertices, ?_⟩
  apply subset_antisymm
  · intro x hx
    rw [hgr, hg0] at hx
    rcases hx with hp | hs
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
      exact drawing.pt_mem_U (mem_univ _)
    · obtain ⟨p, hp⟩ := mem_iUnion.mp hs
      obtain ⟨hp, hxp⟩ := mem_iUnion.mp hp
      obtain ⟨e, _, hep⟩ := Finset.mem_biUnion.mp hp
      have heline : x ∈ drawing.line e.val.1 e.val.2 := by
        rw [hpieces e]
        exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hep, hxp⟩⟩
      exact drawing.line_subset_U (mem_univ _) (mem_univ _) e.property heline
  · intro x hx
    rcases hx with ⟨v, _, hvx⟩ | he
    · exact hvx ▸ Or.inl (hvertices v)
    · obtain ⟨u, he⟩ := mem_iUnion.mp he
      obtain ⟨_, he⟩ := mem_iUnion.mp he
      obtain ⟨v, he⟩ := mem_iUnion.mp he
      obtain ⟨_, he⟩ := mem_iUnion.mp he
      obtain ⟨huv, hxline⟩ := mem_iUnion.mp he
      exact hline_sub u v huv hxline

end GraphMinor.LRPlanarity
