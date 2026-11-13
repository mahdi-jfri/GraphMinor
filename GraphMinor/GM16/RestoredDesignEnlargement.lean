module

public import GraphMinor.GM16.ExceptionalCoreEdges
public import GraphMinor.GM16.DesignDownwardClosure
import GraphMinor.GM09.Basic

/-!
# The enlargement condition for the restored location

For XVI (1.3), pages 51–52, refine the lifted location to remove its
exceptional core edges. Its core now has exactly the old core's edges
and adds only exceptional vertices. The old lifted separator sets
restrict to the old design sets. A new single-edge separator restricts
to at most one old core vertex, which belongs to an old design set
because the local left sides cover all vertices. Downward closure
therefore gives the required design enlargement without changing any
old torso.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- The refined location gives the `|Z|`-enlargement needed in Claim (1)
of the proof of XVI (1.3), page 51. Downward closure preserves every torso
and accounts for the added single-edge separator sets. -/
theorem restored_design_isEnlargement {α : Type u} {β : Type v}
    {G : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    {Z : Set α} (hZ : Z ⊆ V(G))
    {ℒ : Set (Graph α β × Graph α β)} (hLoc : IsGraphLocation (deleteVertices G Z) ℒ)
    (hCover : ∀ x ∈ V(deleteVertices G Z), ∃ p ∈ ℒ, x ∈ V(p.1)) :
    IsGraphEnlargement Z.ncard
      (designDownwardClosure (graphLocationDesign (deleteVertices G Z) ℒ))
      (graphLocationDesign G (restoredLocation G Z ℒ)) := by
  let C := graphLocationCore (deleteVertices G Z) ℒ
  let C' := graphLocationCore G (restoredLocation G Z ℒ)
  have hC : C ≤ deleteVertices G Z := graphLocationCore_le _ _
  have hCG : C ≤ G := hC.trans (deleteVertices_le G Z)
  have hC'G : C' ≤ G := graphLocationCore_le _ _
  have hVC : V(C') = V(C) ∪ Z := vertexSet_restored_core hZ ℒ
  have hEC : E(C') = E(C) := edgeSet_restored_core hZ hEG hLoc
  have hNoZ : ∀ x ∈ V(C), x ∉ Z := fun _ hx => (hC.vertexSet_mono hx).2
  have hDesign := hLoc.isGraphDesign (hVG.subset sdiff_subset)
    (hEG.subset (deleteVertices_le G Z).edgeSet_mono)
  refine ⟨Z, le_refl _, hDesign.downwardClosure,
    (hLoc.restore hZ hEG).isGraphDesign hVG hEG, ?_, ?_, ?_, ?_, ?_⟩
  · change Z ⊆ V(C')
    rw [hVC]
    exact subset_union_right
  · change C ≤ C'
    rw [(Compatible.of_le_le hCG hC'G).le_iff, hVC, hEC]
    exact ⟨subset_union_left, Subset.refl _⟩
  · change V(C') \ V(C) ⊆ Z
    rw [hVC]
    rintro x ⟨hxC | hxZ, hxNot⟩
    · exact (hxNot hxC).elim
    · exact hxZ
  · exact hEC ▸ Subset.refl _
  · rintro X ⟨p, hp, rfl⟩ _
    rcases hp with hp | ⟨e, heK, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := hp
      change (V(liftSeparationLeft G Z q) ∩ V(liftSeparationRight G Z q)) ∩ V(C) ∈ _
      rw [(liftLocationPair_isSeparation hZ (hLoc.isSeparation hq)).2]
      have hBag : V(q.1) ∩ V(q.2) ∈ (graphLocationDesign (deleteVertices G Z) ℒ).2 :=
        mem_image_of_mem _ hq
      have hBagSub : V(q.1) ∩ V(q.2) ⊆ V(C) := hDesign.2.2 hBag
      have hSet : (Z ∪ (V(q.1) ∩ V(q.2))) ∩ V(C) = V(q.1) ∩ V(q.2) := by
        ext x
        constructor
        · rintro ⟨hxZ | hxBag, hxC⟩
          · exact (hNoZ x hxC hxZ).elim
          · exact hxBag
        · intro hx
          exact ⟨Or.inr hx, hBagSub hx⟩
      rw [hSet]
      exact Or.inl ⟨_, hBag, Subset.refl _⟩
    · obtain ⟨z, hzZ, w, hzw⟩ := heK.2
      change (({x | G.Inc e x} ∩ V(G)) ∩ V(C)) ∈ _
      have hEnds : ∀ x, G.Inc e x → x = z ∨ x = w := by
        rintro x ⟨y, hxy⟩
        exact hxy.left_eq_or_eq hzw
      by_cases hwC : w ∈ V(C)
      · obtain ⟨Y, hY, hwY⟩ := location_core_vertex_mem_design_set hCover hwC
        refine Or.inl ⟨Y, hY, ?_⟩
        rintro x ⟨⟨hxInc, _⟩, hxC⟩
        rcases hEnds x hxInc with rfl | rfl
        · exact (hNoZ _ hxC hzZ).elim
        · exact hwY
      · apply Or.inr
        apply eq_empty_iff_forall_notMem.mpr
        rintro x ⟨⟨hxInc, _⟩, hxC⟩
        rcases hEnds x hxInc with rfl | rfl
        · exact hNoZ _ hxC hzZ
        · exact hwC hxC

end GraphMinor.GM16
