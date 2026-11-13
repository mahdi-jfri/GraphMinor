module

public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section14

/-!
# Splitting a framing at a normal hoop

The two subdrawings on either side of a normal hoop give a two-piece gluing
of the original graft. This supplies the gluing used in Cases 2 and 3 of
Graph Minors VIII (16.2), pages 283–284.
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- The grafts on either side of a normal hoop glue to the original graft.
This is the splitting used in Cases 2 and 3 of VIII (16.2). -/
theorem Tube.Framing.isTwoPieceGluing_of_hoop {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} {X : Graft α β} (fr : τ.Framing X)
    {H : Set S} (hH : IsHoop H) (hNH : τ.Γ.IsNormal H)
    (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂) :
    IsTwoPieceGluing X
      (fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).1)
      (fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2) := by
  have : T2Space S := τ.t2Space
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  obtain ⟨hleft, hright⟩ := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hH hle).mp hsub
  have hunion := cap.cylinderBetween_union τ.isCylinder τ.isHoop_F₁ hH τ.isHoop_F₂ hleft hright
  have hinter := cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hH τ.isHoop_F₂ hleft hright
  have hVinter : fr.vertsIn (cylinderBetween τ.F₁ H) ∩
      fr.vertsIn (cylinderBetween H τ.F₂) = fr.vertsIn H := by
    rw [← fr.vertsIn_inter, hinter]
  have hc₁ := isClosed_cylinderBetween
    (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).1
  have hc₂ := isClosed_cylinderBetween
    (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2
  have hchoice : ∀ e ∈ E(X.G),
      (e ∈ fr.edgesIn (cylinderBetween τ.F₁ H) ∧ e ∉ fr.edgesIn (cylinderBetween H τ.F₂)) ∨
      (e ∈ fr.edgesIn (cylinderBetween H τ.F₂) ∧ e ∉ fr.edgesIn (cylinderBetween τ.F₁ H)) := by
    intro e he
    have hedge := (fr.iso.edgeEquiv ⟨e, he⟩).2
    have h := cap.edge_subset_left_or_right τ.isCylinder τ.Γ τ.isHoop_F₁ hH τ.isHoop_F₂
      hleft hright hNH hedge (fun x hx => τ.U_subset (hedge.2.1 hx).1)
    rcases h with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨he, hA⟩, fun ⟨_, h⟩ => hB h⟩
    · exact Or.inr ⟨⟨he, hB⟩, fun ⟨_, h⟩ => hA h⟩
  refine {
    le_A := fr.subGraph_le _ (isClosed_cylinderBetween
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).1)
    le_B := fr.subGraph_le _ (isClosed_cylinderBetween
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2)
    vertexSet_union := ?_
    edgeSet_union := ?_
    edge_disjoint := ?_
    inter_sub_TA := ?_
    inter_sub_TB := ?_
    T_sub_union := ?_
    union_diff_sub_T := ?_ }
  · change fr.vertsIn (cylinderBetween τ.F₁ H) ∪
      fr.vertsIn (cylinderBetween H τ.F₂) = V(X.G)
    rw [← fr.vertsIn_union, hunion, fr.vertsIn_cylinderBetween_F]
  · change E(fr.subGraph (cylinderBetween τ.F₁ H) hc₁) ∪
      E(fr.subGraph (cylinderBetween H τ.F₂) hc₂) = E(X.G)
    rw [fr.subGraph_edgeSet, fr.subGraph_edgeSet]
    apply Subset.antisymm (union_subset (fr.edgesIn_subset_E _) (fr.edgesIn_subset_E _))
    intro e he
    exact (hchoice e he).elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  · change Disjoint E(fr.subGraph (cylinderBetween τ.F₁ H) hc₁)
      E(fr.subGraph (cylinderBetween H τ.F₂) hc₂)
    rw [fr.subGraph_edgeSet, fr.subGraph_edgeSet, disjoint_left]
    intro e he₁ he₂
    rcases hchoice e (fr.edgesIn_subset_E _ he₁) with h | h
    · exact h.2 he₂
    · exact h.2 he₁
  · change fr.vertsIn (cylinderBetween τ.F₁ H) ∩ fr.vertsIn (cylinderBetween H τ.F₂) ⊆
      fr.vertsIn τ.F₁ ∪ fr.vertsIn H
    rw [hVinter]
    exact subset_union_right
  · change fr.vertsIn (cylinderBetween τ.F₁ H) ∩ fr.vertsIn (cylinderBetween H τ.F₂) ⊆
      fr.vertsIn H ∪ fr.vertsIn τ.F₂
    rw [hVinter]
    exact subset_union_left
  · change X.T ⊆ (fr.vertsIn τ.F₁ ∪ fr.vertsIn H) ∪ (fr.vertsIn H ∪ fr.vertsIn τ.F₂)
    rw [← fr.vertsIn_F_union]
    exact fun _ h => h.elim (fun h => Or.inl (Or.inl h)) (fun h => Or.inr (Or.inr h))
  · change ((fr.vertsIn τ.F₁ ∪ fr.vertsIn H) ∪ (fr.vertsIn H ∪ fr.vertsIn τ.F₂)) \
      (fr.vertsIn (cylinderBetween τ.F₁ H) ∩ fr.vertsIn (cylinderBetween H τ.F₂)) ⊆ X.T
    rw [hVinter, ← fr.vertsIn_F_union]
    rintro x ⟨(hx | hx) | (hx | hx), hn⟩
    · exact Or.inl hx
    · exact (hn hx).elim
    · exact (hn hx).elim
    · exact Or.inr hx

/-- Isomorphism closure does not change the tubular grafts of bounded index. -/
theorem isoGraftClass_classB_eq {α : Type u} {β : Type v} (k : ℤ) :
    isoGraftClass (classB (α := α) (β := β) k) = classB k := by
  apply Subset.antisymm
  · rintro X ⟨Y, ⟨hY, hk⟩, hiso⟩
    refine ⟨hY.of_isGraftIso hiso, ?_⟩
    rw [← Graft.index_eq_of_isGraftIso hiso]
    exact hk
  · exact subset_isoGraftClass _

/-- Splitting a framing puts the original graft in the closure under vertex
identification of the direct sum of its two classes. -/
theorem Tube.Framing.mem_WGraftClass_of_hoop {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} [Infinite α] {X : Graft α β} (fr : τ.Framing X)
    {H : Set S} (hH : IsHoop H) (hNH : τ.Γ.IsNormal H)
    (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂)
    {𝒜 ℬ : Set (Graft α β)} (h𝒜 : isoGraftClass 𝒜 = 𝒜) (hℬ : isoGraftClass ℬ = ℬ)
    (hA : fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).1 ∈ 𝒜)
    (hB : fr.subGraft (areLaminarHoops_of_subset_cylinderBetween τ.laminar hH hsub).2 ∈ ℬ) :
    X ∈ WGraftClass (graftDirectSumClass 𝒜 ℬ) := by
  have h := mem_WGraftClass_of_isTwoPieceGluing
    (fr.isTwoPieceGluing_of_hoop hH hNH hsub) hA hB
  rwa [h𝒜, hℬ] at h

end GraphMinor.GM08
