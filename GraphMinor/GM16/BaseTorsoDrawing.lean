module

public import GraphMinor.GM16.BaseTorsoGraph
public import GraphMinor.GM16.ArrangementDiscVertices
import GraphMinor.GM16.SmallGraphInDisc
import GraphMinor.GM09.Basic

/-!
# Drawing the base of the torso outgrowth

In XVI (1.3), page 51, each small torso piece is drawn inside its
society disc at the arrangement's prescribed vertex positions.
The edge partition lets these drawings be combined. Different society
discs meet only at common boundary vertices, so no crossings are created.
The same intersection condition makes every large society disc meet
the base drawing only in vertices.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface GM06 GM09 GM14
universe u v w

/-- Glue the drawings of the small torso pieces into the base graph
in the proof of XVI (1.3), page 51. -/
theorem exists_base_torso_drawing
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {H : Graph α β} (hEH : E(H).Finite)
    {𝒮 : Set (Society α β)} {disc : Society α β → Set S} {pt : α → S}
    (hArr : IsSurfaceArrangement 𝒮 disc pt)
    {F : Society α β → Set β} {P : Society α β → Graph α β}
    (hF : ∀ A, F A ⊆ E(H))
    (hPieces : ∀ A ∈ 𝒮, P A ≤ H ∧ E(P A) = F A ∧
      (A.Ω.bar.ncard ≤ 3 → V(P A) = A.Ω.bar))
    (hV : segregationVertices 𝒮 ⊆ V(H)) :
    ∃ edgeOf : β → Set S,
      (∀ e ∈ E(baseTorsoGraph H 𝒮 F), ∀ x y,
        (baseTorsoGraph H 𝒮 F).IsLink e x y → x ≠ y →
          IsLineWithEnds (edgeOf e) (pt x) (pt y)) ∧
      (∀ e ∈ E(baseTorsoGraph H 𝒮 F), ∀ x,
        (baseTorsoGraph H 𝒮 F).IsLoopAt e x → IsOArc (edgeOf e) ∧ pt x ∈ edgeOf e) ∧
      (∀ e ∈ E(baseTorsoGraph H 𝒮 F), ∀ f ∈ E(baseTorsoGraph H 𝒮 F), e ≠ f →
        edgeOf e ∩ edgeOf f ⊆ pt '' V(baseTorsoGraph H 𝒮 F)) ∧
      (∀ e ∈ E(baseTorsoGraph H 𝒮 F), ∀ x ∈ V(baseTorsoGraph H 𝒮 F),
        pt x ∈ edgeOf e → (baseTorsoGraph H 𝒮 F).Inc e x) ∧
      (∀ A ∈ 𝒮, 3 < A.Ω.bar.ncard → ∀ e ∈ E(baseTorsoGraph H 𝒮 F),
        edgeOf e ∩ disc A ⊆ pt '' V(baseTorsoGraph H 𝒮 F)) := by
  classical
  let G₀ := baseTorsoGraph H 𝒮 F
  have hG₀ : G₀ ≤ H := baseTorsoGraph_le hV
  have hSmallEnds : ∀ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 →
      ∀ e ∈ F A, ∀ x, H.Inc e x → x ∈ A.Ω.bar := by
    intro A hA hsmall e he x ⟨y, hxy⟩
    have heP : e ∈ E(P A) := (hPieces A hA).2.1.symm ▸ he
    have hxyP := ((hPieces A hA).1.isLink_iff heP).mpr hxy
    exact (hPieces A hA).2.2 hsmall ▸ hxyP.left_mem
  have hE₀ : E(G₀) = smallSocietyEdges 𝒮 F := edgeSet_baseTorsoGraph hF hSmallEnds
  have hex : ∀ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 → ∃ J : β → Set S,
      (∀ e ∈ E(P A), ∀ x y, (P A).IsLink e x y → x ≠ y →
        IsLineWithEnds (J e) (pt x) (pt y)) ∧
      (∀ e ∈ E(P A), ∀ x, (P A).IsLoopAt e x → IsOArc (J e) ∧ pt x ∈ J e) ∧
      (∀ e ∈ E(P A), ∀ f ∈ E(P A), e ≠ f → J e ∩ J f ⊆ pt '' V(P A)) ∧
      (∀ e ∈ E(P A), ∀ x ∈ V(P A), pt x ∈ J e → (P A).Inc e x) ∧
      (∀ e ∈ E(P A), J e ⊆ disc A) ∧
      (∀ e ∈ E(P A), J e ∩ discBd (disc A) ⊆ pt '' V(P A)) := by
    intro A hA hsmall
    have hVA := (hPieces A hA).2.2 hsmall
    have hPV : V(P A) ⊆ segregationVertices 𝒮 := by
      rw [hVA]
      exact fun x hx => mem_iUnion₂.mpr ⟨A, hA, hx⟩
    apply exists_small_graph_edges_in_disc (P A)
      (hVA.symm ▸ A.Ω.finite_bar) (hEH.subset (hPieces A hA).1.edgeSet_mono)
      (by rw [hVA]; exact hsmall) (hArr.isClosedDisc A hA).1 pt
      (hArr.injOn_pts.mono hPV)
    intro x hx
    exact arrangement_pt_mem_discBd hS hArr hA (hVA ▸ hx)
  choose J hLine hLoop hInter hInc hSub hMeet using hex
  have hJcongr : ∀ (A B : Society α β) (hA : A ∈ 𝒮) (hB : B ∈ 𝒮)
      (hsA : A.Ω.bar.ncard ≤ 3) (hsB : B.Ω.bar.ncard ≤ 3),
      A = B → ∀ e, J A hA hsA e = J B hB hsB e := by
    intro A B hA hB hsA hsB hAB
    subst B
    intro e
    rfl
  have hOwner : ∀ e ∈ E(G₀), ∃ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 ∧ e ∈ F A := by
    intro e he
    have heSmall : e ∈ smallSocietyEdges 𝒮 F := hE₀ ▸ he
    exact heSmall
  choose owner hOwnerMem hOwnerSmall hOwnerEdge using hOwner
  let edgeOf : β → Set S := fun e => if he : e ∈ E(G₀) then
    J (owner e he) (hOwnerMem e he) (hOwnerSmall e he) e else ∅
  have hEdgeEq : ∀ e (he : e ∈ E(G₀)),
      edgeOf e = J (owner e he) (hOwnerMem e he) (hOwnerSmall e he) e := by
    intro e he
    exact dite_eq_left he
  have hOwnerPiece : ∀ e (he : e ∈ E(G₀)), e ∈ E(P (owner e he)) := by
    intro e he
    exact (hPieces _ (hOwnerMem e he)).2.1.symm ▸ hOwnerEdge e he
  have hCurveSub : ∀ e (he : e ∈ E(G₀)), edgeOf e ⊆ disc (owner e he) := by
    intro e he
    rw [hEdgeEq e he]
    exact hSub _ (hOwnerMem e he) (hOwnerSmall e he) e (hOwnerPiece e he)
  refine ⟨edgeOf, ?_, ?_, ?_, ?_, ?_⟩
  · intro e he x y hxy hne
    rw [hEdgeEq e he]
    exact hLine _ (hOwnerMem e he) (hOwnerSmall e he) e (hOwnerPiece e he) x y
      (((hPieces _ (hOwnerMem e he)).1.isLink_iff (hOwnerPiece e he)).mpr (hxy.mono hG₀)) hne
  · intro e he x hxx
    rw [hEdgeEq e he]
    exact hLoop _ (hOwnerMem e he) (hOwnerSmall e he) e (hOwnerPiece e he) x
      (((hPieces _ (hOwnerMem e he)).1.isLink_iff (hOwnerPiece e he)).mpr (hxx.mono hG₀))
  · intro e he f hf hef x ⟨hxe, hxf⟩
    by_cases howners : owner e he = owner f hf
    · rw [hEdgeEq e he, hJcongr _ _ (hOwnerMem e he) (hOwnerMem f hf)
        (hOwnerSmall e he) (hOwnerSmall f hf) howners e] at hxe
      rw [hEdgeEq f hf] at hxf
      obtain ⟨v, hv, rfl⟩ := hInter _ (hOwnerMem f hf) (hOwnerSmall f hf)
        e (howners ▸ hOwnerPiece e he) f (hOwnerPiece f hf) hef ⟨hxe, hxf⟩
      refine ⟨v, ?_, rfl⟩
      have hvBar := (hPieces _ (hOwnerMem f hf)).2.2 (hOwnerSmall f hf) ▸ hv
      exact mem_iUnion₂.mpr ⟨_, hOwnerMem f hf, hvBar⟩
    · obtain ⟨v, hv, rfl⟩ := hArr.inter_discs _ (hOwnerMem e he) _ (hOwnerMem f hf) howners
        ⟨hCurveSub e he hxe, hCurveSub f hf hxf⟩
      exact ⟨v, mem_iUnion₂.mpr ⟨_, hOwnerMem e he, hv.1⟩, rfl⟩
  · intro e he x hx hxe
    have hxBar := (arrangement_pt_mem_disc_iff hArr (hOwnerMem e he) hx).mp (hCurveSub e he hxe)
    have hxPiece : x ∈ V(P (owner e he)) :=
      (hPieces _ (hOwnerMem e he)).2.2 (hOwnerSmall e he) ▸ hxBar
    rw [hEdgeEq e he] at hxe
    have hIncP := hInc _ (hOwnerMem e he) (hOwnerSmall e he) e (hOwnerPiece e he) x hxPiece hxe
    exact (hG₀.inc_congr he).mpr (hIncP.mono (hPieces _ (hOwnerMem e he)).1)
  · intro A hA hlarge e he x ⟨hxe, hxA⟩
    have hne : owner e he ≠ A := fun heq => by
      have hsmall := hOwnerSmall e he
      rw [heq] at hsmall
      exact not_lt_of_ge hsmall hlarge
    obtain ⟨v, hv, rfl⟩ := hArr.inter_discs _ (hOwnerMem e he) A hA hne
      ⟨hCurveSub e he hxe, hxA⟩
    exact ⟨v, mem_iUnion₂.mpr ⟨A, hA, hv.2⟩, rfl⟩

end GraphMinor.GM16
