module

public import GraphMinor.GM16.SocietyLocationChoices
public import GraphMinor.GM16.SocietyTorsoDecomposition
public import GraphMinor.GM16.BaseTorsoDrawing
import GraphMinor.Minor.Basic
import GraphMinor.GM14.Section7a
import GraphMinor.GM09.Basic

/-!
# The location with ring outgrowth torsos in XVI (1.3)

On page 51 the local locations from (3.2) and the small societies are
assembled into one location. Its torso pieces cover the graph. The
large pieces are rings and the small pieces give a drawing on the
surface. Properness separates the large discs and their ring pieces.
This supplies the details of the location and torso verification
omitted in the paper.
-/

public section
namespace GraphMinor.GM16
open Set Function Graph Surface GM06 GM09 GM14
universe u v w

/-- The location construction in Claim (1) of the proof of XVI (1.3),
page 51. Every finite torso is an outgrowth by at most `κ` rings of
width `2ρ + 1`, on the same surface as the proper arrangement. -/
theorem exists_location_with_ring_torsos
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    {α : Type u} {β : Type v} {G : Graph α β} {ρ κ : ℕ}
    {𝒮 : Set (Society α β)} {disc : Society α β → Set S} {pt : α → S}
    (hType : IsSegregationOfType G ρ κ 𝒮) (hProper : IsProperArrangement 𝒮 disc pt) :
    ∃ ℒ : Set (Graph α β × Graph α β),
      IsGraphLocation G ℒ ∧
      (∀ p ∈ ℒ, (V(p.1) ∩ V(p.2)).ncard ≤ max 3 (2 * ρ + 1)) ∧
      (∀ p ∈ ℒ, ∃ A ∈ 𝒮, p.1 ≤ A.G) ∧
      (∀ H : Graph α β, E(H).Finite →
        IsTorsoOfDesign (graphLocationDesign G ℒ) H →
          IsOutgrowthByRings S H κ (2 * ρ + 1)) ∧
      (∀ x ∈ V(G), ∃ p ∈ ℒ, x ∈ V(p.1)) := by
  classical
  obtain ⟨L, t, hSpec⟩ := exists_society_location_choices hType
  have hSeg := hType.isSegregation
  have hLocal := fun A hA => (hSpec A hA).1
  have hBoundary := fun A hA => (hSpec A hA).2.1
  have hCover := fun A hA => (hSpec A hA).2.2.2.1
  let ℒ := assembledSocietyLocation G 𝒮 L
  refine ⟨ℒ, assembledSocietyLocation_isLocation hSeg hLocal hBoundary, ?_, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨A, hA, q, hq, _, hcut⟩ := assembledSocietyLocation_separator hSeg hLocal hBoundary hp
    rw [hcut]
    exact (hSpec A hA).2.2.1 q hq
  · intro p hp
    obtain ⟨A, hA, q, hq, hleft, _⟩ := assembledSocietyLocation_separator hSeg hLocal hBoundary hp
    exact ⟨A, hA, hleft ▸ (hLocal A hA).isSeparation hq |>.1⟩
  · intro H hEH hTorso
    obtain ⟨F, P, hF, hDisjF, hUnionF, hPieces, hUnionV, hInterV⟩ :=
      exists_society_torso_decomposition hSeg hLocal hBoundary hCover hTorso
    have hSmallV : ∀ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 → V(P A) = A.Ω.bar := by
      intro A hA hsmall
      have hPT := (hPieces A hA).1
      rw [(hSpec A hA).2.2.2.2.1 hsmall] at hPT
      exact smallSocietyLocation_torso_vertices A hPT
    have hRing : ∀ A ∈ 𝒮, 3 < A.Ω.bar.ncard →
        (t A).Nodup ∧ {x | x ∈ t A} = A.Ω.bar ∧ A.Ω.IsClockwiseSeq (t A) ∧
        IsRRing (P A) (2 * ρ + 1) (t A) := by
      intro A hA hlarge
      obtain ⟨ht, hset, hcw, hR⟩ := (hSpec A hA).2.2.2.2.2.1 hlarge
      exact ⟨ht, hset, hcw, hR (P A) (hPieces A hA).1⟩
    have hV : segregationVertices 𝒮 ⊆ V(H) := fun x hx =>
      hTorso.1 ▸ segregationVertices_subset_assembled_core hSeg hBoundary hx
    have hPieceData : ∀ A ∈ 𝒮, P A ≤ H ∧ E(P A) = F A ∧
        (A.Ω.bar.ncard ≤ 3 → V(P A) = A.Ω.bar) :=
      fun A hA => ⟨(hPieces A hA).2.1, (hPieces A hA).2.2.1, hSmallV A hA⟩
    obtain ⟨edgeOf, hLine, hLoop, hEdgeInter, hInc, hDiscMeet⟩ :=
      exists_base_torso_drawing hS hEH hProper.1 hF hPieceData hV
    let G₀ := baseTorsoGraph H 𝒮 F
    have hG₀ : G₀ ≤ H := baseTorsoGraph_le hV
    have hSmallEnds : ∀ A ∈ 𝒮, A.Ω.bar.ncard ≤ 3 →
        ∀ e ∈ F A, ∀ x, H.Inc e x → x ∈ A.Ω.bar := by
      intro A hA hs e he x ⟨y, hxy⟩
      have heP : e ∈ E(P A) := (hPieces A hA).2.2.1.symm ▸ he
      exact hSmallV A hA hs ▸ (((hPieces A hA).2.1.isLink_iff heP).mpr hxy).left_mem
    have hE₀ : E(G₀) = smallSocietyEdges 𝒮 F := edgeSet_baseTorsoGraph hF hSmallEnds
    let Big : Set (Society α β) := {A ∈ 𝒮 | 3 < A.Ω.bar.ncard}
    let : Fintype Big := (hSeg.finite.subset (fun _ h => h.1)).fintype
    let k := Fintype.card Big
    let enum : Fin k ≃ Big := (Fintype.equivFin Big).symm
    let A : Fin k → Society α β := fun i => (enum i).1
    have hA : ∀ i, A i ∈ 𝒮 := fun i => (enum i).2.1
    have hLarge : ∀ i, 3 < (A i).Ω.bar.ncard := fun i => (enum i).2.2
    have hAinj : Injective A := fun i j hij => enum.injective (Subtype.ext hij)
    have hEnum : ∀ B ∈ 𝒮, 3 < B.Ω.bar.ncard → ∃ i, A i = B := by
      intro B hB hlarge
      exact ⟨enum.symm ⟨B, hB, hlarge⟩,
        congrArg Subtype.val (enum.apply_symm_apply ⟨B, hB, hlarge⟩)⟩
    have hk : k ≤ κ := by
      change Fintype.card Big ≤ κ
      rw [Set.fintypeCard_eq_ncard]
      exact hType.vortex_count_le
    refine ⟨H, G₀, ⟨Iso.refl H⟩, k, fun i => disc (A i), fun i => P (A i),
      fun i => t (A i), pt, edgeOf, hk, hG₀, fun i => (hPieces _ (hA i)).2.1,
      ?_, ?_, hProper.1.injOn_pts, hLine, hLoop, hEdgeInter, hInc,
      fun i => (hProper.1.isClosedDisc _ (hA i)).1, ?_, ?_, ?_, ?_, ?_,
      fun i => (hRing _ (hA i) (hLarge i)).2.2.2, ?_, ?_, ?_⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨B, hB, hxB⟩ := mem_iUnion₂.mp (hUnionV ▸ hx)
        by_cases hsmall : B.Ω.bar.ncard ≤ 3
        · left
          exact mem_iUnion₂.mpr ⟨B, hB, hSmallV B hB hsmall ▸ hxB⟩
        · right
          obtain ⟨i, rfl⟩ := hEnum B hB (Nat.lt_of_not_ge hsmall)
          exact mem_iUnion.mpr ⟨i, hxB⟩
      · rintro (hx | hx)
        · exact hG₀.vertexSet_mono hx
        · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
          exact (hPieces _ (hA i)).2.1.vertexSet_mono hxi
    · ext e
      constructor
      · intro he
        obtain ⟨B, hB, heB⟩ := mem_iUnion₂.mp (hUnionF.symm ▸ he)
        by_cases hsmall : B.Ω.bar.ncard ≤ 3
        · left
          rw [hE₀]
          exact ⟨B, hB, hsmall, heB⟩
        · right
          obtain ⟨i, rfl⟩ := hEnum B hB (Nat.lt_of_not_ge hsmall)
          exact mem_iUnion.mpr ⟨i, (hPieces _ (hA i)).2.2.1.symm ▸ heB⟩
      · rintro (he | he)
        · exact hG₀.edgeSet_mono he
        · obtain ⟨i, hei⟩ := mem_iUnion.mp he
          exact (hPieces _ (hA i)).2.1.edgeSet_mono hei
    · intro i j hij
      exact hProper.2 (hA i) (hA j) (fun heq => hij (hAinj heq)) (hLarge i) (hLarge j)
    · intro i e he
      exact hDiscMeet _ (hA i) (hLarge i) e he
    · intro i x hx hpt
      exact arrangement_pt_mem_discBd hS hProper.1 (hA i)
        ((arrangement_pt_mem_disc_iff hProper.1 (hA i) hx).mp hpt)
    · intro i
      ext x
      constructor
      · rintro ⟨hx, hpt⟩
        have hxBar := (arrangement_pt_mem_discBd_iff hS hProper.1 (hA i) hx).mp hpt
        exact (hRing _ (hA i) (hLarge i)).2.1.symm ▸ hxBar
      · intro hx
        have hxBar : x ∈ (A i).Ω.bar := (hRing _ (hA i) (hLarge i)).2.1 ▸ hx
        exact ⟨mem_iUnion₂.mpr ⟨A i, hA i, hxBar⟩,
          arrangement_pt_mem_discBd hS hProper.1 (hA i) hxBar⟩
    · intro i
      refine ⟨(A i).Ω, (hRing _ (hA i) (hLarge i)).2.1.symm,
        (hRing _ (hA i) (hLarge i)).2.2.1, ?_⟩
      rw [← GM14.IsClosedDisc.subBd_eq_discBd hS (hProper.1.isClosedDisc _ (hA i)).1]
      exact hProper.1.natural_order _ (hA i)
    · intro i
      exact (hPieces _ (hA i)).2.2.2.2.trans (hRing _ (hA i) (hLarge i)).2.1.symm
    · intro i
      refine disjoint_left.mpr ?_
      intro e hei he₀
      have heFi : e ∈ F (A i) := (hPieces _ (hA i)).2.2.1 ▸ hei
      obtain ⟨B, hB, hsmall, heFB⟩ := (hE₀ ▸ he₀ : e ∈ smallSocietyEdges 𝒮 F)
      have hne : A i ≠ B := fun heq => by
        have hli := hLarge i
        rw [heq] at hli
        exact not_lt_of_ge hsmall hli
      exact disjoint_left.mp (hDisjF hne) heFi heFB
    · intro i j hij
      have hne : A i ≠ A j := fun heq => hij (hAinj heq)
      refine ⟨disjoint_left.mpr ?_, ?_⟩
      · intro x hxi hxj
        have hx := hInterV _ (hA i) _ (hA j) hne ⟨hxi, hxj⟩
        exact disjoint_left.mp (proper_arrangement_large_boundaries_disjoint hProper
          (hA i) (hA j) hne (hLarge i) (hLarge j)) hx.1 hx.2
      · rw [(hPieces _ (hA i)).2.2.1, (hPieces _ (hA j)).2.2.1]
        exact hDisjF hne

  · exact assembledSocietyLocation_left_vertex_cover hSeg
      (fun A hA => (hSpec A hA).2.2.2.2.2.2)

end GraphMinor.GM16
