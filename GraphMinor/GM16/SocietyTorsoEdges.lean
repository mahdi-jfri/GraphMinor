module

public import GraphMinor.GM16.SocietyLocationCores
import GraphMinor.GM09.Basic

/-!
# Partitioning the torso edges among societies

The location core in XVI (1.3), page 51, is edgeless. Every torso edge
therefore has both ends in one of its separator sets. We choose such a
separator for each edge and assign the edge to its society. The resulting
edge sets are disjoint, cover the torso, and have the local separator
property needed for the ring pieces and the drawn small pieces.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- Each edge of a torso of the assembled location has its ends in
one local separator. This identifies its society in XVI, page 51. -/
theorem exists_local_separator_for_torso_edge {α : Type u} {β : Type v}
    {G H : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    (hCover : ∀ A ∈ 𝒮, ∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1))
    (hTorso : IsTorsoOfDesign
      (graphLocationDesign G (assembledSocietyLocation G 𝒮 ℒ)) H)
    {e : β} (he : e ∈ E(H)) :
    ∃ A ∈ 𝒮, ∃ p ∈ ℒ A, ∀ x, H.Inc e x → x ∈ V(p.1) ∩ V(p.2) := by
  have hEmpty := assembled_core_edgeSet_eq_empty hSeg hLocal hBoundary hCover
  have heNew : e ∈ E(H) \ E(graphLocationCore G (assembledSocietyLocation G 𝒮 ℒ)) := by
    rw [hEmpty]
    exact ⟨he, notMem_empty e⟩
  obtain ⟨X, ⟨p, hp, rfl⟩, hEnds⟩ := hTorso.2.2 e heNew
  obtain ⟨A, hA, q, hq, _, hcut⟩ :=
    assembledSocietyLocation_separator hSeg hLocal hBoundary hp
  refine ⟨A, hA, q, hq, ?_⟩
  intro x hx
  have hxCut : x ∈ V(p.1) ∩ V(p.2) := hEnds x hx
  rw [hcut] at hxCut
  exact hxCut

/-- Choose the society of each torso edge using its separator.
The pieces share vertices on the boundaries but no edges. -/
theorem exists_society_torso_edge_partition {α : Type u} {β : Type v}
    {G H : Graph α β} {𝒮 : Set (Society α β)}
    {ℒ : Society α β → Set (Graph α β × Graph α β)}
    (hSeg : IsGraphSegregation G 𝒮)
    (hLocal : ∀ A ∈ 𝒮, IsGraphLocation A.G (ℒ A))
    (hBoundary : ∀ A ∈ 𝒮, ∀ p ∈ ℒ A, A.Ω.bar ⊆ V(p.2))
    (hCover : ∀ A ∈ 𝒮, ∀ e ∈ E(A.G), ∃ p ∈ ℒ A, e ∈ E(p.1))
    (hTorso : IsTorsoOfDesign
      (graphLocationDesign G (assembledSocietyLocation G 𝒮 ℒ)) H) :
    ∃ F : Society α β → Set β,
      (∀ A, F A ⊆ E(H)) ∧
      (Pairwise fun A B => Disjoint (F A) (F B)) ∧
      (⋃ A ∈ 𝒮, F A) = E(H) ∧
      (∀ A ∈ 𝒮, ∀ e ∈ F A, ∃ p ∈ ℒ A,
        ∀ x, H.Inc e x → x ∈ V(p.1) ∩ V(p.2)) := by
  classical
  have hex : ∀ e ∈ E(H), ∃ A ∈ 𝒮, ∃ p ∈ ℒ A,
      ∀ x, H.Inc e x → x ∈ V(p.1) ∩ V(p.2) := fun _ he =>
    exists_local_separator_for_torso_edge hSeg hLocal hBoundary hCover hTorso he
  choose owner hOwner sep hSep hEnds using hex
  let F : Society α β → Set β := fun A => {e | ∃ he : e ∈ E(H), owner e he = A}
  refine ⟨F, fun A e he => he.choose, ?_, ?_, ?_⟩
  · intro A B hAB
    refine disjoint_left.mpr ?_
    rintro e ⟨he, hA⟩ ⟨he', hB⟩
    exact hAB (hA.symm.trans hB)
  · ext e
    constructor
    · intro heUnion
      obtain ⟨A, _, he⟩ := mem_iUnion₂.mp heUnion
      exact he.choose
    · intro he
      exact mem_iUnion₂.mpr ⟨owner e he, hOwner e he, he, rfl⟩
  · intro A hA e he
    obtain ⟨heH, hOwnerEq⟩ := he
    subst A
    exact ⟨sep e heH, hSep e heH, hEnds e heH⟩

end GraphMinor.GM16
