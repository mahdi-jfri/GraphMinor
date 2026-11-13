module

public import GraphMinor.Compute.Algorithm99TransportRural

/-!
# Keeping a rural drawing under a graph isomorphism

The rural division in step (5) of XIII (9.9) is tested on a bipartite graph.
Restoring loops and parallel edges changes the names of its member vertices,
but not its edges or its drawing. This file transports a rural society along
a graph isomorphism that preserves the names and order of boundary vertices.
The drawing itself and its two discs stay the same.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.Transport Classical

universe u u' v v' w

/-- A drawing of `G` is also a drawing of an isomorphic graph `H`. -/
noncomputable def case3IsoDrawing {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    (iso : GraphMinor.Iso G H) {S : Type w} [TopologicalSpace S]
    (Γ : GraphDrawing G S) : GraphDrawing H S where
  drawing := Γ.drawing
  iso :=
    { vertexEquiv := iso.vertexEquiv.symm.trans Γ.iso.vertexEquiv
      edgeEquiv := iso.edgeEquiv.symm.trans Γ.iso.edgeEquiv
      isLink_iff := by
        intro e x y
        have hi := iso.isLink_iff (iso.edgeEquiv.symm e)
          (iso.vertexEquiv.symm x) (iso.vertexEquiv.symm y)
        simp only [Equiv.apply_symm_apply] at hi
        exact hi.symm.trans (Γ.iso.isLink_iff _ _ _) }

/-- The same point represents corresponding vertices in the transported drawing. -/
theorem case3IsoDrawing_vertexSet {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    (iso : GraphMinor.Iso G H) {S : Type w} [TopologicalSpace S]
    (Γ : GraphDrawing G S) (a : V(G)) :
    graphDrawingVertexSet (case3IsoDrawing iso Γ) (iso.vertexEquiv a).1 =
      graphDrawingVertexSet Γ a.1 := by
  ext p
  constructor
  · rintro ⟨ha, hp⟩
    refine ⟨a.2, ?_⟩
    have heq : (⟨(iso.vertexEquiv a).1, ha⟩ : V(H)) = iso.vertexEquiv a := Subtype.ext rfl
    change (Γ.iso.vertexEquiv (iso.vertexEquiv.symm ⟨_, ha⟩)).1 = p at hp
    simpa only [heq, Equiv.symm_apply_apply] using hp
  · rintro ⟨ha, hp⟩
    refine ⟨(iso.vertexEquiv a).2, ?_⟩
    change (Γ.iso.vertexEquiv (iso.vertexEquiv.symm (iso.vertexEquiv a))).1 = p
    simpa only [Equiv.symm_apply_apply] using hp

private theorem case3DrawingAgrees_empty {α : Type u} {β : Type v}
    {G : Graph α β} {S : Type w} [TopologicalSpace S]
    (Γ : GraphDrawing G S) (Ω : CyclicPerm α) (hΩ : Ω.bar = ∅)
    (C : Set S) (φ : Circle ≃ₜ C) : DrawingAgreesWithOArcHomeo Γ Ω C φ := by
  refine ⟨?_, ?_⟩
  · intro a ha
    exact False.elim (show a ∈ (∅ : Set α) from hΩ ▸ ha)
  · intro a b c habc
    have ha := habc.2.1 a (by simp)
    exact False.elim (show a ∈ (∅ : Set α) from hΩ ▸ ha)

/-- Rurality is preserved by a graph isomorphism that agrees with the boundary
renaming. The embedding `f` is required to describe only boundary vertices.
Member vertices of a division may be renamed by a different bijection. -/
theorem case3RuralSociety_of_boundaryIso {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {S : Society α β} {S' : Society α' β'}
    (iso : GraphMinor.Iso S.G S'.G) (f : α ↪ α')
    (hΩ : S'.Ω = relabelCyclicPerm f S.Ω)
    (hiso : ∀ a (ha : a ∈ S.Ω.bar),
      (iso.vertexEquiv ⟨a, S.bar_subset ha⟩).1 = f a)
    (hR : S.IsRuralSociety) : S'.IsRuralSociety := by
  obtain ⟨Ω₀, h₀, hempty, Γ, Δ, Δ₀, hΔ, hsub, hU, hbd, hbd₀, ⟨φ, hφ, hag⟩, hinner⟩ := hR
  dsimp only at hbd hbd₀ hag hinner
  let Γ' := case3IsoDrawing iso Γ
  let Ω₀' := relabelCyclicPerm f Ω₀
  have hempty' : Ω₀'.bar = ∅ := by
    rw [relabelCyclicPerm_bar, hempty, Set.image_empty]
  have h₀' : Ω₀'.bar ⊆ V(S'.G) := by rw [hempty']; exact Set.empty_subset _
  have hpoint : ∀ a (ha : a ∈ S.Ω.bar),
      graphDrawingVertexSet Γ' (f a) = graphDrawingVertexSet Γ a := by
    intro a ha
    rw [← hiso a ha]
    exact case3IsoDrawing_vertexSet iso Γ ⟨a, S.bar_subset ha⟩
  have hbar : ∀ a : V(S.G), (iso.vertexEquiv a).1 ∈ S'.Ω.bar ↔ a.1 ∈ S.Ω.bar := by
    intro a
    rw [hΩ, relabelCyclicPerm_bar]
    constructor
    · rintro ⟨b, hb, heq⟩
      have hi : iso.vertexEquiv ⟨b, S.bar_subset hb⟩ = iso.vertexEquiv a :=
        Subtype.ext ((hiso b hb).trans heq)
      exact congrArg Subtype.val (iso.vertexEquiv.injective hi) ▸ hb
    · intro ha
      exact ⟨a.1, ha, (hiso a.1 ha).symm⟩
  refine ⟨Ω₀', h₀', hempty', Γ', Δ, Δ₀, hΔ, hsub, hU, ?_, ?_, ⟨φ, hφ, ?_⟩, ?_⟩
  · intro a ha
    let a₀ := iso.vertexEquiv.symm ⟨a, ha⟩
    have he : iso.vertexEquiv a₀ = ⟨a, ha⟩ := iso.vertexEquiv.apply_symm_apply _
    have hp := case3IsoDrawing_vertexSet iso Γ a₀
    rw [he] at hp
    rw [hp, hbd a₀.1 a₀.2]
    exact (by simpa only [he] using (hbar a₀).symm)
  · intro a ha
    let a₀ := iso.vertexEquiv.symm ⟨a, ha⟩
    have he : iso.vertexEquiv a₀ = ⟨a, ha⟩ := iso.vertexEquiv.apply_symm_apply _
    have hp := case3IsoDrawing_vertexSet iso Γ a₀
    rw [he] at hp
    change graphDrawingVertexSet Γ' a ⊆ subBd Δ₀ ↔ a ∈ Ω₀'.bar
    rw [hp, hbd₀ a₀.1 a₀.2, hempty, hempty']
    exact Iff.rfl
  · change DrawingAgreesWithOArcHomeo Γ' S'.Ω (subBd Δ) φ
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [hΩ, relabelCyclicPerm_bar] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [hpoint b hb]
      exact hag.1 b hb
    · intro a b c habc
      rw [hΩ] at habc
      obtain ⟨a₀, b₀, c₀, rfl, rfl, rfl, hclock⟩ :=
        exists_of_isClockwise3_relabelCyclicPerm f S.Ω habc
      have ha₀ := hclock.2.1 a₀ (by simp)
      have hb₀ := hclock.2.1 b₀ (by simp)
      have hc₀ := hclock.2.1 c₀ (by simp)
      simpa only [hpoint a₀ ha₀, hpoint b₀ hb₀, hpoint c₀ hc₀] using hag.2 a₀ b₀ c₀ hclock
  · rcases hinner with ⟨hΔ₀, _⟩ | ⟨hΔ₀, φ₀, hφ₀, _⟩
    · exact Or.inl ⟨hΔ₀, hempty'⟩
    · exact Or.inr ⟨hΔ₀, φ₀, hφ₀, case3DrawingAgrees_empty Γ' Ω₀' hempty' _ φ₀⟩

end GraphMinor.Compute
