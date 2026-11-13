module

public import GraphMinor.GM16.SeparationLiftDeletion
public import GraphMinor.GM16.LocationCore
import GraphMinor.GM09.Basic

/-!
# Restoring exceptional vertices to a location

The pairs lifted in XVI (1.3), page 51, form a location. The old
left-to-right inclusions remain true because all exceptional vertices
are put on both sides, and the right sides keep every available edge.
Deleting the exceptional set from its core recovers the old core.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- The location `ℒ⁺` in the proof of XVI (1.3), page 51. -/
def liftedLocation {α : Type u} {β : Type v} (G : Graph α β) (Z : Set α)
    (ℒ : Set (Graph α β × Graph α β)) : Set (Graph α β × Graph α β) :=
  liftLocationPair G Z '' ℒ

private theorem lift_left_le_right {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {p q : Graph α β × Graph α β}
    (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2)
    (hq : IsGraphSeparation (deleteVertices G Z) q.1 q.2)
    (hpq : p.1 ≤ q.2) (hqp : q.1 ≤ p.2) :
    liftSeparationLeft G Z p ≤ liftSeparationRight G Z q := by
  have hLeft := (liftLocationPair_le hZ hp).1
  have hRight := (liftLocationPair_le hZ hq).2
  have hV : V(p.1) ∪ Z ⊆ V(q.2) ∪ Z := union_subset_union_left Z hpq.vertexSet_mono
  rw [(Compatible.of_le_le hLeft hRight).le_iff]
  refine ⟨hV, ?_⟩
  intro e he
  obtain ⟨x, y, hxy⟩ := (liftSeparationLeft G Z p).exists_isLink_of_mem_edgeSet he
  have hxyG := hxy.mono hLeft
  have heNotQ : e ∉ E(q.1) := by
    intro heQ
    have heSource := hq.1.edgeSet_mono heQ
    have heP := (mem_liftSeparationRight_iff hp heSource).mpr (hqp.edgeSet_mono heQ)
    exact he.2.2 heP
  exact ⟨⟨x, y, hxyG, hV hxy.left_mem, hV hxy.right_mem⟩, hxyG.edge_mem, heNotQ⟩

/-- The lifted pairs form a location, as claimed on page 51 of XVI. -/
theorem IsGraphLocation.lift {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ) :
    IsGraphLocation G (liftedLocation G Z ℒ) := by
  refine ⟨h.finite.image _, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact (liftLocationPair_isSeparation hZ (h.isSeparation hp)).1
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hpq : p ≠ q := fun heq => hne (congrArg (liftLocationPair G Z) heq)
    exact lift_left_le_right hZ (h.isSeparation hp) (h.isSeparation hq)
      (h.left_le_right hp hq hpq) (h.left_le_right hq hp (fun heq => hpq heq.symm))

/-- A lifted separator has at most `|Z|` more vertices than its source. -/
theorem liftedLocation_separator_bound {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ)
    {k : ℕ} (hOrder : ∀ p ∈ ℒ, (V(p.1) ∩ V(p.2)).ncard ≤ k)
    {p : Graph α β × Graph α β} (hp : p ∈ liftedLocation G Z ℒ) :
    (V(p.1) ∩ V(p.2)).ncard ≤ Z.ncard + k := by
  obtain ⟨q, hq, rfl⟩ := hp
  dsimp only [liftLocationPair]
  rw [(liftLocationPair_isSeparation hZ (h.isSeparation hq)).2]
  exact (ncard_union_le Z _).trans (Nat.add_le_add_left (hOrder q hq) _)

/-- The lifted core has the old vertices together with `Z`. -/
theorem vertexSet_lifted_core {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    (ℒ : Set (Graph α β × Graph α β)) :
    V(graphLocationCore G (liftedLocation G Z ℒ)) =
      V(graphLocationCore (deleteVertices G Z) ℒ) ∪ Z := by
  ext x
  constructor
  · rintro ⟨hxG, hxAll⟩
    by_cases hxZ : x ∈ Z
    · exact Or.inr hxZ
    · left
      refine ⟨⟨hxG, hxZ⟩, ?_⟩
      intro p hp
      have hxRight : x ∈ V(p.2) ∪ Z := hxAll _ (mem_image_of_mem _ hp)
      exact hxRight.resolve_right hxZ
  · rintro (⟨⟨hxG, hxZ⟩, hxAll⟩ | hxZ)
    · refine ⟨hxG, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact Or.inl (hxAll p hp)
    · refine ⟨hZ hxZ, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      exact Or.inr hxZ

/-- Deleting the exceptional vertices from the lifted core recovers
exactly the old core. -/
theorem deleteVertices_lifted_core {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ) :
    deleteVertices (graphLocationCore G (liftedLocation G Z ℒ)) Z =
      graphLocationCore (deleteVertices G Z) ℒ := by
  apply deleteVertices_eq_of_source_edges (graphLocationCore_le G _)
    (graphLocationCore_le (deleteVertices G Z) ℒ) (vertexSet_lifted_core hZ ℒ)
  intro e he
  rw [edgeSet_graphLocationCore (h.lift hZ), edgeSet_graphLocationCore h]
  constructor
  · rintro ⟨_, heAll⟩
    refine ⟨he, ?_⟩
    intro p hp
    exact (mem_liftSeparationRight_iff (h.isSeparation hp) he).mp
      (heAll _ (mem_image_of_mem _ hp))
  · rintro ⟨_, heAll⟩
    refine ⟨(deleteVertices_le G Z).edgeSet_mono he, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    exact (mem_liftSeparationRight_iff (h.isSeparation hp) he).mpr (heAll p hp)

end GraphMinor.GM16
