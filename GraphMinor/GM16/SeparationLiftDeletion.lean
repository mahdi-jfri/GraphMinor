module

public import GraphMinor.GM16.SeparationLift
import GraphMinor.GM09.Basic

/-!
# Deleting the restored vertices recovers a separation

The pairs lifted in XVI (1.3), page 51, restrict to the original
pairs after the exceptional set is removed. We first compare their
edge sets on `G` with `Z` deleted, then prove equality of the recovered
vertex and edge sets. This also shows the lifting map is injective.
-/

public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09
universe u v

/-- Vertex deletion preserves subgraph inclusion. -/
theorem deleteVertices_mono {α : Type u} {β : Type v}
    {G H : Graph α β} (h : H ≤ G) (Z : Set α) :
    deleteVertices H Z ≤ deleteVertices G Z := by
  refine ⟨fun x hx => ⟨h.vertexSet_mono hx.1, hx.2⟩, ?_⟩
  intro e x y hxy
  obtain ⟨hH, hx, hy⟩ := (deleteVertices_isLink H Z).mp hxy
  exact (deleteVertices_isLink G Z).mpr ⟨hH.mono h, hx, hy⟩

/-- On edges of the graph with `Z` deleted, the lifted right side is
exactly the original right side. -/
theorem mem_liftSeparationRight_iff {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} {p : Graph α β × Graph α β}
    (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2)
    {e : β} (he : e ∈ E(deleteVertices G Z)) :
    e ∈ E(liftSeparationRight G Z p) ↔ e ∈ E(p.2) := by
  constructor
  · intro heR
    have heUnion : e ∈ E(p.1) ∪ E(p.2) := hp.2.2.2.1.symm ▸ he
    exact heUnion.resolve_left heR.2.2
  · intro heB
    obtain ⟨x, y, hxy⟩ := p.2.exists_isLink_of_mem_edgeSet heB
    have hxyG := hxy.mono (hp.2.1.trans (deleteVertices_le G Z))
    exact ⟨⟨x, y, hxyG, Or.inl hxy.left_mem, Or.inl hxy.right_mem⟩,
      hxyG.edge_mem, fun heA => disjoint_left.mp hp.2.2.2.2 heA heB⟩

/-- On edges outside `Z`, the lifted left side is exactly the original
left side. -/
theorem mem_liftSeparationLeft_iff {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} {p : Graph α β × Graph α β}
    (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2)
    {e : β} (he : e ∈ E(deleteVertices G Z)) :
    e ∈ E(liftSeparationLeft G Z p) ↔ e ∈ E(p.1) := by
  rw [liftSeparationLeft_edgeSet hp]
  constructor
  · rintro ⟨_, heNot⟩
    have heUnion : e ∈ E(p.1) ∪ E(p.2) := hp.2.2.2.1.symm ▸ he
    exact heUnion.resolve_right (fun heB => heNot ((mem_liftSeparationRight_iff hp he).mpr heB))
  · intro heA
    exact ⟨(deleteVertices_le G Z).edgeSet_mono he,
      fun heR => disjoint_left.mp hp.2.2.2.2 heA ((mem_liftSeparationRight_iff hp he).mp heR)⟩

/-- Recover a graph from its edges outside `Z` and its vertex set. -/
theorem deleteVertices_eq_of_source_edges {α : Type u} {β : Type v}
    {G H A : Graph α β} {Z : Set α} (hHG : H ≤ G) (hA : A ≤ deleteVertices G Z)
    (hV : V(H) = V(A) ∪ Z)
    (hE : ∀ e ∈ E(deleteVertices G Z), e ∈ E(H) ↔ e ∈ E(A)) :
    deleteVertices H Z = A := by
  have hDel := deleteVertices_mono hHG Z
  refine (Compatible.of_le_le hDel hA).ext ?_ ?_
  · rw [vertexSet_deleteVertices, hV]
    ext x
    constructor
    · rintro ⟨hxA | hxZ, hxNot⟩
      · exact hxA
      · exact (hxNot hxZ).elim
    · intro hx
      exact ⟨Or.inl hx, (hA.vertexSet_mono hx).2⟩
  · ext e
    constructor
    · intro he
      exact (hE e (hDel.edgeSet_mono he)).mp ((deleteVertices_le H Z).edgeSet_mono he)
    · intro he
      have heSource := hA.edgeSet_mono he
      have heH := (hE e heSource).mpr he
      obtain ⟨x, y, hxy⟩ := A.exists_isLink_of_mem_edgeSet he
      have hxyH := (hHG.isLink_iff heH).mpr (hxy.mono (hA.trans (deleteVertices_le G Z)))
      exact ((deleteVertices_isLink H Z).mpr
        ⟨hxyH, (hA.vertexSet_mono hxy.left_mem).2, (hA.vertexSet_mono hxy.right_mem).2⟩).edge_mem

/-- Deleting `Z` from either side of the lifted pair recovers its
original side, as required in XVI (1.3), page 51. -/
theorem deleteVertices_liftLocationPair {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {p : Graph α β × Graph α β} (hp : IsGraphSeparation (deleteVertices G Z) p.1 p.2) :
    deleteVertices (liftSeparationLeft G Z p) Z = p.1 ∧
      deleteVertices (liftSeparationRight G Z p) Z = p.2 := by
  obtain ⟨hLeft, hRight⟩ := liftLocationPair_le hZ hp
  exact ⟨deleteVertices_eq_of_source_edges hLeft hp.1 rfl
      (fun _ he => mem_liftSeparationLeft_iff hp he),
    deleteVertices_eq_of_source_edges hRight hp.2.1 rfl
      (fun _ he => mem_liftSeparationRight_iff hp he)⟩

/-- A lifted pair determines the original pair. -/
theorem liftLocationPair_injOn {α : Type u} {β : Type v}
    {G : Graph α β} {Z : Set α} (hZ : Z ⊆ V(G))
    {ℒ : Set (Graph α β × Graph α β)} (h : IsGraphLocation (deleteVertices G Z) ℒ) :
    InjOn (liftLocationPair G Z) ℒ := by
  intro p hp q hq heq
  have hL := congrArg (fun r => deleteVertices r.1 Z) heq
  have hR := congrArg (fun r => deleteVertices r.2 Z) heq
  dsimp only [liftLocationPair] at hL hR
  rw [(deleteVertices_liftLocationPair hZ (h.isSeparation hp)).1,
    (deleteVertices_liftLocationPair hZ (h.isSeparation hq)).1] at hL
  rw [(deleteVertices_liftLocationPair hZ (h.isSeparation hp)).2,
    (deleteVertices_liftLocationPair hZ (h.isSeparation hq)).2] at hR
  exact Prod.ext hL hR

end GraphMinor.GM16
