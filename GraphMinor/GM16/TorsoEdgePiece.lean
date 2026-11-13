module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# Assigning torso edges to a local design

The core of the location in XVI (1.3), page 51, has no edges.
Its torso edges are assigned to societies using the separator that
contains their ends. Restricting the global torso to one assigned edge
set gives a torso of the corresponding local design.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The part of a torso assigned to one local design in XVI, page 51. -/
def torsoEdgePiece {α : Type u} {β : Type v} (H : Graph α β)
    (d : GraphDesign α β) (F : Set β) : Graph α β :=
  (H.induce V(d.1)).restrict F

/-- Restricting an induced graph to edges whose ends all lie in the
inducing vertex set keeps exactly those edges. -/
theorem edgeSet_induce_restrict_eq_of_ends_subset
    {α : Type u} {β : Type v} {H : Graph α β} {W : Set α} {F : Set β}
    (hF : F ⊆ E(H)) (hEnds : ∀ e ∈ F, ∀ x, H.Inc e x → x ∈ W) :
    E((H.induce W).restrict F) = F := by
  ext e
  change e ∈ E(H.induce W) ∩ F ↔ e ∈ F
  refine ⟨fun he => he.2, fun he => ⟨?_, he⟩⟩
  obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hF he)
  exact ⟨x, y, hxy, hEnds e he x ⟨y, hxy⟩, hEnds e he y ⟨x, hxy.symm⟩⟩

/-- Assigned edges whose ends lie in local design sets form a torso
of the local design. Its original core is edgeless in the construction
of XVI (1.3). -/
theorem torsoEdgePiece_isTorso {α : Type u} {β : Type v}
    {H : Graph α β} {d : GraphDesign α β} {F : Set β}
    (hDesign : IsGraphDesign d) (hV : V(d.1) ⊆ V(H)) (hE : E(d.1) = ∅)
    (hF : F ⊆ E(H))
    (hEnds : ∀ e ∈ F, ∃ X ∈ d.2, ∀ x, H.Inc e x → x ∈ X) :
    IsTorsoOfDesign d (torsoEdgePiece H d F) ∧
      E(torsoEdgePiece H d F) = F ∧ torsoEdgePiece H d F ≤ H := by
  have hle : torsoEdgePiece H d F ≤ H := restrict_le.trans (H.induce_le hV)
  have hEF : E(torsoEdgePiece H d F) = F := by
    ext e
    change e ∈ E(H.induce V(d.1)) ∩ F ↔ e ∈ F
    refine ⟨fun he => he.2, fun he => ⟨?_, he⟩⟩
    obtain ⟨x, y, hxy⟩ := H.exists_isLink_of_mem_edgeSet (hF he)
    obtain ⟨X, hX, hends⟩ := hEnds e he
    exact ⟨x, y, hxy, hDesign.2.2 hX (hends x ⟨y, hxy⟩),
      hDesign.2.2 hX (hends y ⟨x, hxy.symm⟩)⟩
  refine ⟨⟨rfl, ?_, ?_⟩, hEF, hle⟩
  · refine ⟨Subset.refl _, ?_⟩
    intro e x y hxy
    exact (notMem_empty e (hE ▸ hxy.edge_mem)).elim
  · intro e he
    obtain ⟨X, hX, hends⟩ := hEnds e (hEF ▸ he.1)
    exact ⟨X, hX, fun x hx => hends x (hx.mono hle)⟩

end GraphMinor.GM16
