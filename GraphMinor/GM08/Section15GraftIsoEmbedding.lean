module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section14

/-!
# Transporting an embedded graft across its isomorphism

Compose the vertex and edge bijections with a graft drawing. The root
bijection gives exactly the same boundary condition. This keeps the
disc embedding after finite label transport in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface Graph

universe u v u' v' w

/-- Graft isomorphism preserves embeddability, including the precise
boundary root set. This transfers the labelled disc cut in the proof
of VIII (15.4), page 282. -/
theorem embedsGraft_of_isGraftIso {α : Type u} {β : Type v} {γ : Type u'} {δ : Type v'}
    {S : Type w} [TopologicalSpace S] {A : Graft α β} {B : Graft γ δ}
    (hi : IsGraftIso A B) (hA : EmbedsGraft S A) : EmbedsGraft S B := by
  obtain ⟨i, hT⟩ := hi.symm
  obtain ⟨gd⟩ := hA
  refine ⟨{
    drawing := gd.drawing
    iso := {
      vertexEquiv := i.vertexEquiv.trans gd.iso.vertexEquiv
      edgeEquiv := i.edgeEquiv.trans gd.iso.edgeEquiv
      isLink_iff := fun e x y => (i.isLink_iff e x y).trans (gd.iso.isLink_iff _ _ _) }
    isProper := gd.isProper
    T_subset_V := B.T_subset
    mem_bd_iff := ?_ }⟩
  intro v hv
  exact (gd.mem_bd_iff (i.vertexEquiv ⟨v, hv⟩).1 (i.vertexEquiv ⟨v, hv⟩).2).trans
    (hT ⟨v, hv⟩).symm

end GraphMinor.GM08
