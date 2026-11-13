module

public import GraphMinor.GM08.Section15Tube
public import GraphMinor.GM07.Matched
import GraphMinor.GM08.Section15ImageIso
import GraphMinor.GM08.Section12Subspace

/-!
# Transporting a framing to a boundary-rooted drawing

Carry the original vertex and edge labels into the capped sphere and
then into the cylindrical complement. The exact boundary-root equality
shows that the resulting proper drawing has the original graft's root
set. This is the label and root transport used in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface Graph

universe u v w

/-- Transport a framing through an embedded image drawing and a proper
drawing of the same graph whose boundary vertices are exactly its
framing roots. This is the root-preserving label transport in the
short-tube proof of VIII (15.4), page 282. -/
theorem exists_graftDrawing_of_framing_image {S Y Q : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] [TopologicalSpace Q]
    [T2Space Y] {α : Type u} {β : Type v} {τ : Tube S} {X : Graft α β}
    (fr : τ.Framing X) {j : S → Y} (hj : IsEmbedding j)
    {G : Drawing Y} (hm : GM07.IsMatched τ.Γ G j ∅)
    (H : Drawing Q) (hH : H.IsProper) (i : Iso H.toGraph G.toGraph)
    {k : Q → Y} (hk : Function.Injective k)
    (hiv : ∀ v : H.V, (i.vertexEquiv v).1 = k v.1)
    (hroots : k '' (H.V ∩ bd Q) = j '' (τ.Γ.V ∩ (τ.F₁ ∪ τ.F₂))) :
    ∃ gd : GraftDrawing X.G X.T Q, gd.drawing = H := by
  have : CompactSpace S := τ.isCylinder.compactSpace
  have : T2Space S := τ.t2Space
  let a := (isGraphBij_of_matched_embedding hj hm).toIso
  have hinv : ∀ (e : E(G.toGraph)) (x y : V(G.toGraph)),
      G.toGraph.IsLink e.1 x.1 y.1 ↔
        H.toGraph.IsLink (i.edgeEquiv.symm e).1
          (i.vertexEquiv.symm x).1 (i.vertexEquiv.symm y).1 := by
    intro e x y
    have h := i.isLink_iff (i.edgeEquiv.symm e) (i.vertexEquiv.symm x) (i.vertexEquiv.symm y)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let b : Iso X.G H.toGraph := {
    vertexEquiv := fr.iso.vertexEquiv.trans (a.vertexEquiv.trans i.vertexEquiv.symm)
    edgeEquiv := fr.iso.edgeEquiv.trans (a.edgeEquiv.trans i.edgeEquiv.symm)
    isLink_iff := fun e x y => (fr.iso.isLink_iff e x y).trans
      ((a.isLink_iff _ _ _).trans (hinv _ _ _)) }
  have hcoord : ∀ v : V(X.G), k (b.vertexEquiv v).1 = j (fr.iso.vertexEquiv v).1 := by
    intro v
    rw [← hiv (b.vertexEquiv v)]
    change (i.vertexEquiv (i.vertexEquiv.symm (a.vertexEquiv (fr.iso.vertexEquiv v)))).1 = _
    rw [Equiv.apply_symm_apply]
    rfl
  refine ⟨{
    drawing := H
    iso := b
    isProper := hH
    T_subset_V := X.T_subset
    mem_bd_iff := ?_ }, rfl⟩
  intro v hv
  let x : V(X.G) := ⟨v, hv⟩
  have hxH : (b.vertexEquiv x).1 ∈ H.V := (b.vertexEquiv x).2
  have hrootiff : (b.vertexEquiv x).1 ∈ bd Q ↔
      (fr.iso.vertexEquiv x).1 ∈ τ.F₁ ∪ τ.F₂ := by
    constructor
    · intro hb
      have him : k (b.vertexEquiv x).1 ∈ j '' (τ.Γ.V ∩ (τ.F₁ ∪ τ.F₂)) :=
        hroots ▸ mem_image_of_mem k ⟨hxH, hb⟩
      rw [hcoord x] at him
      obtain ⟨z, hz, heq⟩ := him
      exact hj.injective heq ▸ hz.2
    · intro hb
      have him : k (b.vertexEquiv x).1 ∈ k '' (H.V ∩ bd Q) := by
        rw [hroots, hcoord x]
        exact mem_image_of_mem j ⟨(fr.iso.vertexEquiv x).2, hb⟩
      obtain ⟨z, hz, heq⟩ := him
      exact hk heq ▸ hz.2
  exact hrootiff.trans (fr.mem_F_iff x)

end GraphMinor.GM08
