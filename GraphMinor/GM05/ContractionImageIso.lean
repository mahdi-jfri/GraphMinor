module

public import GraphMinor.GM05.CopyContractionClasses
import GraphMinor.GM05.DrawingContractionClasses
import Mathlib.Logic.Equiv.Set

/-!
# Identifying a contraction from its vertex and edge maps

For GM V, (8.14), the geometric contraction gives the right vertex
fibres, the remaining edges bijectively, and the images of their ends.
These data identify its graph with the abstract contraction. Choose
one representative of each contraction class. Equal fibres make its
image independent of that representative and give a vertex bijection.
-/

public section
namespace GraphMinor.GM05
open Set Graph

/-- Bijections on the actual vertex and edge supports identify a
quotient graph with a contraction, without extending maps to unused
vertex or edge names. -/
theorem exists_iso_contraction_of_support_maps {α β α' β' : Type*}
    (G : Graph α β) (K : Graph α' β') (C : Set β)
    (f : V(G) → V(K)) (hfs : Function.Surjective f)
    (hker : ∀ x y : V(G),f x=f y ↔ y.val∈contractionClass G C x.val)
    (g : E(contract G C) → E(K)) (hgb : Function.Bijective g)
    (hlink : ∀ (e : E(contract G C)) (x y : V(G)),G.IsLink e.val x.val y.val →
      K.IsLink (g e).val (f x).val (f y).val) :
    Nonempty (Iso (contract G C) K) := by
  classical
  have hrep : ∀ X : V(contract G C),∃ x : V(G),contractionClass G C x.val=X.val := by
    intro X
    have hX : X.val∈contractionClass G C '' V(G) := by
      simpa only [contract_vertexSet_eq] using X.prop
    obtain ⟨x,hx,hq⟩ := hX
    exact ⟨⟨x,hx⟩,hq⟩
  choose p hp using hrep
  let F : V(contract G C) → V(K) := fun X ↦ f (p X)
  have hFval (X : V(contract G C)) (x : V(G)) (hx : contractionClass G C x.val=X.val) :
      F X=f x :=
    (hker _ _).mpr ((contractionClass_eq_iff G C _ _).mp ((hp X).trans hx.symm))
  have hFinj : Function.Injective F := by
    intro X Y he
    have hxy := (hker (p X) (p Y)).mp he
    have hq := (contractionClass_eq_iff G C _ _).mpr hxy
    exact Subtype.ext ((hp X).symm.trans (hq.trans (hp Y)))
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨x,rfl⟩ := hfs y
    let X : V(contract G C) := ⟨contractionClass G C x.val,
      contract_vertexSet_eq G C ▸ mem_image_of_mem _ x.prop⟩
    exact ⟨X,hFval X x rfl⟩
  let ev : V(contract G C) ≃ V(K) := Equiv.ofBijective F ⟨hFinj,hFsurj⟩
  let ee : E(contract G C) ≃ E(K) := Equiv.ofBijective g hgb
  have hvclass (x : V(G)) (X : V(contract G C)) (he : f x=ev X) :
      contractionClass G C x.val=X.val :=
    ((contractionClass_eq_iff G C _ _).mpr ((hker x (p X)).mp he)).trans (hp X)
  refine ⟨⟨ev,ee,?_⟩⟩
  intro e X Y
  change (contract G C).IsLink e.val X.val Y.val ↔ K.IsLink (g e).val (ev X).val (ev Y).val
  constructor
  · intro hl
    obtain ⟨he,x,y,hxy,hx,hy⟩ := (contract_link_iff G C e.val X.val Y.val).mp hl
    have hvx : ev X=f ⟨x,hxy.left_mem⟩ := hFval X ⟨x,hxy.left_mem⟩ hx
    have hvy : ev Y=f ⟨y,hxy.right_mem⟩ := hFval Y ⟨y,hxy.right_mem⟩ hy
    rw [hvx,hvy]
    exact hlink e _ _ hxy
  · intro hl
    obtain ⟨a,b,hab⟩ := G.exists_isLink_of_mem_edgeSet e.prop.1
    have hk := hlink e ⟨a,hab.left_mem⟩ ⟨b,hab.right_mem⟩ hab
    apply (contract_link_iff G C e.val X.val Y.val).mpr
    refine ⟨e.prop.2,?_⟩
    rcases hk.isLink_iff.mp hl with ⟨ha,hb⟩|⟨ha,hb⟩
    · exact ⟨a,b,hab,hvclass ⟨a,hab.left_mem⟩ X (Subtype.ext ha),
        hvclass ⟨b,hab.right_mem⟩ Y (Subtype.ext hb)⟩
    · exact ⟨b,a,hab.symm,hvclass ⟨b,hab.right_mem⟩ X (Subtype.ext hb),
        hvclass ⟨a,hab.left_mem⟩ Y (Subtype.ext ha)⟩

/-- Vertex fibres and a bijection on the uncontracted edges identify
an image graph with the abstract contraction. -/
theorem exists_iso_contraction_of_image {α β α' β' : Type*}
    (G : Graph α β) (K : Graph α' β') (C : Set β) (f : α → α') (g : β → β')
    (hV : V(K)=f '' V(G))
    (hker : ∀ x∈V(G),∀ y∈V(G),f x=f y ↔ y∈contractionClass G C x)
    (hE : BijOn g (E(G)\C) E(K))
    (hlink : ∀ e∈E(G)\C,∀ x y,G.IsLink e x y → K.IsLink (g e) (f x) (f y)) :
    Nonempty (Iso (contract G C) K) := by
  let F : V(G) → V(K) := fun x ↦ ⟨f x.val,hV ▸ mem_image_of_mem _ x.prop⟩
  have hFs : Function.Surjective F := by
    intro y
    have hy : y.val∈f '' V(G) := by simpa only [hV] using y.prop
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hFk : ∀ x y : V(G),F x=F y ↔ y.val∈contractionClass G C x.val := by
    intro x y
    exact Subtype.ext_iff.trans (hker _ x.prop _ y.prop)
  let E : E(contract G C) → E(K) := fun e ↦ ⟨g e.val,hE.mapsTo e.prop⟩
  exact exists_iso_contraction_of_support_maps G K C F hFs hFk E hE.bijective
    (fun e x y h ↦ hlink e.val e.prop x.val y.val h)

end GraphMinor.GM05
