module

public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15Identification
import Mathlib.Data.Set.Card

/-!
# Finite quotients of a disc graft

A cutting map identifies pairs of boundary vertices. Repeatedly identify
one such pair until the remaining vertex map is injective. At that point
the map is a graft isomorphism. This is the reconstruction by root
identifications in the short-tube step of VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v u'

/-- An injective vertex map that preserves the root set gives a graft
isomorphism to its image graph. This is the final stage of the root
identifications in VIII (15.4), page 282. -/
theorem isGraftIso_of_injective_vertex_map {α : Type u} {γ : Type u'} {β : Type v}
    {X : Graft α β} {Y : Graft γ β} {f : α → γ} (hG : Y.G = X.G.map f)
    (hf : InjOn f V(X.G)) (hT : ∀ z ∈ V(X.G), z ∈ X.T ↔ f z ∈ Y.T) :
    IsGraftIso X Y := by
  classical
  have hV : f '' V(X.G) = V(Y.G) := by rw [hG, vertexSet_map]
  have hE : E(X.G) = E(Y.G) := by rw [hG, edgeSet_map]
  let fv : V(X.G) → V(Y.G) := fun x => ⟨f x, hV ▸ mem_image_of_mem f x.2⟩
  have hfv : Function.Bijective fv := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hf x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      have hy : y.1 ∈ f '' V(X.G) := hV.symm ▸ y.2
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let ev : V(X.G) ≃ V(Y.G) := Equiv.ofBijective fv hfv
  let ee : E(X.G) ≃ E(Y.G) := {
    toFun := fun e => ⟨e.1, hE ▸ e.2⟩
    invFun := fun e => ⟨e.1, hE.symm ▸ e.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨⟨ev, ee, ?_⟩, ?_⟩
  · intro e x y
    change X.G.IsLink e.1 x.1 y.1 ↔ Y.G.IsLink e.1 (f x.1) (f y.1)
    rw [hG, map_isLink]
    constructor
    · intro hl
      exact ⟨x.1, y.1, hl, rfl, rfl⟩
    · rintro ⟨a, b, hl, ha, hb⟩
      have hax : a = x := hf hl.left_mem x.2 ha
      have hby : b = y := hf hl.right_mem y.2 hb
      simpa only [hax, hby] using hl
  · intro x
    exact hT x x.2

/-- A fibre with at most two vertices that contains two distinct ones
contains exactly those two. This supplies each identification pair in
the short-tube reconstruction of VIII (15.4), page 282. -/
theorem pair_fibre_of_ncard_le_two {α γ : Type*} {V : Set α} (hV : V.Finite)
    {f : α → γ} {p q : α} (hp : p ∈ V) (hq : q ∈ V) (hpq : p ≠ q)
    (hfp : f p = f q) (hcard : {z ∈ V | f z = f p}.ncard ≤ 2) :
    ∀ z ∈ V, f z = f p → z = p ∨ z = q := by
  have hsub : ({p, q} : Set α) ⊆ {z ∈ V | f z = f p} := by
    rintro z (rfl | rfl)
    · exact ⟨hp, rfl⟩
    · exact ⟨hq, hfp.symm⟩
  have heq := eq_of_subset_of_ncard_le hsub
    (by simpa only [ncard_pair hpq] using hcard) (hV.subset (sep_subset _ _))
  intro z hz he
  have hzpair : z ∈ ({p, q} : Set α) := heq.symm ▸ (show z ∈ {z ∈ V | f z = f p} from ⟨hz, he⟩)
  exact hzpair

end GraphMinor.GM08
