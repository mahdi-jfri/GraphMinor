module

public import GraphMinor.GM08.Defs
import GraphMinor.GM08.Section15Quotient
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fin.Embedding

/-!
# Finite vertex labels for the cut graft

A finite vertex set embeds in the infinite label type used for graft
classes. Map the graph and its roots through that embedding. This keeps
the graft up to isomorphism and preserves its index. Agreement on graph
vertices also suffices for equality of mapped graphs. These facts put
the disc cut in the same label types as the original graft in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph

universe u v w t

/-- Two vertex maps agreeing on the vertex set give the same mapped
graph. This is used for the finite label transport in VIII (15.4). -/
theorem map_eq_of_eqOn_vertices {γ : Type u} {δ : Type v} {α : Type w}
    (G : Graph γ δ) {f g : γ → α} (hfg : EqOn f g V(G)) : G.map f = G.map g := by
  apply Graph.ext
  · apply image_congr
    exact hfg
  · intro e x y
    change (∃ a b, G.IsLink e a b ∧ f a = x ∧ f b = y) ↔
      ∃ a b, G.IsLink e a b ∧ g a = x ∧ g b = y
    constructor
    · rintro ⟨a, b, hl, rfl, rfl⟩
      exact ⟨a, b, hl, (hfg hl.left_mem).symm, (hfg hl.right_mem).symm⟩
    · rintro ⟨a, b, hl, rfl, rfl⟩
      exact ⟨a, b, hl, hfg hl.left_mem, hfg hl.right_mem⟩

/-- A finite graft can use an infinite ambient vertex label type while
keeping its edge labels, its isomorphism type, and its index. This is
the vertex label transport for the disc graft in VIII (15.4), page 282. -/
theorem exists_vertex_relabel_graft {γ : Type u} {β : Type v} {α : Type w}
    [Infinite α] (X : Graft γ β) :
    ∃ (Y : Graft α β) (f : γ → α), Y.G = X.G.map f ∧ Y.T = f '' X.T ∧
      InjOn f V(X.G) ∧ IsGraftIso X Y ∧ Y.index = X.index := by
  classical
  let : Fintype V(X.G) := X.finite_G.1.fintype
  let g : V(X.G) ↪ α := ((Fintype.equivFin V(X.G)).toEmbedding.trans Fin.valEmbedding).trans
    (Infinite.natEmbedding α)
  let f : γ → α := fun x => if hx : x ∈ V(X.G) then g ⟨x, hx⟩ else Classical.arbitrary α
  have hval : ∀ x (hx : x ∈ V(X.G)), f x = g ⟨x, hx⟩ := by
    intro x hx
    simp only [f, hx, ↓reduceDIte]
  have hinj : InjOn f V(X.G) := by
    intro x hx y hy he
    rw [hval x hx, hval y hy] at he
    exact congrArg Subtype.val (g.injective he)
  let Y : Graft α β := {
    G := X.G.map f
    T := f '' X.T
    T_subset := image_mono X.T_subset
    finite_G := ⟨X.finite_G.1.image f, X.finite_G.2⟩ }
  have hT : ∀ z ∈ V(X.G), z ∈ X.T ↔ f z ∈ Y.T := by
    intro z hz
    constructor
    · exact fun h => mem_image_of_mem f h
    · rintro ⟨a, ha, he⟩
      exact hinj (X.T_subset ha) hz he ▸ ha
  have hiso : IsGraftIso X Y := isGraftIso_of_injective_vertex_map rfl hinj hT
  refine ⟨Y, f, rfl, rfl, hinj, hiso, ?_⟩
  exact (hinj.mono X.T_subset).ncard_image

end GraphMinor.GM08
