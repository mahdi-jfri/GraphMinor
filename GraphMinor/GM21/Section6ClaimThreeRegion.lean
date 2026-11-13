module

public import GraphMinor.GM21.Section6ClaimThreeWalk
public import GraphMinor.GM21.Section7Plus
import GraphMinor.GM21.Section6ClaimTwo
import GraphMinor.GM21.Section6SurfaceRegions
import GraphMinor.GM11.Regions
import GraphMinor.GM19.Perimeter
import GraphMinor.GM17.CutSide

/-!
# Graph Minors XXI, (6.3), claim (3): regions of `Γ⁺` along jumps and cuffs

Claim (3) of the proof of (6.3) (page 29 of the preprint) says: "If $c(\Sigma) \ge 2$ then
there is a region of $\Gamma$ incident with vertices in two different cuffs". We look for this
region among the regions of the drawing `Γ⁺` in the capped surface `Σ̂` (Section 7 of the paper):
`U(Γ⁺) = U(Γ) ∪ bd(Σ)` and `V(Γ⁺) = V(Γ)`. Its edges are the edges of `Γ` and the spaces of `Γ`,
and `Σ̂` has no boundary, so the region lemmas of Graph Minors XI apply.

* `subset_closure_of_space`: if the closure of a region `p` of `Γ⁺` meets a cuff `C`, then it holds a
  vertex of `Γ` in `C`. A point of `C` is a vertex, or lies in a space, and then `p` has the whole
  space and its ends in its closure.
* `mem_closure_of_jump`: if the closure of `p` meets an edge of a jump `J` of `Γ`, or holds a vertex
  of `J` outside `bd(Σ)`, then it holds every vertex of `J`, in particular both ends. This is the
  walk of `vertexSet_subset_of_propagate`. Each step uses that a vertex of `J` outside `bd(Σ)` has
  exactly two edges in `Γ⁺`, both in `J`, and a region whose closure meets one of them, or their
  common end, has both in its closure (`Regions.union_subset_closure_of_two_edges`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM19 GraphMinor.GM21.Supports

universe u v

section plus

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-- The closure of an image under the embedding of `Σ` in `Σ̂` is the image of the closure. -/
theorem closure_emb_image (hS : IsSurface S) (cap : IsCappedSurface S Shat) (A : Set S) :
    closure (cap.emb '' A) = cap.emb '' closure A := by
  have : T2Space S := hS.2.1
  exact (cap.isClosedEmbedding hS).closure_image_eq A

/-- A point of `Σ` whose image lies in the closure of an image lies in the closure. -/
theorem mem_closure_of_emb (hS : IsSurface S) (cap : IsCappedSurface S Shat) {A : Set S} {x : S}
    (h : cap.emb x ∈ closure (cap.emb '' A)) : x ∈ closure A := by
  rw [closure_emb_image hS cap] at h
  obtain ⟨y, hy, hyx⟩ := h
  exact cap.isEmbedding.injective hyx ▸ hy

variable (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S} (hprop : Γ.IsProper)
  (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)

/-- The edges of `Γ` are edges of `Γ⁺`. -/
theorem emb_mem_E_of_mem_E {e : Set S} (he : e ∈ Γ.E) :
    cap.emb '' e ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).E := by
  rw [capDrawing_E, plusDrawing_E]
  exact ⟨e, Or.inl he, rfl⟩

/-- The spaces of `Γ` are edges of `Γ⁺`. -/
theorem emb_mem_E_of_mem_drawingSpaces {s : Set S} (hs : s ∈ drawingSpaces Γ) :
    cap.emb '' s ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).E := by
  rw [capDrawing_E, plusDrawing_E]
  exact ⟨s, Or.inr hs, rfl⟩

/-- `Γ⁺` is proper, since `Σ̂` has no boundary. -/
theorem capDrawing_plus_isProper : (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).IsProper := by
  intro x hx
  rw [cap.bd_empty] at hx
  exact hx.1.elim

/-- The two ends of an edge of `Γ` are the two ends of its image in `Γ⁺`. -/
theorem closure_emb_inter_V {e : Set S} {a b : S} (h : closure e ∩ Γ.V = {a, b}) :
    closure (cap.emb '' e) ∩ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).V =
      {cap.emb a, cap.emb b} := by
  rw [capDrawing_V, plusDrawing_V, closure_emb_image hS cap,
    ← image_inter cap.isEmbedding.injective, h, image_pair]

/-- At a vertex outside `bd(Σ)`, every edge of `Γ⁺` is the image of an edge of `Γ` at the vertex:
the closures of the spaces lie in `bd(Σ)`. -/
theorem exists_edge_of_mem_closure {f : Set Shat}
    (hf : f ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).E) {x : S} (hxbd : x ∉ bd S)
    (hx : cap.emb x ∈ closure f) : ∃ e ∈ Γ.E, f = cap.emb '' e ∧ x ∈ closure e := by
  rw [capDrawing_E] at hf
  obtain ⟨g, hg, rfl⟩ := hf
  have hxg := mem_closure_of_emb hS cap hx
  rw [plusDrawing_E] at hg
  rcases hg with hg | hg
  · exact ⟨g, hg, rfl, hxg⟩
  · exact (hxbd (closure_minimal ((subset_bd_diff_of_mem_drawingSpaces hg).trans sdiff_subset)
      (isClosed_bd S) hxg)).elim

/-- **A region along a cuff.** If the closure of a region `p` of `Γ⁺` holds the image of a point
`u ∈ bd(Σ)`, then it holds the image of a vertex of `Γ` in the cuff of `u`. Either `u` is a vertex,
or `u` lies in a space `s`; then the closure of `p` holds `s` (`GM11.edge_subset_closure_of_incident`)
and so the ends of `s`. -/
theorem exists_vertex_of_mem_closure_bd {p : Set Shat}
    (hp : p ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).R) {u : S} (hu : u ∈ bd S)
    (hup : cap.emb u ∈ closure p) :
    ∃ x ∈ Γ.V, x ∈ connectedComponentIn (bd S) u ∧ cap.emb x ∈ closure p := by
  have : T2Space S := hS.2.1
  by_cases huV : u ∈ Γ.V
  · exact ⟨u, huV, mem_connectedComponentIn hu, hup⟩
  have hs : connectedComponentIn (bd S \ Γ.V) u ∈ drawingSpaces Γ := ⟨u, ⟨hu, huV⟩, rfl⟩
  set s := connectedComponentIn (bd S \ Γ.V) u
  have huS : u ∈ s := mem_connectedComponentIn ⟨hu, huV⟩
  have hsp : cap.emb '' s ⊆ closure p :=
    GM11.edge_subset_closure_of_incident cap.isClosedSurface
      (emb_mem_E_of_mem_drawingSpaces hS cap hprop hge2 hs) hp ⟨cap.emb u, ⟨u, huS, rfl⟩, hup⟩
  obtain ⟨a, b, hab⟩ := exists_spaceHasEnds_of_mem_drawingSpaces hS hge2 hs
  have haS : a ∈ closure s := hab.2.2.2.2.2 ▸ Or.inr (Or.inl rfl)
  have hline : s ∪ {a, b} ⊆ connectedComponentIn (bd S) u := by
    refine (GM17.isPreconnected_line hab.2.2.2.2.1).subset_connectedComponentIn
      (Or.inl huS) ?_
    rintro z (hz | rfl | rfl)
    · exact (subset_bd_diff_of_mem_drawingSpaces hs hz).1
    · exact hab.2.1.2
    · exact hab.2.2.1.2
  refine ⟨a, hab.2.1.1, hline (Or.inr (Or.inl rfl)), ?_⟩
  have : cap.emb a ∈ closure (cap.emb '' s) := by
    rw [closure_emb_image hS cap]
    exact mem_image_of_mem _ haS
  exact closure_minimal hsp isClosed_closure this

end plus

section jump

variable {α : Type u} {β : Type v} {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {L : Hypergraph α β}

/-- The ends of the edge `ιE e` of `Γ_sub` are the images of the ends of `e`. -/
theorem ends_ιE_eq (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {e : Set S}
    (he : e ∈ Γ.E) : Γ_sub.ends (ιE e) = ιV '' (closure e ∩ Γ.V) := by
  ext x
  simp only [Hypergraph.ends, mem_ofPred_eq]
  constructor
  · intro hx
    have hxV : x ∈ ιV '' Γ.V := hP.ιV_image ▸ Γ_sub.vertex_mem_of_inc hx
    obtain ⟨u, hu, rfl⟩ := hxV
    exact ⟨u, ⟨(hP.inc_iff e he u hu).mp hx, hu⟩, rfl⟩
  · rintro ⟨u, ⟨hue, hu⟩, rfl⟩
    exact (hP.inc_iff e he u hu).mpr hue

/-- An edge of `Γ` at a vertex `x` has `x` as one of its two ends. -/
theorem exists_other_end (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) {e : Set S} (he : e ∈ Γ.E) {x : S}
    (hx : x ∈ closure e ∩ Γ.V) : ∃ u, u ≠ x ∧ closure e ∩ Γ.V = {x, u} := by
  obtain ⟨a, b, hab, h⟩ := CutLine.two_ends_of_linkage hP hL e he
  rw [h] at hx
  rcases hx with rfl | hx
  · exact ⟨b, hab.symm, h⟩
  · rw [mem_singleton_iff] at hx
    subst hx
    exact ⟨a, hab, by rw [h, pair_comm]⟩

/-- **A region along a jump.** Let `p` be a region of `Γ⁺` in `Σ̂`, and `J` a jump of `Γ`. If the
closure of `p` meets an edge of `J`, or holds a vertex of `J` outside `bd(Σ)`, then it holds every
vertex of `J`. -/
theorem mem_closure_of_jump (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (cap : IsCappedSurface S Shat) {p : Set Shat}
    (hp : p ∈ (capDrawing hP.is_surface cap
      (plusDrawing hP.is_surface Γ hP.is_proper_drawing hP.cuff_vertices_ge_two)).R)
    {J : Hypergraph α β} (hJ : J ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)))
    (hstart : (∃ e ∈ Γ.E, ιE e ∈ J.edgeSet ∧ (cap.emb '' e ∩ closure p).Nonempty) ∨
      ∃ x ∈ Γ.V, x ∉ bd S ∧ ιV x ∈ J.vertexSet ∧ cap.emb x ∈ closure p) :
    ∀ x ∈ Γ.V, ιV x ∈ J.vertexSet → cap.emb x ∈ closure p := by
  have hS := hP.is_surface
  have : T2Space S := hS.2.1
  have hprop := hP.is_proper_drawing
  have hge2 := hP.cuff_vertices_ge_two
  have hiso := hP.drawing_iso
  have hdeg := IsExhaustiveLinkage.ncard_incidentEdges_eq_two hP hL
  have hinj := cap.isEmbedding.injective
  set D := capDrawing hS cap (plusDrawing hS Γ hprop hge2)
  -- A region whose closure meets an edge of `Γ⁺` has the whole edge in its closure.
  have hedge : ∀ e ∈ Γ.E, (cap.emb '' e ∩ closure p).Nonempty → cap.emb '' e ⊆ closure p :=
    fun e he hne => GM11.edge_subset_closure_of_incident cap.isClosedSurface
      (emb_mem_E_of_mem_E hS cap hprop hge2 he) hp hne
  have hcl : ∀ e ∈ Γ.E, cap.emb '' e ⊆ closure p → ∀ x ∈ closure e, cap.emb x ∈ closure p :=
    fun e _ hsub x hx => closure_minimal hsub isClosed_closure
      (by rw [closure_emb_image hS cap]; exact mem_image_of_mem _ hx)
  let Z : Set α := {y | ∃ x ∈ Γ.V, ιV x = y ∧ cap.emb x ∈ closure p}
  let ZE : Set β := {f | ∃ e ∈ Γ.E, ιE e = f ∧ cap.emb '' e ⊆ closure p}
  have hnB : ∀ x ∈ Γ.V, ιV x ∉ ιV '' (Γ.V ∩ bd S) → x ∉ bd S := fun x hx h hxbd =>
    h ⟨x, ⟨hx, hxbd⟩, rfl⟩
  have hBn : ∀ x ∈ Γ.V, x ∉ bd S → ιV x ∉ ιV '' (Γ.V ∩ bd S) := by
    rintro x hx hxbd ⟨y, hy, hyx⟩
    exact hxbd (hiso.ιV_injOn hy.1 hx hyx ▸ hy.2)
  have hsub := vertexSet_subset_of_propagate (Z := Z) (ZE := ZE) hJ ?_ ?_ ?_
  · intro x hx hxJ
    obtain ⟨y, hy, hyx, hyp⟩ := hsub hxJ
    rwa [hiso.ιV_injOn hy hx hyx] at hyp
  · -- Along an edge of `ZE`.
    rintro f hfJ ⟨e, he, rfl, hep⟩ y hy
    have hyΓ : Γ_sub.Inc (ιE e) y := GM10.inc_of_le hJ.1 hy
    obtain ⟨x, hx, rfl⟩ : y ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc hyΓ
    exact ⟨x, hx, rfl, hcl e he hep x ((hiso.inc_iff e he x hx).mp hyΓ)⟩
  · -- Through a vertex of `Z` outside `bd(Σ)`.
    rintro y hyJ ⟨x, hx, rfl, hxp⟩ hyB f hfJ hfx
    have hxbd := hnB x hx hyB
    have hinc := incidentEdges_jump_eq hdeg hJ hyJ hyB
    have hfK : f ∈ incidentEdges Γ_sub (ιV x) := hinc ▸ ⟨hfJ, hfx⟩
    have h2 := hdeg (ιV x) (hJ.1.vertexSet_subset hyJ) hyB
    obtain ⟨f₁, f₂, hf12, hf12'⟩ := ncard_eq_two.mp h2
    obtain ⟨f', hff', hf'K⟩ : ∃ f', f' ≠ f ∧ f' ∈ incidentEdges Γ_sub (ιV x) := by
      rw [hf12'] at hfK ⊢
      rcases hfK with rfl | hfK
      · exact ⟨f₂, hf12.symm, Or.inr rfl⟩
      · rw [mem_singleton_iff] at hfK
        subst hfK
        exact ⟨f₁, hf12, Or.inl rfl⟩
    obtain ⟨e, he, rfl⟩ : f ∈ ιE '' Γ.E := hiso.ιE_image ▸ hfK.1
    obtain ⟨e', he', rfl⟩ : f' ∈ ιE '' Γ.E := hiso.ιE_image ▸ hf'K.1
    have hee : e ≠ e' := fun h => hff' (h ▸ rfl)
    have hxe : x ∈ closure e := (hiso.inc_iff e he x hx).mp hfK.2
    have hxe' : x ∈ closure e' := (hiso.inc_iff e' he' x hx).mp hf'K.2
    obtain ⟨a, hax, hea⟩ := exists_other_end hP hL he ⟨hxe, hx⟩
    obtain ⟨b, hbx, heb⟩ := exists_other_end hP hL he' ⟨hxe', hx⟩
    -- The two other ends differ: `J` has no parallel edges.
    have hab : a ≠ b := by
      rintro rfl
      have hf'J : ιE e' ∈ J.edgeSet := (hinc ▸ hf'K : ιE e' ∈ incidentEdges J (ιV x)).1
      have hends : J.ends (ιE e) = J.ends (ιE e') := by
        rw [← hJ.1.ends_eq _ hfJ, ← hJ.1.ends_eq _ hf'J, ends_ιE_eq hP he, ends_ιE_eq hP he', hea,
          heb]
      exact hff' (hJ.2.1.2.2.2.2.1 _ hfJ _ hf'J hends).symm
    have hdegD : ∀ g ∈ D.E, cap.emb x ∈ closure g → g = cap.emb '' e ∨ g = cap.emb '' e' := by
      intro g hg hxg
      obtain ⟨e₀, he₀, rfl, hxe₀⟩ := exists_edge_of_mem_closure hS cap hprop hge2 hg hxbd hxg
      have h₀ : ιE e₀ ∈ incidentEdges Γ_sub (ιV x) :=
        ⟨hiso.ιE_image ▸ mem_image_of_mem ιE he₀, (hiso.inc_iff e₀ he₀ x hx).mpr hxe₀⟩
      rw [hf12'] at h₀ hfK hf'K
      simp only [mem_insert_iff, mem_singleton_iff] at h₀ hfK hf'K
      have hcases : ιE e₀ = ιE e ∨ ιE e₀ = ιE e' := by
        rcases h₀ with h₀ | h₀ <;> rcases hfK with h₁ | h₁ <;> rcases hf'K with h₂ | h₂ <;>
          first
          | exact Or.inl (h₀.trans h₁.symm)
          | exact Or.inr (h₀.trans h₂.symm)
          | exact absurd (h₂.trans h₁.symm) hff' 
      rcases hcases with h | h
      · exact Or.inl (by rw [hiso.ιE_injOn he₀ he h])
      · exact Or.inr (by rw [hiso.ιE_injOn he₀ he' h])
    have hU := Regions.union_subset_closure_of_two_edges cap.isSurface
      (capDrawing_plus_isProper hS cap hprop hge2)
      (emb_mem_E_of_mem_E hS cap hprop hge2 he) (emb_mem_E_of_mem_E hS cap hprop hge2 he')
      (fun h => hee (image_injective.mpr hinj h))
      (by rw [closure_emb_inter_V hS cap hprop hge2 hea, pair_comm])
      (closure_emb_inter_V hS cap hprop hge2 heb)
      (fun h => hax (hinj h)) (fun h => hbx (hinj h)) (fun h => hab (hinj h)) hdegD
      (by rw [cap.bd_empty]; exact notMem_empty _) hp
      ⟨cap.emb x, Or.inl (Or.inr rfl), hxp⟩
    exact ⟨e, he, rfl, fun z hz => hU (Or.inl (Or.inl hz))⟩
  · -- The start.
    rcases hstart with ⟨e, he, heJ, hne⟩ | ⟨x, hx, hxbd, hxJ, hxp⟩
    · exact Or.inl ⟨ιE e, heJ, e, he, rfl, hedge e he hne⟩
    · exact Or.inr ⟨ιV x, hxJ, ⟨x, hx, rfl, hxp⟩, hBn x hx hxbd⟩

end jump

end ClaimThree
end GM21
end GraphMinor
