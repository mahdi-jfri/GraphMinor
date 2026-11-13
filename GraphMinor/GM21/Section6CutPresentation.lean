module

public import GraphMinor.GM21.Section6CutSpaces
public import GraphMinor.GM21.Section6CutNames
public import GraphMinor.GM21.Section6Separation
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6RestrictPres
import GraphMinor.GM21.Section6SideSupports

/-!
# Graph Minors XXI, (6.3), claim (2): the presentation on the cut surface

Claim (2) of the proof of (6.3) (page 28 of the preprint) says that the graph `G'` obtained by
splitting "has a presentation in $\Sigma'$ ... of depth $\le q$ and defect $\le r + 2$". This file
proves it from conditions on the new supports, which `Section6CutPieces.lean` checks for the pieces
of the old supports.

The new supports `K'_1, …, K'_{r₂}` lie over `bd(Σ)`, and `ψ` is one to one on each of them with
`ψ(K'_i) ⊆ F_{τ i}*`. Each `K'_i` has sides `col i`. The new graph is `G` split twice
(`split2`), its graphs are the copies `H'_i` of `μ(ψ(K'_i))` on the sides `col i`, and `μ'(x)` is the
copy of `μ(ψ(x))` on the sides `cu x`. The drawing `Γ'` is drawn as the subgraph of the split graph
on the vertices `ιV'(V(Γ'))` and the edges `ιE(E(Γ))`.

* `supportGraph_cut`: `μ'(K'_i)` is the copy of `μ(ψ(K'_i))`, since the units of `K'_i` are the
  lifts of the units of `ψ(K'_i)`.
* `isPresentation_cut`: these data form a presentation.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

/-- A unit of `Σ'` is carried by `ψ` to a unit of `Σ`: a vertex to its image, a space to its
image. -/
def unitMap {S S' : Type*} (ψ : S' → S) : BoundaryUnit S' → BoundaryUnit S
  | .vertex u => .vertex (ψ u)
  | .space s => .space (ψ '' s)

@[simp] theorem unitMap_vertex {S S' : Type*} (ψ : S' → S) (u : S') :
    unitMap ψ (.vertex u) = .vertex (ψ u) := rfl

@[simp] theorem unitMap_space {S S' : Type*} (ψ : S' → S) (s : Set S') :
    unitMap ψ (.space s) = .space (ψ '' s) := rfl

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)

omit [TopologicalSpace S'] in
/-- A point of `bd(Σ)` outside `V(Γ)` is not on `F`, since `F` meets `bd(Σ)` only in its ends. -/
theorem notMem_line {Γ : Drawing S} (hF : IsProperLineInSurface F a b) (habV : a ∈ Γ.V ∧ b ∈ Γ.V)
    {x : S} (hx : x ∈ bd S) (hxV : x ∉ Γ.V) : x ∉ F := fun hxF => by
  have : x ∈ F ∩ bd S := ⟨hxF, hx⟩
  rw [hF.inter_bd_eq] at this
  rcases this with rfl | rfl
  exacts [hxV habV.1, hxV habV.2]

include h

/-- A space of `Γ'` over `bd(Σ)` is the lift of its image, which is a space of `Γ`. -/
theorem image_space (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V) {s' : Set S'}
    (hs' : s' ∈ drawingSpaces Γ') (hbd : ψ '' s' ⊆ bd S) :
    ψ '' s' ∈ drawingSpaces Γ ∧ ψ ⁻¹' (ψ '' s') = s' := by
  obtain ⟨z, hz⟩ := (GM21.Supports.isConnected_of_mem_drawingSpaces hs').nonempty
  obtain ⟨s, hs, rfl⟩ := h.exists_eq_preimage_of_mem_drawingSpaces hS hF habV hV hs' hz
    (hbd (mem_image_of_mem ψ hz))
  rw [h.image_preimage]
  exact ⟨hs, rfl⟩

/-- If a space of `Γ` lies in `ψ(K)`, then its lift lies in `K`, since `ψ` is one to one off `F`. -/
theorem preimage_space_subset (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {s : Set S} (hs : s ∈ drawingSpaces Γ) {K : Set S'}
    (hsK : s ⊆ ψ '' K) : ψ ⁻¹' s ⊆ K := by
  intro z hz
  obtain ⟨k, hk, hkz⟩ := hsK hz
  have hsd := GM21.Supports.subset_bd_diff_of_mem_drawingSpaces hs hz
  have hzF : ψ z ∉ F := notMem_line hF habV hsd.1 hsd.2
  have hkF : ψ k ∉ F := hkz ▸ hzF
  rwa [← h.injOn_compl hkF hzF hkz]

end IsLineCut

/-! ## The graph `μ'(K')` -/

section supportGraph

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  {Xa : Set α} {Ea : Set β} {Xb : Set (α ⊕ α ⊕ α)} {Eb : Set β}

/-- **`μ'(K')` is the copy of `μ(ψ(K'))`.** Let `ψ` be one to one on `K'`, with `ψ(K') ⊆ F_j*`, let
every unit of `K'` have the sides `c`, and every edge of `μ(ψ(K'))` be on the sides `c`. -/
theorem supportGraph_cut (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V) {K : Set S'}
    {j : Fin r} (hKF : ψ '' K ⊆ F_star j) {cu : BoundaryUnit S' → Bool × Bool} {c : Bool × Bool}
    (hcu_v : ∀ u ∈ Γ'.V ∩ K, cu (.vertex u) = c)
    (hcu_s : ∀ s ∈ drawingSpaces Γ', s ⊆ K → cu (.space s) = c)
    (hcol : ∀ e ∈ (supportGraph G Γ μ (ψ '' K)).edgeSet,
      (e ∈ Ea ↔ c.1 = true) ∧ (e ∈ Eb ↔ c.2 = true)) :
    supportGraph (split2 G Xa Ea Xb Eb) Γ'
        (fun x => isoImage (nm2 Xa Xb (cu x)) id (μ (unitMap ψ x))) K =
      isoImage (nm2 Xa Xb c) id (supportGraph G Γ μ (ψ '' K)) := by
  have hS := hP.is_surface
  have hFj : F_star j ⊆ bd S :=
    GM21.Supports.subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j)
  have hKbd : ψ '' K ⊆ bd S := hKF.trans hFj
  -- The units of `K` and of `ψ(K)`.
  have hsp : ∀ s' ∈ drawingSpaces Γ', s' ⊆ K →
      ψ '' s' ∈ drawingSpaces Γ ∧ ψ '' s' ⊆ ψ '' K ∧ ψ ⁻¹' (ψ '' s') = s' := by
    intro s' hs' hsK
    have h1 := h.image_space hS hF habV hV hs' ((image_mono hsK).trans hKbd)
    exact ⟨h1.1, image_mono hsK, h1.2⟩
  have hsp' : ∀ s ∈ drawingSpaces Γ, s ⊆ ψ '' K →
      ψ ⁻¹' s ∈ drawingSpaces Γ' ∧ ψ ⁻¹' s ⊆ K ∧ ψ '' (ψ ⁻¹' s) = s := by
    intro s hs hsK
    refine ⟨h.preimage_mem_drawingSpaces hS hF habV hV hs, h.preimage_space_subset hF habV hs hsK,
      h.image_preimage s⟩
  have hvx : ∀ u' ∈ Γ'.V ∩ K, ψ u' ∈ Γ.V ∩ ψ '' K := fun u' hu' =>
    ⟨by have := hu'.1; rw [hV] at this; exact this, mem_image_of_mem ψ hu'.2⟩
  have hvx' : ∀ u ∈ Γ.V ∩ ψ '' K, ∃ u' ∈ Γ'.V ∩ K, ψ u' = u := by
    rintro u ⟨huV, k, hk, rfl⟩
    exact ⟨k, ⟨by rw [hV]; exact huV, hk⟩, rfl⟩
  have hμs : ∀ s ∈ drawingSpaces Γ, s ⊆ ψ '' K → μ (.space s) ≤ G := fun s hs hsK =>
    GM21.μ_space_le hP j hs (hsK.trans hKF)
  have hμv : ∀ u ∈ Γ.V ∩ ψ '' K, μ (.vertex u) ≤ G := fun u hu =>
    GM21.μ_vertex_le hP j ⟨hu.1, hKF hu.2⟩
  refine Hypergraph.ext ?_ ?_ ?_
  · ext x
    simp only [supportGraph, isoImage, mem_inter_iff, mem_union, mem_iUnion, mem_image,
      exists_prop, mem_ofPred_eq, unitMap_space, unitMap_vertex]
    constructor
    · rintro ⟨-, ⟨s', ⟨hs', hsK⟩, v, hv, rfl⟩ | ⟨u', hu', v, hv, rfl⟩⟩
      · obtain ⟨h1, h2, -⟩ := hsp s' hs' hsK
        rw [hcu_s s' hs' hsK]
        exact ⟨v, ⟨(hμs _ h1 h2).vertexSet_subset hv, Or.inl ⟨_, ⟨h1, h2⟩, hv⟩⟩, rfl⟩
      · rw [hcu_v u' hu']
        exact ⟨v, ⟨(hμv _ (hvx u' hu')).vertexSet_subset hv,
          Or.inr ⟨_, hvx u' hu', hv⟩⟩, rfl⟩
    · rintro ⟨v, ⟨hvG, ⟨s, ⟨hs, hsK⟩, hvs⟩ | ⟨u, hu, hvu⟩⟩, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := hsp' s hs hsK
        refine ⟨nm2_mem c hvG, Or.inl ⟨_, ⟨h1, h2⟩, v, by rw [h3]; exact hvs, ?_⟩⟩
        rw [hcu_s _ h1 h2]
      · obtain ⟨u', hu', rfl⟩ := hvx' u hu
        refine ⟨nm2_mem c hvG, Or.inr ⟨u', hu', v, hvu, ?_⟩⟩
        rw [hcu_v u' hu']
  · ext e
    simp only [supportGraph, isoImage, split2_edgeSet, image_id, mem_inter_iff, mem_union,
      mem_iUnion, exists_prop, mem_ofPred_eq, unitMap_space, unitMap_vertex]
    constructor
    · rintro ⟨heG, ⟨s', ⟨hs', hsK⟩, he⟩ | ⟨u', hu', he⟩⟩
      · obtain ⟨h1, h2, -⟩ := hsp s' hs' hsK
        exact ⟨heG, Or.inl ⟨_, ⟨h1, h2⟩, he⟩⟩
      · exact ⟨heG, Or.inr ⟨_, hvx u' hu', he⟩⟩
    · rintro ⟨heG, ⟨s, ⟨hs, hsK⟩, he⟩ | ⟨u, hu, he⟩⟩
      · obtain ⟨h1, h2, h3⟩ := hsp' s hs hsK
        exact ⟨heG, Or.inl ⟨_, ⟨h1, h2⟩, by rw [h3]; exact he⟩⟩
      · obtain ⟨u', hu', rfl⟩ := hvx' u hu
        exact ⟨heG, Or.inr ⟨u', hu', he⟩⟩
  · funext e x
    apply propext
    simp only [supportGraph, isoImage, id_eq, unitMap_space, unitMap_vertex]
    constructor
    · rintro ⟨hG, ⟨s', hs', hsK, e₀, v, hinc, rfl, rfl⟩ | ⟨u', hu', e₀, v, hinc, rfl, rfl⟩⟩
      · obtain ⟨h1, h2, -⟩ := hsp s' hs' hsK
        rw [hcu_s s' hs' hsK] at hG ⊢
        exact ⟨e₀, v, ⟨GM10.inc_of_le (hμs _ h1 h2) hinc, Or.inl ⟨_, h1, h2, hinc⟩⟩, rfl, rfl⟩
      · rw [hcu_v u' hu'] at hG ⊢
        exact ⟨e₀, v, ⟨GM10.inc_of_le (hμv _ (hvx u' hu')) hinc,
          Or.inr ⟨_, hvx u' hu', hinc⟩⟩, rfl, rfl⟩
    · rintro ⟨e₀, v, ⟨hG, hU⟩, rfl, rfl⟩
      have he₀ : e₀ ∈ (supportGraph G Γ μ (ψ '' K)).edgeSet := by
        refine ⟨G.edge_mem_of_inc hG, ?_⟩
        rcases hU with ⟨s, hs, hsK, hinc⟩ | ⟨u, hu, hinc⟩
        · exact Or.inl (mem_biUnion (x := s) ⟨hs, hsK⟩ ((μ _).edge_mem_of_inc hinc))
        · exact Or.inr (mem_biUnion (x := u) hu ((μ _).edge_mem_of_inc hinc))
      refine ⟨(split2_inc_nm2_iff (hcol e₀ he₀).1 (hcol e₀ he₀).2).mpr hG, ?_⟩
      rcases hU with ⟨s, hs, hsK, hinc⟩ | ⟨u, hu, hinc⟩
      · obtain ⟨h1, h2, h3⟩ := hsp' s hs hsK
        refine Or.inl ⟨_, h1, h2, e₀, v, by rw [h3]; exact hinc, rfl, ?_⟩
        rw [hcu_s _ h1 h2]
      · obtain ⟨u', hu', rfl⟩ := hvx' u hu
        refine Or.inr ⟨u', hu', e₀, v, hinc, rfl, ?_⟩
        rw [hcu_v u' hu']

end supportGraph

/-! ## The presentation -/

section presentation

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  {Xa : Set α} {Ea : Set β} {Xb : Set (α ⊕ α ⊕ α)} {Eb : Set β}

/-- **The presentation on the cut surface** (Graph Minors XXI, proof of (6.3), claim (2),
page 28 of the preprint). Let `Γ' = ψ⁻¹(Γ)` be drawn in the graph `G` split twice, with the vertex
names `ιV'`, and let the new supports `K_i` satisfy:
* `ψ` is one to one on `K_i`, `ψ(K_i) ⊆ F_{τ i}*`, the sets `K_i` are disjoint supports of `Γ'`
  holding every vertex of `Γ'` in `bd(Σ')`, and every space of `Γ` in a support lies in some
  `ψ(K_i)`;
* every edge of `μ(ψ(K_i))` is on the sides `col i`, every unit of `K_i` has the sides `col i`, and
  a vertex `u` of `Γ'` in `K_i` is named by its copy on the sides `col i`;
* the drawing is drawn as a subgraph: `ιV'` is one to one, names each vertex `u` of `Γ'` by a copy
  of `ιV(ψ(u))`, and the edge `ιE(e)` is incident with `ιV'(u)` exactly when `u` is an end of
  `ψ⁻¹(e)`;
* the copies of the graphs `μ(ψ(K_i))` are disjoint, and with `ιV'(V(Γ'))` they hold every vertex
  of the split graph.
Then `Γ'`, the supports `K_i`, the copies of `μ(ψ(K_i))` and the copies of `μ ∘ ψ` form a
presentation of the split graph in `Σ'`, with depths `q ∘ τ`. -/
theorem isPresentation_cut (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) [ConnectedSpace S'] {Γ' : Drawing S'}
    (hU : Γ'.U = ψ ⁻¹' Γ.U) (hV : Γ'.V = ψ ⁻¹' Γ.V)
    (hE : ∀ e' ∈ Γ'.E, ∃ e ∈ Γ.E, e' = ψ ⁻¹' e)
    (hΓ' : Γ'.IsProper) (hcuff : ∀ C ∈ cuffs S', 2 ≤ (Γ'.V ∩ C).ncard)
    {r₂ : ℕ} {K : Fin r₂ → Set S'} {τ : Fin r₂ → Fin r} {col : Fin r₂ → Bool × Bool}
    (hKsup : ∀ i, IsSupportOfDrawing Γ' (K i))
    (hKdisj : Pairwise (fun i i' => Disjoint (K i) (K i')))
    (hKinj : ∀ i, InjOn ψ (K i)) (hKF : ∀ i, ψ '' K i ⊆ F_star (τ i))
    (hKV : Γ'.V ∩ bd S' ⊆ ⋃ i, K i)
    (hKs : ∀ j, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → ∃ i, s ⊆ ψ '' K i)
    (hcol : ∀ i, ∀ e ∈ (supportGraph G Γ μ (ψ '' K i)).edgeSet,
      (e ∈ Ea ↔ (col i).1 = true) ∧ (e ∈ Eb ↔ (col i).2 = true))
    {ιV' : S' → Name2 α} (hιinj : InjOn ιV' Γ'.V)
    (hιV : ∀ u ∈ Γ'.V, ∃ c, ιV' u = nm2 Xa Xb c (ιV (ψ u)))
    (hιK : ∀ i, ∀ u ∈ Γ'.V ∩ K i, ιV' u = nm2 Xa Xb (col i) (ιV (ψ u)))
    (hinc : ∀ e ∈ Γ.E, ∀ u ∈ Γ'.V,
      (split2 G Xa Ea Xb Eb).Inc (ιE e) (ιV' u) ↔ u ∈ closure (ψ ⁻¹' e))
    (hends : ∀ e ∈ Γ.E, ∀ w, (split2 G Xa Ea Xb Eb).Inc (ιE e) w → w ∈ ιV' '' Γ'.V)
    {cu : BoundaryUnit S' → Bool × Bool}
    (hcu_v : ∀ i, ∀ u ∈ Γ'.V ∩ K i, cu (.vertex u) = col i)
    (hcu_s : ∀ i, ∀ s ∈ drawingSpaces Γ', s ⊆ K i → cu (.space s) = col i)
    (hcover : (split2 G Xa Ea Xb Eb).vertexSet ⊆ ιV' '' Γ'.V ∪
      ⋃ i, nm2 Xa Xb (col i) '' (supportGraph G Γ μ (ψ '' K i)).vertexSet)
    (hdisjH : Pairwise (fun i i' =>
      Disjoint (nm2 Xa Xb (col i) '' (supportGraph G Γ μ (ψ '' K i)).vertexSet)
        (nm2 Xa Xb (col i') '' (supportGraph G Γ μ (ψ '' K i')).vertexSet))) :
    IsPresentation (split2 G Xa Ea Xb Eb) Γ'
      (subOn (split2 G Xa Ea Xb Eb) (ιV' '' Γ'.V) (ιE '' Γ.E)) ιV' (fun e' => ιE (ψ '' e'))
      r₂ K (fun i => isoImage (nm2 Xa Xb (col i)) id (supportGraph G Γ μ (ψ '' K i)))
      (fun x => isoImage (nm2 Xa Xb (cu x)) id (μ (unitMap ψ x))) (q ∘ τ) := by
  have hS := hP.is_surface
  have : T2Space S := hS.2.1
  have : CompactSpace S' := h.compactSpace
  have hFbd : ∀ j, F_star j ⊆ bd S := fun j =>
    GM21.Supports.subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j)
  have hKbd : ∀ i, ψ '' K i ⊆ bd S := fun i => (hKF i).trans (hFbd _)
  have hKcl : ∀ i, IsClosed (K i) := fun i =>
    GM21.Supports.isClosed_of_isSupportOfDrawing h.surface (hKsup i)
  have hIcl : ∀ i, IsClosed (ψ '' K i) := fun i =>
    ((hKcl i).isCompact.image h.continuous).isClosed
  have hle : ∀ i, supportGraph G Γ μ (ψ '' K i) ≤ G := fun i =>
    GM21.supportGraph_le hP (τ i) (hKF i)
  have hleH : ∀ i, supportGraph G Γ μ (ψ '' K i) ≤ H (τ i) := fun i => by
    rw [hP.v2_eq (τ i)]
    exact GM21.supportGraph_mono hP (τ i) subset_rfl (hKF i)
  have hHle : ∀ i, isoImage (nm2 Xa Xb (col i)) id (supportGraph G Γ μ (ψ '' K i)) ≤
      split2 G Xa Ea Xb Eb := fun i => isoImage_nm2_le (hle i) (hcol i)
  have hψV : ∀ u ∈ Γ'.V, ψ u ∈ Γ.V := fun u hu => by rw [hV] at hu; exact hu
  have hιV_sub : ∀ u ∈ Γ.V, ιV u ∈ Γ_sub.vertexSet := fun u hu =>
    hP.ιV_image ▸ mem_image_of_mem ιV hu
  have hιV_G₂ : ιV' '' Γ'.V ⊆ (split2 G Xa Ea Xb Eb).vertexSet := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨c, hc⟩ := hιV u hu
    rw [hc]
    exact nm2_mem c (hP.drawing_subgraph.vertexSet_subset (hιV_sub _ (hψV u hu)))
  have hΓsV : (subOn (split2 G Xa Ea Xb Eb) (ιV' '' Γ'.V) (ιE '' Γ.E)).vertexSet =
      ιV' '' Γ'.V := inter_eq_left.mpr hιV_G₂
  have hΓE_G : ιE '' Γ.E ⊆ G.edgeSet := by
    rw [hP.ιE_image]
    exact hP.drawing_subgraph.edgeSet_subset
  have hΓsE : (subOn (split2 G Xa Ea Xb Eb) (ιV' '' Γ'.V) (ιE '' Γ.E)).edgeSet = ιE '' Γ.E :=
    inter_eq_left.mpr hΓE_G
  have hΓsle : subOn (split2 G Xa Ea Xb Eb) (ιV' '' Γ'.V) (ιE '' Γ.E) ≤ split2 G Xa Ea Xb Eb :=
    subOn_le fun e he _ w hw => by
      obtain ⟨e₀, he₀, rfl⟩ := he
      exact hends e₀ he₀ w hw
  -- The copy on the sides `col i` of a set that meets `V(Γ)` in the images of vertices of `K i`.
  have hcopy : ∀ i (A : Set α) (B : Set S'), B ⊆ Γ'.V ∩ K i →
      A ∩ Γ_sub.vertexSet = ιV '' (ψ '' B) →
      nm2 Xa Xb (col i) '' A ∩ ιV' '' Γ'.V = ιV' '' B := by
    intro i A B hB hA
    apply Subset.antisymm
    · rintro _ ⟨⟨v, hv, rfl⟩, ⟨w, hw, hvw⟩⟩
      obtain ⟨c, hc⟩ := hιV w hw
      have hvw' : v = ιV (ψ w) := eq_of_nm2_eq (hvw.symm.trans hc)
      have hvA : v ∈ A ∩ Γ_sub.vertexSet := ⟨hv, hvw' ▸ hιV_sub _ (hψV w hw)⟩
      rw [hA] at hvA
      obtain ⟨_, ⟨k, hk, rfl⟩, hvk⟩ := hvA
      exact ⟨k, hk, by rw [hιK i k (hB hk), hvk]⟩
    · rintro _ ⟨k, hk, rfl⟩
      have hkA : ιV (ψ k) ∈ A ∩ Γ_sub.vertexSet := by
        rw [hA]
        exact mem_image_of_mem ιV (mem_image_of_mem ψ hk)
      exact ⟨⟨ιV (ψ k), hkA.1, (hιK i k (hB hk)).symm⟩, mem_image_of_mem ιV' (hB hk).1⟩
  have hpsiVK : ∀ i, ψ '' (Γ'.V ∩ K i) = Γ.V ∩ ψ '' K i := by
    intro i
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨hψV u hu.1, mem_image_of_mem ψ hu.2⟩
    · rintro _ ⟨huV, k, hk, rfl⟩
      exact ⟨k, ⟨by rw [hV]; exact huV, hk⟩, rfl⟩
  exact {
    is_surface := h.surface
    is_connected_surface := inferInstance
    is_proper_drawing := hΓ'
    cuff_vertices_ge_two := hcuff
    drawing_subgraph := hΓsle
    drawing_iso := {
      ιV_injOn := hιinj
      ιV_image := hΓsV.symm
      ιE_injOn := by
        intro e₁' he₁ e₂' he₂ heq
        obtain ⟨e₁, he₁', rfl⟩ := hE e₁' he₁
        obtain ⟨e₂, he₂', rfl⟩ := hE e₂' he₂
        simp only [h.image_preimage] at heq
        rw [hP.ιE_injOn he₁' he₂' heq]
      ιE_image := by
        rw [hΓsE]
        apply Subset.antisymm
        · rintro _ ⟨e', he', rfl⟩
          obtain ⟨e, he, rfl⟩ := hE e' he'
          simp only [h.image_preimage]
          exact mem_image_of_mem ιE he
        · rintro _ ⟨e, he, rfl⟩
          exact ⟨ψ ⁻¹' e, h.preimage_mem_E hU hV hE he, by simp only [h.image_preimage]⟩
      inc_iff := by
        intro e' he' u hu
        obtain ⟨e, he, rfl⟩ := hE e' he'
        simp only [h.image_preimage]
        rw [← hinc e he u hu]
        exact ⟨fun h1 => h1.1, fun h1 => ⟨h1, mem_image_of_mem ιE he, mem_image_of_mem ιV' hu⟩⟩ }
    supports_isSupport := hKsup
    supports_disjoint := hKdisj
    bd_vertices_covered := hKV
    v1_sub := hHle
    v1_union_V := by
      apply Subset.antisymm
      · intro x hx
        rcases hcover hx with hx | hx
        · exact Or.inr (hΓsV.symm ▸ hx)
        · exact Or.inl hx
      · rintro x (hx | hx)
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          exact (hHle i).vertexSet_subset hi
        · exact hΓsle.vertexSet_subset hx
    v1_union_E := by
      rw [hΓsE]
      apply Subset.antisymm
      · intro e he
        have he' : e ∈ G.edgeSet := he
        rw [hP.v1_union_E] at he'
        rcases he' with he' | he'
        · obtain ⟨j, hj⟩ := mem_iUnion.mp he'
          rw [hP.v2_eq j] at hj
          obtain ⟨heG, hes | heu⟩ := hj
          · obtain ⟨s, ⟨hs, hsF⟩, hes⟩ := mem_iUnion₂.mp hes
            obtain ⟨i, hi⟩ := hKs j s hs hsF
            refine Or.inl (mem_iUnion.mpr ⟨i, ?_⟩)
            show e ∈ id '' _
            rw [image_id]
            exact ⟨heG, Or.inl (mem_biUnion (x := s) ⟨hs, hi⟩ hes)⟩
          · obtain ⟨u, hu, heu⟩ := mem_iUnion₂.mp heu
            rw [(hP.μ_vertex_sub j u hu).2.1] at heu
            exact absurd heu (notMem_empty e)
        · rw [← hP.ιE_image] at he'
          exact Or.inr he'
      · rintro e (he | he)
        · obtain ⟨i, hi⟩ := mem_iUnion.mp he
          exact (hHle i).edgeSet_subset hi
        · exact hΓE_G he
    v1_disjoint := hdisjH
    v1_inter_V := by
      intro i
      rw [hΓsV]
      refine hcopy i _ _ subset_rfl ?_
      rw [hpsiVK i]
      apply Subset.antisymm
      · exact GM21.supportGraph_vertexSet_inter_subset hP (τ i) (hKF i) (hIcl i)
      · rintro _ ⟨u, hu, rfl⟩
        exact ⟨(GM21.μ_vertex_le_supportGraph_of_subset hP (τ i) (hKF i) hu).vertexSet_subset
          (GM21.ιV_mem_μ_vertex hP (τ i) ⟨hu.1, hKF i hu.2⟩), hιV_sub u hu.1⟩
    v1_inter_E := by
      intro i
      show Disjoint (id '' _) _
      rw [image_id, hΓsE, hP.ιE_image]
      exact (hP.v1_inter_E (τ i)).mono_left (hleH i).edgeSet_subset
    q_pos := fun i => hP.q_pos (τ i)
    μ_vertex_sub := by
      intro i u hu
      have hu' : ψ u ∈ Γ.V ∩ F_star (τ i) := ⟨hψV u hu.1, hKF i (mem_image_of_mem ψ hu.2)⟩
      obtain ⟨-, he, hcard, hint⟩ := hP.μ_vertex_sub (τ i) (ψ u) hu'
      have hle' := GM21.μ_vertex_le_supportGraph_of_subset hP (τ i) (hKF i)
        ⟨hu'.1, mem_image_of_mem ψ hu.2⟩
      simp only [unitMap_vertex, hcu_v i u hu]
      refine ⟨isoImage_le hle' le_rfl (injOn_id _) hle', ?_, ?_, ?_⟩
      · show id '' _ = ∅
        rw [he, image_empty]
      · show (nm2 Xa Xb (col i) '' _).ncard = q (τ i)
        rw [(nm2_injective (col i)).injOn.ncard_image, hcard]
      · rw [hΓsV]
        have := hcopy i _ {u} (singleton_subset_iff.mpr hu) (by rw [hint, image_singleton,
          image_singleton])
        rwa [image_singleton] at this
    μ_space_sub := by
      intro i s hs hsK
      have himg := h.image_space hS hF habV hV hs ((image_mono hsK).trans (hKbd i))
      have hle' := Side.μ_space_le_supportGraph_of_subset hP (τ i) (hKF i) himg.1
        (image_mono hsK)
      simp only [unitMap_space, hcu_s i s hs hsK]
      exact isoImage_le hle' le_rfl (injOn_id _) hle'
    v2_eq := fun i =>
      (supportGraph_cut hP h hF habV hV (hKF i) (hcu_v i) (hcu_s i) (hcol i)).symm
    v3_space := by
      intro i s hs u₁ u₂ hsK hends'
      have himg := h.image_space hS hF habV hV hs ((image_mono hsK).trans (hKbd i))
      have hE2 : SpaceHasEnds Γ (ψ '' s) (ψ u₁) (ψ u₂) :=
        spaceHasEnds_image h.continuous (hKcl i) (hKinj i) hV (hKbd i) hsK himg.1 hends'
      have hcl : closure s ⊆ K i := closure_minimal hsK (hKcl i)
      rw [hends'.2.2.2.2.2] at hcl
      have hu₁ : u₁ ∈ Γ'.V ∩ K i := ⟨hends'.2.1.1, hcl (Or.inr (Or.inl rfl))⟩
      have hu₂ : u₂ ∈ Γ'.V ∩ K i := ⟨hends'.2.2.1.1, hcl (Or.inr (Or.inr rfl))⟩
      obtain ⟨hint, h1, h2, hpaths⟩ := hP.v3_space (τ i) _ himg.1 (ψ u₁) (ψ u₂)
        ((image_mono hsK).trans (hKF i)) hE2
      simp only [unitMap_space, unitMap_vertex, hcu_s i s hs hsK, hcu_v i u₁ hu₁,
        hcu_v i u₂ hu₂]
      refine ⟨?_, isoImage_le h1 le_rfl (injOn_id _) h1, isoImage_le h2 le_rfl (injOn_id _) h2,
        HasDisjointPaths.image_of_injective (nm2_injective _)
          (skeleton_adj_isoImage_of_injective (nm2_injective _)) hpaths⟩
      rw [hΓsV]
      have hB : ({u₁, u₂} : Set S') ⊆ Γ'.V ∩ K i := by
        rintro x (rfl | rfl)
        exacts [hu₁, hu₂]
      have := hcopy i _ {u₁, u₂} hB (by rw [hint, image_pair, image_pair])
      rwa [image_pair] at this
    v4_between := by
      intro i s₁ s₂ u hbtw
      have hsp : ∀ s' ∈ drawingSpaces Γ', s' ⊆ K i → ψ '' s' ∈ drawingSpaces Γ :=
        fun s' hs' hsK => (h.image_space hS hF habV hV hs' ((image_mono hsK).trans (hKbd i))).1
      have h1 := liesBetweenInSupport_image h.continuous (hKinj i) hV (hKbd i) hsp hbtw
      have h2 := Side.liesBetweenInSupport_mono hS hP.cuff_vertices_ge_two
        (hP.supports_isSupport (τ i)) (hKF i) h1
      have hle' := hP.v4_between (τ i) _ _ _ h2
      obtain ⟨⟨huK, huV⟩, hs₁, hs₂, hs₁K, hs₂K, -⟩ := hbtw
      simp only [unitMap_space, unitMap_vertex, hcu_s i s₁ hs₁ hs₁K, hcu_s i s₂ hs₂ hs₂K,
        hcu_v i u ⟨huV, huK⟩]
      rw [← isoImage_inter (nm2_injective _)]
      exact isoImage_le hle' le_rfl (injOn_id _) hle' }

end presentation

end CutLine
end GM21
end GraphMinor
