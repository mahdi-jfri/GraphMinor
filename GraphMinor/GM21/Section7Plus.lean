module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.Section5ThreeTwo
public import GraphMinor.GM21.Section6Supports
public import GraphMinor.GM21.Section4Tangle
import GraphMinor.GM19.LineCut
import GraphMinor.GM19.ThinPainting
import GraphMinor.GM19.RadialExists
import GraphMinor.GM19.Perimeter
import GraphMinor.GM15.Section3Parallel

/-!
# Graph Minors XXI, Section 7: the drawing `Γ^+`

Graph Minors XXI, Section 7 (page 30 of the preprint): "If $\Gamma$ is a drawing in a surface
$\Sigma$ such that $|V(\Gamma) \cap C| \ge 2$ for every cuff $C$, we define $\Gamma^+$ to be the
drawing in $\hat{\Sigma}$ with $U(\Gamma^+) = U(\Gamma) \cup bd(\Sigma)$ and
$V(\Gamma^+) = V(\Gamma)$."

The proof of (7.2) works with `Γ^+` as a graph, `drawingPlusHypergraph`. The proof of (7.3) also
needs it as a drawing in `Σ̂`, to apply (4.6). This file builds it in two steps.

- `plusDrawing` is the drawing in `Σ` with `U = U(Γ) ∪ bd(Σ)` and `V = V(Γ)`. When `Γ` is proper,
  its edges are the edges of `Γ` and the spaces of `Γ` (`plusDrawing_E`), so its graph is
  `drawingPlusHypergraph` (`plusDrawing_toHypergraph`).
- Its image in a capped surface `Σ̂` under `cap.emb` is `Γ^+`. Each pasted open disc is a region of
  `Γ^+` (`cuffDisc_mem_R_capDrawing_plusDrawing`), since its frontier is a cuff, which lies in
  `U(Γ^+)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM19 GraphMinor.GM21.Supports

section PlusDrawing

variable {S : Type} [TopologicalSpace S]

/-- The spaces of `Γ` are the arc-wise components of `bd(Σ) \ V(Γ)`. -/
theorem arcComponentsIn_bd_diff_eq (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    arcComponentsIn (bd S \ Γ.V) = drawingSpaces Γ := by
  have : T2Space S := hS.2.1
  have hV := Γ.finite_V
  unfold drawingSpaces
  rw [componentsIn_bd_diff_eq hS Γ.V hV hge2]
  apply GM19.arcComponentsIn_of_pieces (finite_allCuffSpacePieces hS Γ.V hV hge2)
  · rintro s ⟨C, hC, i, rfl⟩
    exact isPathConnected_vSpaceArc Γ.V hV (cuffHomeo hS hC) (hge2 C hC) i
  · rintro s₁ ⟨C₁, hC₁, i₁, rfl⟩ s₂ ⟨C₂, hC₂, i₂, rfl⟩ hne
    by_cases hC_eq : C₁ = C₂
    · subst hC_eq
      have hi_ne : i₁ ≠ i₂ := fun h => hne (h ▸ rfl)
      exact disjoint_vSpaceArc Γ.V hV (cuffHomeo hS hC₁) (hge2 C₁ hC₁) hi_ne
    · refine Disjoint.mono ?_ ?_ (Surface.cuffs_disjoint hC₁ hC₂ hC_eq)
      · exact (vSpaceArc_subset_diff Γ.V hV _ _ i₁).trans sdiff_subset
      · exact (vSpaceArc_subset_diff Γ.V hV _ _ i₂).trans sdiff_subset
  · rintro s ⟨C, hC, i, rfl⟩ x ⟨hx_cl, hx_bd, hx_notV⟩
    rw [closure_vSpaceArc_eq_union Γ.V hV (cuffHomeo hS hC) (hge2 C hC) i] at hx_cl
    rcases hx_cl with hx_s | rfl | rfl
    · exact hx_s
    · exact (hx_notV (vNode_mem Γ.V hV (cuffHomeo hS hC) i).1).elim
    · exact (hx_notV (vNode_mem Γ.V hV (cuffHomeo hS hC) (nextFin (hge2 C hC) i)).1).elim
  · rw [← componentsIn_bd_diff_eq hS Γ.V hV hge2]
    ext x
    simp only [mem_sUnion]
    constructor
    · intro hx
      exact ⟨_, ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩
    · rintro ⟨s, ⟨y, hy, rfl⟩, hxs⟩
      exact connectedComponentIn_subset _ _ hxs

/-- For a proper drawing `Γ`, the arc-wise components of `(U(Γ) ∪ bd(Σ)) \ V(Γ)` are the edges
and the spaces of `Γ`. -/
theorem arcComponentsIn_plus_eq (hS : IsSurface S) {Γ : Surface.Drawing S} (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    arcComponentsIn ((Γ.U ∪ bd S) \ Γ.V) = Γ.E ∪ drawingSpaces Γ := by
  have : T2Space S := hS.2.1
  have hUbd : Γ.U ∩ bd S ⊆ Γ.V := fun x hx => hprop ⟨hx.2, hx.1⟩
  rw [GM19.arcComponentsIn_union_sdiff Γ.isClosed_U (isClosed_bd S) hUbd,
    arcComponentsIn_bd_diff_eq hS hge2]
  rfl

/-- The drawing in `Σ` with `U = U(Γ) ∪ bd(Σ)` and `V = V(Γ)`, for a proper drawing `Γ` with at
least two vertices in every cuff. Its image in `Σ̂` is the drawing `Γ^+` of Graph Minors XXI,
Section 7 (page 30 of the preprint). -/
noncomputable def plusDrawing (hS : IsSurface S) (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) : Surface.Drawing S where
  U := Γ.U ∪ bd S
  V := Γ.V
  V_subset_U := Γ.V_subset_U.trans subset_union_left
  isClosed_U := Γ.isClosed_U.union (isClosed_bd S)
  finite_V := Γ.finite_V
  finite_edges := by
    rw [arcComponentsIn_plus_eq hS hprop hge2]
    exact Γ.finite_edges.union (drawingSpaces_finite hS hge2)
  edge_cond := by
    intro e he
    rw [arcComponentsIn_plus_eq hS hprop hge2] at he
    rcases he with he | he
    · exact Γ.edge_cond e he
    · obtain ⟨u, v, hs⟩ := exists_spaceHasEnds_of_mem_drawingSpaces hS hge2 he
      refine Or.inl ⟨u, v, hs.2.2.2.1, ?_, ?_⟩
      · have hdisj : e ∩ Γ.V = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
          exact (subset_bd_diff_of_mem_drawingSpaces he hx.1).2 hx.2
        rw [hs.2.2.2.2.2, union_inter_distrib_right, hdisj, empty_union]
        ext x
        simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
        constructor
        · exact fun h => h.1
        · rintro (rfl | rfl)
          · exact ⟨Or.inl rfl, hs.2.1.1⟩
          · exact ⟨Or.inr rfl, hs.2.2.1.1⟩
      · rw [hs.2.2.2.2.2]
        exact hs.2.2.2.2.1

theorem plusDrawing_U (hS : IsSurface S) (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    (plusDrawing hS Γ hprop hge2).U = Γ.U ∪ bd S := rfl

theorem plusDrawing_V (hS : IsSurface S) (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    (plusDrawing hS Γ hprop hge2).V = Γ.V := rfl

theorem plusDrawing_E (hS : IsSurface S) (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) :
    (plusDrawing hS Γ hprop hge2).E = Γ.E ∪ drawingSpaces Γ :=
  arcComponentsIn_plus_eq hS hprop hge2

/-- The graph of `plusDrawing` is `Γ^+` as used in (7.2): vertices `V(Γ)`, and edges the edges
and spaces of `Γ`. -/
theorem plusDrawing_toHypergraph (hS : IsSurface S) (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) (h_fin : (drawingSpaces Γ).Finite) :
    (plusDrawing hS Γ hprop hge2).toHypergraph = drawingPlusHypergraph Γ h_fin := by
  apply Hypergraph.ext
  · rfl
  · exact plusDrawing_E hS Γ hprop hge2
  · funext e v
    apply propext
    change (e ∈ (plusDrawing hS Γ hprop hge2).E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔
      (e ∈ Γ.E ∪ drawingSpaces Γ) ∧ v ∈ Γ.V ∧ v ∈ closure e
    rw [plusDrawing_E]

end PlusDrawing

section CappedPlus

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-- Each pasted open disc of `Σ̂` is a region of `Γ^+` in `Σ̂`: it is open, connected and
disjoint from `U(Γ^+)`, and its frontier is the cuff, which lies in `U(Γ^+)`. -/
theorem cuffDisc_mem_R_capDrawing_plusDrawing (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    (Γ : Surface.Drawing S) (hprop : Γ.IsProper) (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {C : Set S} (hC : C ∈ cuffs S) :
    cap.cuffDisc C ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).R := by
  have : T2Space S := hS.2.1
  have hsurf := cap.isSurface
  have : T2Space Shat := hsurf.2.1
  have hD := cap.cuffDisc_closedDisc C hC
  have heq := cap.cuffDisc_eq_discInt hS hC
  have hCbd : C ⊆ bd S := by
    rcases hC with ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset (bd S) x
  have hnot : ∀ y : S, cap.emb y ∉ cap.cuffDisc C := by
    intro y hy
    have : cap.emb y ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.mpr ⟨C, hC, hy⟩
    exact this (mem_range_self y)
  have hopen : IsOpen (cap.cuffDisc C) := heq ▸ hD.isOpen_discInt hsurf.2.2
  apply GM15.mem_R_of_isOpen_isPreconnected cap.isClosedSurface hopen
  · exact heq ▸ hD.nonempty_discInt
  · exact heq ▸ hD.isPreconnected_discInt
  · rw [capDrawing_U]
    refine disjoint_left.mpr ?_
    rintro x hx ⟨y, -, rfl⟩
    exact hnot y hx
  · rintro x ⟨hx_cl, hx_cl'⟩
    rw [cap.closure_cuffDisc hS hC] at hx_cl
    rcases hx_cl with hxD | ⟨y, hyC, rfl⟩
    · have hcl : IsClosed (univ \ cap.cuffDisc C) := by
        rw [← compl_eq_univ_sdiff]
        exact hopen.isClosed_compl
      exact absurd hxD (hcl.closure_subset hx_cl').2
    · rw [capDrawing_U, plusDrawing_U]
      exact mem_image_of_mem _ (Or.inr (hCbd hyC))

/-- A tangle in the graph of a drawing `D` in `Σ` gives a tangle of the same order in the graph
of its image `capDrawing hS cap D` in `Σ̂`. -/
theorem isTangle_capDrawing (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    (D : Surface.Drawing S) {θ : ℕ} {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle D.toHypergraph θ 𝒯) :
    ∃ 𝒯', IsTangle (capDrawing hS cap D).toHypergraph θ 𝒯' := by
  have : CompactSpace S := hS.1
  have : T2Space Shat := cap.isSurface.2.1
  exact ⟨_, isTangle_mapDrawingInjOn D cap.emb cap.isEmbedding.continuous.continuousOn
    cap.isEmbedding.injective.injOn h𝒯⟩

/-- **(4.6) applied to `Γ^+`**, as in the proof of Graph Minors XXI, (7.3) (page 31 of the
preprint): "Now $\Gamma \setminus X$ is obtained from $\Gamma^+$ by deleting some ... vertices and
edges of $\Gamma^+$, all incident with one of $c(\Sigma)$ regions of $\Gamma^+$ in $\hat{\Sigma}$."

For every `θ' ≥ 1` there is `θ ≥ 1` such that, if `Γ^+` has a tangle of order `≥ θ` and
`X ⊆ V(Γ) ∩ bd(Σ)`, then the image of `Γ \ X` in `Σ̂` has a tangle of order `≥ θ'`. The regions
are the pasted discs (`cuffDisc_mem_R_capDrawing_plusDrawing`). Each deleted vertex is in `X`, and
so on a cuff. Each deleted edge is a space, which lies on a cuff, or an edge of `Γ` with an end
in `X`. -/
theorem exists_tangle_capDrawing_deleteVertices [T2Space S] (hS : IsSurface S)
    (cap : IsCappedSurface S Shat) {θ' : ℕ} (hθ' : 1 ≤ θ') :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Surface.Drawing S) (hprop : Γ.IsProper)
        (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) (X : Set S), X ⊆ bd S →
        (∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
          θ ≤ θ₀ ∧ IsTangle (plusDrawing hS Γ hprop hge2).toHypergraph θ₀ 𝒯) →
        ∃ (θ₁ : ℕ) (𝒯' : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))),
          θ' ≤ θ₁ ∧ IsTangle (capDrawing hS cap (GM12.deleteVertices Γ X)).toHypergraph θ₁ 𝒯' := by
  have : CompactSpace S := hS.1
  have : T2Space Shat := cap.isSurface.2.1
  have : ConnectedSpace Shat := cap.connected
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have : Fintype (cuffs S) := hcuffs_fin.fintype
  let ρ := Fintype.card (cuffs S)
  let eC : Fin ρ ≃ cuffs S := (Fintype.equivFin (cuffs S)).symm
  obtain ⟨θ, hθ, H⟩ := theorem_4_6_proof cap.isSurface cap.bd_empty hθ' ρ
  refine ⟨θ, hθ, fun Γ hprop hge2 X hX h𝒯 => ?_⟩
  have hCbd : ∀ C ∈ cuffs S, C ⊆ bd S := by
    rintro C ⟨x, hx, rfl⟩
    exact connectedComponentIn_subset (bd S) x
  have hcuff_of_bd : ∀ x ∈ bd S, ∃ i : Fin ρ, x ∈ (eC i : Set S) := by
    intro x hx
    rw [← sUnion_cuffs (S := S)] at hx
    obtain ⟨C, hC, hxC⟩ := hx
    exact ⟨eC.symm ⟨C, hC⟩, by simpa using hxC⟩
  have hsub_cl : ∀ i : Fin ρ, cap.emb '' (eC i : Set S) ⊆ closure (cap.cuffDisc (eC i)) := by
    intro i
    rw [cap.closure_cuffDisc hS (eC i).2]
    exact subset_union_right
  let Γp := plusDrawing hS Γ hprop hge2
  let Γ₁ := GM12.deleteVertices Γ X
  have hcont : ContinuousOn cap.emb Γp.U := cap.isEmbedding.continuous.continuousOn
  have hinj : InjOn cap.emb Γp.U := cap.isEmbedding.injective.injOn
  obtain ⟨θ₀, 𝒯, hθ₀, h𝒯p⟩ := h𝒯
  have h𝒯hat : IsTangle (capDrawing hS cap Γp).toHypergraph θ₀ (mapTangleInjOn cap.emb 𝒯) :=
    isTangle_mapDrawingInjOn Γp cap.emb hcont hinj h𝒯p
  have hE_big : (capDrawing hS cap Γp).E = (image cap.emb) '' (Γ.E ∪ drawingSpaces Γ) := by
    rw [capDrawing_E, plusDrawing_E]
  have hE_small : (capDrawing hS cap Γ₁).E = (image cap.emb) '' {e ∈ Γ.E | Disjoint (closure e ∩ Γ.V) X} := by
    rw [capDrawing_E, GM12.deleteVertices_E]
  refine H (capDrawing hS cap Γp) (capDrawing hS cap Γ₁) (fun i => cap.cuffDisc (eC i))
    (fun i => cuffDisc_mem_R_capDrawing_plusDrawing hS cap Γ hprop hge2 (eC i).2) ?_ ?_ ?_
    ⟨θ₀, _, hθ₀, h𝒯hat⟩
  · refine ⟨?_, ?_⟩
    · rw [capDrawing_V, capDrawing_V, GM12.deleteVertices_V]
      exact image_mono sdiff_subset
    · rw [hE_big, hE_small]
      exact image_mono fun e he => Or.inl he.1
  · rintro v ⟨hv_big, hv_small⟩
    rw [capDrawing_V] at hv_big hv_small
    obtain ⟨x, hxV, rfl⟩ := hv_big
    have hxX : x ∈ X := by
      by_contra hxX
      apply hv_small
      rw [GM12.deleteVertices_V]
      exact mem_image_of_mem _ ⟨hxV, hxX⟩
    obtain ⟨i, hxi⟩ := hcuff_of_bd x (hX hxX)
    exact ⟨i, hsub_cl i (mem_image_of_mem _ hxi)⟩
  · rintro e' ⟨he_big, he_small⟩
    rw [hE_big] at he_big
    rw [hE_small] at he_small
    obtain ⟨e, he | he, rfl⟩ := he_big
    · right
      have hnot : ¬ Disjoint (closure e ∩ Γ.V) X := fun h => he_small ⟨e, ⟨he, h⟩, rfl⟩
      obtain ⟨x, ⟨hxcl, hxV⟩, hxX⟩ := not_disjoint_iff.mp hnot
      refine ⟨cap.emb x, image_closure_subset_closure_image cap.isEmbedding.continuous
        (mem_image_of_mem _ hxcl), ?_⟩
      rw [capDrawing_V, capDrawing_V, GM12.deleteVertices_V]
      refine ⟨mem_image_of_mem _ hxV, ?_⟩
      rintro ⟨y, hy, hyx⟩
      have := cap.isEmbedding.injective hyx
      subst this
      exact hy.2 hxX
    · left
      obtain ⟨x, hx⟩ := (isConnected_of_mem_drawingSpaces he).nonempty
      have hx_bd := (subset_bd_diff_of_mem_drawingSpaces he hx).1
      obtain ⟨i, hxi⟩ := hcuff_of_bd x hx_bd
      exact ⟨i, cap.emb x, mem_image_of_mem _ hx, hsub_cl i (mem_image_of_mem _ hxi)⟩

end CappedPlus

end GM21
end GraphMinor
