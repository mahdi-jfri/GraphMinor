module

public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.Section7Three
public import GraphMinor.GM21.Section7Plus
public import GraphMinor.GM21.HypergraphMap
import GraphMinor.GM21.Section5
import GraphMinor.GM21.Section7JumpUnion
import GraphMinor.GM21.Section6Three
import GraphMinor.GM21.Section7
import GraphMinor.GM21.Section2
import GraphMinor.GM19.CapExists
import GraphMinor.GM12.Section73Tangle
import GraphMinor.GM04.Decomposition.Basic

/-!
# Graph Minors XXI, (7.3)

"**7.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a presentation in $\Sigma$ of depth $\le q$, and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage.*" (page 31 of the preprint).

We prove (7.3) from (5.2) (`theorem_5_2_parallel`) and (6.3) (`theorem_6_3_parallel_proof`),
following the paper's proof:

1. Choose `λ` by (6.3), a capped surface `Σ̂` of `Σ`, `θ₁` by (5.2) for `Σ̂` and `2(p + λ)`, and
   `θ₂` by (4.6) (`exists_tangle_capDrawing_deleteVertices`). Let `θ = q θ₂`.
2. By (7.2), `Γ^+` has a tangle of order `θ₂`.
3. Let `L` be a vital `p`-linkage. Let `Γ'` be the union of all paths of `L ∩ Γ` with both ends in
   `bd(Σ)` and no internal vertex in `bd(Σ)` (`jumpUnion`). It is `L ∩ Γ` with the tails of `L`
   deleted (`jumpUnion_eq`, `tailSet`), and `G' = Γ' ∪ H₁ ∪ … ∪ H_r` has a presentation
   (`IsPresentation.restrict`) with the exhaustive vital `p`-linkage `L ∩ G'`. By (6.3), `Γ'` has
   at most `λ` `Σ`-jumps.
4. Let `X` be the vertices of `Γ` in `bd(Σ)` with no edge of `L ∩ Γ`. Every component of
   `(L ∩ Γ) \ X` contains a terminal of `L` outside `bd(Σ)` or includes a `Σ`-jump of `Γ'`, so it
   has at most `λ + p` components (`encard_components_le`), and it is a vital
   `2(λ + p)`-linkage in `Γ \ X` (`encard_terminals_le_two_mul_components`).
5. By (4.6), the image of `Γ \ X` in `Σ̂` has a tangle of order `≥ θ₁`, which contradicts (5.2).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Hypergraph GraphMinor.GM10 GraphMinor.Surface GraphMinor.GM19

universe u v

/-! ## Moving a linkage of `Γ_sub` to the drawing `Γ` -/

section transport

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}

theorem IsDrawingIso.eq_isoImage (hiso : IsDrawingIso Γ Γ_sub ιV ιE) :
    Γ_sub = isoImage ιV ιE Γ.toHypergraph := by
  apply Hypergraph.ext
  · exact hiso.ιV_image.symm
  · exact hiso.ιE_image.symm
  · funext e' v'
    apply propext
    constructor
    · intro h
      have he' : e' ∈ ιE '' Γ.E := hiso.ιE_image ▸ Γ_sub.edge_mem_of_inc h
      have hv' : v' ∈ ιV '' Γ.V := hiso.ιV_image ▸ Γ_sub.vertex_mem_of_inc h
      obtain ⟨e, he, rfl⟩ := he'
      obtain ⟨x, hx, rfl⟩ := hv'
      exact ⟨e, x, ⟨he, hx, (hiso.inc_iff e he x hx).1 h⟩, rfl, rfl⟩
    · rintro ⟨e, x, ⟨he, hx, hxe⟩, rfl, rfl⟩
      exact (hiso.inc_iff e he x hx).2 hxe

theorem IsDrawingIso.deleteVertices_eq_isoImage (hiso : IsDrawingIso Γ Γ_sub ιV ιE) {X : Set S}
    (hX : X ⊆ Γ.V) :
    Γ_sub.deleteVertices (ιV '' X) = isoImage ιV ιE (Γ.toHypergraph.deleteVertices X) := by
  have hle : Γ.toHypergraph.deleteVertices X ≤ Γ.toHypergraph := GM10.deleteVertices_le _ X
  have himg : isoImage ιV ιE (Γ.toHypergraph.deleteVertices X) ≤ Γ_sub := by
    rw [hiso.eq_isoImage]
    exact isoImage_le hle le_rfl hiso.ιE_injOn hle
  apply GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.deleteVertices_le _ _) himg
  · change Γ_sub.vertexSet \ ιV '' X = ιV '' (Γ.V \ X)
    rw [hiso.ιV_injOn.image_sdiff_subset hX, hiso.ιV_image]
  · ext e'
    change e' ∈ {e ∈ Γ_sub.edgeSet | ∀ v ∈ ιV '' X, ¬ Γ_sub.Inc e v} ↔
      e' ∈ ιE '' {e ∈ Γ.E | ∀ v ∈ X, ¬ (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e)}
    constructor
    · rintro ⟨he', hno⟩
      have he'' : e' ∈ ιE '' Γ.E := hiso.ιE_image ▸ he'
      obtain ⟨e, he, rfl⟩ := he''
      refine ⟨e, ⟨he, fun x hx hinc => hno (ιV x) (mem_image_of_mem ιV hx) ?_⟩, rfl⟩
      exact (hiso.inc_iff e he x (hX hx)).2 hinc.2.2
    · rintro ⟨e, ⟨he, hno⟩, rfl⟩
      refine ⟨hiso.ιE_image ▸ mem_image_of_mem ιE he, ?_⟩
      rintro _ ⟨x, hx, rfl⟩ hinc
      exact hno x hx ⟨he, hX hx, (hiso.inc_iff e he x (hX hx)).1 hinc⟩

/-- A vital `N`-linkage of `Γ_sub \ ιV(X)` gives a vital `N`-linkage of the image of `Γ \ X` in
the capped surface. -/
theorem hasVitalPLinkage_capDrawing_deleteVertices [T2Space S] {Shat : Type}
    [TopologicalSpace Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    (hiso : IsDrawingIso Γ Γ_sub ιV ιE) {X : Set S} (hX : X ⊆ Γ.V) {N : ℕ}
    (h : HasVitalPLinkage (Γ_sub.deleteVertices (ιV '' X)) N) :
    HasVitalPLinkage (capDrawing hS cap (GM12.deleteVertices Γ X)).toHypergraph N := by
  have : CompactSpace S := hS.1
  have : T2Space Shat := cap.isSurface.2.1
  rw [hiso.deleteVertices_eq_isoImage hX] at h
  have hleV : (Γ.toHypergraph.deleteVertices X).vertexSet ⊆ Γ.V := fun x hx => hx.1
  have hleE : (Γ.toHypergraph.deleteVertices X).edgeSet ⊆ Γ.E := fun e he => he.1
  rw [hasVitalPLinkage_isoImage (hiso.ιV_injOn.mono hleV) (hiso.ιE_injOn.mono hleE),
    ← GM12.deleteVertices_toHypergraph] at h
  obtain ⟨L₀, hL₀⟩ := h
  exact ⟨_, (isVitalPLinkage_mapDrawingInjOn_of_injOn (GM12.deleteVertices Γ X) cap.emb
    cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn hL₀).1⟩

end transport

/-! ## The separation `(H₁ ∪ … ∪ H_r, Γ)` -/

section separation

variable {α : Type u} {β : Type v} {S : Type} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

theorem IsPresentation.isSeparation (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    G.IsSeparation (Hypergraph.biUnion Finset.univ H) Γ_sub := by
  rw [isSeparation_iff_of_le (biUnion_H_le hP) hP.drawing_subgraph]
  refine ⟨?_, ?_, ?_⟩
  · rw [hP.v1_union_V]
    simp [Hypergraph.biUnion]
  · rw [hP.v1_union_E]
    simp [Hypergraph.biUnion]
  · ext e
    simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_inter_iff, mem_iUnion,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨j, hj⟩ he
    exact disjoint_left.1 (hP.v1_inter_E j) hj he

/-- `V((H₁ ∪ … ∪ H_r) ∩ Γ) = ιV(V(Γ) ∩ bd(Σ))`. -/
theorem IsPresentation.biUnion_inter_eq (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) :
    (Hypergraph.biUnion Finset.univ H).vertexSet ∩ Γ_sub.vertexSet = ιV '' (Γ.V ∩ bd S) := by
  have hFbd : ∀ j, F_star j ⊆ bd S := fun j =>
    subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j)
  apply Subset.antisymm
  · rintro y ⟨hyH, hyΓ⟩
    simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hyH
    obtain ⟨j, hj⟩ := hyH
    have hy : y ∈ ιV '' (Γ.V ∩ F_star j) := hP.v1_inter_V j ▸ ⟨hj, hyΓ⟩
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨u, ⟨hu.1, hFbd j hu.2⟩, rfl⟩
  · rintro _ ⟨u, hu, rfl⟩
    have hu' := hP.bd_vertices_covered hu
    simp only [mem_iUnion] at hu'
    obtain ⟨j, hj⟩ := hu'
    have hy : ιV u ∈ (H j).vertexSet ∩ Γ_sub.vertexSet := hP.v1_inter_V j ▸ ⟨u, ⟨hu.1, hj⟩, rfl⟩
    refine ⟨?_, hy.2⟩
    simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
    exact ⟨j, hy.1⟩

end separation

/-! ## (7.3) -/

/-- **Graph Minors XXI, (7.3)** (page 31 of the preprint):
"**7.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a presentation in $\Sigma$ of depth $\le q$, and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage.*" -/
theorem theorem_7_3_proof :
    GM21Theorem73Statement.{u, v, 0} := by
  intro S _ hconn hS p r q hq
  have : T2Space S := hS.2.1
  -- The constants of the proof.
  obtain ⟨lam, hlam⟩ := theorem_6_3_parallel_proof.{u, v} S hS p r q hq
  obtain ⟨Shat, _, ⟨cap⟩⟩ := exists_cappedSurface _ S hS hconn rfl
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨θ₁, hθ₁, h52'⟩ := theorem_5_2_parallel Shat cap.isSurface cap.bd_empty (2 * (p + lam))
  obtain ⟨θ₂, hθ₂, h46⟩ := exists_tangle_capDrawing_deleteVertices hS cap hθ₁
  refine ⟨q * θ₂, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  intro α β G Γ Γ_sub ιV ιE r' F_star H μ θ_G 𝒯 hG hr' hdepth hθ h𝒯 hsurr ⟨L, hLv, hLp⟩
  obtain ⟨qv, hP, -, -⟩ := id hdepth
  have hiso := hP.drawing_iso
  -- By (7.2), `Γ^+` has a tangle of order `θ₂`.
  obtain ⟨𝒯₂, h𝒯₂⟩ := theorem_7_2_proof hG hθ₂ hq hdepth h𝒯 hθ hsurr
  have hplus : ∃ (θ₀ : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))), θ₂ ≤ θ₀ ∧
      IsTangle (plusDrawing hS Γ hP.is_proper_drawing hP.cuff_vertices_ge_two).toHypergraph
        θ₀ 𝒯 := by
    refine ⟨θ₂, 𝒯₂, le_rfl, ?_⟩
    rw [plusDrawing_toHypergraph _ _ _ _ hdepth.spaces_finite]
    exact h𝒯₂
  -- The separation `(A, Γ)` with `A = H₁ ∪ … ∪ H_r` and `V(A ∩ Γ) = ιV(V(Γ) ∩ bd(Σ))`.
  set A := Hypergraph.biUnion Finset.univ H with hA_def
  have hsep : G.IsSeparation A Γ_sub := hP.isSeparation
  have hBeq : A.vertexSet ∩ Γ_sub.vertexSet = ιV '' (Γ.V ∩ bd S) := hP.biUnion_inter_eq
  set B := A.vertexSet ∩ Γ_sub.vertexSet with hB_def
  have hLG : L ≤ G := hLv.1.1
  set K := L ∩ Γ_sub with hK_def
  set W := tailSet L Γ_sub B with hW_def
  -- The paper's `Γ'`: the union of all paths of `L ∩ Γ` with both ends in `bd(Σ)` and no internal
  -- vertex in `bd(Σ)`. It is `L ∩ Γ` with the tails of `L` deleted.
  set C' := jumpUnion K B with hC'_def
  have hC'eq : C' = K.deleteVertices W := jumpUnion_eq hsep hLv.1
  have hC'le : C' ≤ Γ_sub :=
    (jumpUnion_le K B).trans (GM10.inter_le_right hLG hsep.right_le)
  have hBΓ : B ⊆ Γ_sub.vertexSet := inter_subset_right
  have hBC' : ιV '' (Γ.V ∩ bd S) ⊆ C'.vertexSet := by
    rw [← hBeq, hC'eq]
    intro y hy
    have hyL : y ∈ L.vertexSet := hLv.2.1 ▸ hsep.right_le.vertexSet_subset (hBΓ hy)
    exact ⟨⟨hyL, hBΓ hy⟩, fun hyW => hyW.1.2 hy⟩
  -- The presentation of `G' = Γ' ∪ H₁ ∪ … ∪ H_r`.
  set Γ' := restrictDrawing Γ ιV ιE C' with hΓ'_def
  have hdepth' := hdepth.restrict hC'le hBC'
  have hG'G : C' ∪ A ≤ G :=
    GM10.union_le (hC'le.trans hsep.right_le) hsep.left_le
  have heq : L ∩ (C' ∪ A) = L.deleteVertices W := by
    rw [hC'eq]
    exact inter_eq_deleteVertices_tailSet hsep hLv.1
  have hvital' : IsVitalLinkage (C' ∪ A) (L ∩ (C' ∪ A)) := isVitalLinkage_inter_of_le hLv hG'G
  have hexh : IsExhaustiveLinkage (C' ∪ A) C' r' H (L ∩ (C' ∪ A)) := by
    refine ⟨hvital', ?_, ?_⟩
    · rw [heq]
      rw [hC'eq]
      exact le_deleteVertices_of_disjoint
        ((GM10.deleteVertices_le K W).trans (GM10.inter_le_left hLG hsep.right_le))
        (disjoint_sdiff_left)
    · rw [heq]
      intro x hx
      have hxA := terminals_deleteVertices_tailSet_subset hsep hLv.1 hx
      simpa [hA_def, Hypergraph.biUnion] using hxA
  have hpl : IsPLinkage (C' ∪ A) (L ∩ (C' ∪ A)) p := by
    refine ⟨hvital'.1, ?_⟩
    rw [heq]
    exact (ncard_terminals_deleteVertices_tailSet_le hsep hLv.1).trans hLp.2
  -- By (6.3), `Γ'` has at most `λ` `Σ`-jumps.
  have hjumps : (sigmaJumps Γ' C' ιV).encard ≤ lam :=
    hlam (C' ∪ A) Γ' C' ιV ιE r' F_star H μ (L ∩ (C' ∪ A)) (isGraph_of_le hG'G hG) hr'
      hdepth' hexh hpl
  have hVbd : Γ'.V ∩ bd S = Γ.V ∩ bd S := restrictDrawing_V_inter_bd hiso hC'le hBC'
  have hJ : jumpSet C' B ⊆ sigmaJumps Γ' C' ιV := by
    rintro Q ⟨hQ, hQpath, a, haB, b, hbB, hab, hterm, hin⟩
    rw [hBeq] at haB hbB
    obtain ⟨u, hu, rfl⟩ := haB
    obtain ⟨w, hw, rfl⟩ := hbB
    refine ⟨hQ, hQpath, u, hVbd ▸ hu, w, hVbd ▸ hw, fun h => hab (h ▸ rfl), hterm, ?_⟩
    intro x hx hxQ
    rw [hVbd] at hx
    have hxB : ιV x ∈ B := hBeq ▸ mem_image_of_mem ιV hx
    rcases hin _ hxQ hxB with h | h
    · exact Or.inl (hiso.ιV_injOn hx.1 hu.1 h)
    · exact Or.inr (hiso.ιV_injOn hx.1 hw.1 h)
  -- The vertices `X` of `Γ` in `bd(Σ)` with no edge of `L ∩ Γ`.
  set X' := {x ∈ B | incidentEdges K x = ∅} with hX'_def
  set X := {x ∈ Γ.V ∩ bd S | ιV x ∈ X'} with hX_def
  have hXX' : ιV '' X = X' := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro y hy
      have hyB : y ∈ ιV '' (Γ.V ∩ bd S) := hBeq ▸ hy.1
      obtain ⟨x, hx, rfl⟩ := hyB
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  have hXV : X ⊆ Γ.V := fun x hx => hx.1.1
  have hX'Γ : X' ⊆ Γ_sub.vertexSet := fun x hx => hBΓ hx.1
  -- `(L ∩ Γ) \ X` is a vital linkage of `Γ \ X` with at most `2 (p + λ)` terminals.
  have hKv : IsVitalLinkage Γ_sub K := isVitalLinkage_inter_of_le hLv hsep.right_le
  have hK'v : IsVitalLinkage (Γ_sub.deleteVertices X') (K.deleteVertices X') :=
    (theorem_2_1_proof (p := (terminals K).ncard) ⟨hKv, hKv.1, le_rfl⟩ hX'Γ).1
  -- Each component of `L ∩ (Γ \ X)` contains a terminal of `L` outside `bd(Σ)` or includes a
  -- `Σ`-jump of `Γ'`, so there are at most `λ + p` components.
  have hcomp := encard_components_le hsep hLv.1
  have hfinL : (terminals L).Finite := L.vertexSet_finite.subset fun x hx => hx.1
  have hLenc : (terminals L).encard ≤ p := by
    rw [← hfinL.cast_ncard_eq]
    exact_mod_cast hLp.2
  have hJenc : (jumpSet C' B).encard ≤ lam := (encard_le_encard hJ).trans hjumps
  have hfinK : (terminals (K.deleteVertices X')).Finite :=
    (K.deleteVertices X').vertexSet_finite.subset fun x hx => hx.1
  have hKnc : (terminals (K.deleteVertices X')).ncard ≤ 2 * (p + lam) := by
    have h1 : (terminals (K.deleteVertices X')).encard ≤ ((2 * (p + lam) : ℕ) : ℕ∞) := by
      refine (encard_terminals_le_two_mul_components hK'v.1).trans ?_
      push_cast
      gcongr
      exact hcomp.trans (add_le_add hLenc hJenc)
    rw [← hfinK.cast_ncard_eq] at h1
    exact_mod_cast h1
  have hvp : HasVitalPLinkage (Γ_sub.deleteVertices (ιV '' X)) (2 * (p + lam)) := by
    rw [hXX']
    exact ⟨_, hK'v, hK'v.1, hKnc⟩
  -- Transport to `Σ̂`, and use (4.6) and (5.2).
  have hvp' := hasVitalPLinkage_capDrawing_deleteVertices hS cap hiso hXV hvp
  obtain ⟨θ₃, 𝒯₃, hθ₃, h𝒯₃⟩ :=
    h46 Γ hP.is_proper_drawing hP.cuff_vertices_ge_two X (fun x hx => hx.1.2) hplus
  exact h52' _ θ₃ 𝒯₃ hθ₃ h𝒯₃ hvp'

end GM21
end GraphMinor
