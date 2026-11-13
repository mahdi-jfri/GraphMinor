module

public import GraphMinor.GM21.Section5ThreeTwo
public import GraphMinor.GM21.Section5Linkage
import GraphMinor.GM21.Section2
import GraphMinor.GM12.Section3DiscRegion
import GraphMinor.GM12.Section72RadialExists
import GraphMinor.GM12.Section73
import GraphMinor.GM12.Section74Base
import GraphMinor.GM12.Section74BaseCellularity
import GraphMinor.GM12.Section74DeletedRegion
import GraphMinor.GM12.Section74VertexWalk
import GraphMinor.GM12.Section75Proof
import GraphMinor.GM12.Section77
import GraphMinor.GM12.Section7Proved
import GraphMinor.GM12.Section79
import GraphMinor.GM11.RadialRegions
import GraphMinor.GM11.Section91
import GraphMinor.GM11.CitedResults

/-!
# Graph Minors XXI, Section 5: Proof of (5.1)

Formalization of **(5.1)** (pages 15–17 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

We follow the paper's five-claim proof:
- Claim (1) (`claim_5_1_1`): existence of a vertex `v ∈ Γ.V` with `d({v}, r) ≥ θ'` for every cuff
  region `r`.
- Claim (2) (`claim_5_1_2`): if `Γ \ v` is not 2-cell in `Shat`, then `Γ` has no vital linkage with
  set of terminals `Γ.V ∩ bd S`.
- Claim (3) (`claim_5_1_3`): existence of a respectful tangle `T'` in `Γ' = Γ \ v` restricting `T`
  and preserving atom distances up to an additive constant (`GM12.theorem_7_8_proof` + `GM12.theorem_7_9_proof`).
- Claim (4) (`claim_5_1_4`): no `Γ'`-normal `O`-arc `F` in `S` with `|F ∩ V(Γ')| < |C ∩ V(Γ')|`
  has `C ⊆ ins'(F)`.
- Claim (5) (`claim_5_1_5`): cuff regions of distinct cuffs have `d'`-distance `≥ θ'`.
Applying `theorem_3_2_of_cuff_ins` and `exists_linkage_avoiding_vertex_of_connectingSubdrawings`
then yields a linkage in `Γ \ v` with the same pattern as `L`, showing `L` is not vital.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

/-! ## 1. Helper lemmas on hypergraph pullbacks and normal disc separations -/

section Helpers

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

omit [TopologicalSpace S] [TopologicalSpace Shat] in
private lemma comapSubH_le_self' {G : Hypergraph S (Set S)} {A' : Hypergraph Shat (Set Shat)}
    {ι : S → Shat} (hA' : A' ≤ mapSubH ι G) : comapSubH ι G A' ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, comapSubH, mem_ofPred_eq]
    refine ⟨fun hincG ↦ ⟨hincG, he.2, ?_⟩, fun h ↦ h.1⟩
    have hinc_map : (mapSubH ι G).Inc (ι '' e) (ι v) := ⟨e, v, hincG, rfl, rfl⟩
    exact A'.vertex_mem_of_inc ((GM10.inc_iff_of_le hA' he.2).mpr hinc_map)

omit [TopologicalSpace S] [TopologicalSpace Shat] in
private lemma isSeparation_comapSubH' {G : Hypergraph S (Set S)}
    {A' B' : Hypergraph Shat (Set Shat)} {ι : S → Shat}
    (hsep : (mapSubH ι G).IsSeparation A' B') :
    G.IsSeparation (comapSubH ι G A') (comapSubH ι G B') := by
  have hleA := comapSubH_le_self' hsep.left_le
  have hleB := comapSubH_le_self' hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [comapSubH, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hvG
      have hιv : ι v ∈ A'.vertexSet ∪ B'.vertexSet :=
        hsep.vertexSet_union.symm ▸ mem_image_of_mem ι hvG
      exact hιv.imp (fun h ↦ ⟨hvG, h⟩) (fun h ↦ ⟨hvG, h⟩)
  · ext e
    simp only [comapSubH, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro heG
      have hιe : ι '' e ∈ A'.edgeSet ∪ B'.edgeSet :=
        hsep.edgeSet_union.symm ▸ mem_image_of_mem (image ι) heG
      exact hιe.imp (fun h ↦ ⟨heG, h⟩) (fun h ↦ ⟨heG, h⟩)
  · ext e
    simp only [comapSubH, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heA'⟩, ⟨_, heB'⟩⟩
    exact hsep.notMem_edgeSet_right heA' heB'

private lemma drawing_inter_le' (H : Surface.Drawing Shat) {D : Set Shat} (hD : IsClosed D) :
    (PaintingOrDrawing.drawing H).inter D ≤ H.toHypergraph := by
  refine ⟨inter_subset_left, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change (e ∈ H.E ∧ v ∈ H.V ∧ v ∈ closure e) ↔
    (e ∈ H.E ∧ v ∈ H.V ∧ v ∈ closure e) ∧ e ⊆ D ∧ v ∈ D
  exact ⟨fun h => ⟨h, he.2, hD.closure_subset_iff.mpr he.2 h.2.2⟩, fun h => h.1⟩

/-- If `D` is a closed disc in `Shat` with `subBd D = F` and `(PaintingOrDrawing.drawing H).IsNormal F`,
then `((PaintingOrDrawing.drawing H).inter D, (PaintingOrDrawing.drawing H).interOutside D)` is a
separation of `H.toHypergraph` of order at most `(F ∩ H.V).ncard`. -/
private lemma isSeparation_drawing_inter_interOutside [T2Space Shat]
    (H : Surface.Drawing Shat) {D F : Set Shat} (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hNorm : (PaintingOrDrawing.drawing H).IsNormal F) :
    H.toHypergraph.IsSeparation
      ((PaintingOrDrawing.drawing H).inter D)
      ((PaintingOrDrawing.drawing H).interOutside D) ∧
    separationOrder
      ((PaintingOrDrawing.drawing H).inter D)
      ((PaintingOrDrawing.drawing H).interOutside D) ≤ (F ∩ H.V).ncard := by
  have hAl : (PaintingOrDrawing.drawing H).inter D ≤ H.toHypergraph :=
    drawing_inter_le' H hD.isClosed
  have hBl : (PaintingOrDrawing.drawing H).interOutside D ≤ H.toHypergraph :=
    drawing_inter_le' H isClosed_closure
  refine ⟨(GM10.isSeparation_iff_of_le hAl hBl).mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · ext x
    change (x ∈ H.V ∩ D ∨ x ∈ H.V ∩ closure (univ \ D)) ↔ x ∈ H.V
    constructor
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    · intro hx
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨hx, hxD⟩
      · exact Or.inr ⟨hx, subset_closure ⟨mem_univ x, hxD⟩⟩
  · ext e
    change (e ∈ {e ∈ H.E | e ⊆ D} ∨ e ∈ {e ∈ H.E | e ⊆ closure (univ \ D)}) ↔ e ∈ H.E
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      obtain ⟨x, hxe⟩ := he.1
      have he_pre : IsPreconnected e :=
        (GM11.PaintingOrDrawing.edge_props (Γ := PaintingOrDrawing.drawing H) he).1
      have hdisF : Disjoint e (frontier D) := by
        rw [GM11.subBd_eq_frontier' D, hbd]
        exact disjoint_left.mpr fun y hye hyF =>
          (he.2.1 hye).2 (hNorm ⟨hyF, (he.2.1 hye).1⟩)
      by_cases hxD : x ∈ D
      · exact Or.inl ⟨he, GM12.subset_of_disjoint_frontier he_pre hD.isClosed hdisF hxe hxD⟩
      · have hdisF' : Disjoint e (frontier (closure (univ \ D))) := by
          refine Disjoint.mono_right ?_ hdisF
          intro y hy
          have hy1 : y ∈ frontier (univ \ D) := frontier_closure_subset hy
          rwa [← compl_eq_univ_sdiff, frontier_compl] at hy1
        exact Or.inr ⟨he, GM12.subset_of_disjoint_frontier
          he_pre isClosed_closure hdisF' hxe (subset_closure ⟨mem_univ x, hxD⟩)⟩
  · ext e
    change (e ∈ {e ∈ H.E | e ⊆ D} ∧ e ∈ {e ∈ H.E | e ⊆ closure (univ \ D)}) ↔
      e ∈ (∅ : Set (Set Shat))
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨he, heD⟩, ⟨_, heOut⟩⟩
    obtain ⟨x, hxe⟩ := he.1
    have hxF : x ∈ F := by
      rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure (heD hxe), heOut hxe⟩
    exact (he.2.1 hxe).2 (hNorm ⟨hxF, (he.2.1 hxe).1⟩)
  · have hsub : (((PaintingOrDrawing.drawing H).inter D) ∩
        ((PaintingOrDrawing.drawing H).interOutside D)).vertexSet ⊆ F ∩ H.V := by
      rintro x ⟨⟨hxV, hxD⟩, ⟨_, hxOut⟩⟩
      refine ⟨?_, hxV⟩
      rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
      exact ⟨subset_closure hxD, hxOut⟩
    exact ncard_le_ncard hsub (H.finite_V.subset inter_subset_right)

end Helpers

/-! ## 2. Claim (1) of (5.1) -/

/-- Along a walk `W` in `Γ_hat` ending at a vertex `u ∈ Γ_hat.V` with `d r₁ {u} ≥ θ'`, if the start
vertex `x` has distance `d r₁ {x} < θ'`, then there exists `v' ∈ Γ_hat.V` with
`θ' ≤ d r₁ {v'} ≤ θ' + 1`. -/
private lemma exists_vertex_dist_in_interval_of_walk {Shat : Type}
    [TopologicalSpace Shat] [T2Space Shat] [ConnectedSpace Shat]
    (hcl : IsClosedSurface Shat) {Γ_hat : Surface.Drawing Shat}
    {θ₀ θ' : ℕ} {T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d : Set Shat → Set Shat → ℕ}
    (hd : HasTangleMetric Γ_hat θ₀ T d)
    (hE_ne : Γ_hat.E.Nonempty)
    {r₁ : Set Shat} (hr₁ : r₁ ∈ Γ_hat.R)
    {x u : Shat} (W : GraphWalk Γ_hat.toGraph x u)
    (hu : u ∈ Γ_hat.V) (hu_dist : θ' ≤ d r₁ {u})
    (hx_lt : d r₁ {x} < θ') :
    ∃ v' ∈ Γ_hat.V, θ' ≤ d r₁ {v'} ∧ d r₁ {v'} ≤ θ' + 1 := by
  obtain ⟨_, _, _, hsym, htri, hreg, _⟩ :=
    GM11.gm15_theorem_9_1 Γ_hat θ₀ T d hcl inferInstance hd
  have hr₁A : r₁ ∈ Γ_hat.A := Or.inr hr₁
  induction W with
  | nil _ =>
    exact absurd hx_lt (not_lt.mpr hu_dist)
  | @cons x y u f hl rest ih =>
    have hf : f ∈ Γ_hat.E := hl.1
    have hxV : x ∈ Γ_hat.V := hl.2.1
    have hyV : y ∈ Γ_hat.V := hl.2.2.1
    have hxA : ({x} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨x, hxV, rfl⟩)
    have hyA : ({y} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨y, hyV, rfl⟩)
    obtain ⟨r₀, hr₀, hf_r₀⟩ := exists_region_incident hcl hf
    have hr₀A : r₀ ∈ Γ_hat.A := Or.inr hr₀
    have hx_cl_f : x ∈ closure f := by
      have : x ∈ closure f ∩ Γ_hat.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact this.1
    have hy_cl_f : y ∈ closure f := by
      have : y ∈ closure f ∩ Γ_hat.V := by rw [hl.2.2.2]; exact Or.inr rfl
      exact this.1
    have hx_cl_r₀ : x ∈ closure r₀ := closure_minimal hf_r₀ isClosed_closure hx_cl_f
    have hy_cl_r₀ : y ∈ closure r₀ := closure_minimal hf_r₀ isClosed_closure hy_cl_f
    have hd_x_r₀ : d {x} r₀ ≤ 1 := hreg hE_ne x hxV r₀ hr₀ hx_cl_r₀
    have hd_r₀_y : d r₀ {y} ≤ 1 := by
      rw [hsym r₀ hr₀A {y} hyA]
      exact hreg hE_ne y hyV r₀ hr₀ hy_cl_r₀
    have hd_r₁_r₀ : d r₁ r₀ ≤ θ' := by
      have hstep := htri r₁ hr₁A {x} hxA r₀ hr₀A
      omega
    have hd_r₁_y : d r₁ {y} ≤ θ' + 1 := by
      have hstep := htri r₁ hr₁A r₀ hr₀A {y} hyA
      omega
    by_cases hge : θ' ≤ d r₁ {y}
    · exact ⟨y, hyV, hge, hd_r₁_y⟩
    · exact ih hu hu_dist (not_le.mp hge)

/-- **Claim (1)** in the proof of Graph Minors XXI, (5.1) (page 15 of the preprint):
"(1) *There is a vertex $v$ of $\Gamma$ such that $d(v, r) \ge \theta'$ for every cuff region $r$.*" -/
theorem claim_5_1_1 {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S}
    (hprop : Γ.IsProper) {θ' θ₀ : ℕ} (hθ' : 2 ≤ θ') (hθ₀ : 2 * θ' + 1 ≤ θ₀)
    {T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d : Set Shat → Set Shat → ℕ}
    (hd : HasTangleMetric (capDrawing hS cap Γ) θ₀ T d)
    (hii : ∀ (C₁ C₂ : Set S) (r₁ r₂ : Set Shat),
      C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
      2 * θ' + 1 ≤ d r₁ r₂) :
    ∃ v ∈ Γ.V, ∀ (C : Set S) (r : Set Shat),
      IsCuffRegion hS cap Γ C r → θ' ≤ d {cap.emb v} r := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface Shat := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  let Γ_hat := capDrawing hS cap Γ
  obtain ⟨_, _, _, hsym, htri, hreg, hedge⟩ :=
    GM11.gm15_theorem_9_1 Γ_hat θ₀ T d hcl inferInstance hd
  by_cases hcuffs : (cuffs S).Nonempty
  · obtain ⟨C₁, hC₁⟩ := hcuffs
    obtain ⟨r₁, hr₁_cuff, _, _, _, huniq₁⟩ := exists_unique_cuffRegion hS cap hprop hC₁
    have hr₁ : r₁ ∈ Γ_hat.R := hr₁_cuff.2.1
    have hr₁A : r₁ ∈ Γ_hat.A := Or.inr hr₁
    have hE_ne : Γ_hat.E.Nonempty :=
      GM12.edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 (by omega : 2 ≤ θ₀)
    have hr₁_not_E : r₁ ∉ Γ_hat.E := by
      intro hr₁E
      obtain ⟨z₀, hz₀⟩ := hr₁E.1
      exact region_subset hr₁ hz₀ (hr₁E.2.1 hz₀).1
    obtain ⟨e, he, hd_e⟩ :=
      exists_edge_dist_eq_theta_uncond hcl hd hE_ne hr₁A (Or.inr hr₁_not_E)
    have heA : e ∈ Γ_hat.A := Or.inl (Or.inr he)
    have hcl_e_ne : (closure e ∩ Γ_hat.V).Nonempty := by
      rcases Γ_hat.edge_cond e he with ⟨u₁, u₂, _, hcap, _⟩ | ⟨u₁, hcap, _⟩
      · exact ⟨u₁, by rw [hcap]; exact Or.inl rfl⟩
      · exact ⟨u₁, by rw [hcap]; exact rfl⟩
    obtain ⟨u, hu_cl, huV⟩ := hcl_e_ne
    have huA : ({u} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨u, huV, rfl⟩)
    have hd_u_e : d {u} e ≤ 2 := hedge u huV e he hu_cl
    have hd_r₁_u : θ' ≤ d r₁ {u} := by
      have hstep := htri r₁ hr₁A {u} huA e heA
      omega
    obtain ⟨x₀, hx₀V, hx₀_cl⟩ := exists_vertex_at_region hcl hE_ne hr₁
    have hx₀A : ({x₀} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨x₀, hx₀V, rfl⟩)
    have hd_r₁_x₀ : d r₁ {x₀} ≤ 1 := by
      rw [hsym r₁ hr₁A {x₀} hx₀A]
      exact hreg hE_ne x₀ hx₀V r₁ hr₁ hx₀_cl
    have hpreΓ : IsPreconnected Γ_hat.U := isPreconnected_U_of_isTwoCell hcl hd.1.1
    obtain ⟨W⟩ := exists_walk_of_isPreconnected_U hpreΓ hx₀V huV
    obtain ⟨v', hv'V, hge_v', hle_v'⟩ :=
      exists_vertex_dist_in_interval_of_walk hcl hd hE_ne hr₁ W huV hd_r₁_u (by omega)
    obtain ⟨v, hv, rfl⟩ : ∃ v ∈ Γ.V, cap.emb v = v' := hv'V
    have hv_hat : cap.emb v ∈ Γ_hat.V := mem_image_of_mem _ hv
    have hv'A : ({cap.emb v} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨cap.emb v, hv_hat, rfl⟩)
    refine ⟨v, hv, fun C₂ r₂ hr₂_cuff => ?_⟩
    have hr₂ : r₂ ∈ Γ_hat.R := hr₂_cuff.2.1
    have hr₂A : r₂ ∈ Γ_hat.A := Or.inr hr₂
    rw [hsym {cap.emb v} hv'A r₂ hr₂A]
    by_cases hC_eq : C₂ = C₁
    · subst hC_eq
      have hr_eq : r₂ = r₁ := (huniq₁ r₂ hr₂).1.mp hr₂_cuff
      rw [hr_eq]
      exact hge_v'
    · have hd_r₁_r₂ : 2 * θ' + 1 ≤ d r₁ r₂ := hii C₁ C₂ r₁ r₂ ( Ne.symm hC_eq ) hr₁_cuff hr₂_cuff
      have hstep := htri r₁ hr₁A {cap.emb v} hv'A r₂ hr₂A
      have hsym_v_r₂ := hsym {cap.emb v} hv'A r₂ hr₂A
      omega
  · rw [not_nonempty_iff_eq_empty] at hcuffs
    have hV_ne : Γ_hat.V.Nonempty := by
      have hle := hd.1.2.1.order_le_ncard_vertexSet
      change θ₀ ≤ Γ_hat.V.ncard at hle
      exact (ncard_pos Γ_hat.finite_V).mp (by omega)
    obtain ⟨v', v, hv, rfl⟩ := hV_ne
    refine ⟨v, hv, fun C r hr_cuff => ?_⟩
    have hC := hr_cuff.1
    rw [hcuffs] at hC
    exact hC.elim

/-! ## 3. Claim (2) of (5.1) -/

/-- If `D` is a closed disc with boundary `F`, `F` is `K`-normal, and `K.V ∩ D = {w}`, then
`deleteVertices K {w}` is contained in `closure (univ \ D)`, so restricting `K` to
`closure (univ \ D)` preserves `deleteVertices K {w}`. -/
private lemma deleteVertices_interSet_compl_eq_of_V_inter_eq_singleton {Shat : Type}
    [TopologicalSpace Shat] [T2Space Shat]
    {K : Surface.Drawing Shat} {D F : Set Shat} {w : Shat}
    (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hn : (PaintingOrDrawing.drawing K).IsNormal F)
    (hVD : K.V ∩ D = {w}) :
    GM12.deleteVertices (K.interSet (closure (univ \ D))) {w} = GM12.deleteVertices K {w} := by
  have hfront : frontier D = F := (GM11.subBd_eq_frontier D).symm.trans hbd
  let K' := GM12.deleteVertices K {w}
  have hsub : K'.IsSubdrawing K := GM12.deleteVertices_isSubdrawing K {w}
  rw [GM12.deleteVertices_interSet isClosed_closure]
  apply GM12.interSet_eq_self_of_U_subset isClosed_closure
  rw [K'.U_eq]
  refine union_subset ?_ (iUnion₂_subset fun f hf => ?_)
  · rintro x hxV'
    obtain ⟨hxK, hxw⟩ := (GM12.deleteVertices_V K {w}).subset hxV'
    have hx_not_D : x ∉ D := fun hxD => hxw (by rw [← hVD]; exact ⟨hxK, hxD⟩)
    exact subset_closure ⟨mem_univ x, hx_not_D⟩
  · have hfK : f ∈ K.E := hsub.2 hf
    have hcl_ne : (closure f ∩ K'.V).Nonempty := by
      rcases K'.edge_cond f hf with ⟨u₁, u₂, _, hcap, _⟩ | ⟨u₁, hcap, _⟩
      · exact ⟨u₁, by rw [hcap]; exact Or.inl rfl⟩
      · exact ⟨u₁, by rw [hcap]; exact rfl⟩
    obtain ⟨u₀, hu₀_cl, hu₀V'⟩ := hcl_ne
    have hu₀_not_D : u₀ ∉ D := by
      intro hu₀D
      obtain ⟨hu₀K, hu₀w⟩ := (GM12.deleteVertices_V K {w}).subset hu₀V'
      exact hu₀w (by rw [← hVD]; exact ⟨hu₀K, hu₀D⟩)
    obtain ⟨z₀, hz₀_not_D, hz₀f⟩ :=
      mem_closure_iff.mp hu₀_cl Dᶜ hD.isClosed.isOpen_compl hu₀_not_D
    have hdis_fr : Disjoint f (frontier D) := by
      rw [hfront]
      exact disjoint_left.mpr fun y hyf hyF =>
        (hfK.2.1 hyf).2 (hn ⟨hyF, (hfK.2.1 hyf).1⟩)
    have hf_sub_out : f ⊆ closure (univ \ D) := by
      intro y hyf
      apply subset_closure
      refine ⟨mem_univ y, fun hyD => ?_⟩
      have hf_sub_D : f ⊆ D :=
        GM12.subset_of_disjoint_frontier hfK.2.2.1.isConnected.isPreconnected
          hD.isClosed hdis_fr hyf hyD
      exact hz₀_not_D (hf_sub_D hz₀f)
    exact isClosed_closure.closure_subset_iff.mpr hf_sub_out

/-- Removing selected 1-vertex discs at `w` containing only vertex `w` and at least one edge yields
a subdrawing `Γ₀` of `Γ_hat` with the same vertex set, the same vertex-deletion `deleteVertices`,
only loops at `w` removed, and no remaining 1-vertex selected disc at `w` with `Γ₀.V ∩ D = {w}`
containing an edge. -/
private lemma exists_loop_free_vertex_reduction {Shat : Type}
    [TopologicalSpace Shat] [T2Space Shat] [ConnectedSpace Shat]
    (hcl : IsClosedSurface Shat) {Γ_hat : Surface.Drawing Shat} {θ₀ : ℕ}
    {T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d : Set Shat → Set Shat → ℕ}
    (hθ₀ : 2 ≤ θ₀) (hd : HasTangleMetric Γ_hat θ₀ T d) {w : Shat} (hw : w ∈ Γ_hat.V) :
    ∃ (Γ₀ : Surface.Drawing Shat)
      (T₀ : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
      (d₀ : Set Shat → Set Shat → ℕ),
      Γ₀.IsSubdrawing Γ_hat ∧
      Γ₀.V = Γ_hat.V ∧
      GM12.deleteVertices Γ₀ {w} = GM12.deleteVertices Γ_hat {w} ∧
      (∀ e ∈ Γ_hat.E \ Γ₀.E, closure e ∩ Γ_hat.V ⊆ {w}) ∧
      HasTangleMetric Γ₀ θ₀ T₀ d₀ ∧
      (∀ a ∈ Γ_hat.A ∩ Γ₀.A, ∀ b ∈ Γ_hat.A ∩ Γ₀.A, d a b ≤ d₀ a b) ∧
      (∀ D F : Set Shat, IsClosedDisc D → IsOArc F → subBd D = F →
        (PaintingOrDrawing.drawing Γ₀).IsNormal F → F ∩ Γ₀.V = {w} →
        ((PaintingOrDrawing.drawing Γ₀).inter D,
          (PaintingOrDrawing.drawing Γ₀).interOutside D) ∈ T₀ →
        Γ₀.V ∩ D = {w} →
        ∀ e ∈ Γ₀.E, ¬ e ⊆ D) := by
  classical
  have hex : ∃ n : ℕ, ∃ (K : Surface.Drawing Shat)
      (U : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
      (δ : Set Shat → Set Shat → ℕ),
      K.IsSubdrawing Γ_hat ∧
      K.V = Γ_hat.V ∧
      GM12.deleteVertices K {w} = GM12.deleteVertices Γ_hat {w} ∧
      (∀ e ∈ Γ_hat.E \ K.E, closure e ∩ Γ_hat.V ⊆ {w}) ∧
      HasTangleMetric K θ₀ U δ ∧
      (∀ a ∈ Γ_hat.A ∩ K.A, ∀ b ∈ Γ_hat.A ∩ K.A, d a b ≤ δ a b) ∧
      K.E.ncard = n :=
    ⟨Γ_hat.E.ncard, Γ_hat, T, d, Surface.Drawing.IsSubdrawing.refl Γ_hat, rfl, rfl,
      fun _ h => (h.2 h.1).elim, hd, fun _ _ _ _ => le_rfl, rfl⟩
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hV₀, hdelete₀, hloops₀, hd₀, hcomp₀, hcount⟩ := Nat.find_spec hex
  refine ⟨Γ₀, T₀, d₀, hΓ₀, hV₀, hdelete₀, hloops₀, hd₀, hcomp₀, ?_⟩
  intro D F hD hF hbd hn hFV hm hVD e he heD
  obtain ⟨r, hr, hFr⟩ := GM12.exists_region_of_normal_circle_single_vertex hF hn hFV
  obtain ⟨_, _, d₁, _, hd₁, _, _, hcomp₁, _⟩ :=
    GM12.theorem_7_2_proof hcl hθ₀ hd₀ hD hbd hn hFV hr hFr hm
  let Γ₁ := Γ₀.interSet (closure (univ \ D))
  let T₁ := GM12.restrictTangle T₀ Γ₁.toHypergraph
  have hΓ₁ : Γ₁.IsSubdrawing Γ₀ := Surface.Drawing.span_isSubdrawing Γ₀ _ _
  have hfront : frontier D = F := (GM11.subBd_eq_frontier D).symm.trans hbd
  have hwF : w ∈ F := (hFV.symm ▸ mem_singleton w).1
  have hV₁ : Γ₁.V = Γ_hat.V := by
    apply Subset.antisymm (hΓ₁.1.trans hV₀.le)
    rw [← hV₀]
    intro x hx
    rw [GM11.mem_interSet_V_iff isClosed_closure]
    refine ⟨hx, ?_⟩
    by_cases hxw : x = w
    · subst hxw
      have hxFront : x ∈ frontier D := hfront.symm ▸ hwF
      rw [frontier_eq_closure_inter_closure] at hxFront
      simpa only [compl_eq_univ_sdiff] using hxFront.2
    · have hx_not_D : x ∉ D := fun hxD => hxw (by
        have : x ∈ ({w} : Set Shat) := by rw [← hVD]; exact ⟨hx, hxD⟩
        exact this)
      exact subset_closure ⟨mem_univ x, hx_not_D⟩
  have hdelete₁ : GM12.deleteVertices Γ₁ {w} = GM12.deleteVertices Γ_hat {w} :=
    (deleteVertices_interSet_compl_eq_of_V_inter_eq_singleton hD hbd hn hVD).trans hdelete₀
  have hloops₁ : ∀ f ∈ Γ_hat.E \ Γ₁.E, closure f ∩ Γ_hat.V ⊆ {w} := by
    intro f ⟨hf_hat, hf_not_₁⟩
    by_cases hf₀ : f ∈ Γ₀.E
    · have hf_not_out : ¬ f ⊆ closure (univ \ D) :=
        fun h => hf_not_₁ (GM11.mem_interSet_E_iff.mpr ⟨hf₀, h⟩)
      have hsep_D := (isSeparation_drawing_inter_interOutside Γ₀ hD hbd hn).1
      have hf_in_D : f ⊆ D := by
        have hf_union : f ∈ ((PaintingOrDrawing.drawing Γ₀).inter D).edgeSet ∪
            ((PaintingOrDrawing.drawing Γ₀).interOutside D).edgeSet :=
          hsep_D.edgeSet_union.symm ▸ hf₀
        rcases hf_union with ⟨_, hfD⟩ | ⟨_, hfOut⟩
        · exact hfD
        · exact (hf_not_out hfOut).elim
      have hcl_D : closure f ⊆ D := hD.isClosed.closure_subset_iff.mpr hf_in_D
      rw [← hV₀, ← hVD]
      exact fun x hx => ⟨hx.2, hcl_D hx.1⟩
    · exact hloops₀ f ⟨hf_hat, hf₀⟩
  have hcomp : ∀ a ∈ Γ_hat.A ∩ Γ₁.A, ∀ b ∈ Γ_hat.A ∩ Γ₁.A, d a b ≤ d₁ a b := by
    intro a ha b hb
    have ha₀ := GM12.shared_atom_mem_intermediate hΓ₀ hΓ₁ ha.1 ha.2
    have hb₀ := GM12.shared_atom_mem_intermediate hΓ₀ hΓ₁ hb.1 hb.2
    exact (hcomp₀ a ⟨ha.1, ha₀⟩ b ⟨hb.1, hb₀⟩).trans (hcomp₁ a ⟨ha₀, ha.2⟩ b ⟨hb₀, hb.2⟩)
  have hless : Γ₁.E.ncard < Γ₀.E.ncard := GM12.ncard_edges_outside_lt_of_edge_inside
    (fun x hx => hn ⟨hfront ▸ hx.1, hx.2⟩) he heD
  have hminimal : Nat.find hex ≤ Γ₁.E.ncard := Nat.find_min' hex
    ⟨Γ₁, T₁, d₁, hΓ₁.trans hΓ₀, hV₁, hdelete₁, hloops₁, hd₁, hcomp, rfl⟩
  rw [← hcount] at hminimal
  exact (Nat.not_le_of_lt hless) hminimal

/-- If `M` is a linkage in `B` whose terminals are contained in `{v}`, then `M.vertexSet ⊆ {v}`. -/
private lemma linkage_vertexSet_subset_singleton_of_terminals_subset_singleton {S : Type}
    {B M : Hypergraph S (Set S)} (hM : IsLinkage B M) {v : S}
    (hterm : terminals M ⊆ {v}) :
    M.vertexSet ⊆ {v} := by
  intro u hu
  let C := reachableComponent M u
  have hC : IsComponentOf M C := isComponentOf_reachableComponent hM.2.1 hu
  have huC : u ∈ C.vertexSet := self_mem_reachableComponent hu
  have hB_mem : terminals M ∩ C.vertexSet ∈ linkagePattern M := ⟨C, hC, rfl⟩
  rcases hM.mem_linkagePattern_structure hB_mem with
    ⟨a, ha, hBa, ha0⟩ | ⟨a, ha, b, hb, hab, _⟩
  · have ha0_C : (incidentEdges C a).ncard = 0 := by
      have haC : a ∈ C.vertexSet := by
        have : a ∈ terminals M ∩ C.vertexSet := by rw [hBa]; exact rfl
        exact this.2
      rwa [incidentEdges_component_eq hM.2.1 hC haC]
    have hemp : C.edgeSet = ∅ := by
      by_contra! hne
      have haC : a ∈ C.vertexSet := by
        have : a ∈ terminals M ∩ C.vertexSet := by rw [hBa]; exact rfl
        exact this.2
      have hge1 := isPathGraph_one_le_ncard_incidentEdges (hM.2.2 C hC) hne haC
      omega
    obtain ⟨a', _, hVC, htermC, _⟩ := isPathGraph_of_edgeSet_empty (hM.2.2 C hC) hemp
    have hua' : u = a' := by rwa [hVC, mem_singleton_iff] at huC
    subst hua'
    have ha'_term : u ∈ terminals M := by
      have : u ∈ terminals M ∩ C.vertexSet := by
        rw [hM.terminals_inter_component_eq hC, htermC]
        exact rfl
      exact this.1
    exact hterm ha'_term
  · exfalso
    have hav : a = v := hterm ha
    have hbv : b = v := hterm hb
    exact hab (hav.trans hbv.symm)

/-- **Claim (2)** in the proof of Graph Minors XXI, (5.1) (page 16 of the preprint):
"(2) *If $\Gamma \setminus v$ is not 2-cell in $\hat{\Sigma}$ then there is no vital linkage in
$\Gamma$ with set of terminals $V(\Gamma) \cap bd(\Sigma)$.*" -/
theorem claim_5_1_2 {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S}
    (hprop : Γ.IsProper) {θ' θ₀ : ℕ} (hθ' : 3 ≤ θ') (hθ₀ : θ' ≤ θ₀)
    {T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d : Set Shat → Set Shat → ℕ}
    (hd : HasTangleMetric (capDrawing hS cap Γ) θ₀ T d)
    {v : S} (hv : v ∈ Γ.V)
    (hv_dist : ∀ (C : Set S) (r : Set Shat),
      IsCuffRegion hS cap Γ C r → θ' ≤ d {cap.emb v} r)
    (hnot_twoCell :
      ¬ (PaintingOrDrawing.drawing (GM12.deleteVertices (capDrawing hS cap Γ) {cap.emb v})).IsTwoCell)
    {L : Hypergraph S (Set S)} (hL : IsVitalLinkage Γ.toHypergraph L) :
    terminals L ≠ Γ.V ∩ bd S := by
  intro hterm
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface Shat := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  let Γ_hat := capDrawing hS cap Γ
  have hv_hat : cap.emb v ∈ Γ_hat.V := mem_image_of_mem _ hv
  have hvA : ({cap.emb v} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨cap.emb v, hv_hat, rfl⟩)
  have hE_ne : Γ_hat.E.Nonempty :=
    GM12.edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 (by omega : 2 ≤ θ₀)
  obtain ⟨_, _, _, _, htri, hreg, _⟩ :=
    GM11.gm15_theorem_9_1 Γ_hat θ₀ T d hcl inferInstance hd
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hV₀, hdelete₀, hloops₀, hd₀, hcomp₀, hno_loop_disc⟩ :=
    exists_loop_free_vertex_reduction hcl (by omega : 2 ≤ θ₀) hd hv_hat
  have hv₀ : cap.emb v ∈ Γ₀.V := hV₀.symm ▸ hv_hat
  have hnot_twoCell₀ :
      ¬ (PaintingOrDrawing.drawing (GM12.deleteVertices Γ₀ {cap.emb v})).IsTwoCell := by
    rwa [hdelete₀]
  have hex_disc : ∃ (D F : Set Shat),
      IsClosedDisc D ∧ IsOArc F ∧ subBd D = F ∧
      (PaintingOrDrawing.drawing Γ₀).IsNormal F ∧ F ∩ Γ₀.V = {cap.emb v} ∧
      ((PaintingOrDrawing.drawing Γ₀).inter D,
        (PaintingOrDrawing.drawing Γ₀).interOutside D) ∈ T₀ ∧
      ∃ e ∈ Γ₀.E, e ⊆ D := by
    by_contra! hno
    exact hnot_twoCell₀ (GM12.isTwoCell_delete_vertex_of_no_selected_edge
      hcl (by omega : 2 ≤ θ₀) hd₀ hv₀ hno)
  obtain ⟨D, F, hD, hF, hbd, hn, hFV, hm, e, he, heD⟩ := hex_disc
  have hVD_ne : Γ₀.V ∩ D ≠ {cap.emb v} :=
    fun hVD => hno_loop_disc D F hD hF hbd hn hFV hm hVD e he heD
  have hv_in_D : cap.emb v ∈ D := by
    have hvF : cap.emb v ∈ F := (hFV.symm ▸ mem_singleton (cap.emb v)).1
    have hfront : frontier D = F := (GM11.subBd_eq_frontier D).symm.trans hbd
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl (hfront.symm ▸ hvF).1
  have hex_u : ∃ u ∈ Γ.V, u ≠ v ∧ cap.emb u ∈ D := by
    by_contra! hall
    apply hVD_ne
    apply Subset.antisymm
    · rintro x ⟨hxV₀, hxD⟩
      rw [hV₀] at hxV₀
      rcases hxV₀ with ⟨u, huV, rfl⟩
      by_cases huv : u = v
      · exact mem_singleton_iff.mpr (congrArg cap.emb huv)
      · exact (hall u huV huv hxD).elim
    · exact singleton_subset_iff.mpr ⟨hv₀, hv_in_D⟩
  obtain ⟨u, huV, huv, huD⟩ := hex_u
  have hbd_disj_D : ∀ w ∈ Γ.V ∩ bd S, cap.emb w ∉ D := by
    rintro w ⟨hwV, hw_bd⟩ hwD
    rw [← sUnion_cuffs] at hw_bd
    rcases hw_bd with ⟨C, hC, hwC⟩
    obtain ⟨r₁, hr₁_cuff, _, _, hC_clr, _⟩ := exists_unique_cuffRegion hS cap hprop hC
    have hr₁ : r₁ ∈ Γ_hat.R := hr₁_cuff.2.1
    have hr₁A : r₁ ∈ Γ_hat.A := Or.inr hr₁
    have hw_hat : cap.emb w ∈ Γ_hat.V := mem_image_of_mem _ hwV
    have hw₀ : cap.emb w ∈ Γ₀.V := hV₀.symm ▸ hw_hat
    have hwA : ({cap.emb w} : Set Shat) ∈ Γ_hat.A ∩ Γ₀.A :=
      ⟨Or.inl (Or.inl ⟨cap.emb w, hw_hat, rfl⟩), Or.inl (Or.inl ⟨cap.emb w, hw₀, rfl⟩)⟩
    have hvA₀ : ({cap.emb v} : Set Shat) ∈ Γ_hat.A ∩ Γ₀.A :=
      ⟨hvA, Or.inl (Or.inl ⟨cap.emb v, hv₀, rfl⟩)⟩
    have hd₀_vw : d₀ {cap.emb v} {cap.emb w} ≤ 1 := by
      have hle := GM12.dist_le_of_oarc_disc hcl hd₀ hF hn
        (by rw [hFV, ncard_singleton]; omega) hD hbd hm hvA₀.2 hwA.2
        ⟨cap.emb v, rfl, hv_in_D⟩ ⟨cap.emb w, rfl, hwD⟩
      rwa [hFV, ncard_singleton] at hle
    have hd_vw : d {cap.emb v} {cap.emb w} ≤ 1 :=
      (hcomp₀ {cap.emb v} hvA₀ {cap.emb w} hwA).trans hd₀_vw
    have hd_wr₁ : d {cap.emb w} r₁ ≤ 1 :=
      hreg hE_ne (cap.emb w) hw_hat r₁ hr₁ (hC_clr (mem_image_of_mem _ hwC))
    have hd_vr₁ : d {cap.emb v} r₁ ≤ 2 := by
      have hstep := htri {cap.emb v} hvA {cap.emb w} hwA.1 r₁ hr₁A
      omega
    have hge := hv_dist C r₁ hr₁_cuff
    omega
  -- Now pull back the separation `(interOutside D, inter D)` of `Γ₀.toHypergraph` to `G₀`.
  have hcont_emb : ContinuousOn cap.emb Γ.U := cap.isEmbedding.continuous.continuousOn
  have hinj_emb : InjOn cap.emb Γ.U := cap.isEmbedding.injective.injOn
  have hmap_eq : Γ_hat.toHypergraph = mapSubH cap.emb Γ.toHypergraph :=
    toHypergraph_mapDrawingInjOn Γ cap.emb hcont_emb hinj_emb
  have hΓ₀_le_map : Γ₀.toHypergraph ≤ mapSubH cap.emb Γ.toHypergraph :=
    hmap_eq ▸ isSubdrawing_toHypergraph_le hΓ₀
  let G₀ := comapSubH cap.emb Γ.toHypergraph Γ₀.toHypergraph
  have hG₀_le_Γ : G₀ ≤ Γ.toHypergraph := comapSubH_le_self' hΓ₀_le_map
  have hG₀_V : G₀.vertexSet = Γ.V := by
    ext x
    simp only [G₀, comapSubH, mem_ofPred_eq, Surface.Drawing.toHypergraph]
    refine ⟨fun h => h.1, fun hx => ⟨hx, ?_⟩⟩
    rw [hV₀]
    exact mem_image_of_mem _ hx
  have hL_E_sub : L.edgeSet ⊆ G₀.edgeSet := by
    intro f hfL
    have hfΓ : f ∈ Γ.E := hL.1.1.edgeSet_subset hfL
    refine ⟨hfΓ, ?_⟩
    change cap.emb '' f ∈ Γ₀.E
    by_contra hf_not_₀
    have hf_hat : cap.emb '' f ∈ Γ_hat.E := by
      rw [capDrawing_E]
      exact mem_image_of_mem _ hfΓ
    have hloop := hloops₀ (cap.emb '' f) ⟨hf_hat, hf_not_₀⟩
    have h2 : (L.ends f).ncard = 2 := hL.1.ends_ncard_eq_two hfL
    have hends_sub : L.ends f ⊆ {v} := by
      intro x hx
      have hx_Γ : x ∈ Γ.toHypergraph.ends f := by
        rw [hL.1.1.ends_eq f hfL]
        exact hx
      have hx_cl' : cap.emb x ∈ closure (cap.emb '' f) ∩ Γ_hat.V :=
        ⟨image_closure_subset_closure_image cap.isEmbedding.continuous
          (mem_image_of_mem _ hx_Γ.2.2), mem_image_of_mem _ hx_Γ.2.1⟩
      exact cap.isEmbedding.injective (hloop hx_cl')
    have hle1 : (L.ends f).ncard ≤ 1 :=
      (ncard_le_ncard hends_sub (finite_singleton v)).trans (by rw [ncard_singleton])
    omega
  have hL_le_G₀ : L ≤ G₀ :=
    ⟨by rw [hG₀_V]; exact hL.1.1.vertexSet_subset, hL_E_sub,
      fun f hf => (hG₀_le_Γ.ends_eq f (hL_E_sub hf)).symm.trans (hL.1.1.ends_eq f hf)⟩
  have hL_vital_G₀ : IsVitalLinkage G₀ L := by
    refine ⟨⟨hL_le_G₀, hL.1.2.1, hL.1.2.2⟩, hL.2.1.trans hG₀_V.symm, ?_⟩
    intro L' hL' hpat'
    exact hL.2.2 L' ⟨hL'.1.trans hG₀_le_Γ, hL'.2.1, hL'.2.2⟩ hpat'
  let A_0 := (PaintingOrDrawing.drawing Γ₀).interOutside D
  let B_0 := (PaintingOrDrawing.drawing Γ₀).inter D
  have hsep_0 : Γ₀.toHypergraph.IsSeparation A_0 B_0 :=
    (hd₀.1.2.1.isSeparation hm).symm
  let A := comapSubH cap.emb Γ.toHypergraph A_0
  let B := comapSubH cap.emb Γ.toHypergraph B_0
  have hA_le_G₀ : A ≤ G₀ :=
    ⟨fun x hx => ⟨hx.1, hsep_0.left_le.vertexSet_subset hx.2⟩,
      fun f hf => ⟨hf.1, hsep_0.left_le.edgeSet_subset hf.2⟩,
      fun f hf => (hG₀_le_Γ.ends_eq f ⟨hf.1, hsep_0.left_le.edgeSet_subset hf.2⟩).symm.trans
        ((comapSubH_le_self' (hsep_0.left_le.trans hΓ₀_le_map)).ends_eq f hf)⟩
  have hB_le_G₀ : B ≤ G₀ :=
    ⟨fun x hx => ⟨hx.1, hsep_0.right_le.vertexSet_subset hx.2⟩,
      fun f hf => ⟨hf.1, hsep_0.right_le.edgeSet_subset hf.2⟩,
      fun f hf => (hG₀_le_Γ.ends_eq f ⟨hf.1, hsep_0.right_le.edgeSet_subset hf.2⟩).symm.trans
        ((comapSubH_le_self' (hsep_0.right_le.trans hΓ₀_le_map)).ends_eq f hf)⟩
  have hsep_G₀ : G₀.IsSeparation A B := by
    rw [GM10.isSeparation_iff_of_le hA_le_G₀ hB_le_G₀]
    refine ⟨?_, ?_, ?_⟩
    · ext x
      simp only [A, B, G₀, comapSubH, mem_union, mem_ofPred_eq]
      constructor
      · rintro (h | h)
        · exact ⟨h.1, hsep_0.left_le.vertexSet_subset h.2⟩
        · exact ⟨h.1, hsep_0.right_le.vertexSet_subset h.2⟩
      · rintro ⟨hxΓ, hx₀⟩
        have hx_u : cap.emb x ∈ A_0.vertexSet ∪ B_0.vertexSet :=
          hsep_0.vertexSet_union.symm ▸ hx₀
        exact hx_u.imp (fun h => ⟨hxΓ, h⟩) (fun h => ⟨hxΓ, h⟩)
    · ext f
      simp only [A, B, G₀, comapSubH, mem_union, mem_ofPred_eq]
      constructor
      · rintro (h | h)
        · exact ⟨h.1, hsep_0.left_le.edgeSet_subset h.2⟩
        · exact ⟨h.1, hsep_0.right_le.edgeSet_subset h.2⟩
      · rintro ⟨hfΓ, hf₀⟩
        have hf_u : cap.emb '' f ∈ A_0.edgeSet ∪ B_0.edgeSet :=
          hsep_0.edgeSet_union.symm ▸ hf₀
        exact hf_u.imp (fun h => ⟨hfΓ, h⟩) (fun h => ⟨hfΓ, h⟩)
    · ext f
      simp only [A, B, comapSubH, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨_, hfA⟩, ⟨_, hfB⟩⟩
      exact hsep_0.notMem_edgeSet_right hfA hfB
  obtain ⟨hLB_link, hLB_term⟩ := GM21.theorem_2_2_proof hL_vital_G₀.1 hsep_G₀
  have hLB_vital : IsVitalLinkage B (L ∩ B) := (GM21.theorem_2_3_proof hL_vital_G₀.1 hsep_G₀).2 hL_vital_G₀
  have hterm_LB_sub : terminals (L ∩ B) ⊆ {v} := by
    refine hLB_term.trans (union_subset ?_ ?_)
    · rintro w ⟨hw_term, hw_not_A⟩
      rw [hterm] at hw_term
      exfalso
      apply hw_not_A
      refine ⟨hw_term.1, ?_⟩
      change cap.emb w ∈ Γ₀.V ∩ closure (univ \ D)
      exact ⟨hV₀.symm ▸ mem_image_of_mem _ hw_term.1,
        subset_closure ⟨mem_univ _, hbd_disj_D w hw_term⟩⟩
    · rintro w ⟨hwA, hwB⟩
      have hw_F : cap.emb w ∈ F ∩ Γ₀.V := by
        refine ⟨?_, hwB.2.1⟩
        rw [← hbd, GM11.subBd_eq_frontier, frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
        exact ⟨subset_closure hwB.2.2, hwA.2.2⟩
      rw [hFV, mem_singleton_iff] at hw_F
      exact mem_singleton_iff.mpr (cap.isEmbedding.injective hw_F)
  have hLB_V_sub : (L ∩ B).vertexSet ⊆ {v} :=
    linkage_vertexSet_subset_singleton_of_terminals_subset_singleton hLB_link hterm_LB_sub
  have hu_B : u ∈ B.vertexSet :=
    ⟨huV, show cap.emb u ∈ Γ₀.V from hV₀.symm ▸ mem_image_of_mem _ huV, huD⟩
  have hu_LB : u ∈ (L ∩ B).vertexSet := hLB_vital.2.1.symm ▸ hu_B
  exact huv (hLB_V_sub hu_LB)

/-! ## 4. Claim (3), Claim (4), Claim (5), and Proof of (5.1) -/

/-- **Claim (3)** in the proof of Graph Minors XXI, (5.1) (page 16 of the preprint):
Applying Graph Minors XII, (7.8) and (7.9) to `Γ' = deleteVertices Γ_hat {cap.emb v}` yields a
respectful tangle `T'` of order `θ₀ - 10` in `Γ'` with metric `d'` such that
`(A ∩ Γ', B ∩ Γ') ∈ T'` for every `(A, B) ∈ T` of order `< θ₀ - 10` and `d'(a', b') ≥ d(a, b) - 10`
for all `a, b ∈ Γ_hat.A` and `a', b' ∈ Γ'.A` with `a ⊆ a'` and `b ⊆ b'`. -/
theorem claim_5_1_3 {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S}
    {θ₀ : ℕ} (hθ₀ : 11 ≤ θ₀)
    {T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d : Set Shat → Set Shat → ℕ}
    (hd : HasTangleMetric (capDrawing hS cap Γ) θ₀ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo' :
      (PaintingOrDrawing.drawing (GM12.deleteVertices (capDrawing hS cap Γ) {cap.emb v})).IsTwoCell) :
    let Γ_hat := capDrawing hS cap Γ
    let Γ' := GM12.deleteVertices Γ_hat {cap.emb v}
    ∃ (T' : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
      (d' : Set Shat → Set Shat → ℕ),
      HasTangleMetric Γ' (θ₀ - 10) T' d' ∧
      (∀ A B : Hypergraph Shat (Set Shat),
        (A, B) ∈ T → separationOrder A B < θ₀ - 10 →
        (A ∩ Γ'.toHypergraph, B ∩ Γ'.toHypergraph) ∈ T') ∧
      (∀ a ∈ Γ_hat.A, ∀ b ∈ Γ_hat.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
        a ⊆ a' → b ⊆ b' → d a b - 10 ≤ d' a' b') := by
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface Shat := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  let Γ_hat := capDrawing hS cap Γ
  let Γ' := GM12.deleteVertices Γ_hat {cap.emb v}
  have hv_hat : cap.emb v ∈ Γ_hat.V := mem_image_of_mem _ hv
  have hvA : ({cap.emb v} : Set Shat) ∈ Γ_hat.A := Or.inl (Or.inl ⟨cap.emb v, hv_hat, rfl⟩)
  have hSub : Γ'.IsSubdrawing Γ_hat := GM12.deleteVertices_isSubdrawing Γ_hat {cap.emb v}
  obtain ⟨_, _, hle_ord, _, _, _, hedge⟩ :=
    GM11.gm15_theorem_9_1 Γ_hat θ₀ T d hcl inferInstance hd
  have hdist : ∀ e ∈ Γ_hat.E \ Γ'.E, d {cap.emb v} e ≤ 2 := by
    intro e ⟨he_hat, he_not_'⟩
    rw [GM12.deleteVertices_E, mem_ofPred_eq, not_and, not_disjoint_iff] at he_not_'
    obtain ⟨_, hve_cl, rfl⟩ := he_not_' he_hat
    exact hedge (cap.emb v) hv_hat e he_hat hve_cl.1
  obtain ⟨T'_raw, d'_raw, hd'_raw, hge_raw⟩ :=
    GM12.theorem_7_8_proof hcl (k := 2) (by omega : 2 * 2 + 2 ≤ θ₀)
      hd hvA hSub htwo' hdist (fun _ => le_rfl)
  let T' := GM10.truncation T'_raw (θ₀ - 10)
  let d' : Set Shat → Set Shat → ℕ := fun a' b' => min (d'_raw a' b') (θ₀ - 10)
  have hd' : HasTangleMetric Γ' (θ₀ - 10) T' d' :=
    HasTangleMetric.truncation hd'_raw (by omega : 1 ≤ θ₀ - 10) (by omega : θ₀ - 10 ≤ θ₀ - 2 * 2)
  have hge' : ∀ a ∈ Γ_hat.A, ∀ b ∈ Γ_hat.A, ∀ a' ∈ Γ'.A, ∀ b' ∈ Γ'.A,
      a ⊆ a' → b ⊆ b' → d a b - 10 ≤ d' a' b' := by
    intro a ha b hb a' ha' b' hb' haa' hbb'
    have h1 := hge_raw a ha b hb a' ha' b' hb' haa' hbb'
    have h2 := hle_ord a ha b hb
    change d a b - 10 ≤ min (d'_raw a' b') (θ₀ - 10)
    omega
  have hsep_mem' :=
    (GM12.theorem_7_9_proof hcl hd hSub htwo' (by omega : 10 < θ₀) hd' hge').1
  exact ⟨T', d', hd', hsep_mem', hge'⟩

/-- **Graph Minors XXI, (5.1)** (page 15 of the preprint):
"For every surface $\Sigma$ and integer $p \ge 0$, there exists $\theta > p$ with the following
property. Let $\Gamma$ be a drawing in $\Sigma$ with $|V(\Gamma) \cap bd(\Sigma)| = p$, and let
$\mathcal{T}$ be a respectful tangle in $\Gamma$ of order $\ge \theta$. Suppose that
(i) there is no $\Gamma$-normal $O$-arc $F \subseteq \Sigma$ such that
$|F \cap V(\Gamma)| < |C \cap V(\Gamma)|$ and $C \subseteq ins(F)$ for some cuff $C$ of $\Sigma$,
and
(ii) for every two cuffs $C_1, C_2$, the corresponding cuff regions $r_1, r_2$ satisfy
$d(r_1, r_2) \ge \theta$ where $d$ is the metric of $\mathcal{T}$.
Then there is no vital linkage in $\Gamma$ with set of terminals $V(\Gamma) \cap bd(\Sigma)$." -/
theorem theorem_5_1_proof {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧ ∀ (Γ : Surface.Drawing S), Γ.IsProper →
      (Γ.V ∩ bd S).ncard = p →
      ∀ (θ₀ : ℕ), θ ≤ θ₀ →
      ∀ (T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
        (d : Set Shat → Set Shat → ℕ),
      HasTangleMetric (capDrawing hS cap Γ) θ₀ T d →
      (∀ (F : Set S) (D : Set Shat) (C : Set S),
        (PaintingOrDrawing.drawing Γ).IsNormal F → IsOArc F →
        (F ∩ Γ.V).ncard < (C ∩ Γ.V).ncard → C ∈ cuffs S →
        IsClosedDisc D → subBd D = cap.emb '' F →
        ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
          (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T →
        ¬ cap.emb '' C ⊆ D) →
      (∀ (C₁ C₂ : Set S) (r₁ r₂ : Set Shat),
        C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
        θ ≤ d r₁ r₂) →
      ∀ (L : Hypergraph S (Set S)), IsVitalLinkage Γ.toHypergraph L →
        terminals L ≠ Γ.V ∩ bd S := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface Shat := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  classical
  let t := (cuffs S).ncard
  obtain ⟨θ₁, hθ₁_pos, h32⟩ := theorem_3_2_of_cuff_ins hcl t p
  let θ' := max θ₁ (p + 11)
  let θ := 2 * θ' + 1
  have hθ'_ge_θ₁ : θ₁ ≤ θ' := le_max_left _ _
  have hθ'_ge_p11 : p + 11 ≤ θ' := le_max_right _ _
  have hθ_def : θ = 2 * θ' + 1 := rfl
  refine ⟨θ, by omega, ?_⟩
  intro Γ hprop hp θ₀ hθ₀ T d hd hi hii L hL hterm
  -- Claim (1): find `v ∈ Γ.V` with `d({cap.emb v}, r) ≥ θ'` for every cuff region `r`.
  obtain ⟨v, hv, hv_dist⟩ :=
    claim_5_1_1 hS cap hprop (by omega : 2 ≤ θ') hθ₀ hd hii
  let Γ_hat := capDrawing hS cap Γ
  let Γ' := GM12.deleteVertices Γ_hat {cap.emb v}
  have hv_hat : cap.emb v ∈ Γ_hat.V := mem_image_of_mem _ hv
  have hSub : Γ'.IsSubdrawing Γ_hat := GM12.deleteVertices_isSubdrawing Γ_hat {cap.emb v}
  -- Claim (2): we may assume `Γ'` is 2-cell in `Shat`.
  by_cases htwo' : (PaintingOrDrawing.drawing Γ').IsTwoCell
  swap
  · exact claim_5_1_2 hS cap hprop (by omega : 3 ≤ θ') (by omega : θ' ≤ θ₀)
      hd hv hv_dist htwo' hL hterm
  -- Claim (3): apply XII (7.8) and (7.9) to `Γ'`.
  obtain ⟨T', d', hd', hsep_mem', hge'⟩ :=
    claim_5_1_3 hS cap (by omega : 11 ≤ θ₀) hd hv htwo'
  -- Also note `v ∉ bd S`, since `d({cap.emb v}, r) ≥ θ' ≥ 2` for every cuff region `r`.
  have hE_ne : Γ_hat.E.Nonempty :=
    GM12.edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 (by omega : 2 ≤ θ₀)
  obtain ⟨_, _, _, _, _, hreg_hat, _⟩ :=
    GM11.gm15_theorem_9_1 Γ_hat θ₀ T d hcl inferInstance hd
  have hv_not_bd : v ∉ bd S := by
    intro hv_bd
    rw [← sUnion_cuffs] at hv_bd
    rcases hv_bd with ⟨C, hC, hvC⟩
    obtain ⟨r₁, hr₁_cuff, _, _, hC_clr, _⟩ := exists_unique_cuffRegion hS cap hprop hC
    have hd_le1 := hreg_hat hE_ne (cap.emb v) hv_hat r₁ hr₁_cuff.2.1
      (hC_clr (mem_image_of_mem _ hvC))
    have hge := hv_dist C r₁ hr₁_cuff
    omega
  -- Set up cuff discs `Δ : Fin t → Set Shat` and pattern blocks `Zs : Fin n → Set Shat`.
  have : LocallyConnectedSpace Shat := IsClosedSurface.locallyConnectedSpace hcl
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have : Finite (cuffs S) := hcuffs_fin.to_subtype
  have hcard_cuffs : Nat.card (cuffs S) = t := Nat.card_coe_set_eq (cuffs S)
  let cuffEquiv' : Fin t ≃ cuffs S := (Finite.equivFinOfCardEq hcard_cuffs).symm
  let Δ : Fin t → Set Shat := fun i => closure (cap.cuffDisc (cuffEquiv' i).val)
  have hΔ_disc : ∀ i, IsClosedDisc (Δ i) :=
    fun i => cap.cuffDisc_closedDisc (cuffEquiv' i).val (cuffEquiv' i).property
  have hΔ_bd : ∀ i, discBd (Δ i) = cap.emb '' (cuffEquiv' i).val :=
    fun i => cap.cuffDisc_bd (cuffEquiv' i).val (cuffEquiv' i).property
  have hbd_eq_iUnion : bd S = ⋃ i : Fin t, (cuffEquiv' i).val := by
    rw [← sUnion_cuffs]
    ext x
    simp only [mem_sUnion, mem_iUnion]
    exact ⟨fun ⟨C, hC, hxC⟩ => ⟨cuffEquiv'.symm ⟨C, hC⟩, by simpa using hxC⟩,
      fun ⟨i, hxi⟩ => ⟨(cuffEquiv' i).val, (cuffEquiv' i).property, hxi⟩⟩
  have hv_not_Δ : ∀ i, cap.emb v ∉ Δ i := by
    intro i hvΔ
    have h_inter := capDrawing_inter_closure_cuffDisc hS cap hprop (cuffEquiv' i).property
    have hv_in : cap.emb v ∈ Γ_hat.U ∩ Δ i := ⟨Γ_hat.V_subset_U hv_hat, hvΔ⟩
    rw [h_inter, hΔ_bd i] at hv_in
    obtain ⟨w, hwC, hwv⟩ := hv_in.2
    have hw_eq : w = v := cap.isEmbedding.injective hwv
    subst hw_eq
    apply hv_not_bd
    rw [hbd_eq_iUnion]
    exact mem_iUnion.mpr ⟨i, hwC⟩
  have hΔ_avoid' : ∀ i, IsClosedDisc (Δ i) ∧ Γ'.U ∩ Δ i = Γ'.V ∩ discBd (Δ i) := by
    intro i
    refine ⟨hΔ_disc i, ?_⟩
    apply Subset.antisymm
    · intro x hx
      have hx_hat : x ∈ Γ_hat.U ∩ Δ i := ⟨hSub.U_subset hx.1, hx.2⟩
      rw [capDrawing_inter_closure_cuffDisc hS cap hprop (cuffEquiv' i).property] at hx_hat
      refine ⟨?_, hx_hat.2⟩
      rw [show Γ'.V = Γ_hat.V \ {cap.emb v} from GM12.deleteVertices_V Γ_hat {cap.emb v}]
      exact ⟨hx_hat.1, fun hxv => hv_not_Δ i (hxv ▸ hx.2)⟩
    · intro x hx
      exact ⟨Γ'.V_subset_U hx.1, Surface.discBd_subset (Δ i) hx.2⟩
  have hΔ_disj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)) := by
    intro i₁ i₂ hne
    exact cap.cuffDisc_disjoint (cuffEquiv' i₁).val (cuffEquiv' i₁).property
      (cuffEquiv' i₂).val (cuffEquiv' i₂).property
      (fun h => hne (cuffEquiv'.injective (Subtype.ext h)))
  have hZ_eq : discBoundaryVertices Γ' Δ = cap.emb '' (Γ.V ∩ bd S) := by
    unfold discBoundaryVertices
    rw [show Γ'.V = Γ_hat.V \ {cap.emb v} from GM12.deleteVertices_V Γ_hat {cap.emb v},
      show Γ_hat.V = cap.emb '' Γ.V from capDrawing_V hS cap Γ]
    ext z
    simp only [mem_iUnion, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_image]
    constructor
    · rintro ⟨i, ⟨⟨x, hxV, rfl⟩, _⟩, hz_bd⟩
      rw [hΔ_bd i] at hz_bd
      obtain ⟨y, hyC, hyx⟩ := hz_bd
      have hyx_eq : y = x := cap.isEmbedding.injective hyx
      subst hyx_eq
      refine ⟨y, ⟨hxV, ?_⟩, rfl⟩
      rw [hbd_eq_iUnion]
      exact mem_iUnion.mpr ⟨i, hyC⟩
    · rintro ⟨x, ⟨hxV, hx_bd⟩, rfl⟩
      rw [hbd_eq_iUnion, mem_iUnion] at hx_bd
      rcases hx_bd with ⟨i, hxC⟩
      have hxv : x ≠ v := fun h => hv_not_bd (h ▸ (by rw [hbd_eq_iUnion]; exact mem_iUnion.mpr ⟨i, hxC⟩))
      refine ⟨i, ⟨⟨x, hxV, rfl⟩, fun h => hxv (cap.isEmbedding.injective h)⟩,
        by rw [hΔ_bd i]; exact mem_image_of_mem _ hxC⟩
  have hZ_ncard : (discBoundaryVertices Γ' Δ).ncard ≤ p := by
    rw [hZ_eq, ncard_image_of_injective _ cap.isEmbedding.injective, hp]
  have hpat_fin : (linkagePattern L).Finite := by
    refine (Γ.finite_V.subset fun x (hx : x ∈ terminals L) => hL.1.1.vertexSet_subset hx.1).finite_subsets.subset ?_
    rintro B₀ ⟨C, _, rfl⟩
    exact inter_subset_left
  have : Finite (linkagePattern L) := hpat_fin.to_subtype
  let n := (linkagePattern L).ncard
  have hcard_pat : Nat.card (linkagePattern L) = n := Nat.card_coe_set_eq (linkagePattern L)
  let B : Fin n ≃ linkagePattern L := (Finite.equivFinOfCardEq hcard_pat).symm
  let Zs : Fin n → Set Shat := fun j => cap.emb '' (B j).val
  have hZs_cover : (⋃ j, Zs j) = discBoundaryVertices Γ' Δ := by
    rw [hZ_eq, ← hterm, hL.1.terminals_eq_sUnion_linkagePattern]
    ext z
    simp only [Zs, mem_iUnion, mem_image, mem_sUnion]
    constructor
    · rintro ⟨j, x, hxB, rfl⟩
      exact ⟨x, ⟨(B j).val, (B j).property, hxB⟩, rfl⟩
    · rintro ⟨x, ⟨B₀, hB₀, hxB₀⟩, rfl⟩
      exact ⟨B.symm ⟨B₀, hB₀⟩, x, by simpa using hxB₀, rfl⟩
  have hZs_disj : ∀ i j, i ≠ j → Disjoint (Zs i) (Zs j) := by
    intro i j hij
    have hdisj_B := hL.1.disjoint_of_mem_linkagePattern (B i).property (B j).property
      (fun h => hij (B.injective (Subtype.ext h)))
    exact Disjoint.image hdisj_B cap.isEmbedding.injective.injOn (subset_univ _) (subset_univ _)
  have hZs_feasible : IsTopologicallyFeasible Δ Zs :=
    isTopologicallyFeasible_of_linkage hS cap hprop hL.1 hterm cuffEquiv'
      (fun j => (B j).val) (fun j => (B j).property)
      (fun i j hij => hL.1.disjoint_of_mem_linkagePattern (B i).property (B j).property
        (fun h => hij (B.injective (Subtype.ext h))))
  -- Claim (5): cuff regions in `Γ'` of distinct cuffs have `d'`-distance `≥ θ₁`.
  have hsep_cuffs' : ∀ i j, i ≠ j → ∀ ri' ∈ Γ'.R, (ri' ∩ Δ i).Nonempty →
      ∀ rj' ∈ Γ'.R, (rj' ∩ Δ j).Nonempty → θ₁ ≤ d' ri' rj' := by
    intro i j hij ri' hri' hri'Δ rj' hrj' hrj'Δ
    obtain ⟨ri, hri_cuff, hdisc_i, _, _, _⟩ :=
      exists_unique_cuffRegion hS cap hprop (cuffEquiv' i).property
    obtain ⟨rj, hrj_cuff, hdisc_j, _, _, _⟩ :=
      exists_unique_cuffRegion hS cap hprop (cuffEquiv' j).property
    obtain ⟨ri'_u, hri'_u, hInt_i, _, huniq_i'⟩ :=
      GM12.exists_unique_region_meeting_disc hcl (hΔ_avoid' i).1 (hΔ_avoid' i).2
    obtain ⟨rj'_u, hrj'_u, hInt_j, _, huniq_j'⟩ :=
      GM12.exists_unique_region_meeting_disc hcl (hΔ_avoid' j).1 (hΔ_avoid' j).2
    have hri'_eq : ri' = ri'_u := huniq_i' ri' hri' hri'Δ
    have hrj'_eq : rj' = rj'_u := huniq_j' rj' hrj' hrj'Δ
    subst hri'_eq hrj'_eq
    obtain ⟨xi, hxi⟩ := (hΔ_avoid' i).1.nonempty_discInt
    obtain ⟨xj, hxj⟩ := (hΔ_avoid' j).1.nonempty_discInt
    have hri_sub : ri ⊆ ri' := by
      have hdis : Disjoint ri Γ'.U :=
        Disjoint.mono_right hSub.U_subset (disjoint_left.mpr fun x hxr hxU =>
          region_subset hri_cuff.2.1 hxr hxU)
      have hxi_ri : xi ∈ ri :=
        hdisc_i ((cap.cuffDisc_eq_discInt hS (cuffEquiv' i).property).symm ▸ hxi)
      exact subset_region hri' (region_isPreconnected hri_cuff.2.1) hdis hxi_ri (hInt_i hxi)
    have hrj_sub : rj ⊆ rj' := by
      have hdis : Disjoint rj Γ'.U :=
        Disjoint.mono_right hSub.U_subset (disjoint_left.mpr fun x hxr hxU =>
          region_subset hrj_cuff.2.1 hxr hxU)
      have hxj_rj : xj ∈ rj :=
        hdisc_j ((cap.cuffDisc_eq_discInt hS (cuffEquiv' j).property).symm ▸ hxj)
      exact subset_region hrj' (region_isPreconnected hrj_cuff.2.1) hdis hxj_rj (hInt_j hxj)
    have hCi_ne_Cj : (cuffEquiv' i).val ≠ (cuffEquiv' j).val :=
      fun h => hij (cuffEquiv'.injective (Subtype.ext h))
    have hd_ij : θ ≤ d ri rj := hii _ _ ri rj hCi_ne_Cj hri_cuff hrj_cuff
    have hge_ij := hge' ri (Or.inr hri_cuff.2.1) rj (Or.inr hrj_cuff.2.1)
      ri' (Or.inr hri') rj' (Or.inr hrj') hri_sub hrj_sub
    omega
  -- Claim (4): no `Γ'`-normal O-arc `F_hat` in `discComplement Δ` with `< |C ∩ V(Γ')|` vertices
  -- encloses `discBd (Δ i)` in `ins'(F_hat)`.
  have hno_ins' : ∀ (F_hat D : Set Shat) (i : Fin t),
      Γ'.IsNormal F_hat → IsOArc F_hat → F_hat ⊆ discComplement Δ →
      (Γ'.V ∩ F_hat).ncard < (Γ'.V ∩ discBd (Δ i)).ncard →
      IsClosedDisc D → subBd D = F_hat →
      ((PaintingOrDrawing.drawing Γ').inter D,
        (PaintingOrDrawing.drawing Γ').interOutside D) ∈ T' →
      ¬ discBd (Δ i) ⊆ D := by
    intro F_hat D i hnF' hF_hat hF_sub hlt hD hbdD hmD hbd_sub_D
    let C := (cuffEquiv' i).val
    have hC : C ∈ cuffs S := (cuffEquiv' i).property
    obtain ⟨r₁, hr₁_cuff, _, _, _, _⟩ := exists_unique_cuffRegion hS cap hprop hC
    have hr₁ : r₁ ∈ Γ_hat.R := hr₁_cuff.2.1
    obtain ⟨r₁', hr₁', hr₁_sub⟩ :=
      GM12.exists_atom_superset_of_isSubdrawing hSub (Or.inr hr₁)
    have hC_oarc : IsOArc C := (cuff_statement S hS).2.2 C hC
    obtain ⟨x₀, hx₀C, hx₀V⟩ := (infinite_of_isOArc hC_oarc).exists_notMem_finite Γ.finite_V
    have hx₀_r₁' : cap.emb x₀ ∈ r₁' ∩ D :=
      ⟨hr₁_sub (hr₁_cuff.2.2 ⟨x₀, ⟨hx₀C, hx₀V⟩, rfl⟩),
        hbd_sub_D (by rw [hΔ_bd i]; exact mem_image_of_mem _ hx₀C)⟩
    have hv_not_U' : cap.emb v ∉ Γ'.U := by
      intro hvU'
      have hvV' := (GM12.isSubdrawing_U_inter_V hSub).subset ⟨hvU', hv_hat⟩
      exact ((GM12.deleteVertices_V Γ_hat {cap.emb v}).subset hvV').2 rfl
    obtain ⟨r, hr, hvr⟩ := exists_region_of_notMem hv_not_U'
    have h_cuff_le_p : (Γ'.V ∩ discBd (Δ i)).ncard ≤ p := by
      have hsub_Z : Γ'.V ∩ discBd (Δ i) ⊆ discBoundaryVertices Γ' Δ :=
        subset_iUnion (fun i => Γ'.V ∩ discBd (Δ i)) i
      have hZ_sub_V : discBoundaryVertices Γ' Δ ⊆ Γ'.V :=
        iUnion_subset fun _ => inter_subset_left
      exact (ncard_le_ncard hsub_Z (Γ'.finite_V.subset hZ_sub_V)).trans hZ_ncard
    by_cases hFr : (F_hat ∩ r).Nonempty
    · obtain ⟨y₀, hy₀F, hy₀r⟩ := hFr
      have hy₀D : y₀ ∈ D := by
        have hfront : frontier D = F_hat := (GM11.subBd_eq_frontier D).symm.trans hbdD
        exact hD.isClosed.closure_subset_iff.mpr subset_rfl (hfront.symm ▸ hy₀F).1
      have hcard_F' : (F_hat ∩ Γ'.V).ncard < θ₀ - 10 := by
        rw [Set.inter_comm]
        omega
      have hd'_r_r₁' : d' r r₁' ≤ (F_hat ∩ Γ'.V).ncard :=
        GM12.dist_le_of_oarc_disc hcl hd' hF_hat hnF' hcard_F' hD hbdD hmD
          (Or.inr hr) hr₁' ⟨y₀, hy₀r, hy₀D⟩ ⟨cap.emb x₀, hx₀_r₁'⟩
      have hge_vr₁ := hge' {cap.emb v} (Or.inl (Or.inl ⟨cap.emb v, hv_hat, rfl⟩))
        r₁ (Or.inr hr₁) r (Or.inr hr) r₁' hr₁' (singleton_subset_iff.mpr hvr) hr₁_sub
      have hv_ge := hv_dist C r₁ hr₁_cuff
      rw [Set.inter_comm] at hd'_r_r₁'
      omega
    · rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hFr
      have hU_sub : Γ_hat.U ⊆ Γ'.U ∪ r :=
        GM12.drawing_subset_delete_union_vertex_region hv_hat hr hvr
      have hnF_hat : (PaintingOrDrawing.drawing Γ_hat).IsNormal F_hat := by
        rintro x ⟨hxF, hxU_hat⟩
        rcases hU_sub hxU_hat with hxU' | hxr
        · exact hSub.1 (hnF' ⟨hxF, hxU'⟩)
        · exact (disjoint_left.mp hFr hxF hxr).elim
      have hFV_eq : F_hat ∩ Γ_hat.V = F_hat ∩ Γ'.V := by
        ext x
        simp only [mem_inter_iff]
        rw [show Γ'.V = Γ_hat.V \ {cap.emb v} from GM12.deleteVertices_V Γ_hat {cap.emb v}]
        simp only [mem_sdiff, mem_singleton_iff]
        exact ⟨fun ⟨hxF, hxV⟩ => ⟨hxF, hxV, fun hxv => disjoint_left.mp hFr hxF (hxv ▸ hvr)⟩,
          fun ⟨hxF, hxV, _⟩ => ⟨hxF, hxV⟩⟩
      have hF_range : F_hat ⊆ range cap.emb := by
        have hcomp_sub : discComplement Δ ⊆ range cap.emb := by
          unfold discComplement
          refine (isCompact_range cap.isEmbedding.continuous).isClosed.closure_subset_iff.mpr ?_
          intro x hx
          by_contra hx_not_range
          have hx_compl : x ∈ (range cap.emb)ᶜ := hx_not_range
          rw [cap.compl_eq, mem_iUnion₂] at hx_compl
          rcases hx_compl with ⟨C₀, hC₀, hx_disc⟩
          exact hx (mem_iUnion.mpr ⟨cuffEquiv'.symm ⟨C₀, hC₀⟩,
            subset_closure (by simpa [cuffEquiv'] using hx_disc)⟩)
        exact hF_sub.trans hcomp_sub
      let F : Set S := cap.emb ⁻¹' F_hat
      have hF_img : cap.emb '' F = F_hat := image_preimage_eq_iff.mpr hF_range
      have hF_oarc : IsOArc F := by
        obtain ⟨φ⟩ := id hF_hat
        have hF_closed : IsClosed F :=
          (isCompact_of_isOArc hF_hat).isClosed.preimage cap.isEmbedding.continuous
        let e_emb : F ≃ₜ F_hat :=
          (closedSubsetHomeo F hF_closed cap.emb
            cap.isEmbedding.continuous.continuousOn cap.isEmbedding.injective.injOn).trans
            (Homeomorph.setCongr hF_img)
        exact ⟨φ.trans e_emb.symm⟩
      have hnF : (PaintingOrDrawing.drawing Γ).IsNormal F := by
        rintro x ⟨hxF, hxU⟩
        have hx_hat : cap.emb x ∈ F_hat ∩ Γ_hat.U := ⟨hxF, mem_image_of_mem _ hxU⟩
        obtain ⟨y, hyV, hyx⟩ := hnF_hat hx_hat
        exact cap.isEmbedding.injective hyx ▸ hyV
      have hF_lt_C : (F ∩ Γ.V).ncard < (C ∩ Γ.V).ncard := by
        have h1 : cap.emb '' (F ∩ Γ.V) = Γ'.V ∩ F_hat := by
          rw [Set.inter_comm Γ'.V, ← hFV_eq, image_inter cap.isEmbedding.injective, hF_img, capDrawing_V]
        have h2 : cap.emb '' (C ∩ Γ.V) = Γ'.V ∩ discBd (Δ i) := by
          rw [hΔ_bd i]
          have hv_not_C : cap.emb v ∉ cap.emb '' C := by
            rw [← hΔ_bd i]
            exact fun h => hv_not_Δ i (Surface.discBd_subset (Δ i) h)
          calc cap.emb '' (C ∩ Γ.V)
            _ = cap.emb '' Γ.V ∩ cap.emb '' C := by
                rw [Set.inter_comm C, image_inter cap.isEmbedding.injective]
            _ = (cap.emb '' Γ.V \ {cap.emb v}) ∩ cap.emb '' C := by
                ext z
                simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
                exact ⟨fun ⟨hV, hC'⟩ => ⟨⟨hV, fun hzv => hv_not_C (hzv ▸ hC')⟩, hC'⟩,
                  fun ⟨⟨hV, _⟩, hC'⟩ => ⟨hV, hC'⟩⟩
            _ = Γ'.V ∩ cap.emb '' C := by
                rw [show Γ'.V = Γ_hat.V \ {cap.emb v} from GM12.deleteVertices_V Γ_hat {cap.emb v},
                  show Γ_hat.V = cap.emb '' Γ.V from capDrawing_V hS cap Γ]
        rw [← ncard_image_of_injective (F ∩ Γ.V) cap.isEmbedding.injective,
          ← ncard_image_of_injective (C ∩ Γ.V) cap.isEmbedding.injective, h1, h2]
        exact hlt
      obtain ⟨hsep_D_hat, hord_D_hat⟩ :=
        isSeparation_drawing_inter_interOutside Γ_hat hD hbdD hnF_hat
      have hord_lt : separationOrder
          ((PaintingOrDrawing.drawing Γ_hat).inter D)
          ((PaintingOrDrawing.drawing Γ_hat).interOutside D) < θ₀ - 10 := by
        have h_eq_ncard : (F_hat ∩ Γ_hat.V).ncard = (Γ'.V ∩ F_hat).ncard := by
          rw [hFV_eq, Set.inter_comm]
        omega
      have hmD_hat : ((PaintingOrDrawing.drawing Γ_hat).inter D,
          (PaintingOrDrawing.drawing Γ_hat).interOutside D) ∈ T := by
        rcases hd.1.2.1.axiom1 hsep_D_hat (by omega : separationOrder _ _ < θ₀) with h_in | h_out
        · exact h_in
        · exfalso
          have hord_symm : separationOrder
              ((PaintingOrDrawing.drawing Γ_hat).interOutside D)
              ((PaintingOrDrawing.drawing Γ_hat).inter D) < θ₀ - 10 := by
            rwa [GM10.separationOrder_comm]
          have hmD'_out := hsep_mem' _ _ h_out hord_symm
          rw [GM12.drawing_inter_inter_subdrawing hSub D,
            GM12.drawing_interOutside_inter_subdrawing hSub D] at hmD'_out
          have hsep' := hd'.1.2.1.isSeparation hmD
          have hunion_eq :
              ((PaintingOrDrawing.drawing Γ').inter D) ∪
              ((PaintingOrDrawing.drawing Γ').interOutside D) ∪
              ((PaintingOrDrawing.drawing Γ').interOutside D) = Γ'.toHypergraph := by
            rw [GM10.union_assoc, GM10.union_self, hsep'.union_eq]
          exact hd'.1.2.1.axiom2 hmD hmD'_out hmD'_out hunion_eq
      exact hi F D C hnF hF_oarc hF_lt_C hC hD (hbdD.trans hF_img.symm) hmD_hat
        (by rwa [← hΔ_bd i])
  -- Apply `theorem_3_2_of_cuff_ins` to obtain connecting subdrawings in `Γ'`.
  have hconn : HasConnectingSubdrawings Γ' (discBoundaryVertices Γ' Δ) Zs :=
    h32 Δ Γ' (θ₀ - 10) T' d' n Zs hΔ_avoid' hΔ_disj hZ_ncard hZs_cover hZs_disj
      hZs_feasible (by omega : θ₁ ≤ θ₀ - 10) hd' hsep_cuffs' hno_ins'
  rw [hZ_eq] at hconn
  obtain ⟨L', hL'_link, hv_not_L', hpat_L'⟩ :=
    exists_linkage_avoiding_vertex_of_connectingSubdrawings hS cap hL.1 B hconn
  have hL'_eq_L : L' = L := hL.2.2 L' hL'_link hpat_L'
  subst hL'_eq_L
  exact hv_not_L' (hL.2.1.symm ▸ hv)

end GM21
end GraphMinor
