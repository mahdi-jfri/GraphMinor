module

public import GraphMinor.GM08.Section8Defs
public import GraphMinor.GM07.CylinderGrid
public import GraphMinor.GM11.OArcCircuit

/-!
# Graph Minors VIII, Section 8 (Part 1): Sleeve Uncrossing `(8.1)` and Boss Rings `(8.2)`

This file proves the first two numbered theorems of GM VIII Section 8 (page 268):

- **`theorem_8_1` (`(8.1)`):** Every centred `O`-arc `F` in a disc drawing `D` admits a `SleeveData`
  (an `(r, s)`-nest `(C₁, ..., C_s)` inside `F` and `r` mutually disjoint paths `P₁, ..., P_r`
  between `C₁` and `F` such that each `P_i ∩ C_j` is a path), and hence a sleeve `Γ'`
  (`exists_isSleeve`).
- **`theorem_8_2` (`(8.2)`):** Every `C`-ring of a boss `C` of `D` is centred.
-/

@[expose] public section

namespace GraphMinor
namespace GM08

open Set Function Topology Graph
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM07 GraphMinor.GM09.PlanarNests

universe u

section WalkDegreeHelpers

/-- Every edge of a simple walk links two distinct vertices in its support. -/
theorem exists_ne_link_of_mem_edges_simple {α β : Type*} {G : Graph α β} {a b : α}
    {W : GraphWalk G a b} (hW : W.IsSimple) {e : β} (he : e ∈ W.edges) :
    ∃ y z : α, G.IsLink e y z ∧ y ∈ W.support ∧ z ∈ W.support ∧ y ≠ z := by
  induction W with
  | nil _ => simp at he
  | @cons a c b e₀ hl rest ih =>
    have hnodup : (a :: rest.support).Nodup := hW
    obtain ⟨ha_not, hrest_s⟩ := List.nodup_cons.mp hnodup
    rcases List.mem_cons.mp he with rfl | he'
    · refine ⟨a, c, hl, List.mem_cons_self, List.mem_cons_of_mem _ rest.start_mem_support, ?_⟩
      intro hac
      exact ha_not (hac ▸ rest.start_mem_support)
    · obtain ⟨y, z, hlyz, hy, hz, hyz⟩ := ih hrest_s he'
      exact ⟨y, z, hlyz, List.mem_cons_of_mem _ hy, List.mem_cons_of_mem _ hz, hyz⟩

/-- Every vertex `w` of a circuit subdrawing `B` of `Γ` is either incident to a loop of `B` or
lies in the closures of two distinct edges of `B`. -/
theorem exists_loop_or_two_edges_of_isCircuit {T : Type*} [TopologicalSpace T]
    {Γ B : Drawing T} (hBΓ : B.IsSubdrawing Γ) (hBc : B.IsCircuit) {w : T} (hw : w ∈ B.V) :
    (∃ e ∈ B.E, Γ.toGraph.IsLink e w w) ∨
      ∃ e₁ ∈ B.E, ∃ e₂ ∈ B.E, e₁ ≠ e₂ ∧ w ∈ closure e₁ ∧ w ∈ closure e₂ := by
  obtain ⟨u, W, hWsc, hWpos, hBV, hBE⟩ := hBc
  have hw_sup : w ∈ W.support := by
    have : w ∈ {x | x ∈ W.support} := hBV ▸ hw
    exact this
  have hlinkΓ : ∀ {e x y}, B.toGraph.IsLink e x y → Γ.toGraph.IsLink e x y := fun hl =>
    (hBΓ.isLink_iff hl.1).mp hl
  have hmem_cl : ∀ {e x y}, B.toGraph.IsLink e x y → x ∈ closure e ∧ y ∈ closure e :=
      fun {e x y} hl => by
    have hx : x ∈ closure e ∩ B.V := by rw [hl.2.2.2]; simp
    have hy : y ∈ closure e ∩ B.V := by rw [hl.2.2.2]; simp
    exact ⟨hx.1, hy.1⟩
  by_cases hwu : w = u
  · subst hwu
    cases W with
    | nil _ => simp at hWpos
    | @cons w y _ e₁ hl₁ rest =>
      by_cases hr0 : 0 < rest.length
      · obtain ⟨z, e₂, R₀, hl₂, rfl⟩ := GM07.exists_snoc rest hr0
        have he_nd : (e₁ :: (R₀.edges ++ [e₂])).Nodup := by
          simpa [GraphWalk.edges_append] using hWsc.2
        have he₁₂ : e₁ ≠ e₂ := fun h =>
          (List.nodup_cons.mp he_nd).1 (h ▸ List.mem_append_right _ (by simp))
        have he₁B : e₁ ∈ B.E := by rw [hBE]; simp
        have he₂B : e₂ ∈ B.E := by
          rw [hBE]
          exact List.mem_cons_of_mem _ (by simp [GraphWalk.edges_append])
        exact Or.inr ⟨e₁, he₁B, e₂, he₂B, he₁₂, (hmem_cl hl₁).1, (hmem_cl hl₂).2⟩
      · cases rest with
        | nil _ =>
          have he₁B : e₁ ∈ B.E := by rw [hBE]; simp
          exact Or.inl ⟨e₁, he₁B, hlinkΓ hl₁⟩
        | cons _ _ => simp at hr0
  · obtain ⟨W₁, W₂, rfl⟩ := GraphWalk.exists_append_of_mem W hw_sup
    have hlen₁ : 0 < W₁.length := by
      by_contra h0
      exact hwu (GraphWalk.eq_of_length_eq_zero (W := W₁) (by omega)).symm
    obtain ⟨y₁, e₁, R₁, hl₁, rfl⟩ := GM07.exists_snoc W₁ hlen₁
    obtain ⟨y₂, e₂, hl₂, R₂, rfl⟩ := GM07.exists_cons_of_ne W₂ hwu
    have he_nd : ((R₁.edges ++ [e₁]) ++ (e₂ :: R₂.edges)).Nodup := by
      simpa [GraphWalk.edges_append] using hWsc.2
    have he₁₂ : e₁ ≠ e₂ := fun h =>
      (List.nodup_append.mp he_nd).2.2 e₁ (by simp) e₂ (by simp) h
    have he₁B : e₁ ∈ B.E := by
      rw [hBE]
      simp [GraphWalk.edges_append]
    have he₂B : e₂ ∈ B.E := by
      rw [hBE]
      simp [GraphWalk.edges_append]
    exact Or.inr ⟨e₁, he₁B, e₂, he₂B, he₁₂, (hmem_cl hl₁).2, (hmem_cl hl₂).1⟩

/-- Every internal vertex `w` of a simple walk `W` from `a` to `b` (`w ≠ a`, `w ≠ b`) lies in the
closures of two distinct edges of `W`. -/
theorem exists_two_edges_of_internal_mem_simple {T : Type*} [TopologicalSpace T]
    {P : Drawing T} {a b : T} {W : GraphWalk P.toGraph a b} (hW : W.IsSimple)
    {w : T} (hw : w ∈ W.support) (hwa : w ≠ a) (hwb : w ≠ b) :
    ∃ e₁ ∈ W.edges, ∃ e₂ ∈ W.edges, e₁ ≠ e₂ ∧ w ∈ closure e₁ ∧ w ∈ closure e₂ := by
  obtain ⟨W₁, W₂, rfl⟩ := GraphWalk.exists_append_of_mem W hw
  have hlen₁ : 0 < W₁.length := by
    by_contra h0
    exact hwa (GraphWalk.eq_of_length_eq_zero (W := W₁) (by omega)).symm
  obtain ⟨y₁, e₁, R₁, hl₁, rfl⟩ := GM07.exists_snoc W₁ hlen₁
  obtain ⟨y₂, e₂, hl₂, R₂, rfl⟩ := GM07.exists_cons_of_ne W₂ hwb
  have hmem_cl : ∀ {e x y}, P.toGraph.IsLink e x y → x ∈ closure e ∧ y ∈ closure e :=
      fun {e x y} hl => by
    have hx : x ∈ closure e ∩ P.V := by rw [hl.2.2.2]; simp
    have hy : y ∈ closure e ∩ P.V := by rw [hl.2.2.2]; simp
    exact ⟨hx.1, hy.1⟩
  have hsup_eq : (R₁.append (.cons hl₁ (.nil hl₁.right_mem)) |>.append (.cons hl₂ R₂)).support =
      R₁.support ++ (w :: R₂.support) := by
    simp [GraphWalk.support_append]
  have hnd : (R₁.support ++ (w :: R₂.support)).Nodup := by
    unfold GraphWalk.IsSimple at hW
    rwa [hsup_eq] at hW
  obtain ⟨_, hnd₂, hdisj⟩ := List.nodup_append.mp hnd
  have hw_not_R₁ : w ∉ R₁.support := fun hm => hdisj w hm w List.mem_cons_self rfl
  have hy₁_ne_w : y₁ ≠ w := fun h => hw_not_R₁ (h ▸ R₁.end_mem_support)
  have hy₁_ne_y₂ : y₁ ≠ y₂ := fun h =>
    hdisj y₁ R₁.end_mem_support y₂ (List.mem_cons_of_mem _ R₂.start_mem_support) h
  have he₁₂ : e₁ ≠ e₂ := by
    intro heq
    subst heq
    have heq_set : ({y₁, w} : Set T) = {w, y₂} := hl₁.2.2.2.symm.trans hl₂.2.2.2
    have hy₁_mem : y₁ ∈ ({w, y₂} : Set T) := heq_set ▸ Or.inl rfl
    rcases hy₁_mem with rfl | h'
    · exact hy₁_ne_w rfl
    · exact hy₁_ne_y₂ h'
  exact ⟨e₁, by simp [GraphWalk.edges_append], e₂, by simp [GraphWalk.edges_append],
    he₁₂, (hmem_cl hl₁).2, (hmem_cl hl₂).1⟩

/-- Every path subdrawing has a preconnected point set `U`. -/
theorem isPreconnected_U_of_isPathBetween {T : Type*} [TopologicalSpace T] [T2Space T]
    {P : Drawing T} {a b : T} (hp : P.IsPathBetween a b) : IsPreconnected P.U := by
  by_cases hab : a = b
  · subst hab
    obtain ⟨W, hWs, hPV, hPE⟩ := hp
    cases W with
    | nil _ =>
      have hPU : P.U = {a} := by
        rw [P.U_eq]
        have hV1 : P.V = {a} := by simpa using hPV
        have hE0 : P.E = ∅ := by simpa using hPE
        simp [hV1, hE0]
      rw [hPU]
      exact isPreconnected_singleton
    | @cons a c _ e hl rest =>
      exfalso
      exact (List.nodup_cons.mp hWs).1 rest.end_mem_support
  · exact (GM07.isConnected_line (GM11.isLine_of_isPathBetween hp hab)).isPreconnected

/-- Two subdrawings of `Γ` with disjoint vertex sets have disjoint point sets `U`. -/
theorem disjoint_U_of_disjoint_V_subdrawing {T : Type*} [TopologicalSpace T]
    {Γ A B : Drawing T} (hA : A.IsSubdrawing Γ) (hB : B.IsSubdrawing Γ) (hdV : Disjoint A.V B.V) :
    Disjoint A.U B.U := by
  have hdE : Disjoint A.E B.E := by
    refine Set.disjoint_left.mpr fun e heA heB => ?_
    obtain ⟨y, _, hl⟩ := (A.toGraph.edge_mem_iff_exists_isLink e).mp heA
    have hyA : y ∈ A.V := hl.2.1
    have hy_cl : y ∈ closure e ∩ Γ.V := ⟨by
      have : y ∈ closure e ∩ A.V := by rw [hl.2.2.2]; simp
      exact this.1, hA.1 hyA⟩
    have hyB : y ∈ closure e ∩ B.V := by rwa [hB.closure_inter_V heB]
    exact Set.disjoint_left.mp hdV hyA hyB.2
  refine Set.disjoint_left.mpr fun x hxA hxB => ?_
  by_cases hxV : x ∈ Γ.V
  · have hxAV : x ∈ A.V := by
      by_contra hnot
      obtain ⟨e, heA, hxe⟩ := A.exists_edge_of_mem hxA hnot
      exact ((hA.2 heA).2.1 hxe).2 hxV
    have hxBV : x ∈ B.V := by
      by_contra hnot
      obtain ⟨e, heB, hxe⟩ := B.exists_edge_of_mem hxB hnot
      exact ((hB.2 heB).2.1 hxe).2 hxV
    exact Set.disjoint_left.mp hdV hxAV hxBV
  · obtain ⟨e₁, he₁, hxe₁⟩ := A.exists_edge_of_mem hxA fun h => hxV (hA.1 h)
    obtain ⟨e₂, he₂, hxe₂⟩ := B.exists_edge_of_mem hxB fun h => hxV (hB.1 h)
    have heq : e₁ = e₂ := Γ.edge_eq_of_mem (hA.2 he₁) (hB.2 he₂) hxe₁ hxe₂
    exact Set.disjoint_left.mp hdE he₁ (heq ▸ he₂)

end WalkDegreeHelpers

/-!
## 1. Proof of `(8.1)` on `SphereSurf` and Pullback to General Surfaces
-/

section Theorem81

/-- Sphere-model core of **(8.1)**: every centred `O`-arc `F'` in a disc `Δ'` on `SphereSurf`
(with `OnePoint.infty ∉ Δ'`) admits a `SleeveData`. -/
theorem theorem_8_1_sphere {D' : Drawing SphereSurf} {Δ' F' : Set SphereSurf}
    (hΔ' : IsClosedDisc Δ') (hD'U : D'.U ⊆ Δ') (hinf_Δ : (OnePoint.infty : SphereSurf) ∉ Δ')
    (hc' : IsCentredOArc D' Δ' F') :
    Nonempty (SleeveData D' Δ' F') := by
  classical
  let r := (D'.V ∩ F').ncard
  let s := (r + 1) / 2
  obtain ⟨hF'Δ, hF'o, hF'norm, N₀, hN₀_in, P_init, hP_init, hP_init_dis⟩ := hc'
  rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
  · have hs0 : s = 0 := by omega
    refine ⟨{
      nest := N₀
      circuitDraw := fun j => (Nat.not_lt_zero j.1 (hs0 ▸ j.2)).elim
      isCircuit_draw := fun j => (Nat.not_lt_zero j.1 (hs0 ▸ j.2)).elim
      circuit_inside := hN₀_in
      spoke := fun i => (Nat.not_lt_zero i.1 (hr0 ▸ i.2)).elim
      isPath_spoke := fun i => (Nat.not_lt_zero i.1 (hr0 ▸ i.2)).elim
      pairwise_disjoint_spokes := fun i _ _ => (Nat.not_lt_zero i.1 (hr0 ▸ i.2)).elim
      inter_isPath := fun i _ => (Nat.not_lt_zero i.1 (hr0 ▸ i.2)).elim
    }⟩
  · have hs : 0 < s := by omega
    have hS : IsClosedSurface SphereSurf :=
      (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
    have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
    have : ConnectedSpace SphereSurf :=
      (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).2
    have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
    -- Step 1: Inside disc `D_F` of `F'` in `Δ'` and complementary disc `D₂ = closure (univ \ D_F)`.
    obtain ⟨D_F, hD_F, _⟩ := disc_oArc Δ' F' hΔ' hF'Δ hF'o
    have hDF_disc : IsClosedDisc D_F := hD_F.2.1
    have hDF_bd : discBd D_F = F' := hD_F.2.2.1
    have hinf_not_DF : (OnePoint.infty : SphereSurf) ∉ D_F := fun h => hinf_Δ (hD_F.1 h)
    obtain ⟨hD₂, hbd_D₂₀⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hDF_disc
    set D₂ := closure (univ \ D_F) with hD₂_def
    have hbd_D₂ : discBd D₂ = F' := hbd_D₂₀.trans hDF_bd
    have hoff_DF : ∀ {x : SphereSurf}, x ∉ D_F → x ∈ D₂ :=
      fun hx => subset_closure ⟨mem_univ _, hx⟩
    have hnot_D₂_of_int : ∀ {x : SphereSurf}, x ∈ discInt D_F → x ∉ D₂ := by
      intro x hx hmem
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp hmem _ (hDF_disc.isOpen_discInt hman) hx
      exact hy2.2 hy1.1
    have hD₂_iff : ∀ {x : SphereSurf}, x ∈ D₂ ↔ x ∉ discInt D_F := by
      intro x
      refine ⟨fun hx hint => hnot_D₂_of_int hint hx, fun hnot => ?_⟩
      by_cases hxDF : x ∈ D_F
      · have hxF : x ∈ F' := by
          rw [← hDF_bd]
          exact by_contra fun hnb => hnot ⟨hxDF, hnb⟩
        exact Surface.discBd_subset D₂ (hbd_D₂.symm ▸ hxF)
      · exact hoff_DF hxDF
    have hint_D₂_iff : ∀ {x : SphereSurf}, x ∈ discInt D₂ ↔ x ∉ D_F := by
      intro x
      constructor
      · rintro ⟨hxD₂, hnb⟩ hxDF
        have hxnot : x ∉ discInt D_F := hD₂_iff.mp hxD₂
        exact hnb (hbd_D₂ ▸ hDF_bd ▸ by_contra fun h => hxnot ⟨hxDF, h⟩)
      · intro hxnot
        refine ⟨hoff_DF hxnot, fun hbd => hxnot (Surface.discBd_subset D_F ?_)⟩
        rwa [hDF_bd, ← hbd_D₂]
    -- Step 2: Realize the initial nest circuits `N_draw` and their inside discs `Dn`.
    have hex_N : ∀ j : Fin s, ∃ C : Drawing SphereSurf,
        C.IsCircuit ∧ C.IsSubdrawing D' ∧ C.U = (N₀.circuit j).U := fun j =>
      GM11.exists_circuit_of_oArc (N₀.circuit j).isOArc_U (N₀.circuit j).U_sub_drawing
    choose N_draw hN_circ hN_sub hN_U using hex_N
    let Dn : Fin s → Set SphereSurf := fun j => (N₀.circuit j).ins
    have hDn_disc : ∀ j, IsClosedDisc (Dn j) := fun j => (N₀.circuit j).isInside.2.1
    have hDn_bd : ∀ j, discBd (Dn j) = (N_draw j).U :=
      fun j => (N₀.circuit j).isInside.2.2.1.trans (hN_U j).symm
    have hN_in_DF : ∀ j, (N_draw j).U ⊆ discInt D_F := fun j x hx =>
      (insideOArc_iff_mem_discInt hΔ' hD_F).mp (hN₀_in j x ((hN_U j) ▸ hx))
    have hDn_in_DF : ∀ j, Dn j ⊆ discInt D_F := by
      intro j
      have hdis_bd : Disjoint (discInt D₂) (discBd (Dn j)) := by
        rw [hDn_bd j]
        exact Set.disjoint_left.mpr fun y hyD₂ hyN =>
          (hint_D₂_iff.mp hyD₂) (hN_in_DF j hyN).1
      have hinf_D₂ : (OnePoint.infty : SphereSurf) ∈ discInt D₂ :=
        hint_D₂_iff.mpr hinf_not_DF
      have hinf_not_Dn : (OnePoint.infty : SphereSurf) ∉ Dn j :=
        fun h => hinf_Δ ((N₀.circuit j).isInside.1 h)
      have hsub_DF : Dn j ⊆ D_F := by
        intro z hz
        by_contra hznot
        rcases (hDn_disc j).side hman hD₂.isPreconnected_discInt hdis_bd with hin | hout
        · exact hinf_not_Dn (discInt_subset _ (hin hinf_D₂))
        · exact Set.disjoint_left.mp hout (hint_D₂_iff.mpr hznot) hz
      intro x hx
      by_cases hbd : x ∈ discBd (Dn j)
      · exact hN_in_DF j (hDn_bd j ▸ hbd)
      · refine ⟨hsub_DF hx, fun hxF => ?_⟩
        have hx_front : x ∈ frontier D_F := by
          rwa [IsClosedDisc.frontier_eq_discBd hS hDF_disc]
        exact hx_front.2 (mem_interior.mpr ⟨discInt (Dn j), (discInt_subset _).trans hsub_DF,
          (hDn_disc j).isOpen_discInt hman, ⟨hx, hbd⟩⟩)
    have hDn_strict : ∀ j j' : Fin s, j < j' → Dn j ⊆ discInt (Dn j') := by
      intro j j' hjj'
      have hbd_in : (N_draw j).U ⊆ discInt (Dn j') := fun x hx =>
        (insideOArc_iff_mem_discInt hΔ' (N₀.circuit j').isInside).mp
          (N₀.inside_of_lt hjj' x ((hN_U j) ▸ hx))
      obtain ⟨D_out, hDout_bd⟩ :=
        GM12.isClosedDisc_closure_compl_of_sphere hS hsph (hDn_disc j')
      set E_out := closure (univ \ Dn j')
      have hinf_not_j' : (OnePoint.infty : SphereSurf) ∉ Dn j' :=
        fun h => hinf_Δ ((N₀.circuit j').isInside.1 h)
      have hinf_not_j : (OnePoint.infty : SphereSurf) ∉ Dn j :=
        fun h => hinf_Δ ((N₀.circuit j).isInside.1 h)
      have hinf_int_out : (OnePoint.infty : SphereSurf) ∈ discInt E_out := by
        refine ⟨subset_closure ⟨mem_univ _, hinf_not_j'⟩, fun hbd => ?_⟩
        rw [hDout_bd] at hbd
        exact hinf_not_j' (Surface.discBd_subset _ hbd)
      have hdis_bd : Disjoint (discInt E_out) (discBd (Dn j)) := by
        rw [hDn_bd j]
        refine Set.disjoint_left.mpr fun y hy_out hyN => ?_
        obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy_out.1 _
          ((hDn_disc j').isOpen_discInt hman) (hbd_in hyN)
        exact hz2.2 hz1.1
      have hsub_j' : Dn j ⊆ Dn j' := by
        intro z hz
        by_contra hznot
        have hz_out : z ∈ discInt E_out := by
          refine ⟨subset_closure ⟨mem_univ _, hznot⟩, fun hbd => ?_⟩
          rw [hDout_bd] at hbd
          exact hznot (Surface.discBd_subset _ hbd)
        rcases (hDn_disc j).side hman D_out.isPreconnected_discInt hdis_bd with hin | hout
        · exact hinf_not_j (discInt_subset _ (hin hinf_int_out))
        · exact Set.disjoint_left.mp hout hz_out hz
      intro z hz
      by_cases hbd : z ∈ discBd (Dn j)
      · exact hbd_in (hDn_bd j ▸ hbd)
      · refine ⟨hsub_j' hz, fun hbd' => ?_⟩
        have hz_front : z ∈ frontier (Dn j') := by
          rwa [IsClosedDisc.frontier_eq_discBd hS (hDn_disc j')]
        exact hz_front.2 (mem_interior.mpr ⟨discInt (Dn j), (discInt_subset _).trans hsub_j',
          (hDn_disc j).isOpen_discInt hman, ⟨hz, hbd⟩⟩)
    let D₁ := Dn ⟨0, hs⟩
    have hD₁ : IsClosedDisc D₁ := hDn_disc ⟨0, hs⟩
    have hbd_D₁ : discBd D₁ = (N_draw ⟨0, hs⟩).U := hDn_bd ⟨0, hs⟩
    have hd₁₂ : Disjoint D₁ D₂ :=
      Set.disjoint_left.mpr fun x hx₁ hx₂ => (hD₂_iff.mp hx₂) (hDn_in_DF ⟨0, hs⟩ hx₁)
    -- Step 3: Trim each `P_init i` between `D₁` (last hit) and `D₂` (first hit).
    have hex_P₀ : ∀ i : Fin r, ∃ (P₀ : Drawing SphereSurf) (u₀ v₀ w_prev : SphereSurf)
        (e_last : Set SphereSurf),
        P₀.IsSubdrawing (P_init i) ∧ P₀.IsSubdrawing D' ∧
        u₀ ∈ discBd D₁ ∧ v₀ ∈ F' ∧ P₀.IsPathBetween u₀ v₀ ∧
        P₀.V ∩ D₁ = {u₀} ∧ P₀.V ∩ D₂ = {v₀} ∧ P₀.V ∩ F' = {v₀} ∧
        Disjoint P₀.U (discInt D₁) ∧ Disjoint P₀.U (discInt D₂) ∧ P₀.U ⊆ D_F ∧
        e_last ∈ P₀.E ∧ D'.toGraph.IsLink e_last w_prev v₀ ∧ w_prev ≠ v₀ ∧
        (∀ e ∈ P₀.E, v₀ ∈ closure e → e = e_last) := by
      intro i
      obtain ⟨_, u_in, v_in, hPi_sub, hu_in, hv_in, W_in, hWin_s, _, _⟩ := hP_init i
      have hu_D₁ : u_in ∈ D₁ :=
        Surface.discBd_subset D₁ ((N₀.circuit ⟨0, hs⟩).isInside.2.2.1.symm ▸ hu_in)
      have hv_D₂ : v_in ∈ D₂ := Surface.discBd_subset D₂ (hbd_D₂.symm ▸ hv_in)
      obtain ⟨u₀, hu₀_D₁, _, R_i, hWeq, hu₀_only⟩ :=
        GM07.exists_last_hit_split W_in ⟨u_in, W_in.start_mem_support, hu_D₁⟩
      subst hWeq
      obtain ⟨_, hRi_s⟩ := GM09.isSimple_of_append hWin_s
      obtain ⟨v₀, hv₀_D₂, M_i, _, hReq, hv₀_only⟩ :=
        GM09.PlanarNests.exists_first_hit_split R_i ⟨v_in, R_i.end_mem_support, hv_D₂⟩
      subst hReq
      obtain ⟨hMi_s, _⟩ := GM09.isSimple_of_append hRi_s
      have hu₀_Mi : ∀ z ∈ M_i.support, z ∈ D₁ → z = u₀ := fun z hz hD =>
        hu₀_only z ((GraphWalk.mem_support_append _ _).mpr (Or.inl hz)) hD
      let P₀ := GM11.walkDrawing (P_init i) M_i
      have hP₀_Pi : P₀.IsSubdrawing (P_init i) := GM11.walkDrawing_isSubdrawing _ _
      have hP₀_D' : P₀.IsSubdrawing D' := hP₀_Pi.trans hPi_sub
      have hP₀_path : P₀.IsPathBetween u₀ v₀ := GM11.walkDrawing_isPathBetween _ hMi_s
      have hP₀V_eq : P₀.V = {z | z ∈ M_i.support} := GM11.walkDrawing_V _ _
      have hP₀E_eq : P₀.E = {e | e ∈ M_i.edges} := GM11.walkDrawing_E _ _
      -- Every edge of `P₀` is disjoint from both `D₁` and `D₂`.
      have hedge_disj : ∀ e ∈ P₀.E, Disjoint e D₁ ∧ Disjoint e D₂ := by
        intro e heP₀
        have heMi : e ∈ M_i.edges := by rw [hP₀E_eq] at heP₀; exact heP₀
        have heD' : e ∈ D'.E := hP₀_D'.2 heP₀
        obtain ⟨y, z, hlyz, hyM, hzM, hyz⟩ := exists_ne_link_of_mem_edges_simple hMi_s heMi
        have hlyz' : D'.toGraph.IsLink e y z := (hPi_sub.isLink_iff hlyz.1).mp hlyz
        have hy_cl : y ∈ closure e := (hlyz'.2.2.2 ▸ (by simp : y ∈ ({y, z} : Set _))).1
        have hz_cl : z ∈ closure e := (hlyz'.2.2.2 ▸ (by simp : z ∈ ({y, z} : Set _))).1
        -- First: `Disjoint e D₁`.
        have he_not_N0 : e ∉ (N_draw ⟨0, hs⟩).E := by
          intro heN
          have hyN : y ∈ closure e ∩ (N_draw ⟨0, hs⟩).V := by
            rw [(hN_sub ⟨0, hs⟩).closure_inter_V heN]
            exact ⟨hy_cl, hlyz'.2.1⟩
          have hzN : z ∈ closure e ∩ (N_draw ⟨0, hs⟩).V := by
            rw [(hN_sub ⟨0, hs⟩).closure_inter_V heN]
            exact ⟨hz_cl, hlyz'.2.2.1⟩
          have hyD₁ : y ∈ D₁ :=
            Surface.discBd_subset D₁ (hbd_D₁.symm ▸ (N_draw ⟨0, hs⟩).V_subset_U hyN.2)
          have hzD₁ : z ∈ D₁ :=
            Surface.discBd_subset D₁ (hbd_D₁.symm ▸ (N_draw ⟨0, hs⟩).V_subset_U hzN.2)
          exact hyz ((hu₀_Mi y hyM hyD₁).trans (hu₀_Mi z hzM hzD₁).symm)
        have hdis_bd₁ : Disjoint e (discBd D₁) := by
          rw [hbd_D₁]
          refine Set.disjoint_left.mpr fun p hpe hpU => ?_
          by_cases hpV : p ∈ (N_draw ⟨0, hs⟩).V
          · exact (heD'.2.1 hpe).2 ((hN_sub ⟨0, hs⟩).1 hpV)
          · obtain ⟨e', he', hpe'⟩ := (N_draw ⟨0, hs⟩).exists_edge_of_mem hpU hpV
            exact he_not_N0 (D'.edge_eq_of_mem heD' ((hN_sub ⟨0, hs⟩).2 he') hpe hpe' ▸ he')
        obtain ⟨w₁, hw₁_cl, hw₁_not_D₁⟩ : ∃ w₁ ∈ closure e, w₁ ∉ D₁ := by
          by_cases hyu : y = u₀
          · exact ⟨z, hz_cl, fun hzD => hyz (hyu.trans (hu₀_Mi z hzM hzD).symm)⟩
          · exact ⟨y, hy_cl, fun hyD => hyu (hu₀_Mi y hyM hyD)⟩
        have he_dis_D₁ : Disjoint e D₁ := by
          rcases hD₁.side hman heD'.2.2.1.isConnected.isPreconnected hdis_bd₁ with hin | hout
          · exfalso
            obtain ⟨q, hq_out, hqe⟩ := mem_closure_iff.mp hw₁_cl _ hD₁.isClosed.isOpen_compl hw₁_not_D₁
            exact hq_out (discInt_subset _ (hin hqe))
          · exact hout
        -- Second: `Disjoint e D₂`.
        have hdis_bd₂ : Disjoint e (discBd D₂) := by
          rw [hbd_D₂]
          refine Set.disjoint_left.mpr fun p hpe hpF => ?_
          exact (heD'.2.1 hpe).2 (hF'norm ⟨hpF, (heD'.2.1 hpe).1⟩)
        obtain ⟨w₂, hw₂_cl, hw₂_not_D₂⟩ : ∃ w₂ ∈ closure e, w₂ ∉ D₂ := by
          by_cases hyv : y = v₀
          · exact ⟨z, hz_cl, fun hzD => hyz (hyv.trans (hv₀_only z hzM hzD).symm)⟩
          · exact ⟨y, hy_cl, fun hyD => hyv (hv₀_only y hyM hyD)⟩
        have he_dis_D₂ : Disjoint e D₂ := by
          rcases hD₂.side hman heD'.2.2.1.isConnected.isPreconnected hdis_bd₂ with hin | hout
          · exfalso
            obtain ⟨q, hq_out, hqe⟩ := mem_closure_iff.mp hw₂_cl _ hD₂.isClosed.isOpen_compl hw₂_not_D₂
            exact hq_out (discInt_subset _ (hin hqe))
          · exact hout
        exact ⟨he_dis_D₁, he_dis_D₂⟩
      have huv_ne : u₀ ≠ v₀ := fun h => Set.disjoint_left.mp hd₁₂ hu₀_D₁ (h ▸ hv₀_D₂)
      have hMi_pos : 0 < M_i.length := by
        by_contra h0
        exact huv_ne (GraphWalk.eq_of_length_eq_zero (W := M_i) (by omega))
      -- `u₀ ∈ discBd D₁` and `v₀ ∈ F' = discBd D₂`.
      obtain ⟨y_first, e_first, hl_first, R_first, hM_first⟩ := GM07.exists_cons_of_ne M_i huv_ne
      have he_first_P₀ : e_first ∈ P₀.E := by rw [hP₀E_eq, hM_first]; simp
      have hu₀_cl : u₀ ∈ closure e_first := by
        have : u₀ ∈ closure e_first ∩ (P_init i).V := by rw [hl_first.2.2.2]; simp
        exact this.1
      have hu₀_bd : u₀ ∈ discBd D₁ := by
        by_contra hnb
        obtain ⟨q, hq_int, hqe⟩ :=
          mem_closure_iff.mp hu₀_cl _ (hD₁.isOpen_discInt hman) ⟨hu₀_D₁, hnb⟩
        exact Set.disjoint_left.mp (hedge_disj e_first he_first_P₀).1 hqe hq_int.1
      obtain ⟨w_prev, e_last, M_init, hl_last, hM_last⟩ := GM07.exists_snoc M_i hMi_pos
      have he_last_P₀ : e_last ∈ P₀.E := by
        rw [hP₀E_eq, hM_last]
        simp [GraphWalk.edges_append]
      have hv₀_cl : v₀ ∈ closure e_last := by
        have : v₀ ∈ closure e_last ∩ (P_init i).V := by rw [hl_last.2.2.2]; simp
        exact this.1
      have hv₀_bd : v₀ ∈ discBd D₂ := by
        by_contra hnb
        obtain ⟨q, hq_int, hqe⟩ :=
          mem_closure_iff.mp hv₀_cl _ (hD₂.isOpen_discInt hman) ⟨hv₀_D₂, hnb⟩
        exact Set.disjoint_left.mp (hedge_disj e_last he_last_P₀).2 hqe hq_int.1
      have hv₀_F' : v₀ ∈ F' := hbd_D₂ ▸ hv₀_bd
      have hl_last_D' : D'.toGraph.IsLink e_last w_prev v₀ :=
        (hPi_sub.isLink_iff hl_last.1).mp hl_last
      have hnd_last : (M_init.support ++ [v₀]).Nodup := by
        have h := hMi_s
        unfold GraphWalk.IsSimple at h
        rwa [hM_last, GraphWalk.support_append] at h
      have hv₀_not_init : v₀ ∉ M_init.support := fun hm =>
        (List.nodup_append.mp hnd_last).2.2 v₀ hm v₀ List.mem_cons_self rfl
      have hw_ne_v₀ : w_prev ≠ v₀ := fun h => hv₀_not_init (h ▸ M_init.end_mem_support)
      have h_unique_last : ∀ e ∈ P₀.E, v₀ ∈ closure e → e = e_last := by
        intro e heP₀ hv_cl
        have he_mem : e ∈ M_init.edges ++ [e_last] := by
          have : e ∈ M_i.edges := by rw [hP₀E_eq] at heP₀; exact heP₀
          rwa [hM_last, GraphWalk.edges_append] at this
        rcases List.mem_append.mp he_mem with he_init | he_eq
        · exfalso
          obtain ⟨hMinit_s, _⟩ := GM09.isSimple_of_append (hM_last ▸ hMi_s)
          obtain ⟨a', b', hlab, ha'M, hb'M, _⟩ :=
            exists_ne_link_of_mem_edges_simple hMinit_s he_init
          have hlab' : D'.toGraph.IsLink e a' b' := (hPi_sub.isLink_iff hlab.1).mp hlab
          have hv_ab : v₀ ∈ ({a', b'} : Set SphereSurf) :=
            hlab'.2.2.2 ▸ ⟨hv_cl, hl_last_D'.2.2.1⟩
          rcases hv_ab with rfl | hvb
          · exact hv₀_not_init ha'M
          · exact hv₀_not_init (hvb ▸ hb'M)
        · exact List.mem_singleton.mp he_eq
      have hVD₁ : P₀.V ∩ D₁ = {u₀} := by
        ext z
        simp only [hP₀V_eq, mem_ofPred_eq, mem_inter_iff, mem_singleton_iff]
        exact ⟨fun ⟨hzM, hzD⟩ => hu₀_Mi z hzM hzD,
          by rintro rfl; exact ⟨M_i.start_mem_support, hu₀_D₁⟩⟩
      have hVD₂ : P₀.V ∩ D₂ = {v₀} := by
        ext z
        simp only [hP₀V_eq, mem_ofPred_eq, mem_inter_iff, mem_singleton_iff]
        exact ⟨fun ⟨hzM, hzD⟩ => hv₀_only z hzM hzD,
          by rintro rfl; exact ⟨M_i.end_mem_support, hv₀_D₂⟩⟩
      have hVF' : P₀.V ∩ F' = {v₀} := by
        ext z
        refine ⟨fun ⟨hzV, hzF⟩ => ?_, fun h => (mem_singleton_iff.mp h) ▸
          ⟨by rw [hP₀V_eq]; exact M_i.end_mem_support, hv₀_F'⟩⟩
        have : z ∈ P₀.V ∩ D₂ := ⟨hzV, Surface.discBd_subset D₂ (hbd_D₂.symm ▸ hzF)⟩
        rwa [hVD₂] at this
      have hP₀_dis_int₁ : Disjoint P₀.U (discInt D₁) := by
        refine Set.disjoint_left.mpr fun z hzU hz_int => ?_
        rw [P₀.U_eq] at hzU
        rcases hzU with hzV | hzE
        · have : z = u₀ := by
            have hm : z ∈ P₀.V ∩ D₁ := ⟨hzV, hz_int.1⟩
            rwa [hVD₁, mem_singleton_iff] at hm
          exact hz_int.2 (this ▸ hu₀_bd)
        · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
          obtain ⟨q, hq_int, hqe⟩ :=
            mem_closure_iff.mp hze _ (hD₁.isOpen_discInt hman) hz_int
          exact Set.disjoint_left.mp (hedge_disj e he).1 hqe hq_int.1
      have hP₀_dis_int₂ : Disjoint P₀.U (discInt D₂) := by
        refine Set.disjoint_left.mpr fun z hzU hz_int => ?_
        rw [P₀.U_eq] at hzU
        rcases hzU with hzV | hzE
        · have : z = v₀ := by
            have hm : z ∈ P₀.V ∩ D₂ := ⟨hzV, hz_int.1⟩
            rwa [hVD₂, mem_singleton_iff] at hm
          exact hz_int.2 (this ▸ hv₀_bd)
        · obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hzE
          obtain ⟨q, hq_int, hqe⟩ :=
            mem_closure_iff.mp hze _ (hD₂.isOpen_discInt hman) hz_int
          exact Set.disjoint_left.mp (hedge_disj e he).2 hqe hq_int.1
      have hP₀_DF : P₀.U ⊆ D_F := fun z hz =>
        by_contra fun hznot => Set.disjoint_left.mp hP₀_dis_int₂ hz (hint_D₂_iff.mpr hznot)
      exact ⟨P₀, u₀, v₀, w_prev, e_last, hP₀_Pi, hP₀_D', hu₀_bd, hv₀_F', hP₀_path,
        hVD₁, hVD₂, hVF', hP₀_dis_int₁, hP₀_dis_int₂, hP₀_DF,
        he_last_P₀, hl_last_D', hw_ne_v₀, h_unique_last⟩
    choose P₀ u₀ v₀ w_prev e_last hP₀_Pi hP₀_D' hu₀_bd hv₀_F' hP₀_path
      hP₀_VD₁ hP₀_VD₂ hP₀_VF' hP₀_dis₁ hP₀_dis₂ hP₀_DF
      he_last_P₀ hl_last_D' hw_ne_v₀ h_unique_last using hex_P₀
    have hP₀_dis : ∀ i i', i ≠ i' → Disjoint (P₀ i).V (P₀ i').V := fun i i' hne =>
      (hP_init_dis hne).mono (hP₀_Pi i).1 (hP₀_Pi i').1
    -- Step 4: Form the minimal span `Γ` of the initial nest circuits and trimmed spokes.
    let VΓ : Set SphereSurf := (⋃ j : Fin s, (N_draw j).V) ∪ (⋃ i : Fin r, (P₀ i).V)
    let EΓ : Set (Set SphereSurf) := (⋃ j : Fin s, (N_draw j).E) ∪ (⋃ i : Fin r, (P₀ i).E)
    let Γ : Drawing SphereSurf := D'.span VΓ EΓ
    have hΓ_sub : Γ.IsSubdrawing D' := D'.span_isSubdrawing VΓ EΓ
    have hVΓ_sub : VΓ ⊆ D'.V :=
      union_subset (iUnion_subset fun j => (hN_sub j).1) (iUnion_subset fun i => (hP₀_D' i).1)
    have hEΓ_sub : EΓ ⊆ D'.E :=
      union_subset (iUnion_subset fun j => (hN_sub j).2) (iUnion_subset fun i => (hP₀_D' i).2)
    have hΓE : Γ.E = EΓ := by
      rw [D'.span_E]
      exact inter_eq_left.mpr hEΓ_sub
    have hΓV : Γ.V = VΓ := by
      apply subset_antisymm
      · rintro x (⟨hx, _⟩ | hx)
        · exact hx
        · obtain ⟨e, ⟨heEΓ, _⟩, hxe, hxD'V⟩ := mem_iUnion₂.mp hx
          rcases heEΓ with heN | heP
          · obtain ⟨j, hj⟩ := mem_iUnion.mp heN
            have : x ∈ closure e ∩ (N_draw j).V := by
              rw [(hN_sub j).closure_inter_V hj]
              exact ⟨hxe, hxD'V⟩
            exact Or.inl (mem_iUnion.mpr ⟨j, this.2⟩)
          · obtain ⟨i, hi⟩ := mem_iUnion.mp heP
            have : x ∈ closure e ∩ (P₀ i).V := by
              rw [(hP₀_D' i).closure_inter_V hi]
              exact ⟨hxe, hxD'V⟩
            exact Or.inr (mem_iUnion.mpr ⟨i, this.2⟩)
      · exact fun x hx => Or.inl ⟨hx, hVΓ_sub hx⟩
    have hN_Γ : ∀ j, (N_draw j).IsSubdrawing Γ := fun j =>
      ⟨fun x hx => hΓV ▸ Or.inl (mem_iUnion.mpr ⟨j, hx⟩),
       fun e he => hΓE ▸ Or.inl (mem_iUnion.mpr ⟨j, he⟩)⟩
    have hP₀_Γ : ∀ i, (P₀ i).IsSubdrawing Γ := fun i =>
      ⟨fun x hx => hΓV ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩),
       fun e he => hΓE ▸ Or.inr (mem_iUnion.mpr ⟨i, he⟩)⟩
    have hΓU_eq : Γ.U = (⋃ j : Fin s, (N_draw j).U) ∪ (⋃ i : Fin r, (P₀ i).U) := by
      apply subset_antisymm
      · intro x hx
        rw [Γ.U_eq, hΓV, hΓE] at hx
        rcases hx with (hxN | hxP) | hxE
        · obtain ⟨j, hj⟩ := mem_iUnion.mp hxN
          exact Or.inl (mem_iUnion.mpr ⟨j, (N_draw j).V_subset_U hj⟩)
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
          exact Or.inr (mem_iUnion.mpr ⟨i, (P₀ i).V_subset_U hi⟩)
        · obtain ⟨e, heEΓ, hxe⟩ := mem_iUnion₂.mp hxE
          rcases heEΓ with heN | heP
          · obtain ⟨j, hj⟩ := mem_iUnion.mp heN
            exact Or.inl (mem_iUnion.mpr ⟨j, ((N_draw j).U_eq ▸ Or.inr (mem_iUnion₂.mpr ⟨e, hj, hxe⟩))⟩)
          · obtain ⟨i, hi⟩ := mem_iUnion.mp heP
            exact Or.inr (mem_iUnion.mpr ⟨i, ((P₀ i).U_eq ▸ Or.inr (mem_iUnion₂.mpr ⟨e, hi, hxe⟩))⟩)
      · exact union_subset (iUnion_subset fun j => (hN_Γ j).U_subset)
          (iUnion_subset fun i => (hP₀_Γ i).U_subset)
    have hΓU_DF : Γ.U ⊆ D_F := by
      rw [hΓU_eq]
      exact union_subset
        (iUnion_subset fun j => (hN_in_DF j).trans (discInt_subset _))
        (iUnion_subset fun i => hP₀_DF i)
    have hi₁ : Disjoint Γ.U (discInt D₁) := by
      rw [hΓU_eq]
      refine Disjoint.union_left (Set.disjoint_iUnion_left.mpr fun j => ?_)
        (Set.disjoint_iUnion_left.mpr fun i => hP₀_dis₁ i)
      rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
      · have hj_eq : j = ⟨0, hs⟩ := Fin.ext hj0
        rw [hj_eq, ← hbd_D₁]
        exact Set.disjoint_left.mpr fun x hbd hint => hint.2 hbd
      · have hlt : (⟨0, hs⟩ : Fin s) < j := Fin.lt_def.mpr hjpos
        have hsub : D₁ ⊆ discInt (Dn j) := hDn_strict ⟨0, hs⟩ j hlt
        rw [← hDn_bd j]
        exact Set.disjoint_left.mpr fun x hbd hint => (hsub hint.1).2 hbd
    have hi₂ : Disjoint Γ.U (discInt D₂) :=
      Set.disjoint_left.mpr fun x hxU hxint => (hint_D₂_iff.mp hxint) (hΓU_DF hxU)
    -- Every vertex of `Γ.V ∩ F'` equals `v₀ i` for a unique `i`, and lies in `closure e` for at most
    -- one edge `e = e_last i` of `Γ` (which is a non-loop link).
    have hΓV_F'_unique_edge : ∀ w ∈ Γ.V ∩ F', ∃ i : Fin r, w = v₀ i ∧
        ∀ e ∈ Γ.E, w ∈ closure e → e = e_last i := by
      rintro w ⟨hwΓ, hwF⟩
      rw [hΓV] at hwΓ
      rcases hwΓ with hwN | hwP
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hwN
        exact absurd (hDF_bd.symm ▸ hwF) (hN_in_DF j ((N_draw j).V_subset_U hj)).2
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hwP
        have hw_eq : w = v₀ i := by
          have : w ∈ (P₀ i).V ∩ F' := ⟨hi, hwF⟩
          rwa [hP₀_VF' i] at this
        refine ⟨i, hw_eq, fun e heΓ hw_cl => ?_⟩
        rw [hw_eq] at hw_cl
        rw [hΓE] at heΓ
        rcases heΓ with heN | heP
        · obtain ⟨j, hj⟩ := mem_iUnion.mp heN
          exfalso
          have hcl_sub : closure e ⊆ (N_draw j).U :=
            closure_minimal (fun z hz => by
              rw [(N_draw j).U_eq]
              exact Or.inr (mem_iUnion₂.mpr ⟨e, hj, subset_closure hz⟩))
              (N_draw j).isClosed_U
          exact (hN_in_DF j (hcl_sub hw_cl)).2 (hDF_bd.symm ▸ hv₀_F' i)
        · obtain ⟨i', hi'⟩ := mem_iUnion.mp heP
          by_cases hii' : i' = i
          · rw [hii'] at hi'
            exact h_unique_last i e hi' hw_cl
          · exfalso
            have hv_P₀i' : v₀ i ∈ closure e ∩ (P₀ i').V := by
              rw [(hP₀_D' i').closure_inter_V hi']
              exact ⟨hw_cl, (hl_last_D' i).2.2.1⟩
            have hv_P₀i : v₀ i ∈ (P₀ i).V := by
              have : v₀ i ∈ (P₀ i).V ∩ F' := by rw [hP₀_VF' i]; simp
              exact this.1
            exact Set.disjoint_left.mp (hP₀_dis i i' (Ne.symm hii')) hv_P₀i hv_P₀i'.2
    -- Hence no circuit subdrawing `B` of `Γ` meets `F'`.
    have hB_in_DF : ∀ B : Drawing SphereSurf, B.IsSubdrawing Γ → B.IsCircuit →
        B.U ⊆ discInt D_F := by
      intro B hBΓ hBc x hxBU
      have hxDF : x ∈ D_F := hΓU_DF (hBΓ.U_subset hxBU)
      refine ⟨hxDF, fun hxbd => ?_⟩
      have hxF : x ∈ F' := hDF_bd ▸ hxbd
      have hxD'V : x ∈ D'.V := hF'norm ⟨hxF, (hBΓ.trans hΓ_sub).U_subset hxBU⟩
      have hxBV : x ∈ B.V := by
        by_contra hnot
        obtain ⟨e, heB, hxe⟩ := B.exists_edge_of_mem hxBU hnot
        exact ((hΓ_sub.2 (hBΓ.2 heB)).2.1 hxe).2 hxD'V
      obtain ⟨i, rfl, huniq⟩ := hΓV_F'_unique_edge x ⟨hBΓ.1 hxBV, hxF⟩
      rcases exists_loop_or_two_edges_of_isCircuit hBΓ hBc hxBV with
        ⟨e, heB, hloop⟩ | ⟨e₁, he₁B, e₂, he₂B, he₁₂, hcl₁, hcl₂⟩
      · have hloop_D' : D'.toGraph.IsLink e (v₀ i) (v₀ i) :=
          (hΓ_sub.isLink_iff (hBΓ.2 heB)).mp hloop
        have hcl_v : v₀ i ∈ closure e := by
          have : v₀ i ∈ closure e ∩ D'.V := by rw [hloop_D'.2.2.2]; simp
          exact this.1
        have he_eq : e = e_last i := huniq e (hBΓ.2 heB) hcl_v
        subst he_eq
        have hset_eq : ({w_prev i, v₀ i} : Set SphereSurf) = {v₀ i} := by
          simpa using (hl_last_D' i).2.2.2.symm.trans hloop_D'.2.2.2
        have hw_mem : w_prev i ∈ ({v₀ i} : Set SphereSurf) := hset_eq ▸ Or.inl rfl
        exact hw_ne_v₀ i hw_mem
      · exact he₁₂ ((huniq e₁ (hBΓ.2 he₁B) hcl₁).trans (huniq e₂ (hBΓ.2 he₂B) hcl₂).symm)
    -- Step 5: Wheels, uncrossing with monotonicity, and path trimming.
    obtain ⟨p_in, hp_in⟩ := hD₁.nonempty_discInt
    let a_out : SphereSurf := OnePoint.infty
    have ha_out : a_out ∈ discInt D₂ := hint_D₂_iff.mpr hinf_not_DF
    obtain ⟨H, C₁, C₂, E₁, E₂, q, ℓ, w⟩ := GM07.exists_wheeled Γ hD₁ hD₂ hd₁₂ hi₁ hi₂
    have hC₁I : ∀ x ∈ C₁.U, x ∈ discInt D₁ := fun x hx => w.in₁ (Surface.discBd_subset _ (w.bd₁ ▸ hx))
    have hC₂I : ∀ x ∈ C₂.U, x ∈ discInt D₂ := fun x hx => w.in₂ (Surface.discBd_subset _ (w.bd₂ ▸ hx))
    have hΓ₁ : Disjoint Γ.V C₁.V := Set.disjoint_left.mpr fun x h3 h4 =>
      Set.disjoint_left.mp hi₁ (Γ.V_subset_U h3) (hC₁I x (C₁.V_subset_U h4))
    have hΓ₂ : Disjoint Γ.V C₂.V := Set.disjoint_left.mpr fun x h3 h4 =>
      Set.disjoint_left.mp hi₂ (Γ.V_subset_U h3) (hC₂I x (C₂.V_subset_U h4))
    have h12 : Disjoint C₁.V C₂.V := Set.disjoint_left.mpr fun x h3 h4 =>
      Set.disjoint_left.mp hd₁₂ (hC₁I x (C₁.V_subset_U h3)).1 (hC₂I x (C₂.V_subset_U h4)).1
    obtain ⟨hΔ_w, hbΔ_w₀⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph w.disc₂
    set Δ_w := closure (univ \ E₂) with hΔ_w_def
    have hbΔ_w : discBd Δ_w = C₂.U := hbΔ_w₀.trans w.bd₂
    have hoffΔ_w : ∀ {x : SphereSurf}, x ∉ E₂ → x ∈ Δ_w := fun hx => subset_closure ⟨mem_univ _, hx⟩
    have hnotΔ_w : ∀ {x : SphereSurf}, x ∈ discInt E₂ → x ∉ Δ_w := by
      intro x hx h
      obtain ⟨y, hy1, hy2⟩ := mem_closure_iff.mp h _ (w.disc₂.isOpen_discInt hman) hx
      exact hy2.2 hy1.1
    have hE₁Δ_w : E₁ ⊆ Δ_w := fun x hx =>
      hoffΔ_w fun h => Set.disjoint_left.mp hd₁₂ (w.in₁ hx).1 (w.in₂ h).1
    have hDn_E₁ : ∀ t : Fin s, E₁ ⊆ Dn t := fun t x hx => by
      rcases Nat.eq_zero_or_pos t.1 with ht0 | htpos
      · have ht_eq : t = ⟨0, hs⟩ := Fin.ext ht0
        exact ht_eq ▸ (w.in₁ hx).1
      · exact (discInt_subset _ (w.in₁ hx)) |> fun hx₁ =>
          (discInt_subset _ (hDn_strict ⟨0, hs⟩ t (Fin.lt_def.mpr htpos) hx₁))
    have hDn_Δ_w : ∀ t : Fin s, Dn t ⊆ Δ_w := fun t x hx =>
      hoffΔ_w fun h => (hint_D₂_iff.mp (w.in₂ h)) (hDn_in_DF t hx).1
    have hN_layer : ∀ t : Fin s, (N_draw t).IsCircuit ∧ (N_draw t).IsSubdrawing Γ ∧
        IsClosedDisc (Dn t) ∧ discBd (Dn t) = (N_draw t).U ∧ E₁ ⊆ Dn t ∧ Dn t ⊆ Δ_w :=
      fun t => ⟨hN_circ t, hN_Γ t, hDn_disc t, hDn_bd t, hDn_E₁ t, hDn_Δ_w t⟩
    have hNN_layer : ∀ t t' : Fin s, t < t' → Disjoint (N_draw t).V (N_draw t').V ∧ Dn t ⊆ Dn t' := by
      intro t t' htt'
      refine ⟨Set.disjoint_left.mpr fun x hxt hxt' => ?_,
        (hDn_strict t t' htt').trans (discInt_subset _)⟩
      have hxt_int : x ∈ discInt (Dn t') :=
        hDn_strict t t' htt' (Surface.discBd_subset _ (hDn_bd t ▸ (N_draw t).V_subset_U hxt))
      exact hxt_int.2 (hDn_bd t' ▸ (N_draw t').V_subset_U hxt')
    have hnest := GM07.isDiscNest_of_layers w hΔ_w hbΔ_w hE₁Δ_w hN_layer hNN_layer hΓ₁ hΓ₂ h12
    -- Extend `P₀ i` across the two wheels.
    have hends : ∀ i : Fin r, u₀ i ∈ Γ.V ∩ D₁ ∧ v₀ i ∈ Γ.V ∩ D₂ := fun i => by
      have huV : u₀ i ∈ (P₀ i).V := (hP₀_VD₁ i ▸ mem_singleton (u₀ i) : u₀ i ∈ (P₀ i).V ∩ D₁).1
      have hvV : v₀ i ∈ (P₀ i).V := (hP₀_VD₂ i ▸ mem_singleton (v₀ i) : v₀ i ∈ (P₀ i).V ∩ D₂).1
      exact ⟨⟨(hP₀_Γ i).1 huV, Surface.discBd_subset _ (hu₀_bd i)⟩,
        ⟨(hP₀_Γ i).1 hvV, Surface.discBd_subset _ (hbd_D₂.symm ▸ hv₀_F' i)⟩⟩
    have hstart : ∀ i : Fin r, u₀ i ∈ (P₀ i).V ∧ v₀ i ∈ (P₀ i).V := fun i =>
      ⟨(hP₀_VD₁ i ▸ mem_singleton (u₀ i) : u₀ i ∈ (P₀ i).V ∩ D₁).1,
       (hP₀_VD₂ i ▸ mem_singleton (v₀ i) : v₀ i ∈ (P₀ i).V ∩ D₂).1⟩
    have hext : ∀ i : Fin r, ∃ P' : Drawing SphereSurf,
        P'.IsSubdrawing H ∧ P'.IsPathBetween (q (u₀ i)) (q (v₀ i)) ∧
        P'.V ⊆ (P₀ i).V ∪ {q (u₀ i), q (v₀ i)} ∧ P'.U = ℓ (u₀ i) ∪ (P₀ i).U ∪ ℓ (v₀ i) :=
      fun i => GM07.exists_extended_path w hd₁₂ hi₁ hi₂ (hP₀_Γ i) (hends i).1 (hends i).2 (hP₀_path i)
    choose P₁ hP₁H hP₁p hP₁V hP₁U using hext
    have hq₁ := fun i => w.q₁ _ (hends i).1
    have hq₂ := fun i => w.q₂ _ (hends i).2
    have hu_ud : ∀ i, u₀ i ∈ Γ.V ∩ (D₁ ∪ D₂) := fun i => ⟨(hends i).1.1, Or.inl (hends i).1.2⟩
    have hv_ud : ∀ i, v₀ i ∈ Γ.V ∩ (D₁ ∪ D₂) := fun i => ⟨(hends i).2.1, Or.inr (hends i).2.2⟩
    have hquu : ∀ i i', i ≠ i' → q (u₀ i) ≠ q (u₀ i') := fun i i' hne he => by
      have hne' : u₀ i ≠ u₀ i' := fun h =>
        Set.disjoint_left.mp (hP₀_dis i i' hne) (hstart i).1 (h ▸ (hstart i').1)
      exact Set.disjoint_left.mp (w.disj _ (hu_ud i) _ (hu_ud i') hne')
        (w.line _ (hu_ud i)).1.right_mem (he ▸ (w.line _ (hu_ud i')).1.right_mem)
    have hqvv : ∀ i i', i ≠ i' → q (v₀ i) ≠ q (v₀ i') := fun i i' hne he => by
      have hne' : v₀ i ≠ v₀ i' := fun h =>
        Set.disjoint_left.mp (hP₀_dis i i' hne) (hstart i).2 (h ▸ (hstart i').2)
      exact Set.disjoint_left.mp (w.disj _ (hv_ud i) _ (hv_ud i') hne')
        (w.line _ (hv_ud i)).1.right_mem (he ▸ (w.line _ (hv_ud i')).1.right_mem)
    have hP₁dis : ∀ i i', i ≠ i' → Disjoint (P₁ i).V (P₁ i').V := fun i i' hne =>
      Set.disjoint_left.mpr fun z h3 h4 => by
        have hΓz : ∀ k, z ∈ (P₀ k).V → z ∈ Γ.V := fun k h => (hP₀_Γ k).1 h
        have hc1 : ∀ k, z = q (u₀ k) → z ∈ C₁.V := fun k h => h ▸ hq₁ k
        have hc2 : ∀ k, z = q (v₀ k) → z ∈ C₂.V := fun k h => h ▸ hq₂ k
        rcases hP₁V i h3 with h5 | h5 | h5 <;> rcases hP₁V i' h4 with h6 | h6 | h6
        · exact Set.disjoint_left.mp (hP₀_dis i i' hne) h5 h6
        · exact Set.disjoint_left.mp hΓ₁ (hΓz i h5) (hc1 i' h6)
        · exact Set.disjoint_left.mp hΓ₂ (hΓz i h5) (hc2 i' h6)
        · exact Set.disjoint_left.mp hΓ₁ (hΓz i' h6) (hc1 i h5)
        · exact hquu i i' hne (h5.symm.trans h6)
        · exact Set.disjoint_left.mp h12 (hc1 i h5) (hc2 i' h6)
        · exact Set.disjoint_left.mp hΓ₂ (hΓz i' h6) (hc2 i h5)
        · exact Set.disjoint_left.mp h12 (hc1 i' h6) (hc2 i h5)
        · exact hqvv i i' hne (h5.symm.trans h6)
    have hP₁Δ_w : ∀ i, (P₁ i).U ⊆ Δ_w := fun i => by
      rw [hP₁U]
      refine union_subset
        (union_subset (fun z hz => hoffΔ_w fun h => ?_) (fun z hz => hoffΔ_w fun h => ?_))
        fun z hz => ?_
      · exact Set.disjoint_left.mp hd₁₂ ((w.cap₁ _ (hends i).1).1 hz) (w.in₂ h).1
      · exact Set.disjoint_left.mp hi₂ ((hP₀_Γ i).U_subset hz) (w.in₂ h)
      · by_cases h : z ∈ E₂
        · have h3 : z ∈ ℓ (v₀ i) ∩ E₂ := ⟨hz, h⟩
          rw [(w.cap₂ _ (hends i).2).2.2] at h3
          obtain rfl := h3
          exact Surface.discBd_subset _ (hbΔ_w ▸ C₂.V_subset_U (hq₂ i))
        · exact hoffΔ_w h
    have hpaths : IsDiscPaths H Δ_w C₁ C₂ P₁ :=
      ⟨fun i => ⟨hP₁H i, hP₁Δ_w i, _, hq₁ i, _, hq₂ i, hP₁p i⟩, fun i i' hne => hP₁dis i i' hne⟩
    -- Uncross with monotonicity!
    obtain ⟨C_un, Pu, hC_un, hmono_un, hPu, hinf_un⟩ :=
      planar_nest_uncrossing_mono hS hΔ_w hbΔ_w _ hnest ⟨P₁, hpaths⟩
    obtain ⟨hCdata, hCdis, hCmono, hCend⟩ := hC_un
    obtain ⟨hC0, hCl⟩ := hCend (by omega)
    let i₀ : Fin (s + 2) := ⟨0, by omega⟩
    let il : Fin (s + 2) := ⟨s + 2 - 1, by omega⟩
    let idx : Fin s → Fin (s + 2) := fun j => ⟨j.1 + 1, by omega⟩
    have hidx0 : ∀ j, idx j ≠ i₀ := fun j h => by
      have := congrArg Fin.val h; simp [idx, i₀] at this
    have hidxl : ∀ j, idx j ≠ il := fun j h => by
      have h3 := congrArg Fin.val h; have h4 := j.2; simp only [idx, il] at h3; omega
    let B : Fin s → Drawing SphereSurf := fun j => C_un (idx j)
    let E_B : Fin s → Set SphereSurf := fun j => GM14.discIns Δ_w (B j)
    have hBC₁ : ∀ j, Disjoint (B j).V C₁.V := fun j => by
      have : Disjoint (C_un (idx j)).V (C_un i₀).V := hCdis (hidx0 j)
      rwa [show C_un i₀ = C₁ from hC0] at this
    have hBC₂ : ∀ j, Disjoint (B j).V C₂.V := fun j => by
      have : Disjoint (C_un (idx j)).V (C_un il).V := hCdis (hidxl j)
      rwa [show C_un il = C₂ from hCl] at this
    have hBΓ : ∀ j, (B j).IsSubdrawing Γ := fun j => by
      obtain ⟨c1, -, -⟩ := hCdata (idx j)
      have hVΓ : ∀ x ∈ (B j).V, x ∈ Γ.V := fun x hx => by
        have h3 := c1.1 hx
        rw [w.V] at h3
        rcases h3 with (h | h) | h
        · exact h
        · exact absurd h (Set.disjoint_left.mp (hBC₁ j) hx)
        · exact absurd h (Set.disjoint_left.mp (hBC₂ j) hx)
      refine ⟨hVΓ, fun e he => ?_⟩
      obtain ⟨y, z, hl⟩ := ((B j).toGraph.edge_mem_iff_exists_isLink e).mp he
      exact w.mem_E_of_link hΓ₁ hΓ₂ ((c1.isLink_iff he).mp hl) (hVΓ y hl.2.1) (hVΓ z hl.2.2.1)
    have hBD' : ∀ j, (B j).IsSubdrawing D' := fun j => (hBΓ j).trans hΓ_sub
    have hBc : ∀ j, (B j).IsCircuit := fun j => (hCdata (idx j)).2.1
    have hBU_in_DF : ∀ j, (B j).U ⊆ discInt D_F := fun j => hB_in_DF (B j) (hBΓ j) (hBc j)
    have hEB_spec : ∀ j, E_B j ⊆ Δ_w ∧ IsClosedDisc (E_B j) ∧ discBd (E_B j) = (B j).U :=
      fun j => (GM14.discIns_spec hΔ_w (hBc j) (hCdata (idx j)).2.2).1
    -- `OnePoint.infty = a_out ∉ E_B j`, hence `IsInsideDisc Δ' (B j).U (E_B j)`.
    have hEB_inside : ∀ j, IsInsideDisc Δ' (B j).U (E_B j) := by
      intro j
      obtain ⟨hd1, hd2, hd3⟩ := hEB_spec j
      have hf_dis : Disjoint (discInt D₂) (discBd (E_B j)) := by
        rw [hd3]
        exact hi₂.symm.mono_right (hBΓ j).U_subset
      have ha_not_EB : (OnePoint.infty : SphereSurf) ∉ E_B j := by
        intro haEB
        obtain ⟨z, hz⟩ := w.disc₂.nonempty_discInt
        exact hnotΔ_w hz (hd1 (GM07.side_of_disc hS hD₂ hd2 hf_dis ha_out (w.in₂ hz.1) haEB))
      have hBJ_Δ : (B j).U ⊆ Δ' := (hBU_in_DF j).trans ((discInt_subset _).trans hD_F.1)
      obtain ⟨D_Bj, hD_Bj, _⟩ := disc_oArc Δ' (B j).U hΔ' hBJ_Δ (IsCircuit.isOArc_U (hBc j))
      have hnot_cov : E_B j ∪ D_Bj ≠ univ := by
        intro hu
        have hm : (OnePoint.infty : SphereSurf) ∈ E_B j ∪ D_Bj := hu ▸ mem_univ _
        rcases hm with h1 | h2
        · exact ha_not_EB h1
        · exact hinf_Δ (hD_Bj.1 h2)
      have heq_EB : E_B j = D_Bj :=
        GM12.eq_of_discBd_eq_of_union_ne_univ hman hd2 hD_Bj.2.1 (hd3.trans hD_Bj.2.2.1.symm) hnot_cov
      exact heq_EB ▸ hD_Bj
    -- Monotonicity gives `D₁ ⊆ E_B ⟨0, hs⟩`.
    have hD₁_sub_EB0 : D₁ ⊆ E_B ⟨0, hs⟩ := by
      have hdisc_N0 : GM14.discIns Δ_w (nestAt C₁ C₂ s N_draw (idx ⟨0, hs⟩)) = D₁ := by
        have hidx_eq : nestAt C₁ C₂ s N_draw (idx ⟨0, hs⟩) = N_draw ⟨0, hs⟩ :=
          GM07.nestAt_succ C₁ C₂ s N_draw ⟨0, hs⟩
        rw [hidx_eq]
        exact ((GM14.discIns_spec hΔ_w (hN_circ ⟨0, hs⟩)
          (hbd_D₁ ▸ (Surface.discBd_subset _).trans (hDn_Δ_w ⟨0, hs⟩))).2
          D₁ (hDn_Δ_w ⟨0, hs⟩) hD₁ hbd_D₁).symm
      simpa [E_B, B, hdisc_N0] using hmono_un (idx ⟨0, hs⟩)
    -- Strict nesting of `E_B`: `j < j' → E_B j ⊆ discInt (E_B j')`.
    have hEB_strict : ∀ j j' : Fin s, j < j' → E_B j ⊆ discInt (E_B j') := by
      intro j j' hjj'
      have hsub : E_B j ⊆ E_B j' :=
        hCmono (Fin.le_def.mpr (by simpa [idx] using Nat.le_of_lt (Fin.lt_def.mp hjj')))
      have hne_idx : idx j ≠ idx j' := fun h =>
        (ne_of_lt hjj') (Fin.ext (by simpa [idx] using congrArg Fin.val h))
      have hdU : Disjoint (B j).U (B j').U :=
        disjoint_U_of_disjoint_V_subdrawing (hBΓ j) (hBΓ j') (hCdis hne_idx)
      intro z hz
      have hz_not_Bj' : z ∉ discBd (E_B j') := by
        rw [(hEB_spec j').2.2]
        intro hzBj'
        have hz_not_Bj : z ∉ discBd (E_B j) := by
          rw [(hEB_spec j).2.2]
          exact fun hzBj => Set.disjoint_left.mp hdU hzBj hzBj'
        have hz_front : z ∈ frontier (E_B j') := by
          rw [IsClosedDisc.frontier_eq_discBd hS (hEB_spec j').2.1, (hEB_spec j').2.2]
          exact hzBj'
        exact hz_front.2 (mem_interior.mpr ⟨discInt (E_B j), (discInt_subset _).trans hsub,
          (hEB_spec j).2.1.isOpen_discInt hman, ⟨hz, hz_not_Bj⟩⟩)
      exact ⟨hsub hz, hz_not_Bj'⟩
    -- Trim `Pu i` to `P_raw i` in `Γ` between `D₁` and `D₂`.
    have htrim : ∀ i : Fin r, ∃ (P : Drawing SphereSurf) (u v : SphereSurf),
        P.IsSubdrawing Γ ∧ P.IsSubdrawing (Pu i) ∧ u ∈ D₁ ∧ v ∈ D₂ ∧ P.IsPathBetween u v ∧
        ∀ C_mid : Drawing SphereSurf, C_mid.IsSubdrawing H →
          Disjoint C_mid.V C₁.V → Disjoint C_mid.V C₂.V →
          C_mid.V ∩ (Pu i).V ⊆ P.V ∧ C_mid.E ∩ (Pu i).E ⊆ P.E := by
      intro i
      obtain ⟨c1, -, a', ha', b', hb', hpa⟩ := hPu.1 i
      have h3 := (hinf_un i₀ i).isPreconnected_U
      have h4 := (hinf_un il i).isPreconnected_U
      rw [show C_un i₀ = C₁ from hC0] at h3
      rw [show C_un il = C₂ from hCl] at h4
      exact GM07.exists_trimmed_path w hΓ₁ hΓ₂ h12 c1 ha' hb' hpa h3 h4
    choose P_raw u_raw v_raw hPraw_Γ hPraw_Pu hu_raw hv_raw hPraw_p hPraw_B using htrim
    have hPraw_inf : ∀ (i : Fin r) (j : Fin s),
        Drawing.inf Γ (P_raw i) (B j) = Drawing.inf H (B j) (Pu i) := by
      intro i j
      have hBH := (hCdata (idx j)).1
      have hPuH := (hPu.1 i).1
      obtain ⟨hV, hE⟩ := hPraw_B i (B j) hBH (hBC₁ j) (hBC₂ j)
      refine Drawing.ext_of_V_E ?_ ?_
      · rw [Drawing.inf_V (hPraw_Γ i) (hBΓ j), Drawing.inf_V hBH hPuH]
        exact subset_antisymm (fun x hx => ⟨hx.2, (hPraw_Pu i).1 hx.1⟩) fun x hx => ⟨hV hx, hx.1⟩
      · rw [Drawing.inf_E (hPraw_Γ i), Drawing.inf_E hBH]
        exact subset_antisymm (fun x hx => ⟨hx.2, (hPraw_Pu i).2 hx.1⟩) fun x hx => ⟨hE hx, hx.1⟩
    -- Step 6: Cut each `P_raw i` at its first vertex on `(B ⟨0, hs⟩).V`.
    have hex_spoke : ∀ i : Fin r, ∃ (P' : Drawing SphereSurf) (u' : SphereSurf),
        P'.IsSubdrawing (P_raw i) ∧ P'.IsSubdrawing Γ ∧
        u' ∈ (B ⟨0, hs⟩).U ∧ v_raw i ∈ F' ∧ P'.IsPathBetween u' (v_raw i) ∧
        OArcEncloses Δ' F' P'.U ∧ P'.V ∩ F' = {v_raw i} ∧
        ∀ j : Fin s, P'.V ∩ (B j).V = (P_raw i).V ∩ (B j).V ∧
          P'.E ∩ (B j).E = (P_raw i).E ∩ (B j).E := by
      intro i
      obtain ⟨W_raw, hWraw_s, hPraw_V, hPraw_E⟩ := hPraw_p i
      -- `Drawing.inf Γ (P_raw i) (B ⟨0, hs⟩)` is a path, so `(P_raw i).V ∩ (B ⟨0, hs⟩).V` is nonempty.
      obtain ⟨a₀, _, W_inf0, _, hWinf0_V, _⟩ := hPraw_inf i ⟨0, hs⟩ ▸ hinf_un (idx ⟨0, hs⟩) i
      have ha₀_mem : a₀ ∈ (P_raw i).V ∩ (B ⟨0, hs⟩).V := by
        rw [← Drawing.inf_V (hPraw_Γ i) (hBΓ ⟨0, hs⟩), hWinf0_V]
        exact W_inf0.start_mem_support
      have ha₀_sup : a₀ ∈ W_raw.support := by
        have : a₀ ∈ {z | z ∈ W_raw.support} := hPraw_V ▸ ha₀_mem.1
        exact this
      obtain ⟨u', hu'_B0V, W₁, W₂, hWeq, hu'_first⟩ :=
        GM09.PlanarNests.exists_first_hit_split W_raw ⟨a₀, ha₀_sup, ha₀_mem.2⟩
      subst hWeq
      obtain ⟨hW₁s, hW₂s⟩ := GM09.isSimple_of_append hWraw_s
      let P' := GM11.walkDrawing (P_raw i) W₂
      have hP'_Praw : P'.IsSubdrawing (P_raw i) := GM11.walkDrawing_isSubdrawing _ _
      have hP'_Γ : P'.IsSubdrawing Γ := hP'_Praw.trans (hPraw_Γ i)
      have hP'_path : P'.IsPathBetween u' (v_raw i) := GM11.walkDrawing_isPathBetween _ hW₂s
      have hP'_V : P'.V = {z | z ∈ W₂.support} := GM11.walkDrawing_V _ _
      have hP'_E : P'.E = {e | e ∈ W₂.edges} := GM11.walkDrawing_E _ _
      have hv_F' : v_raw i ∈ F' := by
        have hv_ΓU : v_raw i ∈ Γ.U :=
          Γ.V_subset_U ((hPraw_Γ i).1 (by rw [hPraw_V]; exact (W₁.append W₂).end_mem_support))
        have hv_DF : v_raw i ∈ D_F := hΓU_DF hv_ΓU
        have hv_not_int : v_raw i ∉ discInt D_F := hD₂_iff.mp (hv_raw i)
        rw [← hDF_bd]
        exact by_contra fun hnb => hv_not_int ⟨hv_DF, hnb⟩
      -- Walk `W₁` stays inside `E_B ⟨0, hs⟩` and uses no edges of `B ⟨0, hs⟩`.
      have hW₁_stay : ∀ {a b : SphereSurf} (W₀ : GraphWalk (P_raw i).toGraph a b),
          W₀.IsSimple → a ∈ E_B ⟨0, hs⟩ → (∀ z ∈ W₀.support, z ∈ (B ⟨0, hs⟩).V → z = b) →
          (∀ z ∈ W₀.support, z ∈ E_B ⟨0, hs⟩) ∧ (∀ e ∈ W₀.edges, e ∉ (B ⟨0, hs⟩).E) := by
        intro a b W₀ hW₀s ha_EB hfirst
        induction W₀ with
        | nil _ => exact ⟨fun z hz => (List.mem_singleton.mp hz) ▸ ha_EB, by simp⟩
        | @cons a c b e₀ hl rest ih =>
          obtain ⟨ha_not_rest, hrest_s⟩ := List.nodup_cons.mp hW₀s
          have hab : a ≠ b := fun h => ha_not_rest (h ▸ rest.end_mem_support)
          have ha_not_B0V : a ∉ (B ⟨0, hs⟩).V := fun hm => hab (hfirst a List.mem_cons_self hm)
          have hlΓ : Γ.toGraph.IsLink e₀ a c := ((hPraw_Γ i).isLink_iff hl.1).mp hl
          have he₀_not_B0E : e₀ ∉ (B ⟨0, hs⟩).E := by
            intro heB0
            have ha_cl : a ∈ closure e₀ ∩ Γ.V := ⟨by
              have : a ∈ closure e₀ ∩ (P_raw i).V := by rw [hl.2.2.2]; simp
              exact this.1, hlΓ.2.1⟩
            have : a ∈ closure e₀ ∩ (B ⟨0, hs⟩).V := by
              rwa [(hBΓ ⟨0, hs⟩).closure_inter_V heB0]
            exact ha_not_B0V this.2
          have ha_not_bd : a ∉ discBd (E_B ⟨0, hs⟩) := by
            rw [(hEB_spec ⟨0, hs⟩).2.2]
            intro haU
            obtain ⟨e', he', hae'⟩ := (B ⟨0, hs⟩).exists_edge_of_mem haU ha_not_B0V
            exact ((hΓ_sub.2 ((hBΓ ⟨0, hs⟩).2 he')).2.1 hae').2 (hΓ_sub.1 hlΓ.2.1)
          have ha_int : a ∈ discInt (E_B ⟨0, hs⟩) := ⟨ha_EB, ha_not_bd⟩
          have he₀_dis_bd : Disjoint e₀ (discBd (E_B ⟨0, hs⟩)) := by
            rw [(hEB_spec ⟨0, hs⟩).2.2]
            refine Set.disjoint_left.mpr fun p hpe hpU => ?_
            by_cases hpV : p ∈ (B ⟨0, hs⟩).V
            · exact ((hΓ_sub.2 hlΓ.1).2.1 hpe).2 ((hBD' ⟨0, hs⟩).1 hpV)
            · obtain ⟨e', he', hpe'⟩ := (B ⟨0, hs⟩).exists_edge_of_mem hpU hpV
              exact he₀_not_B0E (D'.edge_eq_of_mem (hΓ_sub.2 hlΓ.1)
                ((hBD' ⟨0, hs⟩).2 he') hpe hpe' ▸ he')
          have ha_cl : a ∈ closure e₀ := by
            have : a ∈ closure e₀ ∩ (P_raw i).V := by rw [hl.2.2.2]; simp
            exact this.1
          have hc_cl : c ∈ closure e₀ := by
            have : c ∈ closure e₀ ∩ (P_raw i).V := by rw [hl.2.2.2]; simp
            exact this.1
          have he₀_sub : e₀ ⊆ discInt (E_B ⟨0, hs⟩) := by
            rcases (hEB_spec ⟨0, hs⟩).2.1.side hman
              (hΓ_sub.2 hlΓ.1).2.2.1.isConnected.isPreconnected he₀_dis_bd with hin | hout
            · exact hin
            · exfalso
              obtain ⟨q, hq_in, hqe⟩ :=
                mem_closure_iff.mp ha_cl _ ((hEB_spec ⟨0, hs⟩).2.1.isOpen_discInt hman) ha_int
              exact Set.disjoint_left.mp hout hqe hq_in.1
          have hc_EB : c ∈ E_B ⟨0, hs⟩ :=
            closure_minimal (he₀_sub.trans (discInt_subset _)) (hEB_spec ⟨0, hs⟩).2.1.isClosed hc_cl
          obtain ⟨ih_sup, ih_ed⟩ := ih hrest_s hc_EB
            (fun z hz hm => hfirst z (List.mem_cons_of_mem _ hz) hm)
          refine ⟨fun z hz => ?_, fun e he => ?_⟩
          · rcases List.mem_cons.mp hz with rfl | hz'
            · exact ha_EB
            · exact ih_sup z hz'
          · rcases List.mem_cons.mp he with rfl | he'
            · exact he₀_not_B0E
            · exact ih_ed e he'
      obtain ⟨hW₁_in_EB0, hW₁_no_B0E⟩ := hW₁_stay W₁ hW₁s (hD₁_sub_EB0 (hu_raw i)) hu'_first
      -- Intersection preservation with all `B j`.
      have hinter_eq : ∀ j : Fin s, P'.V ∩ (B j).V = (P_raw i).V ∩ (B j).V ∧
          P'.E ∩ (B j).E = (P_raw i).E ∩ (B j).E := by
        intro j
        rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
        · have hj_eq : j = ⟨0, hs⟩ := Fin.ext hj0
          subst hj_eq
          refine ⟨subset_antisymm (inter_subset_inter_left _ hP'_Praw.1) ?_,
            subset_antisymm (inter_subset_inter_left _ hP'_Praw.2) ?_⟩
          · rintro z ⟨hzP, hzB⟩
            refine ⟨?_, hzB⟩
            rw [hP'_V]
            rw [hPraw_V] at hzP
            rcases (GraphWalk.mem_support_append _ _).mp hzP with hz₁ | hz₂
            · exact (hu'_first z hz₁ hzB) ▸ W₂.start_mem_support
            · exact hz₂
          · rintro e ⟨heP, heB⟩
            refine ⟨?_, heB⟩
            rw [hP'_E]
            rw [hPraw_E, GraphWalk.edges_append] at heP
            rcases List.mem_append.mp heP with he₁ | he₂
            · exact absurd heB (hW₁_no_B0E e he₁)
            · exact he₂
        · have hlt : (⟨0, hs⟩ : Fin s) < j := Fin.lt_def.mpr hjpos
          have hW₁_no_BjV : ∀ z ∈ W₁.support, z ∉ (B j).V := fun z hz hm =>
            (hEB_strict ⟨0, hs⟩ j hlt (hW₁_in_EB0 z hz)).2
              ((hEB_spec j).2.2 ▸ (B j).V_subset_U hm)
          refine ⟨subset_antisymm (inter_subset_inter_left _ hP'_Praw.1) ?_,
            subset_antisymm (inter_subset_inter_left _ hP'_Praw.2) ?_⟩
          · rintro z ⟨hzP, hzB⟩
            refine ⟨?_, hzB⟩
            rw [hP'_V]
            rw [hPraw_V] at hzP
            rcases (GraphWalk.mem_support_append _ _).mp hzP with hz₁ | hz₂
            · exact absurd hzB (hW₁_no_BjV z hz₁)
            · exact hz₂
          · rintro e ⟨heP, heB⟩
            refine ⟨?_, heB⟩
            rw [hP'_E]
            rw [hPraw_E, GraphWalk.edges_append] at heP
            rcases List.mem_append.mp heP with he₁ | he₂
            · exfalso
              obtain ⟨y, _, hl, hyW₁, _, _⟩ := exists_ne_link_of_mem_edges_simple hW₁s he₁
              have hyΓ : y ∈ closure e ∩ Γ.V := ⟨by
                have : y ∈ closure e ∩ (P_raw i).V := by rw [hl.2.2.2]; simp
                exact this.1, (hPraw_Γ i).1 hl.2.1⟩
              have hyBj : y ∈ closure e ∩ (B j).V := by rwa [(hBΓ j).closure_inter_V heB]
              exact hW₁_no_BjV y hyW₁ hyBj.2
            · exact he₂
      -- `P'.V ∩ F' = {v_raw i}` because `u' ∉ F'` and internal vertices of `W₂` have degree ≥ 2 in `Γ`.
      have hP'_VF' : P'.V ∩ F' = {v_raw i} := by
        ext z
        refine ⟨fun ⟨hzV, hzF⟩ => ?_, fun h => (mem_singleton_iff.mp h) ▸
          ⟨by rw [hP'_V]; exact W₂.end_mem_support, hv_F'⟩⟩
        rw [mem_singleton_iff]
        by_contra hzv
        have hzW₂ : z ∈ W₂.support := by rw [hP'_V] at hzV; exact hzV
        have hzu' : z ≠ u' := fun h => by
          subst h
          exact (hBU_in_DF ⟨0, hs⟩ ((B ⟨0, hs⟩).V_subset_U hu'_B0V)).2 (hDF_bd.symm ▸ hzF)
        obtain ⟨e₁, he₁W, e₂, he₂W, he₁₂, hcl₁, hcl₂⟩ :=
          exists_two_edges_of_internal_mem_simple hW₂s hzW₂ hzu' hzv
        have he₁Γ : e₁ ∈ Γ.E := hP'_Γ.2 (by rw [hP'_E]; exact he₁W)
        have he₂Γ : e₂ ∈ Γ.E := hP'_Γ.2 (by rw [hP'_E]; exact he₂W)
        obtain ⟨k, _, huniq_k⟩ := hΓV_F'_unique_edge z ⟨hP'_Γ.1 hzV, hzF⟩
        exact he₁₂ ((huniq_k e₁ he₁Γ hcl₁).trans (huniq_k e₂ he₂Γ hcl₂).symm)
      have hP'_enc : OArcEncloses Δ' F' P'.U :=
        (oArcEncloses_iff_subset hΔ' hD_F).mpr (hP'_Γ.U_subset.trans hΓU_DF)
      exact ⟨P', u', hP'_Praw, hP'_Γ, (B ⟨0, hs⟩).V_subset_U hu'_B0V, hv_F',
        hP'_path, hP'_enc, hP'_VF', hinter_eq⟩
    choose P' u' hP'_Praw hP'_Γ hu'_B0 hv_raw_F' hP'_path hP'_enc hP'_VF' hinter_eq using hex_spoke
    have hP'_D' : ∀ i, (P' i).IsSubdrawing D' := fun i => (hP'_Γ i).trans hΓ_sub
    have hP'_dis : Pairwise (fun i i' => Disjoint (P' i).V (P' i').V) := fun i i' hne =>
      ((hPu.2 hne).mono (hPraw_Pu i).1 (hPraw_Pu i').1).mono (hP'_Praw i).1 (hP'_Praw i').1
    -- Step 7: Assemble the `DrawingNest` and `SleeveData`.
    let circ_disc : Fin s → DiscCircuit D' Δ' := fun j => {
      U := (B j).U
      ins := E_B j
      U_sub_drawing := (hBD' j).U_subset
      U_sub_disc := (hEB_inside j).2.2.1 ▸ (Surface.discBd_subset _).trans (hEB_inside j).1
      isOArc_U := IsCircuit.isOArc_U (hBc j)
      isInside := hEB_inside j
    }
    let nest_out : DrawingNest D' Δ' r s := {
      circuit := circ_disc
      inside_of_lt := fun {j j'} hjj' x hx =>
        (insideOArc_iff_mem_discInt hΔ' (hEB_inside j')).mpr
          (hEB_strict j j' hjj' (Surface.discBd_subset _ ((hEB_spec j).2.2.symm ▸ hx)))
      radialPath := fun p => (P' p).U
      isPreconnected_radialPath := fun p => isPreconnected_U_of_isPathBetween (hP'_path p)
      radialPath_sub_U := fun p => (hP'_D' p).U_subset
      radialPath_sub_disc := fun p => (hP'_D' p).U_subset.trans hD'U
      pairwise_disjoint_paths := fun p p' hpp' => by
        refine Set.disjoint_left.mpr fun x ⟨hxp, hxV⟩ ⟨hxp', _⟩ => ?_
        have hxpV : x ∈ (P' p).V := by
          by_contra hnot
          obtain ⟨e, he, hxe⟩ := (P' p).exists_edge_of_mem hxp hnot
          exact (((hP'_D' p).2 he).2.1 hxe).2 hxV
        have hxp'V : x ∈ (P' p').V := by
          by_contra hnot
          obtain ⟨e, he, hxe⟩ := (P' p').exists_edge_of_mem hxp' hnot
          exact (((hP'_D' p').2 he).2.1 hxe).2 hxV
        exact Set.disjoint_left.mp (hP'_dis hpp') hxpV hxp'V
      meets_inner := fun p _ => by
        obtain ⟨W, _, hV, _⟩ := hP'_path p
        exact ⟨u' p, (P' p).V_subset_U (by rw [hV]; exact W.start_mem_support), hu'_B0 p⟩
      meets_outer := fun p hs' => by
        let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs' zero_lt_one⟩
        obtain ⟨x_hit, _, W_hit, _, hV_hit, _⟩ := hPraw_inf p j_last ▸ hinf_un (idx j_last) p
        have hx_mem : x_hit ∈ (P_raw p).V ∩ (B j_last).V := by
          rw [← Drawing.inf_V (hPraw_Γ p) (hBΓ j_last), hV_hit]
          exact W_hit.start_mem_support
        have hx_mem' : x_hit ∈ (P' p).V ∩ (B j_last).V := (hinter_eq p j_last).1.symm ▸ hx_mem
        exact ⟨x_hit, (P' p).V_subset_U hx_mem'.1, (B j_last).V_subset_U hx_mem'.2⟩
    }
    refine ⟨{
      nest := nest_out
      circuitDraw := B
      isCircuit_draw := fun j => ⟨hBD' j, hBc j, rfl⟩
      circuit_inside := fun j x hx =>
        (insideOArc_iff_mem_discInt hΔ' hD_F).mpr (hBU_in_DF j hx)
      spoke := P'
      isPath_spoke := fun i => ⟨hs, u' i, v_raw i, hP'_D' i, hu'_B0 i, hv_raw_F' i,
        hP'_path i, hP'_enc i, hP'_VF' i⟩
      pairwise_disjoint_spokes := hP'_dis
      inter_isPath := fun i j => by
        obtain ⟨a_ij, b_ij, hab_ij⟩ := hPraw_inf i j ▸ hinf_un (idx j) i
        refine ⟨Drawing.inf Γ (P_raw i) (B j), a_ij, b_ij,
          (Drawing.inf_isSubdrawing _ _ _).trans hΓ_sub, ?_, ?_, hab_ij⟩
        · rw [Drawing.inf_V (hPraw_Γ i) (hBΓ j), (hinter_eq i j).1]
        · rw [Drawing.inf_E (hPraw_Γ i), (hinter_eq i j).2]
    }⟩

/-- **(8.1)** *If $F$ is centred, there is a $(r, s)$-nest $(C_1, \dots, C_s)$ (where $r, s$ are as
above) such that each $C_i$ is inside $F$, and there are $r$ mutually disjoint paths $P_1, \dots, P_r$
of $\Gamma$ between $C_1$ and $F$, such that the intersection of each $P_i$ and each $C_j$ is a path.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_1_proof {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hc : IsCentredOArc D Δ F) :
    Nonempty (SleeveData D Δ F) := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
  have hD'U_sub : D'.U ⊆ f '' Δ := hD'U ▸ image_mono hDU
  have hc' : IsCentredOArc D' (f '' Δ) (f '' F) :=
    sc.push_isCentredOArc hΔ hDU hD'U hD'V hD'E hc
  obtain ⟨sd'⟩ := theorem_8_1_sphere hΔ' hD'U_sub sc.infty_notMem hc'
  exact ⟨sc.pullBackSleeveData hΔ hDU hD'U hD'V hD'E hc.1 hc.2.1 sd'⟩

/-- Construct a subdrawing `Γ'` of `D` (with `D.U ⊆ Δ` for a closed disc `Δ`) having prescribed
vertex set `V' ⊆ D.V` and edge set `E' ⊆ D.E` whenever `∀ e ∈ E', closure e ∩ D.V ⊆ V'`,
without requiring `[T1Space S]`. -/
theorem exists_span_subdrawing_in_disc {S : Type u} [TopologicalSpace S] {D : Drawing S}
    {Δ : Set S} (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    {V' : Set S} {E' : Set (Set S)} (hV' : V' ⊆ D.V) (hE' : E' ⊆ D.E)
    (hcl : ∀ e ∈ E', closure e ∩ D.V ⊆ V') :
    ∃ Γ' : Drawing S, Γ'.IsSubdrawing D ∧ Γ'.V = V' ∧ Γ'.E = E' := by
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, hcl_e, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  let V'' : Set SphereSurf := f '' V'
  let E'' : Set (Set SphereSurf) := image f '' E'
  have hV''_sub : V'' ⊆ D'.V := hD'V ▸ image_mono hV'
  have hE''_sub : E'' ⊆ D'.E := hD'E ▸ image_mono hE'
  let Γ'' : Drawing SphereSurf := D'.span V'' E''
  have hΓ''E : Γ''.E = E'' := by
    rw [D'.span_E]
    exact inter_eq_left.mpr hE''_sub
  have hΓ''V : Γ''.V = V'' := by
    apply subset_antisymm
    · rintro x' (⟨hx', _⟩ | hx')
      · exact hx'
      · obtain ⟨e', ⟨heE'', _⟩, hx'cl, hx'DV⟩ := mem_iUnion₂.mp hx'
        obtain ⟨e, heE', rfl⟩ := heE''
        obtain ⟨x, hxDV, rfl⟩ := hD'V ▸ hx'DV
        rw [hcl_e e (hE' heE')] at hx'cl
        obtain ⟨y, hycl, hfy⟩ := hx'cl
        have hyΔ : y ∈ Δ :=
          hDU (closure_minimal (fun z hz => ((hE' heE').2.1 hz).1) D.isClosed_U hycl)
        have hxΔ : x ∈ Δ := hDU (D.V_subset_U hxDV)
        obtain rfl := sc.injOn_f hyΔ hxΔ hfy
        exact mem_image_of_mem f (hcl e heE' ⟨hycl, hxDV⟩)
    · exact fun x' hx' => Or.inl ⟨hx', hV''_sub hx'⟩
  obtain ⟨Γ', hΓ'sub, _, hΓ'V, hΓ'E, _, _, _⟩ :=
    sc.exists_pullback_subdrawing hDU hD'U hD'V hD'E (D'.span_isSubdrawing V'' E'')
  refine ⟨Γ', hΓ'sub, ?_, ?_⟩
  · rw [hΓ'V, hΓ''V]
    exact sc.f'_f (hV'.trans (D.V_subset_U.trans hDU))
  · rw [hΓ'E, hΓ''E]
    ext e
    constructor
    · rintro ⟨_, ⟨e₀, he₀, rfl⟩, rfl⟩
      have he₀Δ : e₀ ⊆ Δ := fun z hz => hDU (((hE' he₀).2.1 hz).1)
      rwa [sc.f'_f he₀Δ]
    · intro he
      have heΔ : e ⊆ Δ := fun z hz => hDU (((hE' he).2.1 hz).1)
      exact ⟨f '' e, mem_image_of_mem _ he, sc.f'_f heΔ⟩

/-- Every centred `O`-arc `F` in `D` has a sleeve subdrawing `Γ'` (`IsSleeve D Δ F Γ'`). -/
theorem exists_isSleeve {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hc : IsCentredOArc D Δ F) :
    ∃ Γ' : Drawing S, IsSleeve D Δ F Γ' := by
  obtain ⟨sd⟩ := theorem_8_1_proof hΔ hDU hc
  let V' : Set S := (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V)
  let E' : Set (Set S) := (⋃ j, (sd.circuitDraw j).E) ∪ (⋃ i, (sd.spoke i).E)
  have hV'_sub : V' ⊆ D.V :=
    union_subset (iUnion_subset fun j => (sd.isCircuit_draw j).1.1)
      (iUnion_subset fun i => by obtain ⟨_, _, _, hsub, _⟩ := sd.isPath_spoke i; exact hsub.1)
  have hE'_sub : E' ⊆ D.E :=
    union_subset (iUnion_subset fun j => (sd.isCircuit_draw j).1.2)
      (iUnion_subset fun i => by obtain ⟨_, _, _, hsub, _⟩ := sd.isPath_spoke i; exact hsub.2)
  have hcl : ∀ e ∈ E', closure e ∩ D.V ⊆ V' := by
    rintro e (heC | heP) x ⟨hxe, hxDV⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp heC
      have : x ∈ closure e ∩ (sd.circuitDraw j).V := by
        rw [(sd.isCircuit_draw j).1.closure_inter_V hj]
        exact ⟨hxe, hxDV⟩
      exact Or.inl (mem_iUnion.mpr ⟨j, this.2⟩)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp heP
      obtain ⟨_, _, _, hsub, _⟩ := sd.isPath_spoke i
      have : x ∈ closure e ∩ (sd.spoke i).V := by
        rw [hsub.closure_inter_V hi]
        exact ⟨hxe, hxDV⟩
      exact Or.inr (mem_iUnion.mpr ⟨i, this.2⟩)
  obtain ⟨Γ', hΓ'sub, hΓ'V, hΓ'E⟩ :=
    exists_span_subdrawing_in_disc hΔ hDU hV'_sub hE'_sub hcl
  exact ⟨Γ', hc.1, hc.2.1, hc.2.2.1, hΓ'sub, sd, hΓ'V, hΓ'E⟩

end Theorem81

/-!
## 2. Proof of `(8.2)`: Every `C`-Ring of a Boss `C` Is Centred
-/

section Theorem82

/-- Sphere-model core of the nest-containment step of **(8.2)** (and reused in **(9.1)**):
Given an `(m, k)`-nest `N₁` in `D'` on `SphereSurf` (`OnePoint.infty ∉ Δ'`), and a `D'`-normal
`O`-arc `F' ⊆ Δ'` with `(D'.V ∩ F').ncard < m` that encloses `(N₁.circuit 0).U`, if `0 < k` and
`s ≤ k` satisfies `∀ j < s, (D'.V ∩ F').ncard < 1 + 2 * (k - 1 - j)`, then:
1. `(N₁.circuit j).U` is inside `F'` for all `j < s`, and
2. for every radial path `p` of `N₁` and every `j < k`, `N₁.radialPath p` meets `(N₁.circuit j).U`. -/
theorem nest_circuits_inside_oArc_sphere {D' : Drawing SphereSurf} {Δ' F' : Set SphereSurf}
    (hΔ' : IsClosedDisc Δ') (hinf_Δ : (OnePoint.infty : SphereSurf) ∉ Δ')
    (hF'Δ : F' ⊆ Δ') (hF'o : IsOArc F') (hF'norm : D'.IsNormal F')
    {m k : ℕ} (hk : 0 < k) (N₁ : DrawingNest D' Δ' m k)
    (henc₀ : OArcEncloses Δ' F' (N₁.circuit ⟨0, hk⟩).U)
    (hm_gt : (D'.V ∩ F').ncard < m) :
    (∀ (p : Fin m) (j : Fin k), (N₁.radialPath p ∩ (N₁.circuit j).U).Nonempty) ∧
      ∀ (j : Fin k), (D'.V ∩ F').ncard < 1 + 2 * (k - 1 - j.1) →
        SetInsideOArc Δ' F' (N₁.circuit j).U := by
  classical
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  obtain ⟨D_F, hD_F, _⟩ := disc_oArc Δ' F' hΔ' hF'Δ hF'o
  have hDF_disc : IsClosedDisc D_F := hD_F.2.1
  have hDF_bd : discBd D_F = F' := hD_F.2.2.1
  have hC0_sub_DF : (N₁.circuit ⟨0, hk⟩).U ⊆ D_F :=
    (oArcEncloses_iff_subset hΔ' hD_F).mp henc₀
  -- Strict nesting of `(N₁.circuit j).ins` in `SphereSurf`.
  let E : Fin k → Set SphereSurf := fun j => (N₁.circuit j).ins
  have hE_disc : ∀ j, IsClosedDisc (E j) := fun j => (N₁.circuit j).isInside.2.1
  have hE_bd : ∀ j, discBd (E j) = (N₁.circuit j).U := fun j => (N₁.circuit j).isInside.2.2.1
  have hE_strict : ∀ j j' : Fin k, j < j' → E j ⊆ discInt (E j') := by
    intro j j' hjj'
    have hbd_in : (N₁.circuit j).U ⊆ discInt (E j') := fun x hx =>
      (insideOArc_iff_mem_discInt hΔ' (N₁.circuit j').isInside).mp (N₁.inside_of_lt hjj' x hx)
    obtain ⟨D_out, hDout_bd⟩ :=
      GM12.isClosedDisc_closure_compl_of_sphere hS hsph (hE_disc j')
    set E_out := closure (univ \ E j')
    have hinf_not_j' : (OnePoint.infty : SphereSurf) ∉ E j' :=
      fun h => hinf_Δ ((N₁.circuit j').isInside.1 h)
    have hinf_not_j : (OnePoint.infty : SphereSurf) ∉ E j :=
      fun h => hinf_Δ ((N₁.circuit j).isInside.1 h)
    have hinf_int_out : (OnePoint.infty : SphereSurf) ∈ discInt E_out := by
      refine ⟨subset_closure ⟨mem_univ _, hinf_not_j'⟩, fun hbd => ?_⟩
      rw [hDout_bd] at hbd
      exact hinf_not_j' (Surface.discBd_subset _ hbd)
    have hdis_bd : Disjoint (discInt E_out) (discBd (E j)) := by
      rw [hE_bd j]
      refine Set.disjoint_left.mpr fun y hy_out hyN => ?_
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hy_out.1 _
        ((hE_disc j').isOpen_discInt hman) (hbd_in hyN)
      exact hz2.2 hz1.1
    have hsub_j' : E j ⊆ E j' := by
      intro z hz
      by_contra hznot
      have hz_out : z ∈ discInt E_out := by
        refine ⟨subset_closure ⟨mem_univ _, hznot⟩, fun hbd => ?_⟩
        rw [hDout_bd] at hbd
        exact hznot (Surface.discBd_subset _ hbd)
      rcases (hE_disc j).side hman D_out.isPreconnected_discInt hdis_bd with hin | hout
      · exact hinf_not_j (discInt_subset _ (hin hinf_int_out))
      · exact Set.disjoint_left.mp hout hz_out hz
    intro z hz
    by_cases hbd : z ∈ discBd (E j)
    · exact hbd_in (hE_bd j ▸ hbd)
    · refine ⟨hsub_j' hz, fun hbd' => ?_⟩
      have hz_front : z ∈ frontier (E j') := by
        rwa [IsClosedDisc.frontier_eq_discBd hS (hE_disc j')]
      exact hz_front.2 (mem_interior.mpr ⟨discInt (E j), (discInt_subset _).trans hsub_j',
        (hE_disc j).isOpen_discInt hman, ⟨hz, hbd⟩⟩)
  -- Every radial path `p` meets `(N₁.circuit j).U` for every `j : Fin k`.
  have hrad_meets : ∀ (p : Fin m) (j : Fin k), (N₁.radialPath p ∩ (N₁.circuit j).U).Nonempty := by
    intro p j
    rcases Nat.eq_zero_or_pos j.1 with hj0 | hjpos
    · have hj_eq : j = ⟨0, hk⟩ := Fin.ext hj0
      exact hj_eq ▸ N₁.meets_inner p hk
    · by_cases hjl : j.1 = k - 1
      · have hj_eq : j = ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩ := Fin.ext hjl
        exact hj_eq ▸ N₁.meets_outer p hk
      · have hj_lt_l : j < ⟨k - 1, Nat.sub_lt hk zero_lt_one⟩ :=
          Fin.lt_def.mpr (by have := j.2; dsimp; omega)
        have h0_lt_j : (⟨0, hk⟩ : Fin k) < j := Fin.lt_def.mpr hjpos
        obtain ⟨y_in, hy_rad, hy_C0⟩ := N₁.meets_inner p hk
        obtain ⟨y_out, hyo_rad, hyo_Cl⟩ := N₁.meets_outer p hk
        have hy_Ej : y_in ∈ discInt (E j) :=
          hE_strict ⟨0, hk⟩ j h0_lt_j (Surface.discBd_subset _ ((hE_bd ⟨0, hk⟩).symm ▸ hy_C0))
        have hyo_not_Ej : y_out ∉ E j := fun hm =>
          (hE_strict j _ hj_lt_l hm).2 ((hE_bd _).symm ▸ hyo_Cl)
        by_contra hemp
        have hdis : Disjoint (N₁.radialPath p) (discBd (E j)) := by
          rw [hE_bd j]
          exact Set.not_nonempty_iff_eq_empty.mp hemp |> Set.disjoint_iff_inter_eq_empty.mpr
        rcases (hE_disc j).side hman (N₁.isPreconnected_radialPath p) hdis with hin | hout
        · exact hyo_not_Ej (discInt_subset _ (hin hyo_rad))
        · exact Set.disjoint_left.mp hout hy_rad hy_Ej.1
  refine ⟨hrad_meets, ?_⟩
  -- Pigeonhole: one of the `m` radial paths is disjoint from `F'`.
  have hex_p₀ : ∃ p₀ : Fin m, Disjoint (N₁.radialPath p₀) F' := by
    by_contra! hall
    have hall' : ∀ p : Fin m, (N₁.radialPath p ∩ F').Nonempty :=
      fun p => Set.not_disjoint_iff.mp (hall p)
    choose x hx using hall'
    have hxVF : ∀ p, x p ∈ D'.V ∩ F' := fun p =>
      ⟨hF'norm ⟨(hx p).2, N₁.radialPath_sub_U p (hx p).1⟩, (hx p).2⟩
    have hx_inj : Function.Injective x := fun p q hpq => by
      by_contra hne
      exact Set.disjoint_left.mp (N₁.pairwise_disjoint_paths hne)
        ⟨(hx p).1, (hxVF p).1⟩ ⟨by rw [hpq]; exact (hx q).1, (hxVF p).1⟩
    have hcard_le : m ≤ (D'.V ∩ F').ncard := by
      have hsub : range x ⊆ D'.V ∩ F' := by rintro _ ⟨p, rfl⟩; exact hxVF p
      have hle := Set.ncard_le_ncard hsub (D'.finite_V.subset inter_subset_left)
      rwa [Set.ncard_range_of_injective hx_inj, Nat.card_fin] at hle
    omega
  obtain ⟨p₀, hp₀_dis⟩ := hex_p₀
  -- Since `radialPath p₀` meets `C_0 ⊆ D_F` and misses `F' = discBd D_F`, `radialPath p₀ ⊆ discInt D_F`.
  obtain ⟨y₀, hy₀_rad, hy₀_C0⟩ := N₁.meets_inner p₀ hk
  have hy₀_int : y₀ ∈ discInt D_F :=
    ⟨hC0_sub_DF hy₀_C0, hDF_bd ▸ fun hm => Set.disjoint_left.mp hp₀_dis hy₀_rad hm⟩
  have hp₀_in_DF : N₁.radialPath p₀ ⊆ discInt D_F := by
    have hdis_bd : Disjoint (N₁.radialPath p₀) (discBd D_F) := hDF_bd ▸ hp₀_dis
    rcases hDF_disc.side hman (N₁.isPreconnected_radialPath p₀) hdis_bd with hin | hout
    · exact hin
    · exact absurd hy₀_int.1 (Set.disjoint_left.mp hout hy₀_rad)
  -- Consequently, EVERY `(N₁.circuit j').U` (`j' : Fin k`) has a point in `discInt D_F`!
  have hCj_meets_int : ∀ j' : Fin k, ((N₁.circuit j').U ∩ discInt D_F).Nonempty := by
    intro j'
    obtain ⟨z, hz_rad, hz_Cj'⟩ := hrad_meets p₀ j'
    exact ⟨z, hz_Cj', hp₀_in_DF hz_rad⟩
  -- Now prove `SetInsideOArc Δ' F' (N₁.circuit j).U` when `(D'.V ∩ F').ncard < 1 + 2 * (k - 1 - j)`.
  intro j hj_arith
  by_contra hnot_in
  -- First, `(N₁.circuit j).U` meets `F'`.
  have hCj_meets_F' : ((N₁.circuit j).U ∩ F').Nonempty := by
    by_contra hemp
    have hdis_bd : Disjoint (N₁.circuit j).U (discBd D_F) := by
      rw [hDF_bd]
      exact Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hemp)
    have hCj_conn : IsPreconnected (N₁.circuit j).U := by
      obtain ⟨φ⟩ := (N₁.circuit j).isOArc_U
      have hrange : (N₁.circuit j).U = range (fun t : Circle => (φ t).1) := by
        ext z
        exact ⟨fun hz => ⟨φ.symm ⟨z, hz⟩, by simp⟩, fun ⟨t, ht⟩ => ht ▸ (φ t).2⟩
      rw [hrange]
      exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
    obtain ⟨w_in, hw_Cj, hw_int⟩ := hCj_meets_int j
    rcases hDF_disc.side hman hCj_conn hdis_bd with hin | hout
    · exact hnot_in fun x hx => (insideOArc_iff_mem_discInt hΔ' hD_F).mpr (hin hx)
    · exact Set.disjoint_left.mp hout hw_Cj hw_int.1
  obtain ⟨z_j, hzj_Cj, hzj_F'⟩ := hCj_meets_F'
  -- Second, for every `j' : Fin k` with `j < j'`, `2 ≤ ((N₁.circuit j').U ∩ F').ncard`.
  have htwo_hits : ∀ j' : Fin k, j < j' →
      ∃ a b : SphereSurf, a ∈ (N₁.circuit j').U ∩ F' ∧ b ∈ (N₁.circuit j').U ∩ F' ∧ a ≠ b := by
    intro j' hjj'
    have hfin_j' : ((N₁.circuit j').U ∩ F').Finite :=
      (D'.finite_V).subset fun x ⟨hxU, hxF⟩ => hF'norm ⟨hxF, (N₁.circuit j').U_sub_drawing hxU⟩
    by_cases hcard2 : 2 ≤ ((N₁.circuit j').U ∩ F').ncard
    · obtain ⟨a, ha⟩ := (Set.ncard_pos hfin_j').mp (by omega)
      have hex_b : ∃ b ∈ (N₁.circuit j').U ∩ F', a ≠ b := by
        by_contra! hall_eq
        have hsub1 : (N₁.circuit j').U ∩ F' ⊆ {a} :=
          fun b hb => mem_singleton_iff.mpr (hall_eq b hb).symm
        have hle1 : ((N₁.circuit j').U ∩ F').ncard ≤ 1 := by
          simpa using Set.ncard_le_ncard hsub1 (finite_singleton a)
        omega
      obtain ⟨b, hb, hab⟩ := hex_b
      exact ⟨a, b, ha, hb, hab⟩
    · exfalso
      have hle1 : ((N₁.circuit j').U ∩ F').ncard ≤ 1 := by omega
      have hconn_diff : IsPreconnected ((N₁.circuit j').U \ F') :=
        isPreconnected_oArc_sdiff_of_ncard_le_one (N₁.circuit j').isOArc_U hfin_j' hle1
      have hdis_diff : Disjoint ((N₁.circuit j').U \ F') (discBd D_F) := by
        rw [hDF_bd]
        exact disjoint_sdiff_left
      obtain ⟨w_in, hw_Cj', hw_int⟩ := hCj_meets_int j'
      have hw_diff : w_in ∈ (N₁.circuit j').U \ F' := ⟨hw_Cj', hDF_bd ▸ hw_int.2⟩
      have hdiff_sub : (N₁.circuit j').U \ F' ⊆ discInt D_F := by
        rcases hDF_disc.side hman hconn_diff hdis_diff with hin | hout
        · exact hin
        · exact absurd hw_int.1 (Set.disjoint_left.mp hout hw_diff)
      have hCj'_sub_DF : (N₁.circuit j').U ⊆ D_F := fun x hx => by
        by_cases hxF : x ∈ F'
        · exact Surface.discBd_subset D_F (hDF_bd.symm ▸ hxF)
        · exact discInt_subset _ (hdiff_sub ⟨hx, hxF⟩)
      -- Since `discBd (E j') = (N₁.circuit j').U ⊆ D_F` and `infty ∉ E j' ∪ D_F`, `E j' ⊆ D_F`.
      obtain ⟨D₂, hbd_D₂₀⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hDF_disc
      set E_out := closure (univ \ D_F)
      have hinf_not_DF : (OnePoint.infty : SphereSurf) ∉ D_F := fun h => hinf_Δ (hD_F.1 h)
      have hinf_not_Ej' : (OnePoint.infty : SphereSurf) ∉ E j' :=
        fun h => hinf_Δ ((N₁.circuit j').isInside.1 h)
      have hinf_int_out : (OnePoint.infty : SphereSurf) ∈ discInt E_out := by
        refine ⟨subset_closure ⟨mem_univ _, hinf_not_DF⟩, fun hbd => ?_⟩
        rw [hbd_D₂₀, hDF_bd] at hbd
        exact hinf_not_DF (Surface.discBd_subset D_F (hDF_bd.symm ▸ hbd))
      have hdis_Ej' : Disjoint (discInt E_out) (discBd (E j')) := by
        rw [hE_bd j']
        refine Set.disjoint_left.mpr fun y hy_out hyC => ?_
        have hyDF : y ∈ D_F := hCj'_sub_DF hyC
        by_cases hyF : y ∈ F'
        · exact hy_out.2 (by rwa [hbd_D₂₀, hDF_bd])
        · obtain ⟨z, hz1, hz2⟩ :=
            mem_closure_iff.mp hy_out.1 _ (hDF_disc.isOpen_discInt hman) ⟨hyDF, hDF_bd ▸ hyF⟩
          exact hz2.2 hz1.1
      have hEj'_sub_DF : E j' ⊆ D_F := by
        intro z hz
        by_contra hznot
        have hz_out : z ∈ discInt E_out := by
          refine ⟨subset_closure ⟨mem_univ _, hznot⟩, fun hbd => ?_⟩
          rw [hbd_D₂₀, hDF_bd] at hbd
          exact hznot (Surface.discBd_subset D_F (hDF_bd.symm ▸ hbd))
        rcases (hE_disc j').side hman D₂.isPreconnected_discInt hdis_Ej' with hin | hout
        · exact hinf_not_Ej' (discInt_subset _ (hin hinf_int_out))
        · exact Set.disjoint_left.mp hout hz_out hz
      -- Now `z_j ∈ (N₁.circuit j).U ⊆ discInt (E j') ⊆ interior D_F`, contradicting `z_j ∈ F'`.
      have hzj_int_Ej' : z_j ∈ discInt (E j') :=
        hE_strict j j' hjj' (Surface.discBd_subset _ ((hE_bd j).symm ▸ hzj_Cj))
      have hzj_front : z_j ∈ frontier D_F := by
        rwa [IsClosedDisc.frontier_eq_discBd hS hDF_disc, hDF_bd]
      exact hzj_front.2 (mem_interior.mpr ⟨discInt (E j'), (discInt_subset _).trans hEj'_sub_DF,
        (hE_disc j').isOpen_discInt hman, hzj_int_Ej'⟩)
  -- Pairwise disjointness of `(N₁.circuit a).U` across `a : Fin k`.
  have hC_disj : ∀ a b : Fin k, a ≠ b → Disjoint (N₁.circuit a).U (N₁.circuit b).U := by
    intro a b hab
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · exact Set.disjoint_left.mpr fun x hxa hxb =>
        (hE_strict a b hlt (Surface.discBd_subset _ ((hE_bd a).symm ▸ hxa))).2
          ((hE_bd b).symm ▸ hxb)
    · exact Set.disjoint_left.mpr fun x hxa hxb =>
        (hE_strict b a hgt (Surface.discBd_subset _ ((hE_bd b).symm ▸ hxb))).2
          ((hE_bd a).symm ▸ hxa)
  -- Inject `Fin (1 + 2 * (k - 1 - j.1))` into `D'.V ∩ F'`.
  let sh : Fin (k - 1 - j.1) → Fin k := fun m => ⟨j.1 + 1 + m.1, by have := m.2; have := j.2; omega⟩
  have hsh_gt : ∀ m, j < sh m := fun m => Fin.lt_def.mpr (by dsimp [sh]; omega)
  choose pt₁ pt₂ hpt₁ hpt₂ hpt_ne using fun m => htwo_hits (sh m) (hsh_gt m)
  let g : Fin (1 + 2 * (k - 1 - j.1)) → SphereSurf := fun idx_g =>
    if h0 : idx_g.1 = 0 then z_j
    else
      let t := idx_g.1 - 1
      let m : Fin (k - 1 - j.1) := ⟨t / 2, by have := idx_g.2; dsimp [t]; omega⟩
      if t % 2 = 0 then pt₁ m else pt₂ m
  have hg_mem_C : ∀ idx_g : Fin (1 + 2 * (k - 1 - j.1)),
      (idx_g.1 = 0 ∧ g idx_g ∈ (N₁.circuit j).U ∩ F') ∨
      (∃ hpos : 0 < idx_g.1,
        g idx_g ∈ (N₁.circuit (sh ⟨(idx_g.1 - 1) / 2, by have := idx_g.2; omega⟩)).U ∩ F') := by
    intro idx_g
    by_cases h0 : idx_g.1 = 0
    · refine Or.inl ⟨h0, ?_⟩
      dsimp only [g]
      split_ifs
      exact ⟨hzj_Cj, hzj_F'⟩
    · refine Or.inr ⟨Nat.pos_of_ne_zero h0, ?_⟩
      dsimp only [g]
      split_ifs
      · exact hpt₁ _
      · exact hpt₂ _
  have hg_VF : range g ⊆ D'.V ∩ F' := by
    rintro _ ⟨idx_g, rfl⟩
    rcases hg_mem_C idx_g with ⟨_, hmem⟩ | ⟨_, hmem⟩
    · exact ⟨hF'norm ⟨hmem.2, (N₁.circuit j).U_sub_drawing hmem.1⟩, hmem.2⟩
    · exact ⟨hF'norm ⟨hmem.2, (N₁.circuit _).U_sub_drawing hmem.1⟩, hmem.2⟩
  have hg_inj : Function.Injective g := by
    intro x y hxy
    have hx2 := x.2
    have hy2 := y.2
    apply Fin.ext
    rcases hg_mem_C x with ⟨hx0, hxmem⟩ | ⟨hxpos, hxmem⟩ <;>
      rcases hg_mem_C y with ⟨hy0, hymem⟩ | ⟨hypos, hymem⟩
    · omega
    · exfalso
      have hne_c : j ≠ sh ⟨(y.1 - 1) / 2, by omega⟩ := ne_of_lt (hsh_gt _)
      exact Set.disjoint_left.mp (hC_disj _ _ hne_c) hxmem.1 (hxy ▸ hymem.1)
    · exfalso
      have hne_c : sh ⟨(x.1 - 1) / 2, by omega⟩ ≠ j := ne_of_gt (hsh_gt _)
      exact Set.disjoint_left.mp (hC_disj _ _ hne_c) hxmem.1 (hxy ▸ hymem.1)
    · have hdiv_eq : (x.1 - 1) / 2 = (y.1 - 1) / 2 := by
        by_contra hdiv_ne
        have hsh_ne : sh ⟨(x.1 - 1) / 2, by omega⟩ ≠ sh ⟨(y.1 - 1) / 2, by omega⟩ := by
          intro he
          have := congrArg Fin.val he
          dsimp [sh] at this
          omega
        exact Set.disjoint_left.mp (hC_disj _ _ hsh_ne) hxmem.1 (hxy ▸ hymem.1)
      have hm_eq : (⟨(x.1 - 1) / 2, by omega⟩ : Fin (k - 1 - j.1)) = ⟨(y.1 - 1) / 2, by omega⟩ :=
        Fin.ext hdiv_eq
      dsimp only [g] at hxy
      split_ifs at hxy <;>
        first
        | omega
        | (rw [hm_eq] at hxy; exact absurd hxy (hpt_ne _))
        | (rw [hm_eq] at hxy; exact absurd hxy.symm (hpt_ne _))
  have hcard_ge : 1 + 2 * (k - 1 - j.1) ≤ (D'.V ∩ F').ncard := by
    have hle := Set.ncard_le_ncard hg_VF (D'.finite_V.subset inter_subset_left)
    rwa [Set.ncard_range_of_injective hg_inj, Nat.card_fin] at hle
  omega

/-- **(8.2)** *If $C$ is a boss of $\Gamma$ then every $C$-ring is centred.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_2_proof {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hprop : D.IsNormal (discBd Δ))
    {C : DiscCircuit D Δ} (hboss : IsBoss D Δ C) (hF : IsCRing C F) :
    IsCentredOArc D Δ F := by
  classical
  obtain ⟨hFΔ, hFo, hFnorm, henc_C, hcard_F⟩ := hF
  let k := (D.V ∩ discBd Δ).ncard
  let r := (D.V ∩ F).ncard
  let s := (r + 1) / 2
  have hr_eq : r = circuitRho C := hcard_F
  have hr_lt_k : r < k := hr_eq ▸ hboss.rho_lt
  have hk : 0 < k := by omega
  have hs_le_k : s ≤ k := by omega
  obtain ⟨N₁, hN₁0⟩ := hboss.exists_nest
  have hC0_eq : N₁.circuit ⟨0, hk⟩ = C := hN₁0 hk
  -- Transport `N₁` and `F` to `SphereSurf` to apply `nest_circuits_inside_oArc_sphere`.
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
  let N₁' : DrawingNest D' (f '' Δ) (1 + r) k :=
    sc.pushNest hΔ hDU hD'U hD'V
      (SphereDiscChart.reindexNest (by omega : 1 + circuitRho C = 1 + r) rfl N₁)
  have hF'Δ : f '' F ⊆ f '' Δ := image_mono hFΔ
  have hF'o : IsOArc (f '' F) := sc.oArc_f hFΔ hFo
  have hF'norm : D'.IsNormal (f '' F) := (sc.isNormal_f_iff hDU hD'U hD'V hFΔ).mpr hFnorm
  have hcard_F' : (D'.V ∩ f '' F).ncard = r := sc.ncard_V_inter_f hDU hD'V hFΔ
  have henc₀' : OArcEncloses (f '' Δ) (f '' F) (N₁'.circuit ⟨0, hk⟩).U := by
    have hU0 : (N₁'.circuit ⟨0, hk⟩).U = f '' C.U := by
      change f '' (N₁.circuit ⟨0, hk⟩).U = f '' C.U
      rw [hC0_eq]
    rw [hU0]
    exact (sc.oArcEncloses_f_iff hΔ hFΔ hFo C.U_sub_disc).mpr henc_C
  obtain ⟨hrad_meets', h_in'⟩ :=
    nest_circuits_inside_oArc_sphere hΔ' sc.infty_notMem hF'Δ hF'o hF'norm hk N₁' henc₀'
      (by omega : (D'.V ∩ f '' F).ncard < 1 + r)
  -- Pull back radial-path incidences and inside-`F` containment to `S`.
  have hrad_meets : ∀ (p : Fin r) (j : Fin k),
      (N₁.radialPath ⟨p.1, by omega⟩ ∩ (N₁.circuit j).U).Nonempty := by
    intro p j
    let p' : Fin (1 + r) := ⟨p.1, by omega⟩
    obtain ⟨z', hz'_rad, hz'_Cj⟩ := hrad_meets' p' j
    obtain ⟨x₁, hx₁_rad, rfl⟩ : z' ∈ f '' N₁.radialPath ⟨p.1, by omega⟩ := hz'_rad
    obtain ⟨x₂, hx₂_Cj, hfx⟩ : f x₁ ∈ f '' (N₁.circuit j).U := hz'_Cj
    have hx_eq : x₁ = x₂ :=
      (sc.injOn_f ((N₁.circuit j).U_sub_disc hx₂_Cj)
        (N₁.radialPath_sub_disc _ hx₁_rad) hfx).symm
    exact ⟨x₁, hx₁_rad, hx_eq ▸ hx₂_Cj⟩
  have h_in_F : ∀ j : Fin s,
      SetInsideOArc Δ F (N₁.circuit ⟨j.1, lt_of_lt_of_le j.2 hs_le_k⟩).U := by
    intro j
    let jk : Fin k := ⟨j.1, lt_of_lt_of_le j.2 hs_le_k⟩
    have harith : (D'.V ∩ f '' F).ncard < 1 + 2 * (k - 1 - jk.1) := by
      have hj_lt : j.1 < (r + 1) / 2 := j.2
      dsimp [jk]
      omega
    have hin_f : SetInsideOArc (f '' Δ) (f '' F) (f '' (N₁.circuit jk).U) := h_in' jk harith
    exact (sc.setInsideOArc_f_iff hΔ hFΔ hFo (N₁.circuit jk).U_sub_disc).mp hin_f
  -- Restrict `N₁` to an `(r, s)`-nest `N` inside `F`.
  let N : DrawingNest D Δ r s := {
    circuit := fun j => N₁.circuit ⟨j.1, lt_of_lt_of_le j.2 hs_le_k⟩
    inside_of_lt := fun {i j} hij => N₁.inside_of_lt (Fin.lt_def.mpr (Fin.lt_def.mp hij))
    radialPath := fun p => N₁.radialPath ⟨p.1, by omega⟩
    isPreconnected_radialPath := fun p => N₁.isPreconnected_radialPath _
    radialPath_sub_U := fun p => N₁.radialPath_sub_U _
    radialPath_sub_disc := fun p => N₁.radialPath_sub_disc _
    pairwise_disjoint_paths := fun p q hpq => by
      have hne : (⟨p.1, by omega⟩ : Fin (1 + circuitRho C)) ≠ ⟨q.1, by omega⟩ :=
        fun h => hpq (Fin.ext (Fin.mk.inj h))
      exact N₁.pairwise_disjoint_paths hne
    meets_inner := fun p hs' => hrad_meets p ⟨0, hk⟩
    meets_outer := fun p hs' =>
      hrad_meets p ⟨s - 1, lt_of_lt_of_le (Nat.sub_lt hs' zero_lt_one) hs_le_k⟩
  }
  -- Obtain `r` disjoint paths between `C` and `discBd Δ` by Menger (`circuitRho`), then trim at `F`.
  obtain ⟨P_bd, u_bd, v_bd, hP_bd, hP_bd_dis⟩ :=
    exists_disjoint_paths_of_circuitRho hΔ hDU hprop C hr_eq.le
  have hex_P : ∀ i : Fin r, ∃ (P_F : Drawing S) (hs' : 0 < s) (u v : S),
      P_F.IsSubdrawing (P_bd i) ∧ P_F.IsSubdrawing D ∧
      u ∈ (N.circuit ⟨0, hs'⟩).U ∧ v ∈ F ∧ P_F.IsPathBetween u v := by
    intro i
    have hr_pos : 0 < r := Nat.zero_lt_of_lt i.2
    have hs' : 0 < s := by omega
    obtain ⟨hP_sub, hu_C, hv_bd, hP_path⟩ := hP_bd i
    have hN0_eq : N.circuit ⟨0, hs'⟩ = C := hC0_eq
    have hu_in_F : InsideOArc Δ F (u_bd i) := h_in_F ⟨0, hs'⟩ (u_bd i) (hN0_eq.symm ▸ hu_C)
    obtain ⟨P_F, v'_i, hPF_sub, hPF_D, hv'_F, hPF_path⟩ :=
      exists_trimmed_spoke_to_enclosing hΔ hDU hFΔ hFo hFnorm hP_sub hu_in_F hv_bd hP_path
    exact ⟨P_F, hs', u_bd i, v'_i, hPF_sub, hPF_D, hN0_eq.symm ▸ hu_C, hv'_F, hPF_path⟩
  choose P_F hs_wit u_wit v_wit hPF_Pbd hPF_D hu_wit hv_wit hPF_path using hex_P
  refine ⟨hFΔ, hFo, hFnorm, N, h_in_F, P_F,
    fun i => ⟨hs_wit i, u_wit i, v_wit i, hPF_D i, hu_wit i, hv_wit i, hPF_path i⟩,
    fun i i' hne => (hP_bd_dis hne).mono (hPF_Pbd i).1 (hPF_Pbd i').1⟩

end Theorem82

end GM08
end GraphMinor
