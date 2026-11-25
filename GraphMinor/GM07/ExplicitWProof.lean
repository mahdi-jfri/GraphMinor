module

public import GraphMinor.GM07.ExplicitW
public import GraphMinor.GM07.Section3
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.LPPS22.StarForest

/-!
# Proof of `GraphMinor.GM07.WExplicitStatement`

This file proves `GraphMinor.GM07.wExplicitStatement_holds : WExplicitStatement`, giving the
explicit bound
$$w(\Sigma(a, b, c), k, n) \le 2k \cdot 3^{2n + 3(2a + b) + c + k} + k$$
for Graph Minors VII, (3.6) (`IsW36Bound`), following Lokshtanov, Pilipczuk, Pilipczuk, and
Saurabh (arXiv:2210.14629v1, Appendix A, Theorem A.2) and Geelen, Huynh, and Richter
(J. Combin. Theory Ser. B 132 (2018), Theorem 1.3).

Given a matching `G` with `|V(G)| ≤ 2n` and a forest `H` with `|V(H) ∩ bd(Σ)| ≤ k` in
`Σ = SurfaceModel a b c`:
- If `Y := V(H) ∩ bd(Σ) = ∅` (covering `c = 0` and `k = 0`), the empty drawing is homotopic
  (hence homoplastic) to `H` and has `0` crossings with `G`.
- Otherwise `Y.Nonempty` (so `1 ≤ c` and `1 ≤ k`):
  1. Surround `H` by a thick matching `G_surr` (`exists_marks`, `exists_thick_matching`) with
     pairwise disjoint component discs `c_disc y` (`y ∈ Y`).
  2. For each shared boundary point `y ∈ G.V ∩ Y` belonging to a multi-point disc `D`
     (`|Y ∩ D| ≥ 2`), detach `y` by excising a tiny boundary closed disc `D_y ⊆ D` meeting `G.U`
     only at `{y}` (`exists_shared_bd_half_disc`). Cutting off these discs preserves both the
     ambient surface model `S_sub ≃ₜ SurfaceModel a b c` and each multi-point disc
     `D_sub ≃ₜ SurfaceModel 0 0 1` (`cut_off_discs_model`).
  3. Inside each punctured disc `D_sub`, choose a hub `p_D ∈ discInt D_sub \ G.U` (using
     `dense_compl_iUnion_iArcs`), a small hub disc `Δ_D ⊆ discInt D_sub \ G.U`, and straight
     radial star arcs (`exists_star_in_disc`), extended by `seg_y ⊆ D_y` to `y` at shared points.
     The resulting star-forest `H₁` (`drawing_of_arcs`) is a proper forest
     (`isGraphForest_of_star_arcs`) strictly surrounded by `G_surr`, hence homotopic to `H` by
     `theorem_3_4_claim_2`.
  4. Excise the `p ≤ k` hub discs `Δ_D` from `S_sub` (`remove_discs_model`) to get
     `S_cut ≃ₜ SurfaceModel a b (c + p)`, apply `lpps22_lemma_A_3` to the `n' ≤ n` arcs of `G`
     and the `m ≤ k` truncated rays `L`, glue with the identity on `⋃ Δ_D` and `⋃ D_y`
     (`homeo_glue_id`) to get a boundary-fixing homeomorphism `φ : S ≃ₜ S`, and set
     `H' := mapDrawingHomeo φ H₁`. Then `H'` is homoplastic to `H`, and every point of
     `G.U ∩ H'.U` lies either in `⋃ r, ⋃ j, (φ '' L r ∩ G_arc j)` or in `G.V ∩ Y`, giving
     `|G.U ∩ H'.U| ≤ 2k · 3^(2n + 3(2a + b) + c + k) + k = wExplicit a b c k n`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Filter
open GraphMinor.Surface GraphMinor.GHR18 GraphMinor.LPPS22

/-! ### Helper lemmas -/

/-- The empty drawing on any topological space `S`. -/
private def wexpEmptyDrawing (S : Type) [TopologicalSpace S] : Drawing S where
  U := ∅
  V := ∅
  V_subset_U := Subset.rfl
  isClosed_U := isClosed_empty
  finite_V := finite_empty
  finite_edges := by
    have h : arcComponentsIn ((∅ : Set S) \ ∅) = ∅ := by
      ext C
      simp only [arcComponentsIn, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨x, hx⟩, hsub, -, -⟩
      exact (hsub hx).1
    rw [h]
    exact finite_empty
  edge_cond := by
    intro e he
    obtain ⟨x, hx⟩ := he.1
    exact (he.2.1 hx).1.elim

/-- `mapDrawingHomeo (Homeomorph.refl S) H = H`. -/
private theorem wexp_mapDrawingHomeo_refl {S : Type} [TopologicalSpace S] (H : Drawing S) :
    mapDrawingHomeo (Homeomorph.refl S) H = H := by
  cases H
  simp [mapDrawingHomeo]

/-- A closed disc `D` in a T2 space `S` is a compact connected surface homeomorphic to
`SurfaceModel 0 0 1`, with `bd D = Subtype.val ⁻¹' discBd D`. -/
private theorem isClosedDisc_surface_model {S : Type} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) :
    IsSurface D ∧ ConnectedSpace D ∧ Nonempty (D ≃ₜ SurfaceModel 0 0 1) ∧
      bd D = Subtype.val ⁻¹' discBd D := by
  obtain ⟨φ⟩ := id hD
  obtain ⟨eDisc⟩ := nonempty_disc_homeo
  let e : D ≃ₜ SurfaceModel 0 0 1 := φ.symm.trans eDisc.symm
  have hm := isSurface_model 0 0 1
  have : ConnectedSpace (SurfaceModel 0 0 1) := hm.2
  have hsurf : IsSurface D := isSurface_of_homeo e.symm hm.1
  have hconn : ConnectedSpace D := e.symm.surjective.connectedSpace e.symm.continuous
  have hbd : bd D = Subtype.val ⁻¹' discBd D := by
    ext x
    simp only [discBd, mem_preimage, mem_image]
    exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, he⟩ => Subtype.ext he ▸ hy⟩
  exact ⟨hsurf, hconn, ⟨e⟩, hbd⟩

/-- Finite union of `Fin r`-indexed sets has `ncard` at most the sum of `ncard`s. -/
private theorem ncard_iUnion_fin_le {α : Type*} :
    ∀ {r : ℕ} (F : Fin r → Set α), (⋃ i : Fin r, F i).ncard ≤ ∑ i : Fin r, (F i).ncard
  | 0, _ => by simp
  | r + 1, F => by
    have hun : (⋃ i : Fin (r + 1), F i) = F 0 ∪ ⋃ i : Fin r, F i.succ := by
      ext z; simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        exact Fin.cases (motive := fun i => z ∈ F i → _) (fun h => Or.inl h)
          (fun j h => Or.inr ⟨j, h⟩) i hi
      · rintro (h | ⟨j, hj⟩)
        · exact ⟨0, h⟩
        · exact ⟨j.succ, hj⟩
    rw [hun, Fin.sum_univ_succ]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (ncard_iUnion_fin_le (fun j => F j.succ)) _)

/-- Finite pairwise disjoint union of finite `Fin r`-indexed sets has `ncard` equal to the sum. -/
private theorem ncard_iUnion_fin_eq {α : Type*} :
    ∀ {r : ℕ} {F : Fin r → Set α},
      (∀ i, (F i).Finite) → (Pairwise fun i j => Disjoint (F i) (F j)) →
      (⋃ i : Fin r, F i).ncard = ∑ i : Fin r, (F i).ncard
  | 0, _, _, _ => by simp
  | r + 1, F, hfin, hdisj => by
    have hun : (⋃ i : Fin (r + 1), F i) = F 0 ∪ ⋃ i : Fin r, F i.succ := by
      ext z; simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        exact Fin.cases (motive := fun i => z ∈ F i → _) (fun h => Or.inl h)
          (fun j h => Or.inr ⟨j, h⟩) i hi
      · rintro (h | ⟨j, hj⟩)
        · exact ⟨0, h⟩
        · exact ⟨j.succ, hj⟩
    have hd0 : Disjoint (F 0) (⋃ i : Fin r, F i.succ) :=
      Set.disjoint_iUnion_right.mpr fun i => hdisj (Fin.succ_ne_zero i).symm
    have hfin_rest : (⋃ i : Fin r, F i.succ).Finite := Set.finite_iUnion fun i => hfin i.succ
    rw [hun, Fin.sum_univ_succ, Set.ncard_union_eq hd0 (hfin 0) hfin_rest,
      ncard_iUnion_fin_eq (fun i => hfin i.succ)
        (fun i j hij => hdisj (Fin.succ_injective r |>.ne hij))]

/-! ### Main Theorem: `WExplicitStatement` -/

/-- **Graph Minors VII, (3.6) with explicit LPPS22 bound**:
For every `a b c k n : ℕ`, `IsW36Bound (SurfaceModel a b c) k n (wExplicit a b c k n)`,
where `wExplicit a b c k n = 2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) + k`. -/
theorem wExplicitStatement_holds : WExplicitStatement := by
  classical
  intro a b c k n G H hG hGcard hH hHcard
  let S := SurfaceModel a b c
  have hS : IsSurface S := (isSurface_model a b c).1
  have hconnS : ConnectedSpace S := (isSurface_model a b c).2
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  let Y : Set S := H.V ∩ bd S
  have hYfin : Y.Finite := H.finite_V.subset inter_subset_left
  have hYbd : Y ⊆ bd S := inter_subset_right
  -- Case 1: `Y = ∅` (handles `c = 0` and `k = 0`).
  by_cases hYemp : Y = ∅
  · let H₀ : Drawing S := wexpEmptyDrawing S
    have hH₀_prop : H₀.IsProper := fun _ hx => hx.2.elim
    have hH₀_forest : IsGraphForest H₀.toGraph := by
      intro u W _
      cases W with
      | nil _ => rfl
      | cons hlink _ => exact hlink.2.1.elim
    have hhom : ForestsHomotopic H H₀ := by
      refine ⟨hH.1, hH₀_prop, hH.2, hH₀_forest, ?_, fun s hs => ?_⟩
      · change Y = ∅ ∩ bd S
        rw [hYemp, empty_inter]
      · have hs' : s ∈ Y := hs
        exact (hYemp ▸ hs').elim
    refine ⟨H₀, ⟨hH₀_prop, hH₀_forest⟩,
      ⟨Homeomorph.refl S, fun _ _ => rfl, by rwa [wexp_mapDrawingHomeo_refl]⟩, ?_, ?_⟩
    · have : G.U ∩ H₀.U = ∅ := inter_empty G.U
      rw [this]; exact finite_empty
    · have : G.U ∩ H₀.U = ∅ := inter_empty G.U
      rw [this, ncard_empty]; exact Nat.zero_le _
  -- Case 2: `Y.Nonempty` (so `1 ≤ c` and `1 ≤ k`).
  have hYne : Y.Nonempty := Set.nonempty_iff_ne_empty.mpr hYemp
  have hc_pos : 1 ≤ c := by
    obtain ⟨y₀, hy₀⟩ := hYne
    obtain ⟨-, f_m, hf_m⟩ := presents_ew a b c
    have hnc : (cuffs S).ncard = c := ncard_cuffs hf_m
    have hfin_c : (cuffs S).Finite := (cuff_statement.{0} S hS).2.1
    have hne_c : (cuffs S).Nonempty := ⟨connectedComponentIn (bd S) y₀, y₀, hYbd hy₀, rfl⟩
    have hpos : 0 < (cuffs S).ncard := (Set.ncard_pos hfin_c).mpr hne_c
    omega
  -- Step 1: Thick matching `G_surr` and component discs `c_disc` around `H`.
  obtain ⟨f_mark, ε_mark, hmarks, hmarks_disj⟩ := exists_marks hS hYbd hYfin
  obtain ⟨c_disc, σ₁, σ₂, G_surr, _, _, _, hGsurr_H, hdisc_prop, hdisc_disj, hdisc_int_bd,
    hGsurr_other⟩ := exists_thick_matching hS hH (Y := Y) rfl hmarks hmarks_disj
  have hO_ex : ∀ y : S, ∃ O : Set S, y ∈ Y → IsOpen O ∧ y ∈ O ∧ O \ bd S ⊆ discInt (c_disc y) := by
    intro y
    by_cases hy : y ∈ Y
    · obtain ⟨-, -, O, hO1, hO2, hO3⟩ := hdisc_prop y hy
      exact ⟨O, fun _ => ⟨hO1, hO2, hO3⟩⟩
    · exact ⟨∅, fun h => (hy h).elim⟩
  choose O_y hO_y using hO_ex
  have hO_sub : ∀ y ∈ Y, O_y y ⊆ c_disc y ∧ O_y y ∩ bd S ⊆ discBd (c_disc y) := fun y hy =>
    subset_disc_of_open_diff_bd hS (hO_y y hy).1 (hdisc_prop y hy).1 (hdisc_int_bd y hy) (hO_y y hy).2.2
  -- Step 2: Decompose matching `G` into `n' ≤ n` pairwise disjoint proper `I`-arcs.
  obtain ⟨n', hn', G_arc, hG_arc, hG_disj, hGU_eq, hGV_eq⟩ :=
    drawing_matching_to_family hS hG hGcard
  -- Step 3: Multi-point discs `P_set` (`|Y ∩ D| ≥ 2`), their boundary vertices `Y_in_P`, and shared points `Y_shared`.
  let P_set : Set (Set S) := {D | ∃ y ∈ Y, c_disc y = D ∧ 2 ≤ (Y ∩ D).ncard}
  have hP_fin : P_set.Finite :=
    (hYfin.image c_disc).subset fun D ⟨y, hy, hEq, _⟩ => ⟨y, hy, hEq⟩
  let p : ℕ := hP_fin.toFinset.card
  let eP : Fin p ≃ hP_fin.toFinset := (Finset.equivFin hP_fin.toFinset).symm
  let D_P : Fin p → Set S := fun l => (eP l).1
  have hD_P_mem : ∀ l, D_P l ∈ P_set := fun l => hP_fin.mem_toFinset.mp (eP l).2
  have hD_P_inj : Function.Injective D_P := fun l₁ l₂ h => eP.injective (Subtype.ext h)
  have hD_P_disc : ∀ l, IsClosedDisc (D_P l) := fun l => by
    obtain ⟨y, hy, hEq, _⟩ := hD_P_mem l; rw [← hEq]; exact (hdisc_prop y hy).1
  have hD_P_int_bd : ∀ l, Disjoint (discInt (D_P l)) (bd S) := fun l => by
    obtain ⟨y, hy, hEq, _⟩ := hD_P_mem l; rw [← hEq]; exact hdisc_int_bd y hy
  have hD_P_disj : Pairwise fun l₁ l₂ => Disjoint (D_P l₁) (D_P l₂) := fun l₁ l₂ hne => by
    obtain ⟨y₁, hy₁, hEq₁, _⟩ := hD_P_mem l₁
    obtain ⟨y₂, hy₂, hEq₂, _⟩ := hD_P_mem l₂
    rw [← hEq₁, ← hEq₂]
    exact hdisc_disj y₁ hy₁ y₂ hy₂ (by rw [hEq₁, hEq₂]; exact fun h => hne (hD_P_inj h))
  -- Count bound `2 * p ≤ Y.ncard ≤ k`, hence `p ≤ k`.
  have hp_le_k : p ≤ k := by
    have h2p : 2 * p ≤ k := by
      calc 2 * p = ∑ _l : Fin p, 2 := by simp [mul_comm]
        _ ≤ ∑ l : Fin p, (Y ∩ D_P l).ncard := Finset.sum_le_sum fun l _ => by
            obtain ⟨_, _, _, h2⟩ := hD_P_mem l; exact h2
        _ = (⋃ l : Fin p, (Y ∩ D_P l)).ncard := (ncard_iUnion_fin_eq
            (fun l => hYfin.subset inter_subset_left)
            (fun l₁ l₂ hne => (hD_P_disj hne).mono inter_subset_right inter_subset_right)).symm
        _ ≤ Y.ncard := Set.ncard_le_ncard (iUnion_subset fun _ => inter_subset_left) hYfin
        _ ≤ k := hHcard
    omega
  -- Enumerate `Y_in_P := {y ∈ Y | c_disc y ∈ P_set}` as `y_P : Fin m → S`.
  let Y_in_P : Set S := {y ∈ Y | c_disc y ∈ P_set}
  have hY_in_P_sub : Y_in_P ⊆ Y := fun _ h => h.1
  have hY_in_P_fin : Y_in_P.Finite := hYfin.subset hY_in_P_sub
  let m : ℕ := hY_in_P_fin.toFinset.card
  let eY_P : Fin m ≃ hY_in_P_fin.toFinset := (Finset.equivFin hY_in_P_fin.toFinset).symm
  let y_P : Fin m → S := fun r => (eY_P r).1
  have hy_P_mem : ∀ r, y_P r ∈ Y_in_P := fun r => hY_in_P_fin.mem_toFinset.mp (eY_P r).2
  have hy_P_Y : ∀ r, y_P r ∈ Y := fun r => (hy_P_mem r).1
  have hy_P_inj : Function.Injective y_P := fun r₁ r₂ h => eY_P.injective (Subtype.ext h)
  have hm_le_k : m ≤ k := by
    have hm_eq : m = Y_in_P.ncard := by
      change hY_in_P_fin.toFinset.card = Y_in_P.ncard
      rw [← ncard_coe_finset]; congr 1; ext x; exact hY_in_P_fin.mem_toFinset
    calc m = Y_in_P.ncard := hm_eq
      _ ≤ Y.ncard := Set.ncard_le_ncard hY_in_P_sub hYfin
      _ ≤ k := hHcard
  let compIdx : Fin m → Fin p := fun r => eP.symm ⟨c_disc (y_P r), hP_fin.mem_toFinset.mpr (hy_P_mem r).2⟩
  have hcompIdx_eq : ∀ r, D_P (compIdx r) = c_disc (y_P r) := fun r =>
    congrArg Subtype.val (eP.apply_symm_apply ⟨c_disc (y_P r), hP_fin.mem_toFinset.mpr (hy_P_mem r).2⟩)
  -- Enumerate `Y_shared := {y ∈ Y_in_P | y ∈ G.V}` as `y_sh : Fin q → S`.
  let Y_shared : Set S := {y ∈ Y_in_P | y ∈ G.V}
  have hY_sh_sub : Y_shared ⊆ Y_in_P := fun _ h => h.1
  have hY_sh_fin : Y_shared.Finite := hY_in_P_fin.subset hY_sh_sub
  let q : ℕ := hY_sh_fin.toFinset.card
  let eSh : Fin q ≃ hY_sh_fin.toFinset := (Finset.equivFin hY_sh_fin.toFinset).symm
  let y_sh : Fin q → S := fun i => (eSh i).1
  have hy_sh_mem : ∀ i, y_sh i ∈ Y_shared := fun i => hY_sh_fin.mem_toFinset.mp (eSh i).2
  have hy_sh_Y : ∀ i, y_sh i ∈ Y := fun i => (hy_sh_mem i).1.1
  have hy_sh_GV : ∀ i, y_sh i ∈ G.V := fun i => (hy_sh_mem i).2
  have hy_sh_inj : Function.Injective y_sh := fun i₁ i₂ h => eSh.injective (Subtype.ext h)
  -- For each `i : Fin q`, pick the unique `G_arc (j_sh i)` ending at `y_sh i` and its other end `other_sh i`.
  have hex_Garc_sh : ∀ i : Fin q, ∃ (j : Fin n') (t : S),
      y_sh i ≠ t ∧ IsLineWithEnds (G_arc j) (y_sh i) t ∧ G_arc j ∩ bd S = {y_sh i, t} := fun i => by
    have hmem : y_sh i ∈ ⋃ j, (G_arc j ∩ bd S) := hGV_eq ▸ hy_sh_GV i
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    obtain ⟨s, t, hst, hline, hbd⟩ := hG_arc j
    have hy_st : y_sh i ∈ ({s, t} : Set S) := hbd ▸ hj
    rcases hy_st with h1 | h2
    · exact ⟨j, t, h1 ▸ hst, h1 ▸ hline, by rw [hbd, h1]⟩
    · exact ⟨j, s, h2 ▸ hst.symm, h2 ▸ hline.symm, by rw [hbd, h2, pair_comm]⟩
  choose j_sh other_sh hsh_ne hsh_line hsh_bd using hex_Garc_sh
  -- Step 4: Detach each shared point `y_sh i` with a tiny boundary closed disc `D_sh i`.
  obtain ⟨U_sep, hU_sep, hU_sep_disj⟩ := hY_sh_fin.t2_separation
  have hex_half : ∀ i : Fin q,
      ∃ (D A seg : Set S) (t_D y_mid : S),
        IsClosedDisc D ∧
        D ⊆ U_sep (y_sh i) ∧ D ⊆ O_y (y_sh i) ∧
        D ∩ G.U = {y_sh i} ∧ D ∩ Y = {y_sh i} ∧
        A ⊆ discBd D ∧ y_sh i ≠ t_D ∧ IsLineWithEnds A (y_sh i) t_D ∧
        A ∩ bd S = {y_sh i, t_D} ∧ IsOpen (D \ A) ∧
        y_mid ∈ A \ {y_sh i, t_D} ∧
        IsLineWithEnds seg (y_sh i) y_mid ∧ seg ⊆ D ∧
        seg \ {y_sh i, y_mid} ⊆ discInt D ∧ Disjoint (discInt D) (bd S) := fun i => by
    let K_G : Set S := ⋃ j ∈ ({j : Fin n' | j ≠ j_sh i} : Set (Fin n')), G_arc j
    let K_Y : Set S := Y \ {y_sh i}
    have hKG_cl : IsClosed K_G :=
      Set.toFinite _ |>.isClosed_biUnion fun j _ => by
        obtain ⟨_, _, _, hl, _⟩ := hG_arc j; exact hl.isCompact.isClosed
    have hKY_cl : IsClosed K_Y := (hYfin.subset sdiff_subset).isClosed
    let W_i : Set S :=
      U_sep (y_sh i) ∩ O_y (y_sh i) ∩ K_Gᶜ ∩ K_Yᶜ ∩ ({other_sh i} : Set S)ᶜ
    have hWi_open : IsOpen W_i :=
      ((((hU_sep (y_sh i)).2.inter (hO_y (y_sh i) (hy_sh_Y i)).1).inter
        hKG_cl.isOpen_compl).inter hKY_cl.isOpen_compl).inter isClosed_singleton.isOpen_compl
    have hyi_Wi : y_sh i ∈ W_i := by
      refine ⟨⟨⟨⟨(hU_sep (y_sh i)).1, (hO_y (y_sh i) (hy_sh_Y i)).2.1⟩, ?_⟩, ?_⟩, hsh_ne i⟩
      · intro hmem
        obtain ⟨j, hji, hj⟩ := mem_iUnion₂.mp hmem
        have hy_jsh : y_sh i ∈ G_arc (j_sh i) := (show y_sh i ∈ G_arc (j_sh i) ∩ bd S from
          hsh_bd i ▸ Or.inl rfl).1
        exact Set.disjoint_left.mp (hG_disj hji) hj hy_jsh
      · intro h; exact h.2 rfl
    have hoth_Wi : other_sh i ∉ W_i := fun h => h.2 rfl
    obtain ⟨D, A, seg, t_D, y_mid, hD, hD_W, hD_F, hA_bdD, hstD, hA_line, hA_bdS, hDA_open,
      hymid, hseg_line, hseg_D, hseg_int, hDint_bd⟩ :=
      exists_shared_bd_half_disc hS (hsh_ne i) (hsh_bd i) (hsh_line i) hWi_open hyi_Wi hoth_Wi
    have hD_GU : D ∩ G.U = {y_sh i} := by
      rw [hGU_eq]
      ext z
      simp only [mem_inter_iff, mem_iUnion, mem_singleton_iff]
      constructor
      · rintro ⟨hzD, j, hzj⟩
        by_cases hj : j = j_sh i
        · subst hj
          have : z ∈ ({y_sh i} : Set S) := hD_F ▸ ⟨hzD, hzj⟩
          exact this
        · exact ((hD_W hzD).1.1.2 (mem_iUnion₂.mpr ⟨j, hj, hzj⟩)).elim
      · rintro rfl
        have hmem : y_sh i ∈ D ∩ G_arc (j_sh i) := hD_F.symm ▸ rfl
        exact ⟨hmem.1, j_sh i, hmem.2⟩
    have hD_Y : D ∩ Y = {y_sh i} := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hzD, hzY⟩
        by_contra hne
        exact (hD_W hzD).1.2 ⟨hzY, hne⟩
      · rintro rfl
        exact ⟨(show y_sh i ∈ D ∩ G_arc (j_sh i) from hD_F.symm ▸ rfl).1, hy_sh_Y i⟩
    exact ⟨D, A, seg, t_D, y_mid, hD, fun z hz => (hD_W hz).1.1.1.1, fun z hz => (hD_W hz).1.1.1.2,
      hD_GU, hD_Y, hA_bdD, hstD, hA_line, hA_bdS, hDA_open, hymid, hseg_line, hseg_D, hseg_int, hDint_bd⟩
  choose D_sh A_sh seg_sh t_sh y_mid hD_sh hD_sh_U hD_sh_O hD_sh_GU hD_sh_Y hA_sh_bdD hst_sh
    hA_sh_line hA_sh_bdS hDA_sh_open hymid_A hseg_sh_line hseg_sh_D hseg_sh_int hDint_sh_bd using hex_half
  have hD_sh_disj : Pairwise fun i₁ i₂ => Disjoint (D_sh i₁) (D_sh i₂) := fun i₁ i₂ hne =>
    (hU_sep_disj (hy_sh_mem i₁) (hy_sh_mem i₂) (fun h => hne (hy_sh_inj h))).mono
      (hD_sh_U i₁) (hD_sh_U i₂)
  have hD_sh_in_c : ∀ i, D_sh i ⊆ c_disc (y_sh i) := fun i =>
    (hD_sh_O i).trans (hO_sub (y_sh i) (hy_sh_Y i)).1
  have hymid_nbd : ∀ i, y_mid i ∉ bd S := fun i hbd => by
    have : y_mid i ∈ ({y_sh i, t_sh i} : Set S) := hA_sh_bdS i ▸ ⟨(hymid_A i).1, hbd⟩
    exact (hymid_A i).2 this
  have hymid_in_intc : ∀ i, y_mid i ∈ discInt (c_disc (y_sh i)) := fun i =>
    (hO_y (y_sh i) (hy_sh_Y i)).2.2 ⟨hD_sh_O i ((hA_sh_bdD i).trans (discBd_subset _) (hymid_A i).1),
      hymid_nbd i⟩
  -- Step 5: Cut off `D_sh` from `S` → `S_sub ≃ₜ SurfaceModel a b c`.
  obtain ⟨hcl_sub, hsurf_sub, hconn_sub, hbd_sub, ⟨e_sub_model⟩⟩ :=
    cut_off_discs_model hS (Homeomorph.refl S) hD_sh hD_sh_disj hA_sh_bdD hst_sh hA_sh_bdS
      hA_sh_line hDA_sh_open
  let S_sub := ↥(⋃ i : Fin q, D_sh i \ A_sh i)ᶜ
  -- Step 6: For each multi-point disc `l : Fin p`, cut off the shared half-discs inside `D_P l`
  -- to get `D_sub l ⊆ D_P l`, pick a hub `p_hub l ∈ discInt (D_sub l) \ G.U`, and build its star!
  -- First prove the disc-cutting helper for each `l : Fin p`.
  have hD_sub_ex : ∀ l : Fin p,
      let I_l : Set (Fin q) := {i : Fin q | c_disc (y_sh i) = D_P l}
      ∃ D_sub : Set S,
        IsClosedDisc D_sub ∧
        D_sub = D_P l \ ⋃ i ∈ I_l, (D_sh i \ A_sh i) ∧
        discBd D_sub = (discBd (D_P l) \ ⋃ i ∈ I_l, (D_sh i \ A_sh i)) ∪ ⋃ i ∈ I_l, A_sh i ∧
        discInt D_sub = discInt (D_P l) \ ⋃ i ∈ I_l, D_sh i := by
    intro l I_l
    have hIl_fin : I_l.Finite := Set.toFinite I_l
    let ql : ℕ := hIl_fin.toFinset.card
    let eIl : Fin ql ≃ hIl_fin.toFinset := (Finset.equivFin hIl_fin.toFinset).symm
    let idx : Fin ql → Fin q := fun t => (eIl t).1
    have hidx_mem : ∀ t, c_disc (y_sh (idx t)) = D_P l := fun t => hIl_fin.mem_toFinset.mp (eIl t).2
    have hidx_inj : Function.Injective idx := fun t₁ t₂ h => eIl.injective (Subtype.ext h)
    obtain ⟨hDl_surf, hDl_conn, ⟨eDl⟩, hDl_bd⟩ := isClosedDisc_surface_model (hD_P_disc l)
    have hce_Dl : IsClosedEmbedding (Subtype.val : D_P l → S) :=
      (hD_P_disc l).isClosed.isClosedEmbedding_subtypeVal
    have hcDl : CompactSpace (D_P l) := hDl_surf.1
    have hneDl : Nonempty (D_P l) := hDl_conn.toNonempty
    have hDsh_sub_Dl : ∀ t, D_sh (idx t) ⊆ range (Subtype.val : D_P l → S) := fun t => by
      rw [Subtype.range_val, ← hidx_mem t]; exact hD_sh_in_c (idx t)
    have hDsh_pre : ∀ t, IsClosedDisc (Subtype.val ⁻¹' D_sh (idx t) : Set (D_P l)) ∧
        discBd (Subtype.val ⁻¹' D_sh (idx t) : Set (D_P l)) = Subtype.val ⁻¹' discBd (D_sh (idx t)) :=
      fun t => isClosedDisc_preimage hce_Dl (hD_sh (idx t)) (hDsh_sub_Dl t)
    let D_l : Fin ql → Set (D_P l) := fun t => Subtype.val ⁻¹' D_sh (idx t)
    let A_l : Fin ql → Set (D_P l) := fun t => Subtype.val ⁻¹' A_sh (idx t)
    have hs_in_Dl : ∀ t, y_sh (idx t) ∈ D_P l := fun t =>
      (hidx_mem t) ▸ hD_sh_in_c (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _)
        (show y_sh (idx t) ∈ A_sh (idx t) from (show y_sh (idx t) ∈ A_sh (idx t) ∩ bd S from
          hA_sh_bdS (idx t) ▸ Or.inl rfl).1))
    have ht_in_Dl : ∀ t, t_sh (idx t) ∈ D_P l := fun t =>
      (hidx_mem t) ▸ hD_sh_in_c (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _)
        (show t_sh (idx t) ∈ A_sh (idx t) from (show t_sh (idx t) ∈ A_sh (idx t) ∩ bd S from
          hA_sh_bdS (idx t) ▸ Or.inr rfl).1))
    let s_l : Fin ql → D_P l := fun t => ⟨y_sh (idx t), hs_in_Dl t⟩
    let t_l : Fin ql → D_P l := fun t => ⟨t_sh (idx t), ht_in_Dl t⟩
    have hAl_bd : ∀ t, A_l t ∩ bd (D_P l) = {s_l t, t_l t} := fun t => by
      rw [hDl_bd]
      ext x
      simp only [A_l, mem_inter_iff, mem_preimage, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨hxA, hxbdD⟩
        -- Since `x.1 ∈ A_sh (idx t) ⊆ O_y (y_sh (idx t))`, `x.1 ∈ discBd (D_P l) → x.1 ∈ bd S`!
        have hxO : x.1 ∈ O_y (y_sh (idx t)) :=
          hD_sh_O (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _) hxA)
        have hxbdS : x.1 ∈ bd S := by
          by_contra hnb
          have hint : x.1 ∈ discInt (D_P l) := by
            have h1 := (hO_y (y_sh (idx t)) (hy_sh_Y (idx t))).2.2 ⟨hxO, hnb⟩
            rwa [hidx_mem t] at h1
          exact hint.2 hxbdD
        have hst' : x.1 ∈ ({y_sh (idx t), t_sh (idx t)} : Set S) :=
          hA_sh_bdS (idx t) ▸ ⟨hxA, hxbdS⟩
        rcases hst' with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · intro h
        have hst' : x.1 ∈ ({y_sh (idx t), t_sh (idx t)} : Set S) := by
          rcases h with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        have hmem : x.1 ∈ A_sh (idx t) ∩ bd S := hA_sh_bdS (idx t) |>.symm ▸ hst'
        have hxO : x.1 ∈ O_y (y_sh (idx t)) :=
          hD_sh_O (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _) hmem.1)
        have hxbdD : x.1 ∈ discBd (D_P l) := by
          have h1 := (hO_sub (y_sh (idx t)) (hy_sh_Y (idx t))).2 ⟨hxO, hmem.2⟩
          rwa [hidx_mem t] at h1
        exact ⟨hmem.1, hxbdD⟩
    have hAl_line : ∀ t, IsLineWithEnds (A_l t) (s_l t) (t_l t) := fun t => by
      obtain ⟨f, hf0, hf1⟩ := hA_sh_line (idx t)
      have hf_in : ∀ u : unitInterval, (f u).1 ∈ D_P l := fun u =>
        (hidx_mem t) ▸ hD_sh_in_c (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _) (f u).2)
      let g : unitInterval ≃ₜ A_l t :=
        { toFun := fun u => ⟨⟨(f u).1, hf_in u⟩, (f u).2⟩
          invFun := fun x => f.symm ⟨x.1.1, x.2⟩
          left_inv := fun u => by simp
          right_inv := fun x => by ext; simp
          continuous_toFun := Continuous.subtype_mk
            (Continuous.subtype_mk (continuous_subtype_val.comp f.continuous) _) _
          continuous_invFun := f.symm.continuous.comp
            (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) }
      exact ⟨g, Subtype.ext hf0, Subtype.ext hf1⟩
    obtain ⟨hcl_Dl, hsurf_Dl, hconn_Dl, hbd_Dl, ⟨e_Dl_sub⟩⟩ :=
      cut_off_discs_model hDl_surf eDl (fun t => (hDsh_pre t).1)
        (fun t₁ t₂ hne => (hD_sh_disj (fun h => hne (hidx_inj h))).preimage Subtype.val)
        (fun t => by rw [(hDsh_pre t).2]; exact preimage_mono (hA_sh_bdD (idx t)))
        (fun t h => hst_sh (idx t) (congrArg Subtype.val h))
        hAl_bd hAl_line (fun t => (hDA_sh_open (idx t)).preimage continuous_subtype_val)
    -- Push `↥(⋃ t, D_l t \ A_l t)ᶜ` back into `S` as a closed disc `D_sub`!
    let K_in_D : Set (D_P l) := (⋃ t : Fin ql, D_l t \ A_l t)ᶜ
    obtain ⟨eDisc0⟩ := nonempty_disc_homeo
    have hK_disc : IsClosedDisc K_in_D := ⟨eDisc0.symm.trans e_Dl_sub.symm⟩
    have hK_comp : IsCompact K_in_D := hcl_Dl.isCompact
    obtain ⟨hDsub_disc, hDsub_bd⟩ := isClosedDisc_image_injOn hK_disc hK_comp
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn
    let D_sub : Set S := Subtype.val '' K_in_D
    have hidx_iff : ∀ i : Fin q, i ∈ I_l ↔ ∃ t : Fin ql, idx t = i := fun i => by
      constructor
      · intro hi; exact ⟨eIl.symm ⟨i, hIl_fin.mem_toFinset.mpr hi⟩,
          congrArg Subtype.val (eIl.apply_symm_apply _)⟩
      · rintro ⟨t, rfl⟩; exact hidx_mem t
    have hDsub_eq : D_sub = D_P l \ ⋃ i ∈ I_l, (D_sh i \ A_sh i) := by
      ext z
      simp only [D_sub, K_in_D, mem_image, mem_compl_iff, mem_iUnion, not_exists, Set.mem_sdiff,
        D_l, A_l, mem_preimage]
      constructor
      · rintro ⟨⟨w, hw⟩, hnot, rfl⟩
        refine ⟨hw, fun i hi => ?_⟩
        obtain ⟨t, rfl⟩ := (hidx_iff i).mp hi
        exact hnot t
      · rintro ⟨hzD, hnot⟩
        refine ⟨⟨z, hzD⟩, fun t => hnot (idx t) (hidx_mem t), rfl⟩
    have hDsub_bd_eq : discBd D_sub =
        (discBd (D_P l) \ ⋃ i ∈ I_l, (D_sh i \ A_sh i)) ∪ ⋃ i ∈ I_l, A_sh i := by
      rw [hDsub_bd]
      have hKbd : discBd K_in_D = Subtype.val '' bd K_in_D := rfl
      rw [hKbd, hbd_Dl, hDl_bd]
      ext z
      simp only [mem_image, mem_preimage, mem_union, mem_iUnion, Set.mem_sdiff, A_l]
      constructor
      · rintro ⟨_, ⟨⟨⟨w, hw⟩, hwK⟩, hbdw, rfl⟩, rfl⟩
        rcases hbdw with hwbd | ⟨t, hwt⟩
        · left
          refine ⟨hwbd, ?_⟩
          rintro ⟨i, hi, hzi⟩
          obtain ⟨t, rfl⟩ := (hidx_iff i).mp hi
          exact hwK (mem_iUnion.mpr ⟨t, hzi⟩)
        · right
          exact ⟨idx t, hidx_mem t, hwt⟩
      · rintro (⟨hzbd, hnot⟩ | ⟨i, hi, hzA⟩)
        · have hzD : z ∈ D_P l := discBd_subset (D_P l) hzbd
          have hzK : (⟨z, hzD⟩ : D_P l) ∈ K_in_D := by
            intro hmem
            obtain ⟨t, ht⟩ := mem_iUnion.mp hmem
            exact hnot ⟨idx t, hidx_mem t, ht⟩
          exact ⟨⟨z, hzD⟩, ⟨⟨⟨z, hzD⟩, hzK⟩, Or.inl hzbd, rfl⟩, rfl⟩
        · obtain ⟨t, rfl⟩ := (hidx_iff i).mp hi
          have hzD : z ∈ D_P l :=
            (hidx_mem t) ▸ hD_sh_in_c (idx t) ((hA_sh_bdD (idx t)).trans (discBd_subset _) hzA)
          have hzK : (⟨z, hzD⟩ : D_P l) ∈ K_in_D := by
            intro hmem
            obtain ⟨t', ht'⟩ := mem_iUnion.mp hmem
            by_cases htt' : t' = t
            · subst htt'; exact ht'.2 hzA
            · exact Set.disjoint_left.mp (hD_sh_disj fun h => htt' (hidx_inj h)) ht'.1
                ((hA_sh_bdD (idx t)).trans (discBd_subset _) hzA)
          exact ⟨⟨z, hzD⟩, ⟨⟨⟨z, hzD⟩, hzK⟩, Or.inr ⟨t, hzA⟩, rfl⟩, rfl⟩
    have hDsub_int_eq : discInt D_sub = discInt (D_P l) \ ⋃ i ∈ I_l, D_sh i := by
      change D_sub \ discBd D_sub = (D_P l \ discBd (D_P l)) \ ⋃ i ∈ I_l, D_sh i
      rw [hDsub_bd_eq, hDsub_eq]
      ext z
      simp only [Set.mem_sdiff, mem_union, mem_iUnion, not_or, not_exists, not_and]
      constructor
      · rintro ⟨⟨hzD, hnot1⟩, hnot2, hnot3⟩
        exact ⟨⟨hzD, fun hzbd => hnot2 hzbd hnot1⟩, fun i hi hzDi => hnot1 i hi hzDi (hnot3 i hi)⟩
      · rintro ⟨⟨hzD, hznb⟩, hnotD⟩
        exact ⟨⟨hzD, fun i hi hzDi _ => hnotD i hi hzDi⟩, fun hzbd _ => hznb hzbd,
          fun i hi hzAi => hnotD i hi ((hA_sh_bdD i).trans (discBd_subset _) hzAi)⟩
    exact ⟨D_sub, hDsub_disc, hDsub_eq, hDsub_bd_eq, hDsub_int_eq⟩
  choose D_sub hD_sub_disc hD_sub_eq hD_sub_bd hD_sub_int using hD_sub_ex
  -- For each `r : Fin m`, define the target point `q_pt r ∈ discBd (D_sub (compIdx r))`!
  let shIdx : ∀ r : Fin m, y_P r ∈ G.V → Fin q := fun r hGV =>
    eSh.symm ⟨y_P r, hY_sh_fin.mem_toFinset.mpr ⟨hy_P_mem r, hGV⟩⟩
  have hshIdx_eq : ∀ (r : Fin m) (hGV : y_P r ∈ G.V), y_sh (shIdx r hGV) = y_P r := fun r hGV =>
    congrArg Subtype.val (eSh.apply_symm_apply _)
  let q_pt : Fin m → S := fun r =>
    if hGV : y_P r ∈ G.V then y_mid (shIdx r hGV) else y_P r
  have hq_pt_bd : ∀ r, q_pt r ∈ discBd (D_sub (compIdx r)) := fun r => by
    rw [hD_sub_bd (compIdx r)]
    dsimp only [q_pt]
    split_ifs with hGV
    · right
      refine mem_iUnion₂.mpr ⟨shIdx r hGV, ?_, (hymid_A _).1⟩
      show c_disc (y_sh (shIdx r hGV)) = D_P (compIdx r)
      rw [hshIdx_eq r hGV, hcompIdx_eq r]
    · left
      refine ⟨hcompIdx_eq r ▸ (hdisc_prop (y_P r) (hy_P_Y r)).2.1, ?_⟩
      intro hmem
      obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hmem
      have hy_eq : y_P r = y_sh i := by
        have hmem' : y_P r ∈ ({y_sh i} : Set S) := hD_sh_Y i ▸ ⟨hi.1, hy_P_Y r⟩
        exact hmem'
      exact hGV (hy_eq ▸ hy_sh_GV i)
  have hq_pt_inj : Function.Injective q_pt := fun r₁ r₂ heq => by
    dsimp only [q_pt] at heq
    by_cases h1 : y_P r₁ ∈ G.V <;> by_cases h2 : y_P r₂ ∈ G.V <;> simp only [h1, h2, ↓reduceDIte] at heq
    · -- Both shared: `y_mid i₁ = y_mid i₂` → `D_sh i₁` meets `D_sh i₂` → `i₁ = i₂`!
      have hi12 : shIdx r₁ h1 = shIdx r₂ h2 := by
        by_contra hne
        have hm1 : y_mid (shIdx r₁ h1) ∈ D_sh (shIdx r₁ h1) :=
          (hA_sh_bdD _).trans (discBd_subset _) (hymid_A _).1
        have hm2 : y_mid (shIdx r₂ h2) ∈ D_sh (shIdx r₂ h2) :=
          (hA_sh_bdD _).trans (discBd_subset _) (hymid_A _).1
        exact Set.disjoint_left.mp (hD_sh_disj hne) hm1 (heq ▸ hm2)
      exact hy_P_inj (by rw [← hshIdx_eq r₁ h1, ← hshIdx_eq r₂ h2, hi12])
    · -- `y_mid i₁ = y_P r₂ ∈ bd S`: impossible since `y_mid i₁ ∉ bd S`!
      exact (hymid_nbd (shIdx r₁ h1) (heq ▸ hYbd (hy_P_Y r₂))).elim
    · exact (hymid_nbd (shIdx r₂ h2) (heq.symm ▸ hYbd (hy_P_Y r₁))).elim
    · exact hy_P_inj heq
  -- For each `l : Fin p`, pick `p_hub l ∈ discInt (D_sub l) \ G.U` and run `exists_star_in_disc`!
  have hG_dense : closure G.Uᶜ = univ := by
    rw [hGU_eq]; exact dense_compl_iUnion_iArcs hS hG_arc hG_disj
  have hstar_ex : ∀ l : Fin p,
      let R_l := {r : Fin m | compIdx r = l}
      ∃ (p_hub : S) (Δ : Set S) (R_in L ray : R_l → Set S) (u : R_l → S),
        p_hub ∈ discInt (D_sub l) ∧ p_hub ∉ G.U ∧
        IsClosedDisc Δ ∧ Δ ⊆ discInt (D_sub l) ∧ Disjoint Δ G.U ∧ p_hub ∈ discInt Δ ∧
        (∀ t, R_in t ⊆ Δ ∧ IsLineWithEnds (R_in t) p_hub (u t) ∧ R_in t ∩ discBd Δ = {u t}) ∧
        (∀ t, L t ⊆ D_sub l \ discInt Δ ∧ u t ≠ q_pt t.1 ∧ IsLineWithEnds (L t) (u t) (q_pt t.1) ∧
          L t ∩ (discBd (D_sub l) ∪ discBd Δ) = {u t, q_pt t.1}) ∧
        (∀ t, ray t = R_in t ∪ L t ∧ p_hub ≠ q_pt t.1 ∧ IsLineWithEnds (ray t) p_hub (q_pt t.1) ∧
          ray t ⊆ D_sub l ∧ ray t \ {q_pt t.1} ⊆ discInt (D_sub l)) ∧
        (Pairwise fun t₁ t₂ => ray t₁ ∩ ray t₂ = {p_hub}) ∧
        (Pairwise fun t₁ t₂ => Disjoint (L t₁) (L t₂)) := fun l => by
    have hDsub_int_open : IsOpen (discInt (D_sub l)) := (hD_sub_disc l).isOpen_discInt hS.2.2
    obtain ⟨z₀, hz₀⟩ := (hD_sub_disc l).nonempty_discInt
    have hz₀_cl : z₀ ∈ closure G.Uᶜ := hG_dense.symm ▸ mem_univ z₀
    obtain ⟨p_hub, hp_int, hp_nG⟩ := _root_.mem_closure_iff.mp hz₀_cl _ hDsub_int_open hz₀
    let R_l : Set (Fin m) := {r : Fin m | compIdx r = l}
    have hRl_fin : R_l.Finite := Set.toFinite R_l
    let ml : ℕ := hRl_fin.toFinset.card
    let eRl : Fin ml ≃ R_l :=
      (Finset.equivFin hRl_fin.toFinset).symm.trans
        { toFun := fun x => ⟨x.1, hRl_fin.mem_toFinset.mp x.2⟩
          invFun := fun x => ⟨x.1, hRl_fin.mem_toFinset.mpr x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    let q_l : Fin ml → S := fun a => q_pt (eRl a).1
    have hql_bd : ∀ a, q_l a ∈ discBd (D_sub l) := fun a => (eRl a).2 ▸ hq_pt_bd (eRl a).1
    have hql_inj : Function.Injective q_l := fun a₁ a₂ h => eRl.injective (Subtype.ext (hq_pt_inj h))
    obtain ⟨Δ, R_in', L', ray', u', hΔ, hΔ_sub, hΔ_G, hp_Δ, hR_p, hL_p, hray_p, hray_pw, hL_pw⟩ :=
      exists_star_in_disc (hD_sub_disc l) G.isClosed_U hp_int hp_nG hql_bd hql_inj
    refine ⟨p_hub, Δ, fun t => R_in' (eRl.symm t), fun t => L' (eRl.symm t),
      fun t => ray' (eRl.symm t), fun t => u' (eRl.symm t), hp_int, hp_nG,
      hΔ, hΔ_sub, hΔ_G, hp_Δ,
      fun t => hR_p (eRl.symm t),
      fun t => by simpa [q_l] using hL_p (eRl.symm t),
      fun t => by simpa [q_l] using hray_p (eRl.symm t),
      fun t₁ t₂ hne => hray_pw (eRl.symm.injective.ne hne),
      fun t₁ t₂ hne => hL_pw (eRl.symm.injective.ne hne)⟩
  choose p_hub Δ_hub R_in_l L_l ray_l u_l hp_int hp_nG hΔ_disc hΔ_sub_Dint hΔ_disj_G hp_in_Δint
    hR_in_prop hL_l_prop hray_l_prop hray_l_pw hL_l_pw using hstar_ex
  -- Global `Fin m`-indexed views of `R_in`, `L_arc`, `ray`, `u_pt`.
  let R_in : Fin m → Set S := fun r => R_in_l (compIdx r) ⟨r, rfl⟩
  let L_arc : Fin m → Set S := fun r => L_l (compIdx r) ⟨r, rfl⟩
  let ray : Fin m → Set S := fun r => ray_l (compIdx r) ⟨r, rfl⟩
  let u_pt : Fin m → S := fun r => u_l (compIdx r) ⟨r, rfl⟩
  -- Key inclusion/disjointness facts for `D_sub l`, `Δ_hub l`, `p_hub l`, `ray r`, `L_arc r`.
  have hDsub_sub_DP : ∀ l, D_sub l ⊆ D_P l := fun l => by rw [hD_sub_eq l]; exact sdiff_subset
  have hDsub_int_sub_DPint : ∀ l, discInt (D_sub l) ⊆ discInt (D_P l) := fun l => by
    rw [hD_sub_int l]; exact sdiff_subset
  have hDsub_int_disj_Dsh : ∀ l i, Disjoint (discInt (D_sub l)) (D_sh i) := fun l i => by
    by_cases hl : c_disc (y_sh i) = D_P l
    · rw [hD_sub_int l, Set.disjoint_left]
      intro z hz hzD
      exact hz.2 (mem_iUnion₂.mpr ⟨i, hl, hzD⟩)
    · have hc_eq : D_P (compIdx (eY_P.symm ⟨y_sh i, hY_in_P_fin.mem_toFinset.mpr (hy_sh_mem i).1⟩)) = c_disc (y_sh i) := by
        rw [hcompIdx_eq]
        exact congrArg (fun x => c_disc x.1) (eY_P.apply_symm_apply _)
      have hd : Disjoint (D_P (compIdx (eY_P.symm ⟨y_sh i, hY_in_P_fin.mem_toFinset.mpr (hy_sh_mem i).1⟩))) (D_P l) :=
        hD_P_disj fun h => hl (by rw [← h, hc_eq])
      rw [hc_eq] at hd
      exact hd.symm.mono ((hDsub_int_sub_DPint l).trans (discInt_subset _)) (hD_sh_in_c i)
  have hDsub_sub_Ssub : ∀ l, D_sub l ⊆ (⋃ i : Fin q, D_sh i \ A_sh i)ᶜ := fun l z hz hmem => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    by_cases hl : c_disc (y_sh i) = D_P l
    · rw [hD_sub_eq l] at hz
      exact hz.2 (mem_iUnion₂.mpr ⟨i, hl, hi⟩)
    · have hzDP : z ∈ D_P l := hDsub_sub_DP l hz
      have hzCi : z ∈ c_disc (y_sh i) := hD_sh_in_c i hi.1
      obtain ⟨y', hy', hEq', _⟩ := hD_P_mem l
      exact Set.disjoint_left.mp (hdisc_disj (y_sh i) (hy_sh_Y i) y' hy' (by rw [hEq']; exact hl))
        hzCi (hEq'.symm ▸ hzDP)
  have hΔ_disj_bd : ∀ l, Disjoint (Δ_hub l) (bd S) := fun l =>
    (hD_P_int_bd l).mono ((hΔ_sub_Dint l).trans (hDsub_int_sub_DPint l)) Subset.rfl
  have hΔ_disj_Dsh : ∀ l i, Disjoint (Δ_hub l) (D_sh i) := fun l i =>
    (hDsub_int_disj_Dsh l i).mono (hΔ_sub_Dint l) Subset.rfl
  have hΔ_disj_pw : Pairwise fun l₁ l₂ => Disjoint (Δ_hub l₁) (Δ_hub l₂) := fun l₁ l₂ hne =>
    (hD_P_disj hne).mono
      ((hΔ_sub_Dint l₁).trans ((hDsub_int_sub_DPint l₁).trans (discInt_subset _)))
      ((hΔ_sub_Dint l₂).trans ((hDsub_int_sub_DPint l₂).trans (discInt_subset _)))
  have hphub_nbd : ∀ l, p_hub l ∉ bd S := fun l hbd =>
    Set.disjoint_left.mp (hΔ_disj_bd l) (discInt_subset _ (hp_in_Δint l)) hbd
  have hphub_inj : Function.Injective p_hub := fun l₁ l₂ heq => by
    by_contra hne
    exact Set.disjoint_left.mp (hΔ_disj_pw hne) (discInt_subset _ (hp_in_Δint l₁))
      (heq ▸ discInt_subset _ (hp_in_Δint l₂))
  -- Step 7: Build the star-forest `H₁` via `drawing_of_arcs` and verify `ForestsHomotopic H H₁`!
  let E_arc : Fin m → Set S := fun r =>
    if hGV : y_P r ∈ G.V then ray r ∪ seg_sh (shIdx r hGV) else ray r
  have hE_line : ∀ r, IsLineWithEnds (E_arc r) (p_hub (compIdx r)) (y_P r) := fun r => by
    dsimp only [E_arc]
    split_ifs with hGV
    · have hray_l : IsLineWithEnds (ray r) (p_hub (compIdx r)) (y_mid (shIdx r hGV)) := by
        have h1 := (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.1
        simpa only [q_pt, hGV, ↓reduceDIte] using h1
      have hseg_l : IsLineWithEnds (seg_sh (shIdx r hGV)) (y_mid (shIdx r hGV)) (y_P r) := by
        rw [← hshIdx_eq r hGV]
        exact (hseg_sh_line (shIdx r hGV)).symm
      have hinter : ray r ∩ seg_sh (shIdx r hGV) = {y_mid (shIdx r hGV)} := by
        ext z
        simp only [mem_inter_iff, mem_singleton_iff]
        constructor
        · rintro ⟨hzr, hzs⟩
          by_contra hne
          have hzr_int : z ∈ discInt (D_sub (compIdx r)) := by
            have hsub := (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.2.2
            exact hsub ⟨hzr, by simpa only [q_pt, hGV, ↓reduceDIte, mem_singleton_iff] using hne⟩
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r) (shIdx r hGV))
            hzr_int (hseg_sh_D _ hzs)
        · rintro rfl
          refine ⟨?_, ?_⟩
          · obtain ⟨f, -, hf1⟩ := hray_l; exact hf1 ▸ (f 1).2
          · obtain ⟨f, hf0, -⟩ := hseg_l; exact hf0 ▸ (f 0).2
      exact hray_l.union hseg_l hinter
    · have h1 := (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.1
      simpa only [q_pt, hGV, ↓reduceDIte] using h1
  have hE_sub_DP : ∀ r, E_arc r ⊆ D_P (compIdx r) := fun r => by
    dsimp only [E_arc]
    split_ifs with hGV
    · refine union_subset ((hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.2.1.trans (hDsub_sub_DP _)) ?_
      have hc : c_disc (y_sh (shIdx r hGV)) = D_P (compIdx r) := by
        rw [hshIdx_eq r hGV, hcompIdx_eq r]
      exact (hseg_sh_D _).trans (hc ▸ hD_sh_in_c _)
    · exact (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.2.1.trans (hDsub_sub_DP _)
  have hE_diff_nbd : ∀ r, E_arc r \ {y_P r} ⊆ discInt (D_P (compIdx r)) := fun r z ⟨hzE, hzne⟩ => by
    dsimp only [E_arc] at hzE
    split_ifs at hzE with hGV
    · rcases hzE with hzr | hzs
      · by_cases hzm : z = y_mid (shIdx r hGV)
        · subst hzm
          have hc : c_disc (y_sh (shIdx r hGV)) = D_P (compIdx r) := by
            rw [hshIdx_eq r hGV, hcompIdx_eq r]
          exact hc ▸ hymid_in_intc (shIdx r hGV)
        · have hsub := (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.2.2
          exact hDsub_int_sub_DPint _ (hsub ⟨hzr, by simpa only [q_pt, hGV, ↓reduceDIte, mem_singleton_iff] using hzm⟩)
      · by_cases hzm : z = y_mid (shIdx r hGV)
        · subst hzm
          have hc : c_disc (y_sh (shIdx r hGV)) = D_P (compIdx r) := by
            rw [hshIdx_eq r hGV, hcompIdx_eq r]
          exact hc ▸ hymid_in_intc (shIdx r hGV)
        · have hz_intD : z ∈ discInt (D_sh (shIdx r hGV)) :=
            hseg_sh_int (shIdx r hGV) ⟨hzs, by
              rintro (h | h)
              · exact hzne (h.trans (hshIdx_eq r hGV))
              · exact hzm h⟩
          have hz_nbd : z ∉ bd S := fun h => Set.disjoint_left.mp (hDint_sh_bd _) hz_intD h
          have hc : c_disc (y_sh (shIdx r hGV)) = D_P (compIdx r) := by
            rw [hshIdx_eq r hGV, hcompIdx_eq r]
          exact hc ▸ (hO_y _ (hy_sh_Y _)).2.2 ⟨hD_sh_O _ (discInt_subset _ hz_intD), hz_nbd⟩
    · have hsub := (hray_l_prop (compIdx r) ⟨r, rfl⟩).2.2.2.2
      exact hDsub_int_sub_DPint _ (hsub ⟨hzE, by simpa only [q_pt, hGV, ↓reduceDIte] using hzne⟩)
  let V₁ : Set S := Y ∪ range p_hub
  have hV₁_fin : V₁.Finite := hYfin.union (Set.finite_range p_hub)
  let a_end : Fin m → S := fun r => p_hub (compIdx r)
  let b_end : Fin m → S := y_P
  have hab_ne : ∀ r, a_end r ≠ b_end r := fun r h =>
    hphub_nbd (compIdx r) (by change a_end r ∈ bd S; rw [h]; exact hYbd (hy_P_Y r))
  have haV₁ : ∀ r, a_end r ∈ V₁ := fun r => Or.inr ⟨compIdx r, rfl⟩
  have hbV₁ : ∀ r, b_end r ∈ V₁ := fun r => Or.inl (hy_P_Y r)
  have hE_capV₁ : ∀ r, E_arc r ∩ V₁ = {a_end r, b_end r} := fun r => by
    ext z
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hzE, hzY | ⟨l, rfl⟩⟩
      · right
        by_contra hne
        have hz_int := hE_diff_nbd r ⟨hzE, hne⟩
        exact Set.disjoint_left.mp (hD_P_int_bd (compIdx r)) hz_int (hYbd hzY)
      · left
        have hl_eq : l = compIdx r := by
          by_contra hne
          exact Set.disjoint_left.mp (hD_P_disj hne)
            (hDsub_sub_DP l (discInt_subset _ (hp_int l))) (hE_sub_DP r hzE)
        subst hl_eq; rfl
    · rintro (rfl | rfl)
      · refine ⟨?_, haV₁ r⟩
        obtain ⟨f, hf0, -⟩ := hE_line r
        show p_hub (compIdx r) ∈ E_arc r
        rw [← hf0]; exact (f 0).2
      · refine ⟨?_, hbV₁ r⟩
        obtain ⟨f, -, hf1⟩ := hE_line r
        show y_P r ∈ E_arc r
        rw [← hf1]; exact (f 1).2
  have hray_pw_global : ∀ r₁ r₂ : Fin m, r₁ ≠ r₂ → compIdx r₁ = compIdx r₂ →
      ray r₁ ∩ ray r₂ = {p_hub (compIdx r₁)} := by
    intro r₁ r₂ hne hcomp
    have hsub : ∀ {l₁ l₂ : Fin p} (he : l₁ = l₂) (t : {r : Fin m | compIdx r = l₂}),
        ray_l l₁ ⟨t.1, t.2.trans he.symm⟩ = ray_l l₂ t := by rintro l _ rfl _; rfl
    have hpw : ray_l (compIdx r₁) ⟨r₁, rfl⟩ ∩ ray_l (compIdx r₁) ⟨r₂, hcomp.symm⟩ =
        {p_hub (compIdx r₁)} := hray_l_pw (compIdx r₁) fun h => hne (congrArg Subtype.val h)
    simpa only [ray, hsub hcomp ⟨r₂, rfl⟩] using hpw
  have hL_pw_global : ∀ r₁ r₂ : Fin m, r₁ ≠ r₂ → compIdx r₁ = compIdx r₂ →
      Disjoint (L_arc r₁) (L_arc r₂) := by
    intro r₁ r₂ hne hcomp
    have hsub : ∀ {l₁ l₂ : Fin p} (he : l₁ = l₂) (t : {r : Fin m | compIdx r = l₂}),
        L_l l₁ ⟨t.1, t.2.trans he.symm⟩ = L_l l₂ t := by rintro l _ rfl _; rfl
    have hpw : Disjoint (L_l (compIdx r₁) ⟨r₁, rfl⟩) (L_l (compIdx r₁) ⟨r₂, hcomp.symm⟩) :=
      hL_l_pw (compIdx r₁) fun h => hne (congrArg Subtype.val h)
    simpa only [L_arc, hsub hcomp ⟨r₂, rfl⟩] using hpw
  have hE_disj : Pairwise fun r₁ r₂ => Disjoint (E_arc r₁ \ {a_end r₁, b_end r₁}) (E_arc r₂ \ {a_end r₂, b_end r₂}) := by
    intro r₁ r₂ hne
    rw [Set.disjoint_left]
    intro z ⟨hz1, hz1_ne⟩ ⟨hz2, hz2_ne⟩
    by_cases hcomp : compIdx r₁ = compIdx r₂
    · dsimp only [E_arc] at hz1 hz2
      split_ifs at hz1 with h1 <;> split_ifs at hz2 with h2
      · rcases hz1 with h1r | h1s <;> rcases hz2 with h2r | h2s
        · have heq_p : z = p_hub (compIdx r₁) := by
            have : z ∈ ({p_hub (compIdx r₁)} : Set S) := hray_pw_global r₁ r₂ hne hcomp ▸ ⟨h1r, h2r⟩
            exact this
          exact hz1_ne (Or.inl heq_p)
        · have hzm : z ≠ y_mid (shIdx r₁ h1) := fun h => by
            have hi_ne : shIdx r₁ h1 ≠ shIdx r₂ h2 := fun he =>
              hne (hy_P_inj (by rw [← hshIdx_eq r₁ h1, ← hshIdx_eq r₂ h2, he]))
            exact Set.disjoint_left.mp (hD_sh_disj hi_ne)
              ((hA_sh_bdD _).trans (discBd_subset _) (hymid_A _).1) (h ▸ hseg_sh_D _ h2s)
          have hz_int : z ∈ discInt (D_sub (compIdx r₁)) :=
            (hray_l_prop (compIdx r₁) ⟨r₁, rfl⟩).2.2.2.2
              ⟨h1r, by simpa only [q_pt, h1, ↓reduceDIte, mem_singleton_iff] using hzm⟩
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r₁) (shIdx r₂ h2)) hz_int (hseg_sh_D _ h2s)
        · have hzm : z ≠ y_mid (shIdx r₂ h2) := fun h => by
            have hi_ne : shIdx r₁ h1 ≠ shIdx r₂ h2 := fun he =>
              hne (hy_P_inj (by rw [← hshIdx_eq r₁ h1, ← hshIdx_eq r₂ h2, he]))
            exact Set.disjoint_left.mp (hD_sh_disj hi_ne)
              (hseg_sh_D _ h1s) (h ▸ (hA_sh_bdD _).trans (discBd_subset _) (hymid_A _).1)
          have hz_int : z ∈ discInt (D_sub (compIdx r₂)) :=
            (hray_l_prop (compIdx r₂) ⟨r₂, rfl⟩).2.2.2.2
              ⟨h2r, by simpa only [q_pt, h2, ↓reduceDIte, mem_singleton_iff] using hzm⟩
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r₂) (shIdx r₁ h1)) hz_int (hseg_sh_D _ h1s)
        · have hi_ne : shIdx r₁ h1 ≠ shIdx r₂ h2 := fun he =>
            hne (hy_P_inj (by rw [← hshIdx_eq r₁ h1, ← hshIdx_eq r₂ h2, he]))
          exact Set.disjoint_left.mp (hD_sh_disj hi_ne) (hseg_sh_D _ h1s) (hseg_sh_D _ h2s)
      · rcases hz1 with h1r | h1s
        · have heq_p : z = p_hub (compIdx r₁) := by
            have : z ∈ ({p_hub (compIdx r₁)} : Set S) := hray_pw_global r₁ r₂ hne hcomp ▸ ⟨h1r, hz2⟩
            exact this
          exact hz1_ne (Or.inl heq_p)
        · have hz_int : z ∈ discInt (D_sub (compIdx r₂)) :=
            (hray_l_prop (compIdx r₂) ⟨r₂, rfl⟩).2.2.2.2 ⟨hz2, by
              simpa only [q_pt, h2, ↓reduceDIte, mem_singleton_iff] using fun h => hz2_ne (Or.inr h)⟩
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r₂) (shIdx r₁ h1)) hz_int (hseg_sh_D _ h1s)
      · rcases hz2 with h2r | h2s
        · have heq_p : z = p_hub (compIdx r₁) := by
            have : z ∈ ({p_hub (compIdx r₁)} : Set S) := hray_pw_global r₁ r₂ hne hcomp ▸ ⟨hz1, h2r⟩
            exact this
          exact hz1_ne (Or.inl heq_p)
        · have hz_int : z ∈ discInt (D_sub (compIdx r₁)) :=
            (hray_l_prop (compIdx r₁) ⟨r₁, rfl⟩).2.2.2.2 ⟨hz1, by
              simpa only [q_pt, h1, ↓reduceDIte, mem_singleton_iff] using fun h => hz1_ne (Or.inr h)⟩
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r₁) (shIdx r₂ h2)) hz_int (hseg_sh_D _ h2s)
      · have heq_p : z = p_hub (compIdx r₁) := by
          have : z ∈ ({p_hub (compIdx r₁)} : Set S) := hray_pw_global r₁ r₂ hne hcomp ▸ ⟨hz1, hz2⟩
          exact this
        exact hz1_ne (Or.inl heq_p)
    · -- Different component discs `D_P (compIdx r₁)` and `D_P (compIdx r₂)` are disjoint!
      exact Set.disjoint_left.mp (hD_P_disj hcomp) (hE_sub_DP r₁ hz1) (hE_sub_DP r₂ hz2)
  let H₁ : Drawing S := drawing_of_arcs hV₁_fin hab_ne haV₁ hbV₁ hE_line hE_capV₁ hE_disj
  obtain ⟨hH₁_E, hH₁_cl⟩ := drawing_of_arcs_E hV₁_fin hab_ne haV₁ hbV₁ hE_line hE_capV₁ hE_disj
  have hH₁_prop : H₁.IsProper := fun z ⟨hzbd, hzU⟩ => by
    rcases hzU with hzV | hzE
    · exact hzV
    · obtain ⟨r, hzr⟩ := mem_iUnion.mp hzE
      by_cases hzy : z = y_P r
      · exact hzy ▸ hbV₁ r
      · exact (Set.disjoint_left.mp (hD_P_int_bd (compIdx r)) (hE_diff_nbd r ⟨hzr, hzy⟩) hzbd).elim
  have hH₁_forest : IsGraphForest H₁.toGraph :=
    isGraphForest_of_star_arcs hV₁_fin hab_ne haV₁ hbV₁ hE_line hE_capV₁ hE_disj hy_P_inj
      (Set.disjoint_left.mpr (by
        rintro _ ⟨r₁, h1⟩ ⟨r₂, h2⟩
        exact hphub_nbd (compIdx r₁) (by change a_end r₁ ∈ bd S; rw [h1, ← h2]; exact hYbd (hy_P_Y r₂))))
  have hH₁_Y : H₁.V ∩ bd S = Y := by
    ext z
    simp only [H₁, drawing_of_arcs, V₁, mem_inter_iff, mem_union, mem_range]
    constructor
    · rintro ⟨hzY | ⟨l, rfl⟩, hzbd⟩
      · exact hzY
      · exact (hphub_nbd l hzbd).elim
    · intro hzY; exact ⟨Or.inl hzY, hYbd hzY⟩
  -- Check `MatchingStrictlySurroundsForest G_surr H₁` via `hGsurr_other`!
  have hGsurr_H₁ : MatchingStrictlySurroundsForest G_surr H₁ := by
    refine hGsurr_other H₁ hH₁_Y ?_ ?_ ?_
    · -- Same disc `c_disc u = c_disc v` implies `Nonempty (GraphWalk H₁.toGraph u v)`.
      intro u hu v hv hc_eq
      by_cases huv : u = v
      · subst huv
        exact ⟨.nil (Or.inl hu)⟩
      · have h2 : 2 ≤ (Y ∩ c_disc u).ncard := by
          have hsub : ({u, v} : Set S) ⊆ Y ∩ c_disc u := by
            rintro z (hz | hz)
            · rw [hz]; exact ⟨hu, discBd_subset _ (hdisc_prop u hu).2.1⟩
            · rw [hz]; exact ⟨hv, hc_eq ▸ discBd_subset _ (hdisc_prop v hv).2.1⟩
          calc 2 = ({u, v} : Set S).ncard := (ncard_pair huv).symm
            _ ≤ (Y ∩ c_disc u).ncard := Set.ncard_le_ncard hsub (hYfin.subset inter_subset_left)
        have hcuP : c_disc u ∈ P_set := ⟨u, hu, rfl, h2⟩
        have hcvP : c_disc v ∈ P_set := hc_eq ▸ hcuP
        let ru : Fin m := eY_P.symm ⟨u, hY_in_P_fin.mem_toFinset.mpr ⟨hu, hcuP⟩⟩
        let rv : Fin m := eY_P.symm ⟨v, hY_in_P_fin.mem_toFinset.mpr ⟨hv, hcvP⟩⟩
        have hy_ru : y_P ru = u := congrArg Subtype.val (eY_P.apply_symm_apply _)
        have hy_rv : y_P rv = v := congrArg Subtype.val (eY_P.apply_symm_apply _)
        have hcomp_eq : compIdx ru = compIdx rv :=
          hD_P_inj (by rw [hcompIdx_eq, hcompIdx_eq, hy_ru, hy_rv, hc_eq])
        let hub : S := p_hub (compIdx ru)
        have hlink_u : H₁.toGraph.IsLink (E_arc ru \ {a_end ru, b_end ru}) u hub := by
          refine ⟨hH₁_E.symm ▸ ⟨ru, rfl⟩, Or.inl hu, Or.inr ⟨compIdx ru, rfl⟩, ?_⟩
          change closure (E_arc ru \ {a_end ru, b_end ru}) ∩ V₁ = {u, hub}
          rw [hH₁_cl ru, hE_capV₁ ru, pair_comm]
          simp only [a_end, b_end, hy_ru, hub]
        have hlink_v : H₁.toGraph.IsLink (E_arc rv \ {a_end rv, b_end rv}) hub v := by
          refine ⟨hH₁_E.symm ▸ ⟨rv, rfl⟩, Or.inr ⟨compIdx ru, rfl⟩, Or.inl hv, ?_⟩
          change closure (E_arc rv \ {a_end rv, b_end rv}) ∩ V₁ = {hub, v}
          rw [hH₁_cl rv, hE_capV₁ rv]
          simp only [a_end, b_end, hy_rv, hub, hcomp_eq]
        exact ⟨.cons hlink_u (.cons hlink_v (.nil (Or.inl hv)))⟩
    · -- Every edge incident to a vertex in `c_disc y` has its closure inside `c_disc y`.
      intro e he u _ y hy hu_cl hu_cy
      obtain ⟨r, rfl⟩ := hH₁_E ▸ he
      rw [hH₁_cl r] at hu_cl ⊢
      have hcy_eq : D_P (compIdx r) = c_disc y := by
        obtain ⟨y', hy', hEq', _⟩ := hD_P_mem (compIdx r)
        by_contra hne
        have hd := hdisc_disj y' hy' y hy (by rw [hEq']; exact hne)
        exact Set.disjoint_left.mp hd (hEq'.symm ▸ hE_sub_DP r hu_cl) hu_cy
      exact hcy_eq ▸ hE_sub_DP r
    · -- Any point of `H₁.U ∩ discBd (c_disc y)` lies in `Y`.
      intro y hy z hzU hzbd
      rcases hzU with hzY | hzE
      · rcases hzY with hzY | ⟨l, rfl⟩
        · exact hzY
        · obtain ⟨y', hy', hEq', _⟩ := hD_P_mem l
          by_cases hcy : c_disc y = D_P l
          · exact ((hDsub_int_sub_DPint l (hp_int l)).2 (hcy ▸ hzbd)).elim
          · exact (Set.disjoint_left.mp (hdisc_disj y hy y' hy' (by rw [hEq']; exact hcy))
              (discBd_subset _ hzbd) (hEq'.symm ▸ hDsub_sub_DP l (discInt_subset _ (hp_int l)))).elim
      · obtain ⟨r, hzr⟩ := mem_iUnion.mp hzE
        by_cases hzy : z = y_P r
        · exact hzy ▸ hy_P_Y r
        · have hz_int := hE_diff_nbd r ⟨hzr, hzy⟩
          obtain ⟨y', hy', hEq', _⟩ := hD_P_mem (compIdx r)
          by_cases hcy : c_disc y = D_P (compIdx r)
          · exact (hz_int.2 (hcy ▸ hzbd)).elim
          · exact (Set.disjoint_left.mp (hdisc_disj y hy y' hy' (by rw [hEq']; exact hcy))
              (discBd_subset _ hzbd) (hEq'.symm ▸ discInt_subset _ hz_int)).elim
  have hHom : ForestsHomotopic H H₁ :=
    theorem_3_4_claim_2 hS ⟨hH, rfl⟩ ⟨⟨hH₁_prop, hH₁_forest⟩, hH₁_Y⟩ hGsurr_H hGsurr_H₁
  -- Step 8: Excise the `p` hub discs `Δ_hub` in `S_sub ≃ₜ SurfaceModel a b c`, apply `lpps22_lemma_A_3`,
  -- glue twice with `id` on `⋃ Δ_hub` and `⋃ D_sh` to get `φ : S ≃ₜ S`!
  have hce_sub : IsClosedEmbedding (Subtype.val : S_sub → S) := hcl_sub.isClosedEmbedding_subtypeVal
  have hcSsub : CompactSpace S_sub := hsurf_sub.1
  have ht2Ssub : T2Space S_sub := hsurf_sub.2.1
  have hneSsub : Nonempty S_sub := hconn_sub.toNonempty
  have hΔ_in_Ssub : ∀ l, Δ_hub l ⊆ range (Subtype.val : S_sub → S) := fun l => by
    rw [Subtype.range_val]
    exact (hΔ_sub_Dint l).trans ((discInt_subset _).trans (hDsub_sub_Ssub l))
  have hΔ_pre : ∀ l, IsClosedDisc (Subtype.val ⁻¹' Δ_hub l : Set S_sub) ∧
      discBd (Subtype.val ⁻¹' Δ_hub l : Set S_sub) = Subtype.val ⁻¹' discBd (Δ_hub l) :=
    fun l => isClosedDisc_preimage hce_sub (hΔ_disc l) (hΔ_in_Ssub l)
  let Δ_sub : Fin p → Set S_sub := fun l => Subtype.val ⁻¹' Δ_hub l
  have hΔ_sub_bd : ∀ l, Disjoint (Δ_sub l) (bd S_sub) := fun l => by
    rw [hbd_sub, Set.disjoint_left]
    intro x hxΔ hxbd
    rcases hxbd with hxbdS | hxA
    · exact Set.disjoint_left.mp (hΔ_disj_bd l) hxΔ hxbdS
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
      exact Set.disjoint_left.mp (hΔ_disj_Dsh l i) hxΔ ((hA_sh_bdD i).trans (discBd_subset _) hxi)
  have hΔ_sub_disj : Pairwise fun l₁ l₂ => Disjoint (Δ_sub l₁) (Δ_sub l₂) := fun l₁ l₂ hne =>
    (hΔ_disj_pw hne).preimage Subtype.val
  obtain ⟨hcl_cut, hsurf_cut, hconn_cut, hbd_cut, ⟨e_cut_model⟩⟩ :=
    remove_discs_model hsurf_sub e_sub_model (fun l => (hΔ_pre l).1) hΔ_sub_bd hΔ_sub_disj
  let S_cut := ↥(⋃ l : Fin p, discInt (Δ_sub l))ᶜ
  have hΔ_sub_int : ∀ l, discInt (Δ_sub l) = Subtype.val ⁻¹' discInt (Δ_hub l) := fun l => by
    change Δ_sub l \ discBd (Δ_sub l) = _
    rw [(hΔ_pre l).2]; rfl
  -- Lift `G_arc` and `L_arc` into `S_cut` (via `S_sub`).
  let valCut : S_cut → S := fun x => x.1.1
  have hvalCut_inj : Function.Injective valCut :=
    Subtype.val_injective.comp Subtype.val_injective
  have hG_in_Ssub : ∀ j, G_arc j ⊆ (⋃ i : Fin q, D_sh i \ A_sh i)ᶜ := fun j z hz hmem => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    have hzGU : z ∈ G.U := hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hz⟩
    have hz_eq : z = y_sh i := by
      have : z ∈ ({y_sh i} : Set S) := hD_sh_GU i ▸ ⟨hi.1, hzGU⟩
      exact this
    exact hi.2 (hz_eq ▸ (show y_sh i ∈ A_sh i ∩ bd S from hA_sh_bdS i ▸ Or.inl rfl).1)
  have hG_in_Scut : ∀ j, G_arc j ⊆ range valCut := fun j z hz => by
    have hz_sub : z ∈ (⋃ i : Fin q, D_sh i \ A_sh i)ᶜ := hG_in_Ssub j hz
    have hz_cut : (⟨z, hz_sub⟩ : S_sub) ∈ (⋃ l : Fin p, discInt (Δ_sub l))ᶜ := by
      intro hmem
      obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
      rw [hΔ_sub_int l] at hl
      exact Set.disjoint_left.mp (hΔ_disj_G l) (discInt_subset _ hl)
        (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hz⟩)
    exact ⟨⟨⟨z, hz_sub⟩, hz_cut⟩, rfl⟩
  have hL_in_Scut : ∀ r, L_arc r ⊆ range valCut := fun r z hz => by
    have hL_sub_D : L_arc r ⊆ D_sub (compIdx r) \ discInt (Δ_hub (compIdx r)) :=
      (hL_l_prop (compIdx r) ⟨r, rfl⟩).1
    have hz_sub : z ∈ (⋃ i : Fin q, D_sh i \ A_sh i)ᶜ :=
      hDsub_sub_Ssub (compIdx r) (hL_sub_D hz).1
    have hz_cut : (⟨z, hz_sub⟩ : S_sub) ∈ (⋃ l : Fin p, discInt (Δ_sub l))ᶜ := by
      intro hmem
      obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
      rw [hΔ_sub_int l] at hl
      by_cases hlr : l = compIdx r
      · subst hlr; exact (hL_sub_D hz).2 hl
      · exact Set.disjoint_left.mp (hD_P_disj hlr)
          (hDsub_sub_DP l (hΔ_sub_Dint l (discInt_subset _ hl) |>.1))
          (hDsub_sub_DP (compIdx r) (hL_sub_D hz).1)
    exact ⟨⟨⟨z, hz_sub⟩, hz_cut⟩, rfl⟩
  -- Helper to lift `IsLineWithEnds` along `valCut`.
  have lift_line_cut : ∀ {A : Set S} {s t : S}, A ⊆ range valCut → s ≠ t → IsLineWithEnds A s t →
      ∃ s' t' : S_cut, valCut s' = s ∧ valCut t' = t ∧ s' ≠ t' ∧
        IsLineWithEnds (valCut ⁻¹' A) s' t' := by
    intro A s t hAsub hst ⟨f, hf0, hf1⟩
    obtain ⟨s', hs'⟩ := hAsub (hf0 ▸ (f 0).2)
    obtain ⟨t', ht'⟩ := hAsub (hf1 ▸ (f 1).2)
    have hinv_mem : ∀ u : unitInterval, ∃ x : S_cut, valCut x = (f u).1 := fun u => hAsub (f u).2
    let lift_f : unitInterval → (valCut ⁻¹' A : Set S_cut) := fun u =>
      ⟨Classical.choose (hinv_mem u), by
        show valCut (Classical.choose (hinv_mem u)) ∈ A
        rw [Classical.choose_spec (hinv_mem u)]; exact (f u).2⟩
    have hlift_val : ∀ u, valCut (lift_f u).1 = (f u).1 := fun u => Classical.choose_spec (hinv_mem u)
    have hlift_cont : Continuous lift_f := by
      have hval_emb : Topology.IsInducing valCut :=
        Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
      rw [continuous_induced_rng]
      show Continuous (fun u => (lift_f u).1)
      rw [hval_emb.continuous_iff]
      have heq : valCut ∘ (fun u => (lift_f u).1) = fun u => (f u).1 := funext hlift_val
      rw [heq]
      exact continuous_subtype_val.comp f.continuous
    let g_homeo : unitInterval ≃ₜ (valCut ⁻¹' A : Set S_cut) :=
      { toFun := lift_f
        invFun := fun x => f.symm ⟨valCut x.1, x.2⟩
        left_inv := fun u => by
          apply f.injective; apply Subtype.ext
          change (f (f.symm ⟨valCut (lift_f u).1, _⟩)).1 = (f u).1
          rw [f.apply_symm_apply]; exact hlift_val u
        right_inv := fun x => by
          apply Subtype.ext; apply hvalCut_inj
          rw [hlift_val]; exact congrArg Subtype.val (f.apply_symm_apply ⟨valCut x.1, x.2⟩)
        continuous_toFun := hlift_cont
        continuous_invFun := f.symm.continuous.comp
          (Continuous.subtype_mk (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_subtype_val)) _) }
    refine ⟨s', t', hs', ht', fun h => hst (by rw [← hs', ← ht', h]), ⟨g_homeo, ?_, ?_⟩⟩
    · apply hvalCut_inj; rw [hs']; exact (hlift_val 0).trans hf0
    · apply hvalCut_inj; rw [ht']; exact (hlift_val 1).trans hf1
  have hbd_cut_eq : ∀ x : S_cut, x ∈ bd S_cut ↔
      valCut x ∈ bd S ∨ valCut x ∈ (⋃ i : Fin q, A_sh i) ∨ valCut x ∈ (⋃ l : Fin p, discBd (Δ_hub l)) := by
    intro x
    rw [hbd_cut, mem_preimage, mem_union, hbd_sub, mem_preimage, mem_union]
    simp only [valCut, mem_iUnion]
    constructor
    · rintro ((h1 | ⟨i, h2⟩) | ⟨l, h3⟩)
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨i, h2⟩)
      · rw [(hΔ_pre l).2] at h3; exact Or.inr (Or.inr ⟨l, h3⟩)
    · rintro (h1 | ⟨i, h2⟩ | ⟨l, h3⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨i, h2⟩)
      · exact Or.inr ⟨l, by rw [(hΔ_pre l).2]; exact h3⟩
  let G_cut : Fin n' → Set S_cut := fun j => valCut ⁻¹' G_arc j
  let L_cut : Fin m → Set S_cut := fun r => valCut ⁻¹' L_arc r
  have hG_cut : ∀ j, ∃ s t : S_cut, s ≠ t ∧ IsLineWithEnds (G_cut j) s t ∧
      G_cut j ∩ bd S_cut = {s, t} := fun j => by
    obtain ⟨s, t, hst, hl, hbd⟩ := hG_arc j
    obtain ⟨s', t', hs', ht', hst', hl'⟩ := lift_line_cut (hG_in_Scut j) hst hl
    refine ⟨s', t', hst', hl', ?_⟩
    ext x
    simp only [G_cut, mem_inter_iff, mem_preimage, hbd_cut_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxG, hxbd | hxA | hxΔ⟩
      · have hst0 : valCut x ∈ ({s, t} : Set S) := hbd ▸ ⟨hxG, hxbd⟩
        rcases hst0 with h | h
        · exact Or.inl (hvalCut_inj (h.trans hs'.symm))
        · exact Or.inr (hvalCut_inj (h.trans ht'.symm))
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
        have hxGU : valCut x ∈ G.U := hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩
        have hxeq : valCut x = y_sh i := by
          have : valCut x ∈ ({y_sh i} : Set S) :=
            hD_sh_GU i ▸ ⟨(hA_sh_bdD i).trans (discBd_subset _) hxi, hxGU⟩
          exact this
        have hst0 : valCut x ∈ ({s, t} : Set S) := hbd ▸ ⟨hxG, hxeq ▸ hYbd (hy_sh_Y i)⟩
        rcases hst0 with h | h
        · exact Or.inl (hvalCut_inj (h.trans hs'.symm))
        · exact Or.inr (hvalCut_inj (h.trans ht'.symm))
      · obtain ⟨l, hxl⟩ := mem_iUnion.mp hxΔ
        exact (Set.disjoint_left.mp (hΔ_disj_G l) (discBd_subset _ hxl)
          (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩)).elim
    · rintro (rfl | rfl)
      · have hmem : s ∈ G_arc j ∩ bd S := hbd.symm ▸ Or.inl rfl
        exact ⟨hs'.symm ▸ hmem.1, Or.inl (hs'.symm ▸ hmem.2)⟩
      · have hmem : t ∈ G_arc j ∩ bd S := hbd.symm ▸ Or.inr rfl
        exact ⟨ht'.symm ▸ hmem.1, Or.inl (ht'.symm ▸ hmem.2)⟩
  have hG_cut_disj : Pairwise fun j₁ j₂ => Disjoint (G_cut j₁) (G_cut j₂) := fun j₁ j₂ hne =>
    (hG_disj hne).preimage valCut
  have hL_cut : ∀ r, ∃ u v : S_cut, u ≠ v ∧ IsLineWithEnds (L_cut r) u v ∧
      L_cut r ∩ bd S_cut = {u, v} := fun r => by
    obtain ⟨hL_sub, huv, hL_line, hL_bd⟩ := hL_l_prop (compIdx r) ⟨r, rfl⟩
    obtain ⟨u', v', hu', hv', huv', hl'⟩ := lift_line_cut (hL_in_Scut r) huv hL_line
    refine ⟨u', v', huv', hl', ?_⟩
    ext x
    simp only [L_cut, mem_inter_iff, mem_preimage, hbd_cut_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hxL, hxbd | hxA | hxΔ⟩
      · have hx_in : valCut x ∈ discBd (D_sub (compIdx r)) := by
          have hxD : valCut x ∈ D_sub (compIdx r) := (hL_sub hxL).1
          by_contra hnb
          exact Set.disjoint_left.mp (hD_P_int_bd (compIdx r)) (hDsub_int_sub_DPint _ ⟨hxD, hnb⟩) hxbd
        have huv0 : valCut x ∈ ({u_pt r, q_pt r} : Set S) := hL_bd ▸ ⟨hxL, Or.inl hx_in⟩
        rcases huv0 with h | h
        · exact Or.inl (hvalCut_inj (h.trans hu'.symm))
        · exact Or.inr (hvalCut_inj (h.trans hv'.symm))
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxA
        have hx_in : valCut x ∈ discBd (D_sub (compIdx r)) := by
          have hxD : valCut x ∈ D_sub (compIdx r) := (hL_sub hxL).1
          by_contra hnb
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r) i) ⟨hxD, hnb⟩
            ((hA_sh_bdD i).trans (discBd_subset _) hxi)
        have huv0 : valCut x ∈ ({u_pt r, q_pt r} : Set S) := hL_bd ▸ ⟨hxL, Or.inl hx_in⟩
        rcases huv0 with h | h
        · exact Or.inl (hvalCut_inj (h.trans hu'.symm))
        · exact Or.inr (hvalCut_inj (h.trans hv'.symm))
      · obtain ⟨l, hxl⟩ := mem_iUnion.mp hxΔ
        have hlr : l = compIdx r := by
          by_contra hne
          exact Set.disjoint_left.mp (hD_P_disj hne)
            (hDsub_sub_DP l (discInt_subset _ (hΔ_sub_Dint l (discBd_subset _ hxl))))
            (hDsub_sub_DP (compIdx r) (hL_sub hxL).1)
        subst hlr
        have huv0 : valCut x ∈ ({u_pt r, q_pt r} : Set S) := hL_bd ▸ ⟨hxL, Or.inr hxl⟩
        rcases huv0 with h | h
        · exact Or.inl (hvalCut_inj (h.trans hu'.symm))
        · exact Or.inr (hvalCut_inj (h.trans hv'.symm))
    · rintro (rfl | rfl)
      · have hmem : u_pt r ∈ L_arc r ∩ (discBd (D_sub (compIdx r)) ∪ discBd (Δ_hub (compIdx r))) :=
          hL_bd.symm ▸ Or.inl rfl
        have hu_Δ : u_pt r ∈ discBd (Δ_hub (compIdx r)) :=
          (show u_pt r ∈ R_in r ∩ discBd (Δ_hub (compIdx r)) from
            (hR_in_prop (compIdx r) ⟨r, rfl⟩).2.2.symm ▸ rfl).2
        exact ⟨hu'.symm ▸ hmem.1, Or.inr (Or.inr (mem_iUnion.mpr ⟨compIdx r, hu'.symm ▸ hu_Δ⟩))⟩
      · have hmem : q_pt r ∈ L_arc r ∩ (discBd (D_sub (compIdx r)) ∪ discBd (Δ_hub (compIdx r))) :=
          hL_bd.symm ▸ Or.inr rfl
        refine ⟨hv'.symm ▸ hmem.1, ?_⟩
        dsimp only [q_pt] at hv'
        split_ifs at hv' with hGV
        · exact Or.inr (Or.inl (mem_iUnion.mpr ⟨shIdx r hGV, hv'.symm ▸ (hymid_A _).1⟩))
        · exact Or.inl (hv'.symm ▸ hYbd (hy_P_Y r))
  have hL_cut_disj : Pairwise fun r₁ r₂ => Disjoint (L_cut r₁) (L_cut r₂) := by
    intro r₁ r₂ hne
    rw [Set.disjoint_left]
    intro x hx1 hx2
    by_cases hcomp : compIdx r₁ = compIdx r₂
    · exact Set.disjoint_left.mp (hL_pw_global r₁ r₂ hne hcomp) hx1 hx2
    · exact Set.disjoint_left.mp (hD_P_disj hcomp)
        (hDsub_sub_DP (compIdx r₁) ((hL_l_prop (compIdx r₁) ⟨r₁, rfl⟩).1 hx1).1)
        (hDsub_sub_DP (compIdx r₂) ((hL_l_prop (compIdx r₂) ⟨r₂, rfl⟩).1 hx2).1)
  have hbd_cut_disj : ∀ j r, Disjoint (G_cut j ∩ bd S_cut) (L_cut r ∩ bd S_cut) := fun j r => by
    rw [Set.disjoint_left]
    intro x ⟨hxG, hxbd⟩ ⟨hxL, _⟩
    -- `valCut x ∈ G_arc j ∩ bd S_cut` forces `valCut x ∈ G.V`!
    have hxGV : valCut x ∈ G.V := by
      rcases (hbd_cut_eq x).mp hxbd with hbdS | hA | hΔ
      · exact hGV_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG, hbdS⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hA
        have hxGU : valCut x ∈ G.U := hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩
        have hxeq : valCut x = y_sh i := by
          have : valCut x ∈ ({y_sh i} : Set S) :=
            hD_sh_GU i ▸ ⟨(hA_sh_bdD i).trans (discBd_subset _) hxi, hxGU⟩
          exact this
        exact hxeq ▸ hy_sh_GV i
      · obtain ⟨l, hxl⟩ := mem_iUnion.mp hΔ
        exact (Set.disjoint_left.mp (hΔ_disj_G l) (discBd_subset _ hxl)
          (hGU_eq.symm ▸ mem_iUnion.mpr ⟨j, hxG⟩)).elim
    -- Meanwhile `valCut x ∈ L_arc r ∩ bd S_cut` forces `valCut x ∈ {u_pt r, q_pt r}`, neither of which is in `G.V`!
    obtain ⟨u', v', -, -, hLbd'⟩ := hL_cut r
    have hx_uv : valCut x ∈ ({u_pt r, q_pt r} : Set S) := by
      obtain ⟨hL_sub, -, -, hL_bd⟩ := hL_l_prop (compIdx r) ⟨r, rfl⟩
      rcases (hbd_cut_eq x).mp hxbd with hbdS | hA | hΔ
      · have hx_in : valCut x ∈ discBd (D_sub (compIdx r)) := by
          by_contra hnb
          exact Set.disjoint_left.mp (hD_P_int_bd (compIdx r))
            (hDsub_int_sub_DPint _ ⟨(hL_sub hxL).1, hnb⟩) hbdS
        exact hL_bd ▸ ⟨hxL, Or.inl hx_in⟩
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hA
        have hx_in : valCut x ∈ discBd (D_sub (compIdx r)) := by
          by_contra hnb
          exact Set.disjoint_left.mp (hDsub_int_disj_Dsh (compIdx r) i)
            ⟨(hL_sub hxL).1, hnb⟩ ((hA_sh_bdD i).trans (discBd_subset _) hxi)
        exact hL_bd ▸ ⟨hxL, Or.inl hx_in⟩
      · obtain ⟨l, hxl⟩ := mem_iUnion.mp hΔ
        have hlr : l = compIdx r := by
          by_contra hne
          exact Set.disjoint_left.mp (hD_P_disj hne)
            (hDsub_sub_DP l (discInt_subset _ (hΔ_sub_Dint l (discBd_subset _ hxl))))
            (hDsub_sub_DP (compIdx r) (hL_sub hxL).1)
        subst hlr
        exact hL_bd ▸ ⟨hxL, Or.inr hxl⟩
    rcases hx_uv with hu_eq | hq_eq
    · have hu_Δ : u_pt r ∈ Δ_hub (compIdx r) :=
        (hR_in_prop (compIdx r) ⟨r, rfl⟩).1
          (show u_pt r ∈ R_in r from (show u_pt r ∈ R_in r ∩ discBd (Δ_hub (compIdx r)) from
            (hR_in_prop (compIdx r) ⟨r, rfl⟩).2.2.symm ▸ rfl).1)
      exact Set.disjoint_left.mp (hΔ_disj_G (compIdx r)) hu_Δ (hu_eq ▸ G.V_subset_U hxGV)
    · dsimp only [q_pt] at hq_eq
      split_ifs at hq_eq with hGV
      · exact hymid_nbd (shIdx r hGV) (hq_eq ▸ hG.2.1 hxGV)
      · exact hGV (hq_eq ▸ hxGV)
  -- Apply LPPS22 Lemma A.3 in `S_cut ≃ₜ SurfaceModel a b (c + p)`!
  obtain ⟨φ_cut, hφ_cut_fix, hφ_cut_fin, hφ_cut_sum⟩ :=
    lpps22_lemma_A_3 hsurf_cut e_cut_model (by omega : 1 ≤ c + p)
      hG_cut hG_cut_disj hL_cut hL_cut_disj hbd_cut_disj
  -- Glue 1: extend `φ_cut` by `id` on `⋃ l, Δ_sub l` to get `φ_sub : S_sub ≃ₜ S_sub`.
  let A₁ : Set S_sub := (⋃ l : Fin p, discInt (Δ_sub l))ᶜ
  let B₁ : Set S_sub := ⋃ l : Fin p, Δ_sub l
  have hB₁_cl : IsClosed B₁ := isClosed_iUnion_of_finite fun l => (hΔ_pre l).1.isClosed
  have hAB₁ : A₁ ∪ B₁ = univ := by
    ext x
    simp only [A₁, B₁, mem_union, mem_compl_iff, mem_iUnion, mem_univ, iff_true]
    by_cases h : ∃ l, x ∈ discInt (Δ_sub l)
    · obtain ⟨l, hl⟩ := h; exact Or.inr ⟨l, discInt_subset _ hl⟩
    · exact Or.inl h
  have hfix₁ : ∀ x : S_cut, x.1 ∈ B₁ → (φ_cut x).1 = x.1 := fun x hxB => by
    obtain ⟨l, hxl⟩ := mem_iUnion.mp hxB
    have hxl_bd : x.1 ∈ discBd (Δ_sub l) := by
      by_contra hnb; exact x.2 (mem_iUnion.mpr ⟨l, hxl, hnb⟩)
    have hx_bd : x ∈ bd S_cut := by rw [hbd_cut]; exact Or.inr (mem_iUnion.mpr ⟨l, hxl_bd⟩)
    exact congrArg Subtype.val (hφ_cut_fix x hx_bd)
  let φ_sub : S_sub ≃ₜ S_sub := homeo_glue_id hcl_cut hB₁_cl hAB₁ φ_cut hfix₁
  -- Glue 2: extend `φ_sub` by `id` on `⋃ i, D_sh i` to get `φ : S ≃ₜ S`.
  let A₂ : Set S := (⋃ i : Fin q, D_sh i \ A_sh i)ᶜ
  let B₂ : Set S := ⋃ i : Fin q, D_sh i
  have hB₂_cl : IsClosed B₂ := isClosed_iUnion_of_finite fun i => (hD_sh i).isClosed
  have hAB₂ : A₂ ∪ B₂ = univ := by
    ext x
    simp only [A₂, B₂, mem_union, mem_compl_iff, mem_iUnion, mem_univ, iff_true]
    by_cases h : ∃ i, x ∈ D_sh i \ A_sh i
    · obtain ⟨i, hi⟩ := h; exact Or.inr ⟨i, hi.1⟩
    · exact Or.inl h
  have hφ_sub_fix_bd : ∀ x : S_sub, x ∈ bd S_sub → φ_sub x = x := fun x hxbd => by
    have hxA₁ : x ∈ A₁ := fun hmem => by
      obtain ⟨l, hl⟩ := mem_iUnion.mp hmem
      exact Set.disjoint_left.mp (hΔ_sub_bd l) (discInt_subset _ hl) hxbd
    rw [homeo_glue_id_apply_mem_left hcl_cut hB₁_cl hAB₁ φ_cut hfix₁ hxA₁]
    exact congrArg Subtype.val (hφ_cut_fix ⟨x, hxA₁⟩ (by rw [hbd_cut]; exact Or.inl hxbd))
  have hfix₂ : ∀ x : S_sub, x.1 ∈ B₂ → (φ_sub x).1 = x.1 := fun x hxB => by
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
    have hxiA : x.1 ∈ A_sh i := by
      by_contra hna; exact x.2 (mem_iUnion.mpr ⟨i, hxi, hna⟩)
    have hxbd : x ∈ bd S_sub := by rw [hbd_sub]; exact Or.inr (mem_iUnion.mpr ⟨i, hxiA⟩)
    exact congrArg Subtype.val (hφ_sub_fix_bd x hxbd)
  let φ : S ≃ₜ S := homeo_glue_id hcl_sub hB₂_cl hAB₂ φ_sub hfix₂
  -- Verify `φ` fixes `bd S`, every `Δ_hub l`, every `D_sh i`, and agrees with `φ_cut` on `S_cut`.
  have hφ_bd : ∀ x ∈ bd S, φ x = x := fun x hxbd => by
    by_cases hxB₂ : x ∈ B₂
    · exact homeo_glue_id_apply_mem_right hcl_sub hB₂_cl hAB₂ φ_sub hfix₂ hxB₂
    · have hxA₂ : x ∈ A₂ := ((mem_union _ _ _).mp (hAB₂.symm ▸ mem_univ x)).resolve_right hxB₂
      rw [homeo_glue_id_apply_mem_left hcl_sub hB₂_cl hAB₂ φ_sub hfix₂ hxA₂]
      exact congrArg Subtype.val (hφ_sub_fix_bd ⟨x, hxA₂⟩ (by rw [hbd_sub]; exact Or.inl hxbd))
  have hφ_Δ : ∀ l, ∀ x ∈ Δ_hub l, φ x = x := fun l x hxΔ => by
    have hxA₂ : x ∈ A₂ := Subtype.range_val (s := A₂) ▸ hΔ_in_Ssub l hxΔ
    rw [homeo_glue_id_apply_mem_left hcl_sub hB₂_cl hAB₂ φ_sub hfix₂ hxA₂]
    have hxB₁ : (⟨x, hxA₂⟩ : S_sub) ∈ B₁ := mem_iUnion.mpr ⟨l, hxΔ⟩
    exact congrArg Subtype.val (homeo_glue_id_apply_mem_right hcl_cut hB₁_cl hAB₁ φ_cut hfix₁ hxB₁)
  have hφ_Dsh : ∀ i, ∀ x ∈ D_sh i, φ x = x := fun i x hxi =>
    homeo_glue_id_apply_mem_right hcl_sub hB₂_cl hAB₂ φ_sub hfix₂ (mem_iUnion.mpr ⟨i, hxi⟩)
  have hφ_cut_eq : ∀ x : S_cut, φ (valCut x) = valCut (φ_cut x) := fun x => by
    rw [homeo_glue_id_apply_mem_left hcl_sub hB₂_cl hAB₂ φ_sub hfix₂ x.1.2]
    exact congrArg Subtype.val (homeo_glue_id_apply_mem_left hcl_cut hB₁_cl hAB₁ φ_cut hfix₁ x.2)
  -- Step 9: Set `H' := mapDrawingHomeo φ H₁`, verify `IsSurfaceForest H'`, `ForestsHomoplastic H H'`,
  -- and bound `(G.U ∩ H'.U).ncard ≤ wExplicit a b c k n`!
  let H' : Drawing S := mapDrawingHomeo φ H₁
  have hH'_forest : IsSurfaceForest H' := IsSurfaceForest.map_homeo φ ⟨hH₁_prop, hH₁_forest⟩
  have hH'_homopl : ForestsHomoplastic H H' :=
    ⟨φ, hφ_bd, ForestsHomotopic.map_homeo φ hHom⟩
  have himg_eq : ∀ r j, φ '' L_arc r ∩ G_arc j = valCut '' (φ_cut '' L_cut r ∩ G_cut j) := fun r j => by
    ext z
    constructor
    · rintro ⟨⟨x, hxL, rfl⟩, hzG⟩
      obtain ⟨x', hx'⟩ := hL_in_Scut r hxL
      subst hx'
      refine ⟨φ_cut x', ⟨⟨x', hxL, rfl⟩, ?_⟩, (hφ_cut_eq x').symm⟩
      show valCut (φ_cut x') ∈ G_arc j
      rwa [← hφ_cut_eq x']
    · rintro ⟨y, ⟨⟨x', hx'L, rfl⟩, hyG⟩, rfl⟩
      exact ⟨⟨valCut x', hx'L, hφ_cut_eq x'⟩, hyG⟩
  have hcross_sub : G.U ∩ H'.U ⊆
      (⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)) ∪ (G.V ∩ Y) := by
    rintro z ⟨hzGU, ⟨x, hxH₁, rfl⟩⟩
    rcases hxH₁ with (hxY | ⟨l, rfl⟩) | hxE
    · right
      have hφx : φ x = x := hφ_bd x (hYbd hxY)
      rw [hφx] at hzGU ⊢
      exact ⟨hG.1 ⟨hYbd hxY, hzGU⟩, hxY⟩
    · exfalso
      have hφp : φ (p_hub l) = p_hub l := hφ_Δ l _ (discInt_subset _ (hp_in_Δint l))
      rw [hφp] at hzGU
      exact hp_nG l hzGU
    · obtain ⟨r, hxr⟩ := mem_iUnion.mp hxE
      have hray_un : ray r = R_in r ∪ L_arc r := (hray_l_prop (compIdx r) ⟨r, rfl⟩).1
      dsimp only [E_arc] at hxr
      split_ifs at hxr with hGV
      · rcases hxr with hxr_ray | hxr_seg
        · rw [hray_un] at hxr_ray
          rcases hxr_ray with hxRin | hxL
          · exfalso
            have hxΔ : x ∈ Δ_hub (compIdx r) := (hR_in_prop (compIdx r) ⟨r, rfl⟩).1 hxRin
            rw [hφ_Δ (compIdx r) x hxΔ] at hzGU
            exact Set.disjoint_left.mp (hΔ_disj_G (compIdx r)) hxΔ hzGU
          · left
            obtain ⟨j, hzj⟩ := mem_iUnion.mp (hGU_eq ▸ hzGU)
            exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨j, ⟨x, hxL, rfl⟩, hzj⟩⟩
        · right
          have hxD : x ∈ D_sh (shIdx r hGV) := hseg_sh_D _ hxr_seg
          rw [hφ_Dsh (shIdx r hGV) x hxD] at hzGU ⊢
          have hxeq : x = y_sh (shIdx r hGV) := by
            have : x ∈ ({y_sh (shIdx r hGV)} : Set S) := hD_sh_GU _ ▸ ⟨hxD, hzGU⟩
            exact this
          exact hxeq ▸ ⟨hy_sh_GV _, hy_sh_Y _⟩
      · rw [hray_un] at hxr
        rcases hxr with hxRin | hxL
        · exfalso
          have hxΔ : x ∈ Δ_hub (compIdx r) := (hR_in_prop (compIdx r) ⟨r, rfl⟩).1 hxRin
          rw [hφ_Δ (compIdx r) x hxΔ] at hzGU
          exact Set.disjoint_left.mp (hΔ_disj_G (compIdx r)) hxΔ hzGU
        · left
          obtain ⟨j, hzj⟩ := mem_iUnion.mp (hGU_eq ▸ hzGU)
          exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨j, ⟨x, hxL, rfl⟩, hzj⟩⟩
  have hfin_L : (⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)).Finite :=
    Set.finite_iUnion fun r => Set.finite_iUnion fun j => by
      rw [himg_eq r j]; exact (hφ_cut_fin r j).image valCut
  have hfin_GVY : (G.V ∩ Y).Finite := hYfin.subset inter_subset_right
  have hfin_tot : (G.U ∩ H'.U).Finite := (hfin_L.union hfin_GVY).subset hcross_sub
  have hcard_L : (⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)).ncard ≤
      2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) := by
    calc (⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)).ncard
        ≤ ∑ r : Fin m, (⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)).ncard := ncard_iUnion_fin_le _
      _ ≤ ∑ r : Fin m, ∑ j : Fin n', (φ '' L_arc r ∩ G_arc j).ncard :=
          Finset.sum_le_sum fun r _ => ncard_iUnion_fin_le _
      _ = ∑ r : Fin m, ∑ j : Fin n', (φ_cut '' L_cut r ∩ G_cut j).ncard :=
          Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by
            rw [himg_eq r j, Set.ncard_image_of_injective _ hvalCut_inj]
      _ ≤ m * 3 ^ (2 * n' + 3 * (2 * a + b) + (c + p)) := hφ_cut_sum
      _ ≤ (2 * k) * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) := by
          refine Nat.mul_le_mul (by omega) ?_
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard_GVY : (G.V ∩ Y).ncard ≤ k :=
    (Set.ncard_le_ncard inter_subset_right hYfin).trans hHcard
  have hcard_tot : (G.U ∩ H'.U).ncard ≤ wExplicit a b c k n := by
    calc (G.U ∩ H'.U).ncard
        ≤ ((⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)) ∪ (G.V ∩ Y)).ncard :=
          Set.ncard_le_ncard hcross_sub (hfin_L.union hfin_GVY)
      _ ≤ (⋃ r : Fin m, ⋃ j : Fin n', (φ '' L_arc r ∩ G_arc j)).ncard + (G.V ∩ Y).ncard :=
          Set.ncard_union_le _ _
      _ ≤ 2 * k * 3 ^ (2 * n + 3 * (2 * a + b) + c + k) + k := Nat.add_le_add hcard_L hcard_GVY
      _ = wExplicit a b c k n := rfl
  exact ⟨H', hH'_forest, hH'_homopl, hfin_tot, hcard_tot⟩

end GraphMinor.GM07
