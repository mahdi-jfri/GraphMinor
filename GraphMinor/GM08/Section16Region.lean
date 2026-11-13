module

public import GraphMinor.GM07.TameDisc
public import GraphMinor.GM11.RadialAccess
import GraphMinor.GM07.CuffStep

/-!
# Graph Minors VIII, Section 16: Closed-Surface Region Helpers

Topological lemmas on closed surfaces and spheres used in `Tube.exists_hoop_step_inward`
(`GraphMinor/GM08/Section16Step.lean`):

- `isPathConnected_compl_union_pinched`: on a sphere `Z`, removing a closed disc `B₁` together with
  finitely many closed discs `Δ_i` that each meet `B₁` in a single boundary point `u_i` and are
  pairwise disjoint outside `B₁` leaves an open path-connected exterior.
- `isClosed_U_diff_edge`: removing a single edge `e ∈ Γ.E` from `Γ.U` yields a closed set.
- `closure_edge_subset_closure_component`: if an edge `e ∈ Γ.E` disjoint from a closed set `B₁`
  meets the closure of `R = connectedComponentIn (B₁ ∪ Γ.U)ᶜ q₀`, then `closure e ⊆ closure R`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Topology GraphMinor.Surface GraphMinor.GM11

/-- In a closed surface `Z`, removing a closed disc `Δ` that meets `Uᶜ` in a single boundary point
`u ∈ discBd Δ` from an open path-connected set `U` preserves openness and path-connectedness. -/
theorem isPathConnected_diff_pinched_disc {Z : Type} [TopologicalSpace Z]
    (hS : IsClosedSurface Z) {U Δ : Set Z} {u : Z}
    (hUo : IsOpen U) (hUp : IsPathConnected U) (hne : (U \ Δ).Nonempty)
    (hΔ : IsClosedDisc Δ) (_hu : u ∈ discBd Δ) (hinter : Δ ∩ Uᶜ = {u}) :
    IsOpen (U \ Δ) ∧ IsPathConnected (U \ Δ) := by
  have : T2Space Z := hS.2.1
  have hman : ∀ z : Z, IsManifoldPoint z := fun z => (hS.2.2 z).isManifoldPoint
  have hopen : IsOpen (U \ Δ) := hUo.sdiff hΔ.isClosed
  refine ⟨hopen, ?_⟩
  obtain ⟨z₀, hz₀⟩ := hne
  refine ⟨z₀, hz₀, fun y hy => ?_⟩
  by_cases hzy : z₀ = y
  · subst hzy; exact JoinedIn.refl hz₀
  have hbd_sub : discBd Δ ⊆ ({z₀, y} : Set Z)ᶜ := by
    intro x hx hmem
    have hxΔ : x ∈ Δ := Surface.discBd_subset Δ hx
    rcases hmem with rfl | rfl
    · exact hz₀.2 hxΔ
    · exact hy.2 hxΔ
  obtain ⟨E, hE, hΔE, hEW⟩ := exists_disc_around hman hΔ (fun x _ => hS.2.2 x)
    (Finite.isClosed (by simp : ({z₀, y} : Set Z).Finite)).isOpen_compl hbd_sub
  have hz₀_notE : z₀ ∉ E := fun h => by
    rcases hEW h with h1 | h2
    · exact hz₀.2 h1
    · exact h2 (Or.inl rfl)
  have hy_notE : y ∉ E := fun h => by
    rcases hEW h with h1 | h2
    · exact hy.2 h1
    · exact h2 (Or.inr rfl)
  obtain ⟨D, hD, hΔD, hDE, hdiffU, hbdDU, _, _⟩ :=
    GM07.exists_disc_push_off hΔ hE hΔE hUo.isClosed_compl
  have hz₀_notD : z₀ ∉ D := fun h => hz₀_notE (hDE h).1
  have hy_notD : y ∉ D := fun h => hy_notE (hDE h).1
  have hbdD_sub : discBd D \ {u} ⊆ U \ Δ := by
    rintro x ⟨hxBd, hxu⟩
    have hxD : x ∈ D := Surface.discBd_subset D hxBd
    have hx_notΔ : x ∉ Δ := fun hxΔ => hxu (hinter ▸ ⟨hxΔ, hbdDU ⟨hxBd, hxΔ⟩⟩)
    have hxU : x ∈ U := by_contra fun hnU => disjoint_left.mp hdiffU ⟨hxD, hx_notΔ⟩ hnU
    exact ⟨hxU, hx_notΔ⟩
  have hbdD_pc : IsPathConnected (discBd D \ {u}) := by
    obtain ⟨φ⟩ := hD.isOArc_discBd
    by_cases huBd : u ∈ discBd D
    · have heq : discBd D \ {u} = (fun w : Circle => (φ w).1) '' {φ.symm ⟨u, huBd⟩}ᶜ := by
        ext x
        constructor
        · rintro ⟨hx, hxu⟩
          refine ⟨φ.symm ⟨x, hx⟩, fun h => hxu ?_, by simp⟩
          exact congrArg Subtype.val (φ.symm.injective h)
        · rintro ⟨w, hw, rfl⟩
          refine ⟨(φ w).2, fun h => hw ?_⟩
          have hsub : φ w = ⟨u, huBd⟩ := Subtype.ext h
          simp [← hsub]
      rw [heq]
      exact (Circle.isPathConnected_compl_singleton _).image
        (continuous_subtype_val.comp φ.continuous)
    · have heq : discBd D \ {u} = discBd D := by
        ext x; exact ⟨fun h => h.1, fun h => ⟨h, fun e => huBd (e ▸ h)⟩⟩
      rw [heq]
      have heq2 : discBd D = range (fun w : Circle => (φ w).1) := by
        ext x; exact ⟨fun hx => ⟨φ.symm ⟨x, hx⟩, by simp⟩, fun ⟨w, hw⟩ => hw ▸ (φ w).2⟩
      rw [heq2]
      have : PathConnectedSpace Circle := inferInstance
      exact isPathConnected_range (continuous_subtype_val.comp φ.continuous)
  obtain ⟨γ, hγU⟩ := hUp.joinedIn z₀ hz₀.1 y hy.1
  have hu_notU : u ∉ U := fun huU => (hinter.symm.subset rfl).2 huU
  by_cases hhit : (range γ ∩ D).Nonempty
  · have hK : IsCompact (γ ⁻¹' D) := (hD.isClosed.preimage γ.continuous).isCompact
    obtain ⟨x_hit, ⟨t_hit, rfl⟩, hxD⟩ := hhit
    obtain ⟨t₁, ht₁D, hlow₁⟩ := hK.exists_isLeast ⟨t_hit, hxD⟩
    obtain ⟨t₂, ht₂D, hhigh₂⟩ := hK.exists_isGreatest ⟨t_hit, hxD⟩
    have ht₁_pos : (0 : unitInterval) < t₁ :=
      lt_of_le_of_ne t₁.2.1 fun h0 => hz₀_notD (by simpa [← h0] using ht₁D)
    have ht₂_lt : t₂ < (1 : unitInterval) :=
      lt_of_le_of_ne t₂.2.2 fun h1 => hy_notD (by simpa [h1] using ht₂D)
    have ht₁_bd : γ t₁ ∈ discBd D := by
      rw [← IsClosedDisc.frontier_eq_discBd hS hD, frontier_eq_closure_inter_closure]
      refine ⟨subset_closure ht₁D, ?_⟩
      have hcl_real : (t₁ : ℝ) ∈ closure (Ioo (0 : ℝ) (t₁ : ℝ)) := by
        rw [closure_Ioo (show (0 : ℝ) ≠ (t₁ : ℝ) from (Subtype.coe_lt_coe.mpr ht₁_pos).ne)]
        exact right_mem_Icc.mpr ht₁_pos.le
      have ht₁_cl : t₁ ∈ closure (Ioo (0 : unitInterval) t₁) := by
        rw [mem_closure_iff]
        intro V hV ht₁V
        obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
        obtain ⟨r, hrW, hr1, hr2⟩ := mem_closure_iff.mp hcl_real W hW ht₁V
        exact ⟨⟨r, hr1.le, le_trans hr2.le t₁.2.2⟩, hrW, hr1, hr2⟩
      refine closure_mono ?_
        (image_closure_subset_closure_image γ.continuous ⟨t₁, ht₁_cl, rfl⟩)
      rintro _ ⟨s, hs, rfl⟩ hsD
      exact not_le.mpr hs.2 (hlow₁ hsD)
    have ht₂_bd : γ t₂ ∈ discBd D := by
      rw [← IsClosedDisc.frontier_eq_discBd hS hD, frontier_eq_closure_inter_closure]
      refine ⟨subset_closure ht₂D, ?_⟩
      have hcl_real : (t₂ : ℝ) ∈ closure (Ioo (t₂ : ℝ) (1 : ℝ)) := by
        rw [closure_Ioo (show (t₂ : ℝ) ≠ (1 : ℝ) from (Subtype.coe_lt_coe.mpr ht₂_lt).ne)]
        exact left_mem_Icc.mpr ht₂_lt.le
      have ht₂_cl : t₂ ∈ closure (Ioo t₂ (1 : unitInterval)) := by
        rw [mem_closure_iff]
        intro V hV ht₂V
        obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
        obtain ⟨r, hrW, hr1, hr2⟩ := mem_closure_iff.mp hcl_real W hW ht₂V
        exact ⟨⟨r, le_trans t₂.2.1 hr1.le, hr2.le⟩, hrW, hr1, hr2⟩
      refine closure_mono ?_
        (image_closure_subset_closure_image γ.continuous ⟨t₂, ht₂_cl, rfl⟩)
      rintro _ ⟨s, hs, rfl⟩ hsD
      exact not_le.mpr hs.1 (hhigh₂ hsD)
    have hγt₁_mem : γ t₁ ∈ discBd D \ {u} :=
      ⟨ht₁_bd, fun h => hu_notU (mem_singleton_iff.mp h ▸ hγU t₁)⟩
    have hγt₂_mem : γ t₂ ∈ discBd D \ {u} :=
      ⟨ht₂_bd, fun h => hu_notU (mem_singleton_iff.mp h ▸ hγU t₂)⟩
    have hj1 : JoinedIn (U \ Δ) z₀ (γ t₁) := by
      let f1 : ℝ → Z := fun s => γ (projIcc 0 1 zero_le_one (s * t₁))
      refine JoinedIn.ofLine (f := f1)
        (γ.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
        (by simp [f1]) (by simp [f1]) ?_
      rintro _ ⟨s, hs, rfl⟩
      have hst : s * (t₁ : ℝ) ∈ Icc (0 : ℝ) 1 :=
        ⟨mul_nonneg hs.1 t₁.2.1, (mul_le_of_le_one_left t₁.2.1 hs.2).trans t₁.2.2⟩
      rcases eq_or_lt_of_le hs.2 with rfl | hs_lt
      · have heq : projIcc 0 1 zero_le_one ((1 : ℝ) * t₁) = t₁ := by simp
        change γ (projIcc 0 1 zero_le_one ((1 : ℝ) * t₁)) ∈ U \ Δ
        rw [heq]
        exact hbdD_sub hγt₁_mem
      · have hlt_t₁ : projIcc 0 1 zero_le_one (s * t₁) < t₁ := by
          change (projIcc 0 1 zero_le_one (s * t₁) : ℝ) < t₁
          rw [projIcc_of_mem zero_le_one hst]
          exact mul_lt_of_lt_one_left ht₁_pos hs_lt
        exact ⟨hγU _, fun hxΔ => not_le.mpr hlt_t₁ (hlow₁ (hΔD hxΔ))⟩
    have hj2 : JoinedIn (U \ Δ) (γ t₁) (γ t₂) :=
      (hbdD_pc.joinedIn _ hγt₁_mem _ hγt₂_mem).mono hbdD_sub
    have hj3 : JoinedIn (U \ Δ) (γ t₂) y := by
      let f3 : ℝ → Z := fun s => γ (projIcc 0 1 zero_le_one ((1 - s) * t₂ + s))
      refine JoinedIn.ofLine (f := f3)
        (γ.continuous.comp (continuous_projIcc.comp (by fun_prop))).continuousOn
        (by simp [f3]) (by simp [f3]) ?_
      rintro _ ⟨s, hs, rfl⟩
      have hst : (1 - s) * (t₂ : ℝ) + s ∈ Icc (0 : ℝ) 1 :=
        ⟨by nlinarith [hs.1, hs.2, t₂.2.1], by nlinarith [hs.1, hs.2, t₂.2.2]⟩
      rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
      · have heq : projIcc 0 1 zero_le_one ((1 - (0 : ℝ)) * t₂ + 0) = t₂ := by simp
        change γ (projIcc 0 1 zero_le_one ((1 - (0 : ℝ)) * t₂ + 0)) ∈ U \ Δ
        rw [heq]
        exact hbdD_sub hγt₂_mem
      · have hgt_t₂ : t₂ < projIcc 0 1 zero_le_one ((1 - s) * t₂ + s) := by
          change (t₂ : ℝ) < (projIcc 0 1 zero_le_one ((1 - s) * t₂ + s) : ℝ)
          rw [projIcc_of_mem zero_le_one hst]
          have ht₂_lt' : (t₂ : ℝ) < 1 := ht₂_lt
          nlinarith
        exact ⟨hγU _, fun hxΔ => not_le.mpr hgt_t₂ (hhigh₂ (hΔD hxΔ))⟩
    exact (hj1.trans hj2).trans hj3
  · refine ⟨γ, fun t => ⟨hγU t, fun hxΔ => hhit ⟨γ t, mem_range_self t, hΔD hxΔ⟩⟩⟩

/-- Finite-set induction of `isPathConnected_diff_pinched_disc` for pairwise exterior-disjoint
pinched discs attached to `B₁`. -/
theorem isPathConnected_compl_union_pinched {Z : Type} [TopologicalSpace Z]
    (hS : IsClosedSurface Z) (hsph : IsSphere Z) {B₁ : Set Z} (hB₁ : IsClosedDisc B₁)
    {z₀ : Z} (hz₀_notB₁ : z₀ ∉ B₁)
    {ι : Type*} (Δ : ι → Set Z) (u : ι → Z) (s : Finset ι)
    (hdisc : ∀ i ∈ s, IsClosedDisc (Δ i))
    (hu_bd : ∀ i ∈ s, u i ∈ discBd (Δ i))
    (hpinch : ∀ i ∈ s, Δ i ∩ B₁ = {u i})
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Δ i ∩ Δ j ⊆ B₁)
    (hz₀_off : ∀ i ∈ s, z₀ ∉ Δ i) :
    IsOpen ((B₁ ∪ ⋃ i ∈ s, Δ i)ᶜ) ∧ IsPathConnected ((B₁ ∪ ⋃ i ∈ s, Δ i)ᶜ) := by
  classical
  have : T2Space Z := hS.2.1
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty]
    obtain ⟨hE, hbE⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hB₁
    have heq : B₁ᶜ = discInt (closure (univ \ B₁)) := by
      ext x
      rw [mem_compl_iff, discInt, mem_sdiff, hbE]
      constructor
      · intro hx
        exact ⟨subset_closure ⟨mem_univ x, hx⟩, fun hb => hx (Surface.discBd_subset B₁ hb)⟩
      · rintro ⟨hxcl, hnotBd⟩ hxB₁
        have hxfr : x ∈ frontier B₁ := by
          rw [frontier_eq_closure_inter_closure, hB₁.isClosed.closure_eq, compl_eq_univ_sdiff]
          exact ⟨hxB₁, hxcl⟩
        rw [IsClosedDisc.frontier_eq_discBd hS hB₁] at hxfr
        exact hnotBd hxfr
    have hopen : IsOpen B₁ᶜ := hB₁.isClosed.isOpen_compl
    have hopen' : IsOpen (discInt (closure (univ \ B₁))) := heq ▸ hopen
    have hz₀' : z₀ ∈ discInt (closure (univ \ B₁)) := heq ▸ hz₀_notB₁
    rw [heq]
    exact ⟨hopen', GM11.isPathConnected_of_isOpen hS hopen' hE.isPreconnected_discInt ⟨z₀, hz₀'⟩⟩
  | @insert i₀ s hi₀ ih =>
    have hdisc' : ∀ i ∈ s, IsClosedDisc (Δ i) := fun i hi => hdisc i (Finset.mem_insert_of_mem hi)
    have hu_bd' : ∀ i ∈ s, u i ∈ discBd (Δ i) := fun i hi => hu_bd i (Finset.mem_insert_of_mem hi)
    have hpinch' : ∀ i ∈ s, Δ i ∩ B₁ = {u i} :=
      fun i hi => hpinch i (Finset.mem_insert_of_mem hi)
    have hpair' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Δ i ∩ Δ j ⊆ B₁ :=
      fun i hi j hj hij => hpair i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have hz₀_off' : ∀ i ∈ s, z₀ ∉ Δ i := fun i hi => hz₀_off i (Finset.mem_insert_of_mem hi)
    obtain ⟨hUo, hUp⟩ := ih hdisc' hu_bd' hpinch' hpair' hz₀_off'
    let U := (B₁ ∪ ⋃ i ∈ s, Δ i)ᶜ
    have hset_eq : (B₁ ∪ ⋃ i ∈ insert i₀ s, Δ i)ᶜ = U \ Δ i₀ := by
      ext x
      simp only [U, mem_compl_iff, mem_union, mem_iUnion, Finset.mem_insert, mem_sdiff]
      constructor
      · intro h
        refine ⟨fun hBs => h ?_, fun hx0 => h (Or.inr ⟨i₀, Or.inl rfl, hx0⟩)⟩
        rcases hBs with hB | ⟨i, hi, hxi⟩
        · exact Or.inl hB
        · exact Or.inr ⟨i, Or.inr hi, hxi⟩
      · rintro ⟨hU, hnot0⟩ (hB | ⟨i, rfl | hi, hxi⟩)
        · exact hU (Or.inl hB)
        · exact hnot0 hxi
        · exact hU (Or.inr ⟨i, hi, hxi⟩)
    rw [hset_eq]
    have hi₀_mem : i₀ ∈ insert i₀ s := Finset.mem_insert_self i₀ s
    have hinter : Δ i₀ ∩ Uᶜ = {u i₀} := by
      simp only [U, compl_compl]
      apply Subset.antisymm
      · rintro x ⟨hx0, hxB | hxU⟩
        · exact (hpinch i₀ hi₀_mem).subset ⟨hx0, hxB⟩
        · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxU
          have hij : i₀ ≠ j := fun e => hi₀ (e ▸ hj)
          have hxB := hpair i₀ hi₀_mem j (Finset.mem_insert_of_mem hj) hij ⟨hx0, hxj⟩
          exact (hpinch i₀ hi₀_mem).subset ⟨hx0, hxB⟩
      · rintro x rfl
        have hu0 : u i₀ ∈ Δ i₀ ∩ B₁ := (hpinch i₀ hi₀_mem).symm.subset rfl
        exact ⟨hu0.1, Or.inl hu0.2⟩
    have hne : (U \ Δ i₀).Nonempty := ⟨z₀, ⟨by
      simp only [U, mem_compl_iff, mem_union, mem_iUnion, not_or, not_exists]
      exact ⟨hz₀_notB₁, hz₀_off'⟩, hz₀_off i₀ hi₀_mem⟩⟩
    exact isPathConnected_diff_pinched_disc hS hUo hUp hne
      (hdisc i₀ hi₀_mem) (hu_bd i₀ hi₀_mem) hinter

/-- Distinct edges of a drawing are disjoint. -/
theorem disjoint_edges_of_ne_local {Z : Type*} [TopologicalSpace Z] (Γ : Drawing Z)
    {e₁ e₂ : Set Z} (he₁ : e₁ ∈ Γ.E) (he₂ : e₂ ∈ Γ.E) (hne : e₁ ≠ e₂) :
    Disjoint e₁ e₂ := by
  rw [disjoint_left]
  intro x hx₁ hx₂
  have hpc : IsPathConnected (e₁ ∪ e₂) := he₁.2.2.1.union he₂.2.2.1 ⟨x, hx₁, hx₂⟩
  have hsub : e₁ ∪ e₂ ⊆ Γ.U \ Γ.V := union_subset he₁.2.1 he₂.2.1
  have heq₁ : e₁ ∪ e₂ = e₁ := he₁.2.2.2 _ hsub hpc subset_union_left
  have heq₂ : e₁ ∪ e₂ = e₂ := he₂.2.2.2 _ hsub hpc subset_union_right
  exact hne (heq₁.symm.trans heq₂)

/-- For any edge `e ∈ Γ.E` of a drawing on a Hausdorff space `Z`, `Γ.U \ e` is closed. -/
theorem isClosed_U_diff_edge {Z : Type} [TopologicalSpace Z] [T2Space Z]
    (Γ : Drawing Z) {e : Set Z} (he : e ∈ Γ.E) :
    IsClosed (Γ.U \ e) := by
  classical
  have heq : Γ.U \ e = Γ.V ∪ ⋃ e' ∈ Γ.E \ {e}, closure e' := by
    ext x
    constructor
    · rintro ⟨hxU, hxe⟩
      by_cases hxV : x ∈ Γ.V
      · exact Or.inl hxV
      · obtain ⟨e', he', hxe'⟩ := Γ.exists_edge_of_mem hxU hxV
        have hne : e' ≠ e := fun h => hxe (h ▸ hxe')
        exact Or.inr (mem_biUnion ⟨he', hne⟩ (subset_closure hxe'))
    · rintro (hxV | hx)
      · exact ⟨Γ.V_subset_U hxV, fun hxe => (he.2.1 hxe).2 hxV⟩
      · obtain ⟨e', ⟨he', hne⟩, hxcl⟩ := mem_iUnion₂.mp hx
        refine ⟨Γ.closure_subset_U he' hxcl, fun hxe => ?_⟩
        by_cases hxV : x ∈ Γ.V
        · exact (he.2.1 hxe).2 hxV
        · have hxe' : x ∈ e' :=
            (GM09.closure_edge_diff_V_eq Γ he').subset ⟨hxcl, hxV⟩
          exact disjoint_left.mp (disjoint_edges_of_ne_local Γ he' he hne) hxe' hxe
  rw [heq]
  exact Γ.finite_V.isClosed.union
    ((Γ.finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure)

/-- If `R = connectedComponentIn (B₁ ∪ Γ.U)ᶜ q₀` on a closed surface `Z` and an edge `e ∈ Γ.E`
disjoint from a closed set `B₁` meets `closure R`, then `closure e ⊆ closure R`. -/
theorem closure_edge_subset_closure_component {Z : Type} [TopologicalSpace Z]
    (hS : IsClosedSurface Z) (Γ : Drawing Z) {B₁ : Set Z} (hB₁ : IsClosed B₁)
    {q₀ : Z} {e : Set Z} (he : e ∈ Γ.E) (hdisB : Disjoint e B₁)
    (hhit : (e ∩ closure (connectedComponentIn (B₁ ∪ Γ.U)ᶜ q₀)).Nonempty) :
    closure e ⊆ closure (connectedComponentIn (B₁ ∪ Γ.U)ᶜ q₀) := by
  have : T2Space Z := hS.2.1
  have hman : ∀ z : Z, IsManifoldPoint z := fun z => (hS.2.2 z).isManifoldPoint
  let Ω : Set Z := (B₁ ∪ Γ.U)ᶜ
  let R : Set Z := connectedComponentIn Ω q₀
  suffices he_sub : e ⊆ closure R from closure_minimal he_sub isClosed_closure
  have hlocal : ∀ x ∈ e, ∃ J a b, a ≠ b ∧ IsLineWithEnds J a b ∧ J ⊆ closure e ∧
      J \ {a, b} ⊆ e ∧ x ∈ J \ {a, b} ∧ IsOpen ((Subtype.val : e → Z) ⁻¹' (J \ {a, b})) ∧
      IsClosed (Γ.U \ (J \ {a, b})) := by
    intro x hxe
    have hx_notV : x ∉ Γ.V := (he.2.1 hxe).2
    have hcl_diff : closure e \ Γ.V = e := GM09.closure_edge_diff_V_eq Γ he
    rcases Γ.edge_cond e he with ⟨u, v, huv, hcap, hline⟩ | ⟨u, hcap, ho⟩
    · have he_eq : closure e \ {u, v} = e := by
        calc closure e \ {u, v}
            = closure e \ Γ.V := by
              ext y
              simp only [mem_sdiff]
              exact ⟨fun ⟨hy, hnuv⟩ => ⟨hy, fun hyV => hnuv (hcap.subset ⟨hy, hyV⟩)⟩,
                fun ⟨hy, hyV⟩ => ⟨hy, fun huv' => hyV (hcap.symm.subset huv').2⟩⟩
          _ = e := hcl_diff
      refine ⟨closure e, u, v, huv, hline, Subset.rfl, he_eq.le,
        by rw [he_eq]; exact hxe, ?_, ?_⟩
      · rw [he_eq]
        have : (Subtype.val : e → Z) ⁻¹' e = univ := eq_univ_of_forall fun y => y.2
        rw [this]
        exact isOpen_univ
      · rw [he_eq]
        exact isClosed_U_diff_edge Γ he
    · obtain ⟨φ⟩ := id ho
      let c₀ : Circle := φ.symm ⟨x, subset_closure hxe⟩
      let cu : Circle := φ.symm ⟨u, (hcap.symm.subset rfl).1⟩
      have hc₀_ne_cu : c₀ ≠ cu := fun h => by
        have hval : (φ c₀).1 = (φ cu).1 := congrArg (fun c => (φ c).1) h
        simp only [c₀, cu, Homeomorph.apply_symm_apply] at hval
        exact hx_notV (hval ▸ (hcap.symm.subset rfl).2)
      let g : ℝ → Circle := fun t => c₀ * Circle.exp t
      have hg_cont : Continuous g := continuous_const.mul Circle.exp.continuous
      have h0_mem : (0 : ℝ) ∈ g ⁻¹' ({cu}ᶜ : Set Circle) := by
        simpa [g] using hc₀_ne_cu
      obtain ⟨ε, hε, hball⟩ :=
        Metric.isOpen_iff.mp (isOpen_compl_singleton.preimage hg_cont) 0 h0_mem
      let δ : ℝ := min (ε / 2) (Real.pi / 3)
      have hδ : 0 < δ := lt_min (half_pos hε) (div_pos Real.pi_pos (by norm_num))
      have hδ_lt_ε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
      have hδ_lt_pi : 2 * δ < 2 * Real.pi := by
        have := min_le_right (ε / 2) (Real.pi / 3)
        linarith [Real.pi_pos]
      let ψ : unitInterval → Z := fun t => (φ (g (δ * (2 * (t : ℝ) - 1)))).1
      have hψ_cont : Continuous ψ :=
        continuous_subtype_val.comp (φ.continuous.comp (hg_cont.comp (by fun_prop)))
      have hψ_inj : Injective ψ := by
        intro t₁ t₂ heq
        have hgc : g (δ * (2 * (t₁ : ℝ) - 1)) = g (δ * (2 * (t₂ : ℝ) - 1)) :=
          φ.injective (Subtype.ext heq)
        have hexp : Circle.exp (δ * (2 * (t₁ : ℝ) - 1)) = Circle.exp (δ * (2 * (t₂ : ℝ) - 1)) :=
          mul_left_cancel hgc
        rw [Circle.exp_eq_exp] at hexp
        obtain ⟨n, hn⟩ := hexp
        have hdiff_lt : |δ * (2 * (t₁ : ℝ) - 1) - δ * (2 * (t₂ : ℝ) - 1)| < 2 * Real.pi := by
          have : |2 * (t₁ : ℝ) - 1 - (2 * (t₂ : ℝ) - 1)| ≤ 2 := by
            rw [abs_le]; constructor <;> linarith [t₁.2.1, t₁.2.2, t₂.2.1, t₂.2.2]
          calc |δ * (2 * (t₁ : ℝ) - 1) - δ * (2 * (t₂ : ℝ) - 1)|
              = δ * |2 * (t₁ : ℝ) - 1 - (2 * (t₂ : ℝ) - 1)| := by
                rw [← mul_sub, abs_mul, abs_of_pos hδ]
            _ ≤ 2 * δ := by nlinarith
            _ < 2 * Real.pi := hδ_lt_pi
        have hn0 : n = 0 := by
          by_contra hn0
          have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
          have h2pi_pos : 0 < 2 * Real.pi := mul_pos zero_lt_two Real.pi_pos
          have hge : 2 * Real.pi ≤ |(n : ℝ) * (2 * Real.pi)| := by
            rw [abs_mul, abs_of_pos h2pi_pos]
            nlinarith
          have heq_abs : |δ * (2 * (t₁ : ℝ) - 1) - δ * (2 * (t₂ : ℝ) - 1)| =
              |(n : ℝ) * (2 * Real.pi)| := congrArg abs (by linarith)
          linarith
        subst hn0
        simp only [Int.cast_zero, zero_mul, add_zero] at hn
        have := mul_left_cancel₀ hδ.ne' hn
        exact Subtype.ext (by linarith)
      let J := range ψ
      let a := ψ 0
      let b := ψ 1
      have hab : a ≠ b := fun h => zero_ne_one (hψ_inj h)
      have hemb : IsEmbedding ψ := (hψ_cont.isClosedEmbedding hψ_inj).isEmbedding
      have hline : IsLineWithEnds J a b := ⟨hemb.toHomeomorph, rfl, rfl⟩
      have hJ_sub_e : J ⊆ e := by
        rintro _ ⟨t, rfl⟩
        have habs : |δ * (2 * (t : ℝ) - 1) - 0| < ε := by
          have : |2 * (t : ℝ) - 1| ≤ 1 := abs_le.mpr ⟨by linarith [t.2.1], by linarith [t.2.2]⟩
          rw [sub_zero, abs_mul, abs_of_pos hδ]
          nlinarith
        have hne_cu : g (δ * (2 * (t : ℝ) - 1)) ≠ cu := hball (by simpa [Metric.mem_ball] using habs)
        have hne_u : ψ t ≠ u := fun h => hne_cu (φ.injective (Subtype.ext (h.trans (by simp [cu]))))
        rw [← hcl_diff]
        exact ⟨(φ _).2, fun hyV => hne_u (hcap.subset ⟨(φ _).2, hyV⟩)⟩
      let mid : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
      have hψ_mid : ψ mid = x := by
        simp [ψ, mid, g, c₀]
      have hx_mem : x ∈ J \ {a, b} := by
        rw [← hψ_mid]
        refine ⟨⟨mid, rfl⟩, ?_⟩
        rintro (h0 | h1)
        · have := congrArg Subtype.val (hψ_inj h0); dsimp [mid] at this; norm_num at this
        · have := congrArg Subtype.val (hψ_inj h1); dsimp [mid] at this; norm_num at this
      have hJ_int_eq : J \ {a, b} = (fun c : Circle => (φ c).1) '' (g '' Ioo (-δ) δ) := by
        ext y
        constructor
        · rintro ⟨⟨t, rfl⟩, hnot⟩
          have ht0 : t ≠ 0 := fun h => hnot (Or.inl (congrArg ψ h))
          have ht1 : t ≠ 1 := fun h => hnot (Or.inr (congrArg ψ h))
          have ht0' : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (Subtype.coe_ne_coe.mpr ht0).symm
          have ht1' : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (Subtype.coe_ne_coe.mpr ht1)
          exact ⟨_, ⟨δ * (2 * (t : ℝ) - 1), ⟨by nlinarith, by nlinarith⟩, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨s, ⟨hs1, hs2⟩, rfl⟩, rfl⟩
          let t : unitInterval := ⟨(s / δ + 1) / 2,
            by have := (lt_div_iff₀ hδ).mpr (by linarith : -1 * δ < s); linarith,
            by have := (div_lt_iff₀ hδ).mpr (by linarith : s < 1 * δ); linarith⟩
          have hst : δ * (2 * (t : ℝ) - 1) = s := by dsimp [t]; field_simp; ring
          rw [← hst]
          refine ⟨⟨t, rfl⟩, ?_⟩
          rintro (h0 | h1)
          · have hval := congrArg Subtype.val (hψ_inj h0)
            dsimp [t] at hval
            have : s / δ = -1 := by linarith
            have : s = -δ := by rw [div_eq_iff hδ.ne'] at this; linarith
            linarith
          · have hval := congrArg Subtype.val (hψ_inj h1)
            dsimp [t] at hval
            have : s / δ = 1 := by linarith
            have : s = δ := by rw [div_eq_iff hδ.ne'] at this; linarith
            linarith
      let mL : Circle ≃ₜ Circle :=
        ⟨Equiv.mulLeft c₀, continuous_const.mul continuous_id, continuous_const.mul continuous_id⟩
      have hg_open : IsOpen (g '' Ioo (-δ) δ) := by
        have hg_eq : g '' Ioo (-δ) δ = mL '' (Circle.exp '' Ioo (-δ) δ) := by
          rw [← image_comp]; rfl
        rw [hg_eq]
        exact mL.isOpenMap _ (isLocalHomeomorph_circleExp.isOpenMap _ isOpen_Ioo)
      have hopen_cl : IsOpen ((Subtype.val : closure e → Z) ⁻¹' (J \ {a, b})) := by
        have heq : (Subtype.val : closure e → Z) ⁻¹' (J \ {a, b}) = φ '' (g '' Ioo (-δ) δ) := by
          ext z
          rw [mem_preimage, hJ_int_eq]
          exact ⟨fun ⟨c, hc, hcz⟩ => ⟨c, hc, Subtype.ext hcz⟩,
            fun ⟨c, hc, hcz⟩ => ⟨c, hc, congrArg Subtype.val hcz⟩⟩
        rw [heq]
        exact φ.isOpenMap _ hg_open
      have hopen_e : IsOpen ((Subtype.val : e → Z) ⁻¹' (J \ {a, b})) := by
        let incl : e → closure e := fun y => ⟨y.1, subset_closure y.2⟩
        have hincl_cont : Continuous incl := Continuous.subtype_mk continuous_subtype_val _
        exact hopen_cl.preimage hincl_cont
      have hcl_compl_J : IsClosed (closure e \ (J \ {a, b})) := by
        have heq : closure e \ (J \ {a, b}) =
            (fun c : Circle => (φ c).1) '' ((g '' Ioo (-δ) δ)ᶜ) := by
          rw [hJ_int_eq]
          ext y
          constructor
          · rintro ⟨hycl, hynot⟩
            exact ⟨φ.symm ⟨y, hycl⟩, fun h => hynot ⟨_, h, by simp⟩, by simp⟩
          · rintro ⟨c, hc, rfl⟩
            refine ⟨(φ c).2, ?_⟩
            rintro ⟨c', hc', heq'⟩
            exact hc ((φ.injective (Subtype.ext heq')) ▸ hc')
        rw [heq]
        exact (hg_open.isClosed_compl.isCompact.image
          (continuous_subtype_val.comp φ.continuous)).isClosed
      have hcl_U : IsClosed (Γ.U \ (J \ {a, b})) := by
        have heq : Γ.U \ (J \ {a, b}) = (Γ.U \ e) ∪ (closure e \ (J \ {a, b})) := by
          have hsub1 : J \ {a, b} ⊆ e := sdiff_subset.trans hJ_sub_e
          have hsub2 : closure e ⊆ Γ.U := Γ.closure_subset_U he
          ext y
          simp only [mem_sdiff, mem_union]
          constructor
          · rintro ⟨hyU, hnot⟩
            by_cases hye : y ∈ e
            · exact Or.inr ⟨subset_closure hye, hnot⟩
            · exact Or.inl ⟨hyU, hye⟩
          · rintro (⟨hyU, hye⟩ | ⟨hycl, hnot⟩)
            · exact ⟨hyU, fun hj => hye (hsub1 hj)⟩
            · exact ⟨hsub2 hycl, hnot⟩
        rw [heq]
        exact (isClosed_U_diff_edge Γ he).union hcl_compl_J
      exact ⟨J, a, b, hab, hline, hJ_sub_e.trans subset_closure,
        sdiff_subset.trans hJ_sub_e, hx_mem, hopen_e, hcl_U⟩
  let S_cl : Set e := (Subtype.val : e → Z) ⁻¹' closure R
  have hS_closed : IsClosed S_cl := isClosed_closure.preimage continuous_subtype_val
  have hS_open : IsOpen S_cl := by
    rw [isOpen_iff_forall_mem_open]
    intro x₀ hx₀
    obtain ⟨J, a, b, hab, hline, hJ_cl, hJ_e, hx₀J, hopen_J, hcl_UJ⟩ := hlocal x₀.1 x₀.2
    let Z_lens := B₁ ∪ (Γ.U \ (J \ {a, b}))
    have hZ_closed : IsClosed Z_lens := hB₁.union hcl_UJ
    have hJZ : J ∩ Z_lens ⊆ {a, b} := by
      rintro y ⟨hyJ, hyB | ⟨_, hnot⟩⟩
      · by_contra hnuv
        exact disjoint_left.mp hdisB (hJ_e ⟨hyJ, hnuv⟩) hyB
      · by_contra hnuv
        exact hnot ⟨hyJ, hnuv⟩
    obtain ⟨D, A, B, hD, hJD, hDZ, _, _, hbdDJ, hD_eq, hApc, hBpc, _, _, hdisAJ, hdisBJ,
      hJ_clA, hJ_clB, _, _, _, _, _⟩ :=
      exists_edge_lens_sides hS hline hab hZ_closed hJZ
    have hx₀_intD : x₀.1 ∈ discInt D :=
      ⟨hJD hx₀J.1, fun hb => hx₀J.2 (hbdDJ ⟨hb, hx₀J.1⟩)⟩
    obtain ⟨r, hr_intD, hrR⟩ :=
      mem_closure_iff.mp hx₀ (discInt D) (hD.isOpen_discInt hman) hx₀_intD
    have hr_notJ : r ∉ J := fun hrJ =>
      (connectedComponentIn_subset Ω q₀ hrR) (Or.inr (Γ.closure_subset_U he (hJ_cl hrJ)))
    have hA_Ω : A ⊆ Ω := by
      intro y hyA
      have hyD : y ∈ D := hD_eq ▸ Or.inl (Or.inl hyA)
      have hy_notJ : y ∉ J := disjoint_left.mp hdisAJ hyA
      have hy_notZ : y ∉ Z_lens := fun hyZ =>
        hy_notJ (by rcases hDZ ⟨hyD, hyZ⟩ with rfl | rfl
                    · exact hline.left_mem
                    · exact hline.right_mem)
      rintro (hyB₁ | hyU)
      · exact hy_notZ (Or.inl hyB₁)
      · exact hy_notZ (Or.inr ⟨hyU, fun hj => hy_notJ hj.1⟩)
    have hB_Ω : B ⊆ Ω := by
      intro y hyB
      have hyD : y ∈ D := hD_eq ▸ Or.inl (Or.inr hyB)
      have hy_notJ : y ∉ J := disjoint_left.mp hdisBJ hyB
      have hy_notZ : y ∉ Z_lens := fun hyZ =>
        hy_notJ (by rcases hDZ ⟨hyD, hyZ⟩ with rfl | rfl
                    · exact hline.left_mem
                    · exact hline.right_mem)
      rintro (hyB₁ | hyU)
      · exact hy_notZ (Or.inl hyB₁)
      · exact hy_notZ (Or.inr ⟨hyU, fun hj => hy_notJ hj.1⟩)
    have hJ_sub_clR : J ⊆ closure R := by
      rcases (hD_eq ▸ hr_intD.1 : r ∈ A ∪ B ∪ J) with (hrA | hrB) | hrJ
      · have hAR : A ⊆ R := by
          have hsub := hApc.subset_connectedComponentIn hrA hA_Ω
          rwa [show connectedComponentIn Ω r = R from (connectedComponentIn_eq hrR).symm] at hsub
        exact hJ_clA.trans (closure_mono hAR)
      · have hBR : B ⊆ R := by
          have hsub := hBpc.subset_connectedComponentIn hrB hB_Ω
          rwa [show connectedComponentIn Ω r = R from (connectedComponentIn_eq hrR).symm] at hsub
        exact hJ_clB.trans (closure_mono hBR)
      · exact absurd hrJ hr_notJ
    refine ⟨(Subtype.val : e → Z) ⁻¹' (J \ {a, b}), ?_, hopen_J, hx₀J⟩
    intro y hy
    exact hJ_sub_clR hy.1
  have : ConnectedSpace e := isConnected_iff_connectedSpace.mp he.2.2.1.isConnected
  obtain ⟨z_hit, hze, hzcl⟩ := hhit
  have hS_ne : S_cl.Nonempty := ⟨⟨z_hit, hze⟩, hzcl⟩
  have hS_univ : S_cl = univ := IsClopen.eq_univ ⟨hS_closed, hS_open⟩ hS_ne
  intro y hye
  have : (⟨y, hye⟩ : e) ∈ S_cl := hS_univ ▸ mem_univ _
  exact this

end GraphMinor.GM08
