module

public import GraphMinor.GM03.Section2j
public import GraphMinor.GM03.Section2k
public import GraphMinor.Surface.Collar
public import GraphMinor.Surface.Cap
public import GraphMinor.Surface.Crossing
public import GraphMinor.Surface.PlaneLog

/-!
# Graph Minors III, Section 2l: O-Arc Circuit Enumeration and Annulus Monotone Bipartite Ordering
(for (2.3))

This file establishes the cyclic circuit parameterization and universal-cover non-crossing
monotonicity for radial arcs across a planar annulus for `(2.3)` (page 55) of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
`three_le_ncard_V_of_isCircuit_simple`, `exists_circuitCycle_of_homeo`, `rect_strip_noncrossing`,
and `annulus_monotone_bipartite_order`.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Metric
open Graph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11

local notation "𝕀" => unitInterval

universe u v

/-! ## 3. `O`-Arc Circuit Enumeration and Annulus Monotone Bipartite Ordering -/

section AnnulusOrder

/-- Every simple circuit drawing `C` has `3 ≤ C.V.ncard`. -/
theorem three_le_ncard_V_of_isCircuit_simple {S : Type*} [TopologicalSpace S] [T2Space S]
    {C : Drawing S} (hC : C.IsCircuit) (hSimple : C.toGraph.Simple) :
    3 ≤ C.V.ncard := by
  obtain ⟨u, W, hCyc, hPos, hV, _⟩ := hC
  have hlen3 : 3 ≤ W.length := by
    rcases W with _ | ⟨hl₁, W₁⟩
    · simp at hPos
    · rcases W₁ with _ | ⟨hl₂, W₂⟩
      · exact (hSimple.not_isLoopAt _ _ hl₁).elim
      · rcases W₂ with _ | ⟨_, _⟩
        · have heq := hSimple.eq_of_isLink hl₁ hl₂.symm
          have hnd := List.nodup_cons.mp hCyc.2
          exact (hnd.1 (heq ▸ List.mem_cons_self)).elim
        · simp [GraphWalk.length]
  have htail_nd : W.support.tail.Nodup := hCyc.1
  have htail_len : W.support.tail.length = W.length := by
    have hsup_len : ∀ {a b : S} (Q : GraphWalk C.toGraph a b), Q.support.length = Q.length + 1 := by
      intro a b Q
      induction Q with
      | nil _ => rfl
      | cons _ _ ih => simp [GraphWalk.support, GraphWalk.length, ih]
    cases h : W.support with
    | nil =>
      have := hsup_len W
      rw [h] at this; simp at this
    | cons _ tl =>
      have := hsup_len W
      rw [h] at this; simp at this ⊢; omega
  have hsub : {x | x ∈ W.support.tail} ⊆ C.V := by
    rw [hV]
    intro x hx
    exact List.mem_of_mem_tail hx
  classical
  have hcard_tail : {x | x ∈ W.support.tail}.ncard = W.length := by
    have heq_set : {x | x ∈ W.support.tail} = (W.support.tail.toFinset : Set S) := by ext x; simp
    rw [heq_set, Set.ncard_coe_finset, List.toFinset_card_of_nodup htail_nd, htail_len]
  have hle := Set.ncard_le_ncard hsub C.finite_V
  omega

/-- Given a simple circuit drawing `C : Drawing S`, a homeomorphism `φ : Circle ≃ₜ C.U`, and a base
angle `α₀ : ℝ`, sorting the vertex angles in `Ico α₀ (α₀ + 2 * Real.pi)` constructs
`cyc : CircuitCycle C.toGraph C.V.ncard` with strictly increasing angles `θ_v : Fin C.V.ncard → ℝ`. -/
theorem exists_circuitCycle_of_homeo {S : Type*} [TopologicalSpace S] [T2Space S]
    (C : Drawing S) (hC : C.IsCircuit) (hSimple : C.toGraph.Simple)
    (φ : Circle ≃ₜ C.U) (α₀ : ℝ) :
    ∃ (cyc : CircuitCycle C.toGraph C.V.ncard) (θ_v : Fin C.V.ncard → ℝ),
      StrictMono θ_v ∧
      (∀ t : Fin C.V.ncard, θ_v t ∈ Ico α₀ (α₀ + 2 * Real.pi)) ∧
      (∀ t : Fin C.V.ncard, (φ (Circle.exp (θ_v t))).1 = cyc.u t) ∧
      (∀ θ ∈ Ico α₀ (α₀ + 2 * Real.pi), (φ (Circle.exp θ)).1 ∈ C.V →
        ∃ t : Fin C.V.ncard, θ = θ_v t) := by
  classical
  let p := C.V.ncard
  have hp3 : 3 ≤ p := three_le_ncard_V_of_isCircuit_simple hC hSimple
  have hp2 : 2 ≤ p := by omega
  let ψ : ℝ → S := fun θ => (φ (Circle.exp θ)).1
  have hψ_cont : Continuous ψ :=
    continuous_subtype_val.comp (φ.continuous.comp Circle.exp.continuous)
  have hψ_mem : ∀ θ : ℝ, ψ θ ∈ C.U := fun θ => (φ (Circle.exp θ)).2
  have hψ_eq_iff : ∀ s t : ℝ, ψ s = ψ t ↔ ∃ m : ℤ, s = t + m * (2 * Real.pi) := by
    intro s t
    constructor
    · intro h
      have h1 := φ.injective (Subtype.ext h)
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h1
      exact ⟨m, by linarith⟩
    · rintro ⟨m, rfl⟩
      have hexp : Circle.exp (t + m * (2 * Real.pi)) = Circle.exp t :=
        Circle.exp_eq_exp.mpr ⟨m, by ring⟩
      dsimp only [ψ]
      rw [hexp]
  have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hψ_inj_lt : ∀ {s t : ℝ}, |s - t| < 2 * Real.pi → ψ s = ψ t → s = t := by
    intro s t hlt heq
    obtain ⟨m, hm⟩ := (hψ_eq_iff s t).mp heq
    have hm0 : m = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      have h2 : |s - t| = |(m : ℝ)| * (2 * Real.pi) := by
        rw [hm, add_sub_cancel_left, abs_mul, abs_of_pos h2pi]
      nlinarith
    rw [hm, hm0]; ring
  let angOf : C.U → ℝ := fun x => toIcoMod h2pi α₀ (Complex.arg ((φ.symm x : Circle) : ℂ))
  have hang_mem : ∀ x : C.U, angOf x ∈ Ico α₀ (α₀ + 2 * Real.pi) :=
    fun x => toIcoMod_mem_Ico h2pi α₀ _
  have hψ_ang : ∀ x : C.U, ψ (angOf x) = x.1 := by
    intro x
    let z : Circle := φ.symm x
    have hk := self_sub_toIcoDiv_zsmul h2pi α₀ (Complex.arg (z : ℂ))
    have hexp : Circle.exp (angOf x) = z := by
      rw [← Circle.exp_arg z]
      refine Circle.exp_eq_exp.mpr ⟨-toIcoDiv h2pi α₀ (Complex.arg (z : ℂ)), ?_⟩
      dsimp only [angOf]
      rw [← hk, zsmul_eq_mul]
      push_cast; ring
    dsimp only [ψ]
    rw [hexp]
    exact congrArg Subtype.val (φ.apply_symm_apply x)
  let angV : S → ℝ := fun v => if hv : v ∈ C.U then angOf ⟨v, hv⟩ else α₀
  have hangV_eq : ∀ {v : S} (hv : v ∈ C.U), angV v = angOf ⟨v, hv⟩ := by
    intro v hv
    dsimp only [angV]
    split_ifs
    rfl
  have hangV_inj : InjOn angV C.V := by
    intro x hx y hy heq
    have hxU : x ∈ C.U := C.V_subset_U hx
    have hyU : y ∈ C.U := C.V_subset_U hy
    rw [hangV_eq hxU, hangV_eq hyU] at heq
    have := congrArg ψ heq
    rwa [hψ_ang ⟨x, hxU⟩, hψ_ang ⟨y, hyU⟩] at this
  let S_ang : Finset ℝ := C.finite_V.toFinset.image angV
  have hcard_S : S_ang.card = p := by
    dsimp only [S_ang, p]
    rw [Finset.card_image_of_injOn (fun x hx y hy h =>
      hangV_inj (C.finite_V.mem_toFinset.mp hx) (C.finite_V.mem_toFinset.mp hy) h)]
    exact (Set.ncard_eq_toFinset_card C.V C.finite_V).symm
  let θ_emb : Fin p ↪o ℝ := S_ang.orderEmbOfFin hcard_S
  let θ_v : Fin p → ℝ := fun t => θ_emb t
  have hθ_strict : StrictMono θ_v := θ_emb.strictMono
  have hθ_mem_S : ∀ t : Fin p, θ_v t ∈ S_ang := fun t => S_ang.orderEmbOfFin_mem hcard_S t
  have hS_iff : ∀ θ : ℝ, θ ∈ S_ang ↔ θ ∈ Ico α₀ (α₀ + 2 * Real.pi) ∧ ψ θ ∈ C.V := by
    intro θ
    dsimp only [S_ang]
    rw [Finset.mem_image]
    constructor
    · rintro ⟨v, hv_fin, rfl⟩
      have hvV : v ∈ C.V := C.finite_V.mem_toFinset.mp hv_fin
      have hvU : v ∈ C.U := C.V_subset_U hvV
      rw [hangV_eq hvU, hψ_ang ⟨v, hvU⟩]
      exact ⟨hang_mem ⟨v, hvU⟩, hvV⟩
    · rintro ⟨hIco, hV⟩
      refine ⟨ψ θ, C.finite_V.mem_toFinset.mpr hV, ?_⟩
      rw [hangV_eq (hψ_mem θ)]
      have hmem2 := hang_mem ⟨ψ θ, hψ_mem θ⟩
      refine hψ_inj_lt ?_ (hψ_ang ⟨ψ θ, hψ_mem θ⟩)
      rw [abs_lt]
      constructor <;> linarith [hIco.1, hIco.2, hmem2.1, hmem2.2]
  have hθ_Ico : ∀ t : Fin p, θ_v t ∈ Ico α₀ (α₀ + 2 * Real.pi) :=
    fun t => ((hS_iff (θ_v t)).mp (hθ_mem_S t)).1
  have hθ_in_V : ∀ t : Fin p, ψ (θ_v t) ∈ C.V :=
    fun t => ((hS_iff (θ_v t)).mp (hθ_mem_S t)).2
  have hθ_of_V : ∀ θ ∈ Ico α₀ (α₀ + 2 * Real.pi), ψ θ ∈ C.V → ∃ t : Fin p, θ = θ_v t := by
    intro θ hIco hV
    have hmem : θ ∈ Set.range θ_emb := by
      rw [Finset.range_orderEmbOfFin S_ang hcard_S]
      exact (hS_iff θ).mpr ⟨hIco, hV⟩
    obtain ⟨t, ht⟩ := hmem
    exact ⟨t, ht.symm⟩
  let u : Fin p → S := fun t => ψ (θ_v t)
  have hu_inj : Injective u := by
    intro t₁ t₂ heq
    have h1 := hθ_Ico t₁
    have h2 := hθ_Ico t₂
    have hteq : θ_v t₁ = θ_v t₂ := hψ_inj_lt (by
      rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]) heq
    exact hθ_strict.injective hteq
  have hu_range : V(C.toGraph) = range u := by
    change C.V = range u
    refine Subset.antisymm (fun v hv => ?_) (by rintro _ ⟨t, rfl⟩; exact hθ_in_V t)
    have hvU : v ∈ C.U := C.V_subset_U hv
    obtain ⟨t, ht⟩ := hθ_of_V (angOf ⟨v, hvU⟩) (hang_mem ⟨v, hvU⟩)
      (by rw [hψ_ang ⟨v, hvU⟩]; exact hv)
    exact ⟨t, by dsimp only [u]; rw [← ht, hψ_ang ⟨v, hvU⟩]⟩
  -- Define consecutive open arcs `ce t` along `Circle`
  let hi : Fin p → ℝ := fun t =>
    if h : t.1 + 1 < p then θ_v ⟨t.1 + 1, h⟩ else θ_v ⟨0, by omega⟩ + 2 * Real.pi
  let ce : Fin p → Set S := fun t => ψ '' Ioo (θ_v t) (hi t)
  have hhi_gt : ∀ t : Fin p, θ_v t < hi t ∧ hi t - θ_v t < 2 * Real.pi := by
    intro t
    dsimp only [hi]
    split_ifs with h
    · have hlt : θ_v t < θ_v ⟨t.1 + 1, h⟩ := hθ_strict (Fin.lt_def.mpr (by dsimp only; omega))
      have h1 := hθ_Ico t
      have h2 := hθ_Ico ⟨t.1 + 1, h⟩
      exact ⟨hlt, by linarith [h1.1, h2.2]⟩
    · have h0_lt : θ_v ⟨0, by omega⟩ < θ_v t :=
        hθ_strict (Fin.lt_def.mpr (by have ht_lt : t.1 < p := t.2; dsimp only; omega))
      have h1 := hθ_Ico ⟨0, by omega⟩
      have h2 := hθ_Ico t
      exact ⟨by linarith [h1.1, h2.2], by linarith⟩
  have hhi_ψ : ∀ t : Fin p, ψ (hi t) = u (nextSpoke t) := by
    intro t
    dsimp only [hi, nextSpoke, u]
    split_ifs with h
    · have hmod : (t.1 + 1) % p = t.1 + 1 := Nat.mod_eq_of_lt h
      congr 2; exact Fin.ext hmod.symm
    · have ht_eq : t.1 + 1 = p := by have := t.2; omega
      have hmod : (t.1 + 1) % p = 0 := by rw [ht_eq, Nat.mod_self]
      have hper : ψ (θ_v ⟨0, by omega⟩ + 2 * Real.pi) = ψ (θ_v ⟨0, by omega⟩) :=
        (hψ_eq_iff _ _).mpr ⟨1, by ring⟩
      rw [hper]
      congr 2; exact Fin.ext hmod.symm
  have hce_sub : ∀ t : Fin p, ce t ⊆ C.U \ C.V := by
    rintro t _ ⟨s, hs, rfl⟩
    refine ⟨hψ_mem s, fun hsV => ?_⟩
    dsimp only [hi] at hs
    split_ifs at hs with h
    · have hs_Ico : s ∈ Ico α₀ (α₀ + 2 * Real.pi) :=
        ⟨le_trans (hθ_Ico t).1 hs.1.le, lt_trans hs.2 (hθ_Ico ⟨t.1 + 1, h⟩).2⟩
      obtain ⟨r, rfl⟩ := hθ_of_V s hs_Ico hsV
      have h1 : t < r := hθ_strict.lt_iff_lt.mp hs.1
      have h2 : r < ⟨t.1 + 1, h⟩ := hθ_strict.lt_iff_lt.mp hs.2
      have := Fin.lt_def.mp h1; have := Fin.lt_def.mp h2; dsimp only at *; omega
    · by_cases hs_lt : s < α₀ + 2 * Real.pi
      · have hs_Ico : s ∈ Ico α₀ (α₀ + 2 * Real.pi) :=
          ⟨le_trans (hθ_Ico t).1 hs.1.le, hs_lt⟩
        obtain ⟨r, rfl⟩ := hθ_of_V s hs_Ico hsV
        have h1 : t < r := hθ_strict.lt_iff_lt.mp hs.1
        have := Fin.lt_def.mp h1; have := r.2; omega
      · have hs' : s - 2 * Real.pi ∈ Ico α₀ (α₀ + 2 * Real.pi) :=
          ⟨by linarith, by linarith [(hθ_Ico ⟨0, by omega⟩).2, hs.2]⟩
        have hψ' : ψ (s - 2 * Real.pi) ∈ C.V := by
          have heq : ψ (s - 2 * Real.pi) = ψ s := (hψ_eq_iff _ _).mpr ⟨-1, by ring⟩
          rwa [heq]
        obtain ⟨r, hr⟩ := hθ_of_V (s - 2 * Real.pi) hs' hψ'
        have h0_le : θ_v ⟨0, by omega⟩ ≤ θ_v r :=
          hθ_strict.monotone (Fin.le_def.mpr (Nat.zero_le _))
        linarith [hs.2]
  have hcover : C.U \ C.V = ⋃ t : Fin p, ce t := by
    refine Subset.antisymm (fun x ⟨hxU, hxV⟩ => ?_) (iUnion_subset hce_sub)
    let s := angOf ⟨x, hxU⟩
    have hs_Ico : s ∈ Ico α₀ (α₀ + 2 * Real.pi) := hang_mem ⟨x, hxU⟩
    have hψs : ψ s = x := hψ_ang ⟨x, hxU⟩
    have hs_ne : ∀ t : Fin p, s ≠ θ_v t := fun t heq => hxV (hψs ▸ heq ▸ hθ_in_V t)
    by_cases hs0 : s < θ_v ⟨0, by omega⟩
    · refine mem_iUnion.mpr ⟨⟨p - 1, by omega⟩, s + 2 * Real.pi, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · linarith [(hθ_Ico ⟨p - 1, by omega⟩).2, hs_Ico.1]
        · dsimp only [hi]
          split_ifs with h
          · omega
          · linarith
      · rw [← hψs]
        exact (hψ_eq_iff _ _).mpr ⟨1, by ring⟩
    · have hs0_gt : θ_v ⟨0, by omega⟩ < s := lt_of_le_of_ne (not_lt.mp hs0) (hs_ne _).symm
      by_cases hsp : θ_v ⟨p - 1, by omega⟩ < s
      · refine mem_iUnion.mpr ⟨⟨p - 1, by omega⟩, s, ⟨hsp, ?_⟩, hψs⟩
        dsimp only [hi]
        split_ifs with h
        · omega
        · linarith [hs_Ico.2, (hθ_Ico ⟨0, by omega⟩).1]
      · have hsp_lt : s < θ_v ⟨p - 1, by omega⟩ := lt_of_le_of_ne (not_lt.mp hsp) (hs_ne _)
        -- Largest `t` with `θ_v t < s`
        let P_set : Finset (Fin p) := Finset.univ.filter (fun t => θ_v t < s)
        have hP_ne : P_set.Nonempty := ⟨⟨0, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs0_gt⟩⟩
        let t_max := P_set.max' hP_ne
        have ht_lt : θ_v t_max < s := (Finset.mem_filter.mp (P_set.max'_mem hP_ne)).2
        have ht_lt_p : t_max.1 + 1 < p := by
          by_contra hge
          have ht_lt2 : t_max.1 < p := t_max.2
          have heq : t_max = ⟨p - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
          linarith [heq ▸ ht_lt]
        have hs_lt_next : s < θ_v ⟨t_max.1 + 1, ht_lt_p⟩ := by
          by_contra hge
          have hgt : θ_v ⟨t_max.1 + 1, ht_lt_p⟩ < s :=
            lt_of_le_of_ne (not_lt.mp hge) (hs_ne _).symm
          have hle := P_set.le_max' ⟨t_max.1 + 1, ht_lt_p⟩
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
          have := Fin.le_def.mp hle; dsimp only at this; omega
        refine mem_iUnion.mpr ⟨t_max, s, ⟨ht_lt, ?_⟩, hψs⟩
        dsimp only [hi]
        split_ifs
        exact hs_lt_next
  have hcl_ce : ∀ t : Fin p, closure (ce t) = ψ '' Icc (θ_v t) (hi t) := by
    intro t
    have hlt := (hhi_gt t).1
    refine Subset.antisymm ?_ ?_
    · exact closure_minimal (image_mono Ioo_subset_Icc_self) (isCompact_Icc.image hψ_cont).isClosed
    · rw [← closure_Ioo hlt.ne]
      exact image_closure_subset_closure_image hψ_cont
  have hce_cap_V : ∀ t : Fin p, closure (ce t) ∩ C.V = {u t, u (nextSpoke t)} := by
    intro t
    rw [hcl_ce t]
    refine Subset.antisymm ?_ ?_
    · rintro x ⟨⟨s, hs, rfl⟩, hsV⟩
      rcases eq_or_lt_of_le hs.1 with rfl | hgt
      · exact mem_insert _ _
      · rcases eq_or_lt_of_le hs.2 with rfl | hlt
        · rw [hhi_ψ t]; exact mem_insert_of_mem _ rfl
        · exact ((hce_sub t ⟨s, ⟨hgt, hlt⟩, rfl⟩).2 hsV).elim
    · rintro x (rfl | rfl)
      · exact ⟨⟨θ_v t, ⟨le_rfl, (hhi_gt t).1.le⟩, rfl⟩, hθ_in_V t⟩
      · exact ⟨⟨hi t, ⟨(hhi_gt t).1.le, le_rfl⟩, hhi_ψ t⟩, hθ_in_V (nextSpoke t)⟩
  have hce_disj : ∀ ⦃t₁ t₂ : Fin p⦄, t₁ ≠ t₂ → Disjoint (ce t₁) (ce t₂) := by
    intro t₁ t₂ hne
    rw [Set.disjoint_left]
    rintro x ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, heq⟩
    -- Shift both `s₁` and `s₂` into `Ico (θ_v 0) (θ_v 0 + 2 * Real.pi)`
    let θ₀ := θ_v ⟨0, by omega⟩
    have hnorm : ∀ (t : Fin p) (s : ℝ), s ∈ Ioo (θ_v t) (hi t) →
        s ∈ Ioo θ₀ (θ₀ + 2 * Real.pi) := by
      intro t s hs
      have h0_le : θ₀ ≤ θ_v t := hθ_strict.monotone (Fin.le_def.mpr (Nat.zero_le _))
      dsimp only [hi] at hs
      split_ifs at hs with h
      · have h_lt : θ_v ⟨t.1 + 1, h⟩ < θ₀ + 2 * Real.pi := by
          linarith [(hθ_Ico ⟨t.1 + 1, h⟩).2, (hθ_Ico ⟨0, by omega⟩).1]
        exact ⟨lt_of_le_of_lt h0_le hs.1, lt_trans hs.2 h_lt⟩
      · exact ⟨lt_of_le_of_lt h0_le hs.1, hs.2⟩
    have hn₁ := hnorm t₁ s₁ hs₁
    have hn₂ := hnorm t₂ s₂ hs₂
    have hs_eq : s₁ = s₂ := hψ_inj_lt (by
      rw [abs_lt]; constructor <;> linarith [hn₁.1, hn₁.2, hn₂.1, hn₂.2]) heq.symm
    subst hs_eq
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hhi_le : hi t₁ ≤ θ_v t₂ := by
        dsimp only [hi]
        split_ifs with h
        · exact hθ_strict.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hlt; dsimp only; omega))
        · have := Fin.lt_def.mp hlt; have := t₂.2; omega
      linarith [hs₁.2, hs₂.1]
    · have hhi_le : hi t₂ ≤ θ_v t₁ := by
        dsimp only [hi]
        split_ifs with h
        · exact hθ_strict.monotone (Fin.le_def.mpr (by have := Fin.lt_def.mp hgt; dsimp only; omega))
        · have := Fin.lt_def.mp hgt; have := t₁.2; omega
      linarith [hs₂.2, hs₁.1]
  have hce_pc : ∀ t : Fin p, IsPathConnected (ce t) := fun t =>
    ((convex_Ioo (θ_v t) (hi t)).isPathConnected (nonempty_Ioo.mpr (hhi_gt t).1)).image hψ_cont
  have hce_mem_E : ∀ t : Fin p, ce t ∈ C.E := by
    intro t
    refine ⟨(hce_pc t).nonempty, hce_sub t, hce_pc t, ?_⟩
    intro K hK_sub hK_pc hce_K
    refine Subset.antisymm (fun y hyK => ?_) hce_K
    by_contra hy_not
    obtain ⟨t', hy_t'⟩ := mem_iUnion.mp (hcover ▸ hK_sub hyK)
    have ht_ne : t ≠ t' := fun h => hy_not (h ▸ hy_t')
    let A := closure (ce t)
    let B := ⋃ s ∈ (Finset.univ.erase t : Finset (Fin p)), closure (ce s)
    have hA_cl : IsClosed A := isClosed_closure
    have hB_cl : IsClosed B :=
      ((Finset.univ.erase t : Finset (Fin p)).finite_toSet).isClosed_biUnion
        (fun _ _ => isClosed_closure)
    have hK_AB : K ⊆ A ∪ B := by
      intro z hzK
      obtain ⟨r, hzr⟩ := mem_iUnion.mp (hcover ▸ hK_sub hzK)
      by_cases hrt : r = t
      · exact Or.inl (subset_closure (hrt ▸ hzr))
      · exact Or.inr (mem_biUnion (Finset.mem_erase.mpr ⟨hrt, Finset.mem_univ r⟩)
          (subset_closure hzr))
    obtain ⟨x₀, hx₀⟩ := (hce_pc t).nonempty
    obtain ⟨w, hwK, hwA, hwB⟩ := isPreconnected_closed_iff.mp hK_pc.isConnected.isPreconnected
      A B hA_cl hB_cl hK_AB ⟨x₀, hce_K hx₀, subset_closure hx₀⟩
      ⟨y, hyK, mem_biUnion (Finset.mem_erase.mpr ⟨ht_ne.symm, Finset.mem_univ t'⟩)
        (subset_closure hy_t')⟩
    have hw_not_V : w ∉ C.V := (hK_sub hwK).2
    -- Since `w ∈ closure (ce t) \ C.V`, `w ∈ ce t`; similarly `w ∈ ce s` for some `s ≠ t`
    have hw_ce_t : w ∈ ce t := by
      dsimp only [A] at hwA
      rw [hcl_ce t] at hwA
      obtain ⟨s, hs, rfl⟩ := hwA
      rcases eq_or_lt_of_le hs.1 with rfl | hgt
      · exact (hw_not_V (hθ_in_V t)).elim
      · rcases eq_or_lt_of_le hs.2 with rfl | hlt
        · rw [hhi_ψ t] at hw_not_V
          exact (hw_not_V (hθ_in_V (nextSpoke t))).elim
        · exact ⟨s, ⟨hgt, hlt⟩, rfl⟩
    obtain ⟨s', hs'_er, hws'⟩ := mem_iUnion₂.mp hwB
    have hws'_ce : w ∈ ce s' := by
      rw [hcl_ce s'] at hws'
      obtain ⟨s, hs, rfl⟩ := hws'
      rcases eq_or_lt_of_le hs.1 with rfl | hgt
      · exact (hw_not_V (hθ_in_V s')).elim
      · rcases eq_or_lt_of_le hs.2 with rfl | hlt
        · rw [hhi_ψ s'] at hw_not_V
          exact (hw_not_V (hθ_in_V (nextSpoke s'))).elim
        · exact ⟨s, ⟨hgt, hlt⟩, rfl⟩
    exact Set.disjoint_left.mp (hce_disj (Finset.mem_erase.mp hs'_er).1.symm) hw_ce_t hws'_ce
  have hce_inj : Injective ce := by
    intro t₁ t₂ heq
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := (hce_pc t₁).nonempty
    exact Set.disjoint_left.mp (hce_disj hne) hx₀ (heq ▸ hx₀)
  have hE_range : E(C.toGraph) = range ce := by
    change C.E = range ce
    refine Subset.antisymm (fun e he => ?_) (by rintro _ ⟨t, rfl⟩; exact hce_mem_E t)
    obtain ⟨x₀, hx₀⟩ := he.2.2.1.nonempty
    obtain ⟨t, hxt⟩ := mem_iUnion.mp (hcover ▸ he.2.1 hx₀)
    exact ⟨t, (C.edge_eq_of_mem he (hce_mem_E t) hx₀ hxt).symm⟩
  refine ⟨{ hp := hp2
            u := u
            ce := ce
            u_inj := hu_inj
            ce_inj := hce_inj
            vertexSet_eq := hu_range
            edgeSet_eq := hE_range
            isLink_ce := fun t => ⟨hce_mem_E t, hθ_in_V t, hθ_in_V (nextSpoke t), hce_cap_V t⟩ },
    θ_v, hθ_strict, hθ_Ico, fun _ => rfl, hθ_of_V⟩

/-- Left-side frontier membership for a rectangle `Icc a b ×ℂ Icc c d`. -/
private theorem left_subset_frontier_rect {a b c d : ℝ} {z : ℂ}
    (ha : z.re = a) (hz : z.im ∈ Icc c d) (hab : a ≤ b) :
    z ∈ frontier (Icc a b ×ℂ Icc c d) := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) := (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq]
  refine ⟨Complex.mem_reProdIm.mpr ⟨by rw [ha]; exact ⟨le_rfl, hab⟩, hz⟩, fun hi => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
  have h1 : z - ((ρ / 2 : ℝ) : ℂ) ∈ ball z ρ := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h2 := (Complex.mem_reProdIm.mp (interior_subset (hball h1))).1.1
  simp only [Complex.sub_re, Complex.ofReal_re] at h2
  linarith

/-- Right-side frontier membership for a rectangle `Icc a b ×ℂ Icc c d`. -/
private theorem right_subset_frontier_rect {a b c d : ℝ} {z : ℂ}
    (hb : z.re = b) (hz : z.im ∈ Icc c d) (hab : a ≤ b) :
    z ∈ frontier (Icc a b ×ℂ Icc c d) := by
  have hcl : IsClosed (Icc a b ×ℂ Icc c d) := (isCompact_Icc.reProdIm isCompact_Icc).isClosed
  rw [hcl.frontier_eq]
  refine ⟨Complex.mem_reProdIm.mpr ⟨by rw [hb]; exact ⟨hab, le_rfl⟩, hz⟩, fun hi => ?_⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hi
  have h1 : z + ((ρ / 2 : ℝ) : ℂ) ∈ ball z ρ := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h2 := (Complex.mem_reProdIm.mp (interior_subset (hball h1))).1.2
  simp only [Complex.add_re, Complex.ofReal_re] at h2
  linarith

/-- **Rectangle Strip Non-Crossing Lemma:**
Two continuous paths `A_L, B_L : 𝕀 → ℂ` across the vertical strip `0 ≤ re ≤ r₀` (`0 < r₀`) whose
open interiors `Ioo 0 1` lie in `0 < re < r₀` and are disjoint satisfy:
`(A_L 0).im < (B_L 0).im → (A_L 1).im ≤ (B_L 1).im`. -/
theorem rect_strip_noncrossing {r₀ : ℝ} (hr₀ : 0 < r₀)
    {A_L B_L : 𝕀 → ℂ} (hA_cont : Continuous A_L) (hB_cont : Continuous B_L)
    (hA0 : (A_L 0).re = 0) (hA1 : (A_L 1).re = r₀)
    (hA_in : ∀ t : 𝕀, (0 : 𝕀) < t → t < 1 → (A_L t).re ∈ Ioo 0 r₀)
    (hB0 : (B_L 0).re = 0) (hB1 : (B_L 1).re = r₀)
    (hB_in : ∀ t : 𝕀, (0 : 𝕀) < t → t < 1 → (B_L t).re ∈ Ioo 0 r₀)
    (hdisj : Disjoint (A_L '' Ioo 0 1) (B_L '' Ioo 0 1))
    (hlt0 : (A_L 0).im < (B_L 0).im) :
    (A_L 1).im ≤ (B_L 1).im := by
  by_contra hnot
  have hlt1 : (B_L 1).im < (A_L 1).im := not_le.mp hnot
  -- Bound the imaginary parts of `A_L` and `B_L` strictly inside `(-M, M)`
  obtain ⟨C₁, hC₁⟩ := (isCompact_range (Complex.continuous_im.comp hA_cont)).isBounded.subset_closedBall 0
  obtain ⟨C₂, hC₂⟩ := (isCompact_range (Complex.continuous_im.comp hB_cont)).isBounded.subset_closedBall 0
  let M : ℝ := max (|C₁| + 1) (|C₂| + 1)
  have hM_pos : 0 < M := by dsimp only [M]; positivity
  have hA_im : ∀ t : 𝕀, |(A_L t).im| < M := by
    intro t
    have h := mem_closedBall_zero_iff.mp (hC₁ ⟨t, rfl⟩)
    rw [Real.norm_eq_abs] at h
    change |(A_L t).im| ≤ C₁ at h
    have : |C₁| + 1 ≤ M := le_max_left _ _
    linarith [le_abs_self C₁]
  have hB_im : ∀ t : 𝕀, |(B_L t).im| < M := by
    intro t
    have h := mem_closedBall_zero_iff.mp (hC₂ ⟨t, rfl⟩)
    rw [Real.norm_eq_abs] at h
    change |(B_L t).im| ≤ C₂ at h
    have : |C₂| + 1 ≤ M := le_max_right _ _
    linarith [le_abs_self C₂]
  let R : Set ℂ := Icc 0 r₀ ×ℂ Icc (-M) M
  obtain ⟨hR_disc, hR_bd⟩ := isClosedDisc_rect hr₀ (by linarith : -M < M)
  have hA_re : ∀ t : 𝕀, (A_L t).re ∈ Icc 0 r₀ := by
    intro t
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have : t = 0 := Subtype.ext ht0.symm; rw [this, hA0]; exact ⟨le_rfl, hr₀.le⟩
    · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
      · have : t = 1 := Subtype.ext ht1; rw [this, hA1]; exact ⟨hr₀.le, le_rfl⟩
      · exact Ioo_subset_Icc_self (hA_in t ht0 ht1)
  have hB_re : ∀ t : 𝕀, (B_L t).re ∈ Icc 0 r₀ := by
    intro t
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have : t = 0 := Subtype.ext ht0.symm; rw [this, hB0]; exact ⟨le_rfl, hr₀.le⟩
    · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
      · have : t = 1 := Subtype.ext ht1; rw [this, hB1]; exact ⟨hr₀.le, le_rfl⟩
      · exact Ioo_subset_Icc_self (hB_in t ht0 ht1)
  have hA_sub : range A_L ⊆ R := by
    rintro _ ⟨t, rfl⟩
    exact Complex.mem_reProdIm.mpr ⟨hA_re t, ⟨(abs_lt.mp (hA_im t)).1.le, (abs_lt.mp (hA_im t)).2.le⟩⟩
  have hB_sub : range B_L ⊆ R := by
    rintro _ ⟨t, rfl⟩
    exact Complex.mem_reProdIm.mpr ⟨hB_re t, ⟨(abs_lt.mp (hB_im t)).1.le, (abs_lt.mp (hB_im t)).2.le⟩⟩
  let a := A_L 0; let c := A_L 1; let b := B_L 0; let d := B_L 1
  have ha_bd : a ∈ discBd R := hR_bd ▸ left_subset_frontier_rect hA0
    ⟨(abs_lt.mp (hA_im 0)).1.le, (abs_lt.mp (hA_im 0)).2.le⟩ hr₀.le
  have hb_bd : b ∈ discBd R := hR_bd ▸ left_subset_frontier_rect hB0
    ⟨(abs_lt.mp (hB_im 0)).1.le, (abs_lt.mp (hB_im 0)).2.le⟩ hr₀.le
  have hc_bd : c ∈ discBd R := hR_bd ▸ right_subset_frontier_rect hA1
    ⟨(abs_lt.mp (hA_im 1)).1.le, (abs_lt.mp (hA_im 1)).2.le⟩ hr₀.le
  have hd_bd : d ∈ discBd R := hR_bd ▸ right_subset_frontier_rect hB1
    ⟨(abs_lt.mp (hB_im 1)).1.le, (abs_lt.mp (hB_im 1)).2.le⟩ hr₀.le
  have hac : a ≠ c := fun h => by have := congrArg Complex.re h; dsimp only [a, c] at this; linarith
  have hbd : b ≠ d := fun h => by have := congrArg Complex.re h; dsimp only [b, d] at this; linarith
  have hab : a ≠ b := fun h => by have := congrArg Complex.im h; dsimp only [a, b] at this; linarith
  have had : a ≠ d := fun h => by have := congrArg Complex.re h; dsimp only [a, d] at this; linarith
  have hcb : c ≠ b := fun h => by have := congrArg Complex.re h; dsimp only [c, b] at this; linarith
  have hcd : c ≠ d := fun h => by have := congrArg Complex.im h; dsimp only [c, d] at this; linarith
  -- Separate `b` and `d` in `frontier R \ {a, c}` using the line through `a` and `c`
  have hcomp_ne : connectedComponentIn (discBd R \ {a, c}) b ≠
      connectedComponentIn (discBd R \ {a, c}) d := by
    intro heq
    let ell : ℝ → ℝ := fun x => (1 - x / r₀) * a.im + (x / r₀) * c.im
    let U_plus : Set ℂ := {z | ell z.re < z.im}
    let U_minus : Set ℂ := {z | z.im < ell z.re}
    have hUp_open : IsOpen U_plus := isOpen_lt
      (((continuous_const.sub (Complex.continuous_re.div_const r₀)).mul continuous_const).add
        ((Complex.continuous_re.div_const r₀).mul continuous_const)) Complex.continuous_im
    have hUm_open : IsOpen U_minus := isOpen_lt Complex.continuous_im
      (((continuous_const.sub (Complex.continuous_re.div_const r₀)).mul continuous_const).add
        ((Complex.continuous_re.div_const r₀).mul continuous_const))
    have hfr_sides : ∀ z ∈ frontier R, z.re = 0 ∨ z.re = r₀ ∨ z.im = -M ∨ z.im = M := by
      intro z hz
      have hcl : IsClosed R := (isCompact_Icc.reProdIm isCompact_Icc).isClosed
      rw [hcl.frontier_eq] at hz
      obtain ⟨hzR, hzni⟩ := hz
      obtain ⟨⟨hx0, hxr⟩, ⟨hy0, hyM⟩⟩ := Complex.mem_reProdIm.mp hzR
      by_contra hnone
      push Not at hnone
      have hopen : IsOpen (Ioo 0 r₀ ×ℂ Ioo (-M) M) :=
        (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
      have hsub : Ioo 0 r₀ ×ℂ Ioo (-M) M ⊆ R := fun w hw => by
        obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hw
        exact Complex.mem_reProdIm.mpr ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩
      exact hzni (mem_interior.mpr ⟨_, hsub, hopen, Complex.mem_reProdIm.mpr
        ⟨⟨lt_of_le_of_ne hx0 hnone.1.symm, lt_of_le_of_ne hxr hnone.2.1⟩,
          ⟨lt_of_le_of_ne hy0 hnone.2.2.1.symm, lt_of_le_of_ne hyM hnone.2.2.2⟩⟩⟩)
    have hcov : discBd R \ {a, c} ⊆ U_plus ∪ U_minus := by
      intro z ⟨hz_bd, hz_ne⟩
      have hz_fr : z ∈ frontier R := hR_bd ▸ hz_bd
      have hzR : z ∈ R := (isCompact_Icc.reProdIm isCompact_Icc).isClosed.frontier_subset hz_fr
      obtain ⟨⟨hx0, hxr⟩, _⟩ := Complex.mem_reProdIm.mp hzR
      have ha_im_bd := abs_lt.mp (hA_im 0)
      have hc_im_bd := abs_lt.mp (hA_im 1)
      have hell_bd : -M < ell z.re ∧ ell z.re < M := by
        have ht0 : 0 ≤ z.re / r₀ := div_nonneg hx0 hr₀.le
        have ht1 : 0 ≤ 1 - z.re / r₀ := by
          have : z.re / r₀ ≤ 1 := (div_le_one hr₀).mpr hxr
          linarith
        have hsum : (1 - z.re / r₀) + z.re / r₀ = 1 := by ring
        rcases eq_or_lt_of_le ht0 with h0 | h0
        · have hz0 : z.re / r₀ = 0 := h0.symm
          dsimp only [ell]; rw [hz0]; simp only [sub_zero, one_mul, zero_mul, add_zero]
          exact ha_im_bd
        · constructor
          · nlinarith [mul_lt_mul_of_pos_left hc_im_bd.1 h0,
              mul_le_mul_of_nonneg_left ha_im_bd.1.le ht1]
          · nlinarith [mul_lt_mul_of_pos_left hc_im_bd.2 h0,
              mul_le_mul_of_nonneg_left ha_im_bd.2.le ht1]
      rcases lt_trichotomy (ell z.re) z.im with hlt_z | heq_z | hgt_z
      · exact Or.inl hlt_z
      · exfalso
        rcases hfr_sides z hz_fr with hre0 | hrer | him0 | himM
        · have hz_eq_a : z = a := by
            apply Complex.ext
            · exact hre0.trans hA0.symm
            · rw [← heq_z]; dsimp only [ell]; rw [hre0]; simp
          exact hz_ne (Or.inl hz_eq_a)
        · have hz_eq_c : z = c := by
            apply Complex.ext
            · exact hrer.trans hA1.symm
            · rw [← heq_z]; dsimp only [ell]; rw [hrer, div_self hr₀.ne']; ring
          exact hz_ne (Or.inr (mem_singleton_iff.mpr hz_eq_c))
        · linarith [hell_bd.1, him0]
        · linarith [hell_bd.2, himM]
      · exact Or.inr hgt_z
    have hb_in : b ∈ discBd R \ {a, c} :=
      ⟨hb_bd, fun h => by rcases h with h | h; exact hab h.symm; exact hcb (mem_singleton_iff.mp h).symm⟩
    have hd_in : d ∈ discBd R \ {a, c} :=
      ⟨hd_bd, fun h => by rcases h with h | h; exact had h.symm; exact hcd (mem_singleton_iff.mp h).symm⟩
    have hb_Up : b ∈ U_plus := by
      change ell b.re < b.im
      dsimp only [ell, b, a]; rw [hB0]; simp only [zero_div, sub_zero, one_mul, zero_mul, add_zero]
      exact hlt0
    have hd_Um : d ∈ U_minus := by
      change d.im < ell d.re
      dsimp only [ell, d, c]; rw [hB1, div_self hr₀.ne']; simp only [sub_self, zero_mul, one_mul, zero_add]
      exact hlt1
    have hsub_Up : connectedComponentIn (discBd R \ {a, c}) b ⊆ U_plus :=
      isPreconnected_connectedComponentIn.subset_left_of_subset_union hUp_open hUm_open
        (Set.disjoint_left.mpr fun z (h1 : ell z.re < z.im) (h2 : z.im < ell z.re) => lt_asymm h1 h2)
        ((connectedComponentIn_subset _ _).trans hcov)
        ⟨b, mem_connectedComponentIn hb_in, hb_Up⟩
    have hd_Up : d ∈ U_plus := hsub_Up (heq.symm ▸ mem_connectedComponentIn hd_in)
    exact lt_asymm (show ell d.re < d.im from hd_Up) (show d.im < ell d.re from hd_Um)
  have hcross : PairsCrossOn (discBd R) a c b d :=
    ⟨ha_bd, hb_bd, hc_bd, hd_bd, hac, hbd, hab, had, hcb, hcd, hcomp_ne⟩
  obtain ⟨z, ⟨s, rfl⟩, ⟨t, hst⟩⟩ := disc_crossing R (range A_L) (range B_L) a c b d hR_disc
    hA_sub hB_sub (isCompact_range hA_cont) (isCompact_range hB_cont)
    (isConnected_range hA_cont) (isConnected_range hB_cont)
    ⟨0, rfl⟩ ⟨1, rfl⟩ ⟨0, rfl⟩ ⟨1, rfl⟩ hcross
  -- `A_L s = B_L t` contradicts disjointness on `[0, 1]`
  rcases eq_or_lt_of_le (unitInterval.nonneg s) with hs0 | hs0
  · have hs_eq : s = 0 := Subtype.ext hs0.symm
    subst hs_eq
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have ht_eq : t = 0 := Subtype.ext ht0.symm
      subst ht_eq
      exact hab hst.symm
    · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
      · have ht_eq : t = 1 := Subtype.ext ht1
        subst ht_eq
        exact had hst.symm
      · have hre := congrArg Complex.re hst
        linarith [(hB_in t ht0 ht1).1, hA0]
  · rcases eq_or_lt_of_le (unitInterval.le_one s) with hs1 | hs1
    · have hs_eq : s = 1 := Subtype.ext hs1
      subst hs_eq
      rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
      · have ht_eq : t = 0 := Subtype.ext ht0.symm
        subst ht_eq
        exact hcb hst.symm
      · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
        · have ht_eq : t = 1 := Subtype.ext ht1
          subst ht_eq
          exact hcd hst.symm
        · have hre := congrArg Complex.re hst
          linarith [(hB_in t ht0 ht1).2, hA1]
    · rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
      · have ht_eq : t = 0 := Subtype.ext ht0.symm
        subst ht_eq
        have hre := congrArg Complex.re hst
        linarith [(hA_in s hs0 hs1).1, hB0]
      · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
        · have ht_eq : t = 1 := Subtype.ext ht1
          subst ht_eq
          have hre := congrArg Complex.re hst
          linarith [(hA_in s hs0 hs1).2, hB1]
        · exact Set.disjoint_left.mp hdisj ⟨s, ⟨hs0, hs1⟩, rfl⟩ ⟨t, ⟨ht0, ht1⟩, hst⟩

/-- **Annulus Monotone Bipartite Ordering:**
Given nested closed discs `Δ_in ⊆ Δ_out \ discBd Δ_out` on a closed surface `S`, an inner boundary
homeomorphism `φ_in : Circle ≃ₜ discBd Δ_in`, a base angle `α_base : ℝ`, an outer simple circuit
drawing `C_out : Drawing S` with `discBd Δ_out = C_out.U`, and a finite family `γ : ι → 𝕀 → S` of
continuous injective arcs from `discBd Δ_in` to `C_out.V` whose open interiors lie in
`interior Δ_out \ Δ_in` and are pairwise disjoint, there exist:
- an outer `CircuitCycle C_out.toGraph C_out.V.ncard` and normalized `φ_out : Circle ≃ₜ C_out.U`,
- an ordering `σ : Fin m ≃ ι` (`m = Nat.card ι`),
- `Monotone` inner angles `α_ord : Fin m → ℝ` in `Ico α_base (α_base + 2 * Real.pi)` realizing
  `γ (σ r) 0`, and
- `Monotone` outer slots `f : Fin m → Fin (C_out.V.ncard + 1)` realizing `γ (σ r) 1`. -/
theorem annulus_monotone_bipartite_order {S : Type*} [TopologicalSpace S] (hS : IsClosedSurface S)
    {Δ_in Δ_out : Set S} (hΔ_in : IsClosedDisc Δ_in) (hΔ_out : IsClosedDisc Δ_out)
    (hin : Δ_in ⊆ Δ_out \ discBd Δ_out)
    (φ_in : Circle ≃ₜ discBd Δ_in) (α_base : ℝ)
    (C_out : Drawing S) (hCout_circ : C_out.IsCircuit) (hCout_simple : C_out.toGraph.Simple)
    (hbd_out : discBd Δ_out = C_out.U)
    {ι : Type*} [Finite ι] (γ : ι → 𝕀 → S)
    (hγ_cont : ∀ i, Continuous (γ i))
    (hγ_inj : ∀ i, Injective (γ i))
    (hγ0 : ∀ i, γ i 0 ∈ discBd Δ_in)
    (hγ1 : ∀ i, γ i 1 ∈ C_out.V)
    (hγ_in : ∀ i (t : 𝕀), (0 : 𝕀) < t → t < 1 → γ i t ∈ interior Δ_out \ Δ_in)
    (hγ_disj : ∀ ⦃i j⦄, i ≠ j → Disjoint (γ i '' Ioo 0 1) (γ j '' Ioo 0 1)) :
    haveI : T2Space S := hS.2.1
    ∃ (cyc_out : CircuitCycle C_out.toGraph C_out.V.ncard)
      (φ_out : Circle ≃ₜ C_out.U) (θ_out : Fin C_out.V.ncard → ℝ)
      (m : ℕ) (σ : Fin m ≃ ι)
      (α_ord : Fin m → ℝ) (f : Fin m → Fin (C_out.V.ncard + 1)),
      StrictMono θ_out ∧
      (∀ t, θ_out t ∈ Ico 0 (2 * Real.pi)) ∧
      (∀ t, (φ_out (Circle.exp (θ_out t))).1 = cyc_out.u t) ∧
      (∀ θ ∈ Ico 0 (2 * Real.pi), (φ_out (Circle.exp θ)).1 ∈ C_out.V → ∃ t, θ = θ_out t) ∧
      Monotone α_ord ∧
      (∀ r : Fin m, α_ord r ∈ Ico α_base (α_base + 2 * Real.pi)) ∧
      (∀ r : Fin m, (φ_in (Circle.exp (α_ord r))).1 = γ (σ r) 0) ∧
      Monotone f ∧
      (∀ r : Fin m, cyc_out.u ⟨(f r).1 % C_out.V.ncard,
        Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ = γ (σ r) 1) := by
  classical
  have : T2Space S := hS.2.1
  let p_out := C_out.V.ncard
  have hp_out3 : 3 ≤ p_out := three_le_ncard_V_of_isCircuit_simple hCout_circ hCout_simple
  obtain ⟨m, ⟨e_idx⟩⟩ := Finite.exists_equiv_fin ι
  let σ_base : Fin m ≃ ι := e_idx.symm
  -- Map `Δ_out` to `closedBall (0 : ℂ) 2` with `Δ_in` on `closedBall 0 1` via `exists_disc_collar`
  obtain ⟨c, c', hc_cont, hc'_cont, hc_maps, hc'_maps, hc'c, hcc', hc_ball1, hc_sph2, hc_in⟩ :=
    exists_disc_collar hΔ_in hΔ_out hin φ_in
  have hc'_inj : InjOn c' Δ_out := (show LeftInvOn c c' Δ_out from hcc').injOn
  -- Build raw outer homeomorphism `φ_raw : Circle ≃ₜ C_out.U` via `w ↦ c (2 * (w : ℂ))`
  have h2_mem : ∀ w : Circle, (2 : ℂ) * (w : ℂ) ∈ sphere (0 : ℂ) 2 := by
    intro w
    rw [mem_sphere_zero_iff_norm, norm_mul, Circle.norm_coe, mul_one]
    norm_num
  have h2_ball : ∀ w : Circle, (2 : ℂ) * (w : ℂ) ∈ closedBall (0 : ℂ) 2 :=
    fun w => sphere_subset_closedBall (h2_mem w)
  let rawMap : Circle → C_out.U := fun w =>
    ⟨c ((2 : ℂ) * (w : ℂ)), hbd_out ▸ hc_sph2 ▸ mem_image_of_mem c (h2_mem w)⟩
  have hraw_cont : Continuous rawMap :=
    Continuous.subtype_mk (hc_cont.comp_continuous (continuous_const.mul continuous_subtype_val) h2_ball) _
  have hraw_bij : Bijective rawMap := by
    refine ⟨fun w₁ w₂ heq => ?_, fun y => ?_⟩
    · have h1 := hc'c (h2_ball w₁)
      have h2 := hc'c (h2_ball w₂)
      have hval : c ((2 : ℂ) * (w₁ : ℂ)) = c ((2 : ℂ) * (w₂ : ℂ)) := congrArg Subtype.val heq
      have hmul : (2 : ℂ) * (w₁ : ℂ) = (2 : ℂ) * (w₂ : ℂ) := h1.symm.trans (congrArg c' hval |>.trans h2)
      exact Circle.ext (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hmul)
    · have hy_sph : y.1 ∈ c '' sphere 0 2 := by rw [hc_sph2, hbd_out]; exact y.2
      obtain ⟨z, hz_sph, hcz⟩ := hy_sph
      have hnorm : ‖z / 2‖ = 1 := by
        rw [norm_div, mem_sphere_zero_iff_norm.mp hz_sph]
        norm_num
      let w : Circle := ⟨z / 2, mem_sphere_zero_iff_norm.mpr hnorm⟩
      refine ⟨w, Subtype.ext ?_⟩
      dsimp only [rawMap]
      have hzw : (2 : ℂ) * (w : ℂ) = z := mul_div_cancel₀ z (by norm_num : (2 : ℂ) ≠ 0)
      rw [hzw, hcz]
  let φ_raw : Circle ≃ₜ C_out.U :=
    hraw_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective rawMap hraw_bij)
  have hφ_raw_apply : ∀ w : Circle, (φ_raw w).1 = c ((2 : ℂ) * (w : ℂ)) := fun _ => rfl
  -- Transport each arc `γ (σ_base k)` via `c'` to the planar annulus `1 ≤ ‖z‖ ≤ 2`
  have hγ_sub_out : ∀ i (t : 𝕀), γ i t ∈ Δ_out := by
    intro i t
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have : t = 0 := Subtype.ext ht0.symm; rw [this]
      exact (hin (GM11.discBd_subset Δ_in (hγ0 i))).1
    · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
      · have : t = 1 := Subtype.ext ht1; rw [this]
        exact GM11.discBd_subset Δ_out (hbd_out.symm ▸ C_out.V_subset_U (hγ1 i))
      · exact interior_subset (hγ_in i t ht0 ht1).1
  let Γ_c : Fin m → 𝕀 → ℂ := fun k t => c' (γ (σ_base k) t)
  have hΓ_cont : ∀ k, Continuous (Γ_c k) := fun k =>
    hc'_cont.comp_continuous (hγ_cont (σ_base k)) (hγ_sub_out (σ_base k))
  have hΓ_inj : ∀ k, Injective (Γ_c k) := fun k t₁ t₂ heq =>
    hγ_inj (σ_base k) (hc'_inj (hγ_sub_out _ t₁) (hγ_sub_out _ t₂) heq)
  have hΓ_norm0 : ∀ k, ‖Γ_c k 0‖ = 1 := by
    intro k
    obtain ⟨w, hw⟩ := φ_in.surjective ⟨γ (σ_base k) 0, hγ0 (σ_base k)⟩
    have hc_w : c (w : ℂ) = γ (σ_base k) 0 := (hc_in w).trans (congrArg Subtype.val hw)
    have hw_b2 : (w : ℂ) ∈ closedBall (0 : ℂ) 2 :=
      closedBall_subset_closedBall (by norm_num) (mem_closedBall_zero_iff.mpr (Circle.norm_coe w).le)
    have h_eq : Γ_c k 0 = (w : ℂ) := by
      dsimp only [Γ_c]; rw [← hc_w, hc'c hw_b2]
    rw [h_eq, Circle.norm_coe]
  have hΓ_norm1 : ∀ k, ‖Γ_c k 1‖ = 2 := by
    intro k
    have hmem_bd : γ (σ_base k) 1 ∈ discBd Δ_out := hbd_out.symm ▸ C_out.V_subset_U (hγ1 (σ_base k))
    obtain ⟨z, hz_sph, hcz⟩ := hc_sph2 ▸ hmem_bd
    have h_eq : Γ_c k 1 = z := by
      dsimp only [Γ_c]; rw [← hcz, hc'c (sphere_subset_closedBall hz_sph)]
    rw [h_eq, mem_sphere_zero_iff_norm.mp hz_sph]
  have hΓ_norm_in : ∀ k (t : 𝕀), (0 : 𝕀) < t → t < 1 → 1 < ‖Γ_c k t‖ ∧ ‖Γ_c k t‖ < 2 := by
    intro k t ht0 ht1
    have hin_t := hγ_in (σ_base k) t ht0 ht1
    have hb2 : Γ_c k t ∈ closedBall (0 : ℂ) 2 := hc'_maps (interior_subset hin_t.1)
    have hle2 : ‖Γ_c k t‖ ≤ 2 := mem_closedBall_zero_iff.mp hb2
    have hgt1 : 1 < ‖Γ_c k t‖ := by
      by_contra hle1
      have hb1 : Γ_c k t ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr (not_lt.mp hle1)
      have hmem_in : c (Γ_c k t) ∈ Δ_in := hc_ball1 ▸ mem_image_of_mem c hb1
      rw [hcc' (interior_subset hin_t.1)] at hmem_in
      exact hin_t.2 hmem_in
    have hlt2 : ‖Γ_c k t‖ < 2 := by
      refine lt_of_le_of_ne hle2 fun heq2 => ?_
      have hsph : Γ_c k t ∈ sphere (0 : ℂ) 2 := mem_sphere_zero_iff_norm.mpr heq2
      have hmem_bd : c (Γ_c k t) ∈ discBd Δ_out := hc_sph2 ▸ mem_image_of_mem c hsph
      rw [hcc' (interior_subset hin_t.1)] at hmem_bd
      exact (GM11.IsClosedDisc.frontier_eq_discBd hS hΔ_out ▸ hmem_bd).2 hin_t.1
    exact ⟨hgt1, hlt2⟩
  have hΓ_ne0 : ∀ k t, Γ_c k t ≠ 0 := by
    intro k t h0
    have hnorm0 : ‖Γ_c k t‖ = 0 := by rw [h0, norm_zero]
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have : t = 0 := Subtype.ext ht0.symm; linarith [this ▸ hΓ_norm0 k]
    · rcases eq_or_lt_of_le (unitInterval.le_one t) with ht1 | ht1
      · have : t = 1 := Subtype.ext ht1; linarith [this ▸ hΓ_norm1 k]
      · linarith [(hΓ_norm_in k t ht0 ht1).1]
  -- Choose continuous logarithm `L k : 𝕀 → ℂ` normalized so `(L k 0).im ∈ Ico α_base (α_base + 2π)`
  have h2pi : (0 : ℝ) < 2 * Real.pi := Real.two_pi_pos
  have hex_L : ∀ k : Fin m, ∃ L : 𝕀 → ℂ,
      Continuous L ∧ (∀ t : 𝕀, Complex.exp (L t) = Γ_c k t) ∧
      (L 0).im ∈ Ico α_base (α_base + 2 * Real.pi) := by
    intro k
    obtain ⟨g, hg_cont, hg_exp⟩ := hasLogOn_unitInterval (hΓ_cont k) (hΓ_ne0 k)
    let n : ℤ := toIcoDiv h2pi α_base (g 0).im
    let L : 𝕀 → ℂ := fun t => g t - (n : ℂ) * (2 * Real.pi * Complex.I)
    have hL_cont : Continuous L := (continuousOn_univ.mp hg_cont).sub continuous_const
    have hL_exp : ∀ t : 𝕀, Complex.exp (L t) = Γ_c k t := by
      intro t
      dsimp only [L]
      rw [sub_eq_add_neg, Complex.exp_add, hg_exp t (mem_univ t)]
      have hexp1 : Complex.exp (-((n : ℂ) * (2 * Real.pi * Complex.I))) = 1 := by
        rw [show -((n : ℂ) * (2 * Real.pi * Complex.I)) = ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
          by push_cast; ring]
        exact Complex.exp_int_mul_two_pi_mul_I (-n)
      rw [hexp1, mul_one]
    have hL_im0 : (L 0).im ∈ Ico α_base (α_base + 2 * Real.pi) := by
      have hk := self_sub_toIcoDiv_zsmul h2pi α_base (g 0).im
      have him_eq : (L 0).im = toIcoMod h2pi α_base (g 0).im := by
        dsimp only [L, n]
        rw [← hk, zsmul_eq_mul]
        simp [Complex.sub_im, Complex.mul_im]
      rw [him_eq]
      exact toIcoMod_mem_Ico h2pi α_base (g 0).im
    exact ⟨L, hL_cont, hL_exp, hL_im0⟩
  choose L hL_cont hL_exp hL_im0 using hex_L
  have hL_re : ∀ k t, (L k t).re = Real.log ‖Γ_c k t‖ := by
    intro k t
    have := congrArg norm (hL_exp k t)
    rw [Complex.norm_exp] at this
    exact Real.exp_injective (this.trans (Real.exp_log (norm_pos_iff.mpr (hΓ_ne0 k t))).symm)
  have hL_re0 : ∀ k, (L k 0).re = 0 := fun k => by rw [hL_re, hΓ_norm0, Real.log_one]
  have hL_re1 : ∀ k, (L k 1).re = Real.log 2 := fun k => by rw [hL_re, hΓ_norm1]
  have hr₀_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_re_in : ∀ k (t : 𝕀), (0 : 𝕀) < t → t < 1 → (L k t).re ∈ Ioo 0 (Real.log 2) := by
    intro k t ht0 ht1
    rw [hL_re]
    obtain ⟨h1, h2⟩ := hΓ_norm_in k t ht0 ht1
    exact ⟨Real.log_pos h1, Real.log_lt_log (by linarith) h2⟩
  -- Shifted lifts `(k₁, n₁) ≠ (k₂, n₂)` are disjoint on `Ioo 0 1`
  have hL_shift_disj : ∀ (k₁ k₂ : Fin m) (n₁ n₂ : ℤ), (k₁, n₁) ≠ (k₂, n₂) →
      Disjoint ((fun t => L k₁ t + (n₁ : ℂ) * (2 * Real.pi * Complex.I)) '' Ioo 0 1)
        ((fun t => L k₂ t + (n₂ : ℂ) * (2 * Real.pi * Complex.I)) '' Ioo 0 1) := by
    intro k₁ k₂ n₁ n₂ hne
    rw [Set.disjoint_left]
    rintro z ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    dsimp only at heq
    have hexp_eq : Γ_c k₁ s = Γ_c k₂ t := by
      have h1 : Complex.exp (L k₁ s + (n₁ : ℂ) * (2 * Real.pi * Complex.I)) = Γ_c k₁ s := by
        rw [Complex.exp_add, hL_exp, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      have h2 : Complex.exp (L k₂ t + (n₂ : ℂ) * (2 * Real.pi * Complex.I)) = Γ_c k₂ t := by
        rw [Complex.exp_add, hL_exp, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [← h1, ← heq, h2]
    have hγ_eq : γ (σ_base k₁) s = γ (σ_base k₂) t := by
      have hc1 := hcc' (hγ_sub_out (σ_base k₁) s)
      have hc2 := hcc' (hγ_sub_out (σ_base k₂) t)
      exact hc1.symm.trans (congrArg c hexp_eq |>.trans hc2)
    by_cases hk : k₁ = k₂
    · subst hk
      have hst : s = t := hγ_inj (σ_base k₁) hγ_eq
      subst hst
      have h2piI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      have hn_eq_c : (n₂ : ℂ) = (n₁ : ℂ) := mul_right_cancel₀ h2piI_ne (add_left_cancel heq)
      have hn_eq : n₁ = n₂ := (Int.cast_injective hn_eq_c).symm
      exact hne (Prod.ext rfl hn_eq)
    · exact Set.disjoint_left.mp (hγ_disj (σ_base.injective.ne hk))
        ⟨s, hs, rfl⟩ ⟨t, ht, hγ_eq.symm⟩
  -- Sort `Fin m` lexicographically by `((L k 0).im, (L k 1).im)`
  let α_raw : Fin m → ℝ := fun k => (L k 0).im
  let β_raw : Fin m → ℝ := fun k => (L k 1).im
  let leRel : Fin m → Fin m → Bool := fun i j =>
    decide (α_raw i < α_raw j ∨ (α_raw i = α_raw j ∧ β_raw i ≤ β_raw j))
  have hleRel_trans : ∀ a b c : Fin m, leRel a b = true → leRel b c = true → leRel a c = true := by
    intro a b c hab hbc
    simp only [leRel, decide_eq_true_eq] at hab hbc ⊢
    rcases hab with h1 | ⟨h1a, h1b⟩ <;> rcases hbc with h2 | ⟨h2a, h2b⟩
    · exact Or.inl (lt_trans h1 h2)
    · exact Or.inl (h2a ▸ h1)
    · exact Or.inl (h1a ▸ h2)
    · exact Or.inr ⟨h1a.trans h2a, le_trans h1b h2b⟩
  have hleRel_total : ∀ a b : Fin m, (leRel a b || leRel b a) = true := by
    intro a b
    simp only [leRel, Bool.or_eq_true, decide_eq_true_eq]
    rcases lt_trichotomy (α_raw a) (α_raw b) with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (β_raw a) (β_raw b) with hb | hb
      · exact Or.inl (Or.inr ⟨h, hb⟩)
      · exact Or.inr (Or.inr ⟨h.symm, hb⟩)
    · exact Or.inr (Or.inl h)
  let sortedList : List (Fin m) := (List.finRange m).mergeSort leRel
  have hperm : sortedList.Perm (List.finRange m) := List.mergeSort_perm (List.finRange m) leRel
  have hlen_s : sortedList.length = m := hperm.length_eq.trans List.length_finRange
  have hnd_s : sortedList.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange m)
  have hpw_s : sortedList.Pairwise (fun i j => leRel i j = true) :=
    List.pairwise_mergeSort hleRel_trans hleRel_total (List.finRange m)
  let π₀ : Fin m → Fin m := fun r => sortedList[r.1]'(by rw [hlen_s]; exact r.2)
  have hπ₀_inj : Injective π₀ := by
    intro r₁ r₂ heq
    have := (List.Nodup.getElem_inj_iff hnd_s).mp heq
    exact Fin.ext this
  let π_eqv : Fin m ≃ Fin m := Equiv.ofBijective π₀ (Finite.injective_iff_bijective.mp hπ₀_inj)
  let σ : Fin m ≃ ι := π_eqv.trans σ_base
  let α_ord : Fin m → ℝ := fun r => α_raw (π_eqv r)
  let β_ord : Fin m → ℝ := fun r => β_raw (π_eqv r)
  have hord_pair : ∀ ⦃r₁ r₂ : Fin m⦄, r₁ < r₂ →
      α_ord r₁ ≤ α_ord r₂ ∧ β_ord r₁ ≤ β_ord r₂ ∧ β_ord r₂ ≤ β_ord r₁ + 2 * Real.pi := by
    intro r₁ r₂ hlt
    have hne_π : π_eqv r₁ ≠ π_eqv r₂ := π_eqv.injective.ne (Fin.ne_of_lt hlt)
    have hrel : leRel (π_eqv r₁) (π_eqv r₂) = true :=
      List.pairwise_iff_getElem.mp hpw_s r₁.1 r₂.1 (by rw [hlen_s]; exact r₁.2)
        (by rw [hlen_s]; exact r₂.2) (Fin.lt_def.mp hlt)
    simp only [leRel, decide_eq_true_eq] at hrel
    have hβ_le : β_ord r₁ ≤ β_ord r₂ := by
      rcases hrel with hα_lt | ⟨_, hβ⟩
      · exact rect_strip_noncrossing hr₀_pos (hL_cont (π_eqv r₁)) (hL_cont (π_eqv r₂))
          (hL_re0 _) (hL_re1 _) (hL_re_in _) (hL_re0 _) (hL_re1 _) (hL_re_in _)
          (by simpa using hL_shift_disj (π_eqv r₁) (π_eqv r₂) 0 0 (fun h => hne_π (Prod.mk.inj h).1))
          hα_lt
      · exact hβ
    have hβ_2pi : β_ord r₂ ≤ β_ord r₁ + 2 * Real.pi := by
      let L_shift : 𝕀 → ℂ := fun t => L (π_eqv r₁) t + ((1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I)
      have hshift_re : ∀ t : 𝕀, (L_shift t).re = (L (π_eqv r₁) t).re := fun t => by
        dsimp only [L_shift]; simp [Complex.add_re, Complex.mul_re]
      have hshift_im : ∀ t : 𝕀, (L_shift t).im = (L (π_eqv r₁) t).im + 2 * Real.pi := fun t => by
        dsimp only [L_shift]; simp [Complex.add_im, Complex.mul_im]
      have hα_lt_2pi : (L (π_eqv r₂) 0).im < (L_shift 0).im := by
        rw [hshift_im 0]
        linarith [(hL_im0 (π_eqv r₁)).1, (hL_im0 (π_eqv r₂)).2]
      have hle := rect_strip_noncrossing (B_L := L_shift) hr₀_pos (hL_cont (π_eqv r₂))
        ((hL_cont (π_eqv r₁)).add continuous_const)
        (hL_re0 _) (hL_re1 _) (hL_re_in _)
        ((hshift_re 0).trans (hL_re0 _))
        ((hshift_re 1).trans (hL_re1 _))
        (fun t ht0 ht1 => (hshift_re t).symm ▸ hL_re_in (π_eqv r₁) t ht0 ht1)
        (by
          have hd := hL_shift_disj (π_eqv r₂) (π_eqv r₁) 0 1 (by intro h; injection h with _ h2; omega)
          simpa [L_shift] using hd)
        hα_lt_2pi
      rw [hshift_im 1] at hle
      exact hle
    exact ⟨hrel.elim le_of_lt (fun h => le_of_eq h.1), hβ_le, hβ_2pi⟩
  have hα_mono : Monotone α_ord := fun r₁ r₂ hle =>
    (eq_or_lt_of_le hle).elim (fun h => h ▸ le_rfl) (fun h => (hord_pair h).1)
  have hβ_mono : Monotone β_ord := fun r₁ r₂ hle =>
    (eq_or_lt_of_le hle).elim (fun h => h ▸ le_rfl) (fun h => (hord_pair h).2.1)
  -- Endpoint formulas for `α_ord r` and `β_ord r`
  have hα_end : ∀ r : Fin m, (φ_in (Circle.exp (α_ord r))).1 = γ (σ r) 0 := by
    intro r
    let k := π_eqv r
    have hexp0 : Complex.exp (L k 0) = (Circle.exp (α_ord r) : ℂ) := by
      have hre0 := hL_re0 k
      have hl : L k 0 = (α_ord r : ℂ) * Complex.I := by
        apply Complex.ext
        · simp [hre0]
        · simp [α_ord, α_raw, k]
      rw [hl, Circle.coe_exp]
    have hΓ0 : Γ_c k 0 = (Circle.exp (α_ord r) : ℂ) := (hL_exp k 0).symm.trans hexp0
    have hc_eq : c (Γ_c k 0) = γ (σ r) 0 := hcc' (hγ_sub_out (σ r) 0)
    rw [← hc_in (Circle.exp (α_ord r)), ← hΓ0, hc_eq]
  have hβ_end : ∀ r : Fin m, (φ_raw (Circle.exp (β_ord r))).1 = γ (σ r) 1 := by
    intro r
    let k := π_eqv r
    have hexp1 : Complex.exp (L k 1) = (2 : ℂ) * (Circle.exp (β_ord r) : ℂ) := by
      have hre1 := hL_re1 k
      have hl : L k 1 = (Real.log 2 : ℂ) + (β_ord r : ℂ) * Complex.I := by
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, hre1]
          ring
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, β_ord, β_raw, k]
      rw [hl, Complex.exp_add, Circle.coe_exp]
      norm_cast
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      push_cast; rfl
    have hΓ1 : Γ_c k 1 = (2 : ℂ) * (Circle.exp (β_ord r) : ℂ) := (hL_exp k 1).symm.trans hexp1
    have hc_eq : c (Γ_c k 1) = γ (σ r) 1 := hcc' (hγ_sub_out (σ r) 1)
    rw [hφ_raw_apply, ← hΓ1, hc_eq]
  -- Choose shift angle `β₀` (`0` if `m = 0`, `β_ord 0` if `m > 0`) to define `φ_out` and `cyc_out`
  let β₀ : ℝ := if hm : 0 < m then β_ord ⟨0, hm⟩ else 0
  let rotHomeo : Circle ≃ₜ Circle :=
    { toFun := fun z => Circle.exp β₀ * z
      invFun := fun z => Circle.exp (-β₀) * z
      left_inv := fun z => by
        dsimp only
        rw [← mul_assoc, ← Circle.exp_add, neg_add_cancel, Circle.exp_zero, one_mul]
      right_inv := fun z => by
        dsimp only
        rw [← mul_assoc, ← Circle.exp_add, add_neg_cancel, Circle.exp_zero, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let φ_out : Circle ≃ₜ C_out.U := rotHomeo.trans φ_raw
  have hφ_out_exp : ∀ θ : ℝ, (φ_out (Circle.exp θ)).1 = (φ_raw (Circle.exp (β₀ + θ))).1 := by
    intro θ
    change (φ_raw (Circle.exp β₀ * Circle.exp θ)).1 = _
    rw [← Circle.exp_add]
  obtain ⟨cyc_out, θ_out, hθ_strict, hθ_Ico, hθ_u, hθ_of_V⟩ :=
    exists_circuitCycle_of_homeo C_out hCout_circ hCout_simple φ_out 0
  simp only [zero_add] at hθ_Ico hθ_of_V
  -- Define monotone outer slots `f : Fin m → Fin (p_out + 1)`
  by_cases hm : 0 < m
  · have hβ₀_eq : β₀ = β_ord ⟨0, hm⟩ := by dsimp only [β₀]; split_ifs; rfl
    have hθ0_eq_zero : θ_out ⟨0, by omega⟩ = 0 := by
      have hv0 : (φ_out (Circle.exp 0)).1 ∈ C_out.V := by
        rw [hφ_out_exp 0, add_zero, hβ₀_eq, hβ_end ⟨0, hm⟩]
        exact hγ1 (σ ⟨0, hm⟩)
      obtain ⟨t, ht⟩ := hθ_of_V 0 ⟨le_rfl, h2pi⟩ hv0
      have h0_le : θ_out ⟨0, by omega⟩ ≤ θ_out t :=
        hθ_strict.monotone (Fin.le_def.mpr (Nat.zero_le _))
      linarith [(hθ_Ico ⟨0, by omega⟩).1, ht]
    let θ_ext : Fin (p_out + 1) → ℝ := fun s =>
      if hs : s.1 < p_out then θ_out ⟨s.1, hs⟩ else 2 * Real.pi
    have hθ_ext_strict : StrictMono θ_ext := by
      intro s₁ s₂ hlt
      dsimp only [θ_ext]
      split_ifs with h1 h2 h2
      · exact hθ_strict (Fin.lt_def.mpr (Fin.lt_def.mp hlt))
      · exact (hθ_Ico ⟨s₁.1, h1⟩).2
      · have := Fin.lt_def.mp hlt; omega
      · have := Fin.lt_def.mp hlt; have := s₁.2; have := s₂.2; omega
    have hex_slot : ∀ r : Fin m, ∃ s : Fin (p_out + 1), θ_ext s = β_ord r - β₀ := by
      intro r
      have hlo : 0 ≤ β_ord r - β₀ := by
        rw [hβ₀_eq]
        exact sub_nonneg.mpr (hβ_mono (Fin.le_def.mpr (Nat.zero_le _)))
      have hhi : β_ord r - β₀ ≤ 2 * Real.pi := by
        rw [hβ₀_eq]
        rcases eq_or_lt_of_le (Fin.le_def.mpr (Nat.zero_le r.1) : (⟨0, hm⟩ : Fin m) ≤ r) with hr0 | hr_pos
        · rw [← hr0]; linarith
        · linarith [(hord_pair hr_pos).2.2]
      rcases eq_or_lt_of_le hhi with heq_2pi | hlt_2pi
      · refine ⟨⟨p_out, Nat.lt_succ_self _⟩, ?_⟩
        dsimp only [θ_ext]
        split_ifs with h
        · omega
        · exact heq_2pi.symm
      · have hv_mem : (φ_out (Circle.exp (β_ord r - β₀))).1 ∈ C_out.V := by
          rw [hφ_out_exp, add_sub_cancel, hβ_end r]
          exact hγ1 (σ r)
        obtain ⟨t, ht⟩ := hθ_of_V (β_ord r - β₀) ⟨hlo, hlt_2pi⟩ hv_mem
        refine ⟨⟨t.1, Nat.lt_succ_of_lt t.2⟩, ?_⟩
        dsimp only [θ_ext]
        split_ifs with h
        · exact ht.symm
        · exact (h t.2).elim
    choose f hf_spec using hex_slot
    have hf_mono : Monotone f := fun r₁ r₂ hle =>
      hθ_ext_strict.le_iff_le.mp (by rw [hf_spec r₁, hf_spec r₂]; linarith [hβ_mono hle])
    have hf_end : ∀ r : Fin m, cyc_out.u ⟨(f r).1 % p_out,
        Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ = γ (σ r) 1 := by
      intro r
      have hspec := hf_spec r
      dsimp only [θ_ext] at hspec
      split_ifs at hspec with hs_lt
      · have hmod : (f r).1 % p_out = (f r).1 := Nat.mod_eq_of_lt hs_lt
        have hfin : (⟨(f r).1 % p_out, Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ : Fin p_out) =
            ⟨(f r).1, hs_lt⟩ := Fin.ext hmod
        rw [hfin, ← hθ_u ⟨(f r).1, hs_lt⟩, hspec, hφ_out_exp, add_sub_cancel, hβ_end r]
      · have hs_eq : (f r).1 = p_out := by have := (f r).2; omega
        have hmod : (f r).1 % p_out = 0 := by rw [hs_eq, Nat.mod_self]
        have hfin : (⟨(f r).1 % p_out, Nat.mod_lt _ (by have := cyc_out.hp; omega)⟩ : Fin p_out) =
            ⟨0, by omega⟩ := Fin.ext hmod
        have hβr : β_ord r = β₀ + 2 * Real.pi := by linarith
        have hexp_per : Circle.exp (β₀ + 2 * Real.pi) = Circle.exp β₀ :=
          Circle.exp_eq_exp.mpr ⟨1, by ring⟩
        rw [hfin, ← hθ_u ⟨0, by omega⟩, hθ0_eq_zero, hφ_out_exp 0, add_zero, ← hexp_per,
          ← hβr, hβ_end r]
    exact ⟨cyc_out, φ_out, θ_out, m, σ, α_ord, f, hθ_strict, hθ_Ico, hθ_u, hθ_of_V,
      hα_mono, fun r => hL_im0 (π_eqv r), hα_end, hf_mono, hf_end⟩
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    exact ⟨cyc_out, φ_out, θ_out, 0, σ, α_ord, Fin.elim0, hθ_strict, hθ_Ico, hθ_u, hθ_of_V,
      fun r => Fin.elim0 r, fun r => Fin.elim0 r, fun r => Fin.elim0 r,
      fun r => Fin.elim0 r, fun r => Fin.elim0 r⟩

end AnnulusOrder

end GraphMinor.GM03

