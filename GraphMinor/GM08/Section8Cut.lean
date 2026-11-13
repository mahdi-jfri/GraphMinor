module

public import GraphMinor.GM08.Section8Sleeve
public import GraphMinor.GM07.DiscChain

/-!
# Graph Minors VIII, Section 8 (Part 2): Vertex Cuts Across a Centred O-Arc `(8.3)`

This file proves **(8.3)** of GM VIII Section 8 (pages 268–269):
for a `D`-normal centred `O`-arc `F` in a closed disc `Δ` and a `D`-normal `[0, 1]`-arc `I` with
ends in `F` and all other points inside `F`,
`|I ∩ V(D)| ≥ min(|F₁ ∩ V(D)|, |F₂ ∩ V(D)|)`,
where `F₁, F₂` are the closures of the two components into which the ends of `I` divide `F`.
-/

@[expose] public section

namespace GraphMinor
namespace GM08

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM07

universe u

section ChartComponentHelpers

/-- Under mutually inverse continuous maps on `X` and `φ '' X`, connected components in `φ '' X`
are the images under `φ` of connected components in `X`. -/
private theorem connectedComponentIn_image_gen {S₁ : Type*} {S₂ : Type*}
    [TopologicalSpace S₁] [TopologicalSpace S₂] {X : Set S₁} {φ : S₁ → S₂} {ψ : S₂ → S₁}
    (hφ : ContinuousOn φ X) (hψ : ContinuousOn ψ (φ '' X)) (hψφ : ∀ x ∈ X, ψ (φ x) = x)
    {x : S₁} (hx : x ∈ X) :
    connectedComponentIn (φ '' X) (φ x) = φ '' connectedComponentIn X x := by
  have hφψ : ∀ y ∈ φ '' X, φ (ψ y) = y := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hψφ z hz]
  apply Subset.antisymm
  · have hsub : connectedComponentIn (φ '' X) (φ x) ⊆ φ '' X := connectedComponentIn_subset _ _
    have hψ_sub : ψ '' connectedComponentIn (φ '' X) (φ x) ⊆ X := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hsub hy
      rwa [hψφ z hz]
    have hψ_pre : IsPreconnected (ψ '' connectedComponentIn (φ '' X) (φ x)) :=
      isPreconnected_connectedComponentIn.image ψ (hψ.mono hsub)
    have hx_mem : x ∈ ψ '' connectedComponentIn (φ '' X) (φ x) :=
      ⟨φ x, mem_connectedComponentIn (mem_image_of_mem φ hx), hψφ x hx⟩
    have hle := hψ_pre.subset_connectedComponentIn hx_mem hψ_sub
    intro y hy
    refine ⟨ψ y, hle (mem_image_of_mem ψ hy), hφψ y (hsub hy)⟩
  · have hsub : connectedComponentIn X x ⊆ X := connectedComponentIn_subset _ _
    have hφ_pre : IsPreconnected (φ '' connectedComponentIn X x) :=
      isPreconnected_connectedComponentIn.image φ (hφ.mono hsub)
    exact hφ_pre.subset_connectedComponentIn
      (mem_image_of_mem φ (mem_connectedComponentIn hx)) (image_mono hsub)

private theorem componentsIn_image_gen {S₁ : Type*} {S₂ : Type*}
    [TopologicalSpace S₁] [TopologicalSpace S₂] {X : Set S₁} {φ : S₁ → S₂} {ψ : S₂ → S₁}
    (hφ : ContinuousOn φ X) (hψ : ContinuousOn ψ (φ '' X)) (hψφ : ∀ x ∈ X, ψ (φ x) = x) :
    componentsIn (φ '' X) = image φ '' componentsIn X := by
  ext C'
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨connectedComponentIn X x, ⟨x, hx, rfl⟩,
      (connectedComponentIn_image_gen hφ hψ hψφ hx).symm⟩
  · rintro ⟨C, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨φ x, mem_image_of_mem φ hx, connectedComponentIn_image_gen hφ hψ hψφ hx⟩

/-- Along `SphereDiscChart Δ f f'`, for any `A ⊆ Δ` and `V ⊆ Δ`, `f` maps `closure A ∩ V`
bijectively onto `closure (f '' A) ∩ f '' V` (without requiring `[T1Space S]`). -/
private theorem image_closure_inter_eq_of_subset_disc {S : Type u} [TopologicalSpace S]
    {Δ : Set S} {f : S → OnePoint EuclideanPlane} {f' : OnePoint EuclideanPlane → S}
    (sc : SphereDiscChart Δ f f') {A V : Set S} (hAΔ : A ⊆ Δ) (hVΔ : V ⊆ Δ) :
    f '' (closure A ∩ V) = closure (f '' A) ∩ f '' V := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxcl, hxV⟩, rfl⟩
    refine ⟨?_, mem_image_of_mem f hxV⟩
    rw [mem_closure_iff]
    intro W hWopen hfxW
    have hcont : ContinuousOn f Δ := sc.fc
    rw [continuousOn_iff] at hcont
    obtain ⟨U, hUopen, hxU, hUsub⟩ := hcont x (hVΔ hxV) W hWopen hfxW
    obtain ⟨z, hzU, hzA⟩ := mem_closure_iff.mp hxcl U hUopen hxU
    exact ⟨f z, hUsub ⟨hzU, hAΔ hzA⟩, mem_image_of_mem f hzA⟩
  · rintro ⟨hycl, ⟨x, hxV, rfl⟩⟩
    refine ⟨x, ⟨?_, hxV⟩, rfl⟩
    rw [mem_closure_iff]
    intro U hUopen hxU
    have hcont' : ContinuousOn f' (f '' Δ) := sc.f'c
    rw [continuousOn_iff] at hcont'
    have hfx_mem : f x ∈ f '' Δ := mem_image_of_mem f (hVΔ hxV)
    have hfx_U : f' (f x) ∈ U := by rwa [sc.f'f (hVΔ hxV)]
    obtain ⟨W, hWopen, hfxW, hWsub⟩ := hcont' (f x) hfx_mem U hUopen hfx_U
    obtain ⟨w, hwW, ⟨z, hzA, rfl⟩⟩ := mem_closure_iff.mp hycl W hWopen hfxW
    have hzU : z ∈ U := by
      have hfz : f' (f z) ∈ U := hWsub ⟨hwW, mem_image_of_mem f (hAΔ hzA)⟩
      rwa [sc.f'f (hAΔ hzA)] at hfz
    exact ⟨z, hzU, hzA⟩

end ChartComponentHelpers

section SphereModel83

/-- In `SphereSurf`, if a closed disc `E` avoiding `OnePoint.infty` has `discBd E ⊆ discInt D_F`
for a closed disc `D_F` avoiding `OnePoint.infty`, then `E ⊆ discInt D_F`. -/
theorem insideDisc_subset_discInt_of_bd_subset_sphere {E D_F : Set SphereSurf}
    (hE : IsClosedDisc E) (hDF : IsClosedDisc D_F)
    (hinf_E : (OnePoint.infty : SphereSurf) ∉ E)
    (hinf_DF : (OnePoint.infty : SphereSurf) ∉ D_F)
    (hbd : discBd E ⊆ discInt D_F) :
    E ⊆ discInt D_F := by
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hsph : Surface.IsSphere SphereSurf := ⟨Homeomorph.refl _⟩
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  obtain ⟨hDout_disc, hDout_bd⟩ := GM12.isClosedDisc_closure_compl_of_sphere hS hsph hDF
  set D_out := closure (univ \ D_F)
  have hinf_out : (OnePoint.infty : SphereSurf) ∈ discInt D_out := by
    refine ⟨subset_closure ⟨mem_univ _, hinf_DF⟩, fun hb => ?_⟩
    rw [hDout_bd] at hb
    exact hinf_DF (Surface.discBd_subset _ hb)
  have hdis_bd : Disjoint (discInt D_out) (discBd E) := by
    refine Set.disjoint_left.mpr fun y hy_out hyE => ?_
    obtain ⟨z, hz1, hz2⟩ :=
      mem_closure_iff.mp hy_out.1 _ (hDF.isOpen_discInt hman) (hbd hyE)
    exact hz2.2 hz1.1
  have hsub : E ⊆ D_F := by
    intro z hzE
    by_contra hznot
    have hz_out : z ∈ discInt D_out := by
      refine ⟨subset_closure ⟨mem_univ _, hznot⟩, fun hb => ?_⟩
      rw [hDout_bd] at hb
      exact hznot (Surface.discBd_subset _ hb)
    rcases hE.side hman (IsClosedDisc.isPreconnected_discInt hDout_disc) hdis_bd with
      hin | hout
    · exact hinf_E (hin hinf_out).1
    · exact Set.disjoint_left.mp hout hz_out hzE
  intro z hzE
  refine ⟨hsub hzE, fun hz_bd => ?_⟩
  have hz_not_bdE : z ∉ discBd E := fun h => (hbd h).2 hz_bd
  have hz_front : z ∈ frontier D_F := by
    rwa [IsClosedDisc.frontier_eq_discBd hS hDF]
  exact hz_front.2 (mem_interior.mpr
    ⟨discInt E, (discInt_subset _).trans hsub, hE.isOpen_discInt hman, ⟨hzE, hz_not_bdE⟩⟩)

/-- Sphere-model version of **(8.3)**. -/
theorem theorem_8_3_sphere {D' : Drawing SphereSurf} {Δ' F' I' : Set SphereSurf}
    {a' b' : SphereSurf} {A'₁ A'₂ : Set SphereSurf}
    (hΔ' : IsClosedDisc Δ') (hinf : (OnePoint.infty : SphereSurf) ∉ Δ')
    (hD'U : D'.U ⊆ Δ') (hc' : IsCentredOArc D' Δ' F')
    (hI'norm : D'.IsNormal I') (hI'line : IsLineWithEnds I' a' b')
    (ha'F : a' ∈ F') (hb'F : b' ∈ F')
    (hI'in : SetInsideOArc Δ' F' (I' \ {a', b'}))
    (hcomp' : componentsIn (F' \ {a', b'}) = {A'₁, A'₂}) (hA'ne : A'₁ ≠ A'₂) :
    min (closure A'₁ ∩ D'.V).ncard (closure A'₂ ∩ D'.V).ncard ≤ (I' ∩ D'.V).ncard := by
  classical
  have hS : IsClosedSurface SphereSurf :=
    (GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hman : ∀ p : SphereSurf, IsManifoldPoint p := fun p => (hS.2.2 p).isManifoldPoint
  have ha'b' : a' ≠ b' := hI'line.ne'
  have ⟨hI'l, hI'r⟩ : a' ∈ I' ∧ b' ∈ I' := by
    obtain ⟨φ, h0, h1⟩ := hI'line
    exact ⟨h0 ▸ (φ 0).2, h1 ▸ (φ 1).2⟩
  have ⟨hF'Δ, hF'o, hF'norm, _⟩ := hc'
  -- Express `A'₁, A'₂` via the two lines `J₁, J₂` between `a'` and `b'` along `F'`.
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ_union, hJ_inter⟩ := hF'o.lines ha'F hb'F ha'b'
  have hcl_sub : ∀ {L : Set SphereSurf}, IsLineWithEnds L a' b' → closure (L \ {a', b'}) ⊆ L :=
    fun hL => closure_minimal sdiff_subset hL.isCompact.isClosed
  have hJ12_dis : Disjoint (closure (J₁ \ {a', b'})) (J₂ \ {a', b'}) :=
    disjoint_left.mpr fun z h1 h2 => h2.2 (hJ_inter ▸ ⟨hcl_sub hJ₁ h1, h2.1⟩)
  have hJ21_dis : Disjoint (J₁ \ {a', b'}) (closure (J₂ \ {a', b'})) :=
    disjoint_left.mpr fun z h1 h2 => h1.2 (hJ_inter ▸ ⟨h1.1, hcl_sub hJ₂ h2⟩)
  have hcomp_J : componentsIn (F' \ {a', b'}) = {J₁ \ {a', b'}, J₂ \ {a', b'}} := by
    rw [← componentsIn_union_eq_pair
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hJ₁)
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hJ₂)
      (GM14.IsLineWithEnds.nonempty_sdiff_pair hJ₁)
      (GM14.IsLineWithEnds.nonempty_sdiff_pair hJ₂) hJ12_dis hJ21_dis,
      ← union_sdiff_distrib, hJ_union]
  have hcl_J₁ : closure (J₁ \ {a', b'}) = J₁ := GM11.closure_sdiff_pair hJ₁
  have hcl_J₂ : closure (J₂ \ {a', b'}) = J₂ := GM11.closure_sdiff_pair hJ₂
  have hpair_eq : ({A'₁, A'₂} : Set (Set SphereSurf)) = {J₁ \ {a', b'}, J₂ \ {a', b'}} :=
    hcomp'.symm.trans hcomp_J
  have hA₁_mem : A'₁ = J₁ \ {a', b'} ∨ A'₁ = J₂ \ {a', b'} := by
    have : A'₁ ∈ ({J₁ \ {a', b'}, J₂ \ {a', b'}} : Set (Set SphereSurf)) :=
      hpair_eq ▸ mem_insert _ _
    simpa using this
  have hA₂_mem : A'₂ = J₁ \ {a', b'} ∨ A'₂ = J₂ \ {a', b'} := by
    have : A'₂ ∈ ({J₁ \ {a', b'}, J₂ \ {a', b'}} : Set (Set SphereSurf)) :=
      hpair_eq ▸ mem_insert_of_mem _ (mem_singleton _)
    simpa using this
  have hmin_eq :
      min (closure A'₁ ∩ D'.V).ncard (closure A'₂ ∩ D'.V).ncard =
        min (J₁ ∩ D'.V).ncard (J₂ ∩ D'.V).ncard := by
    rcases hA₁_mem with h1 | h1 <;> rcases hA₂_mem with h2 | h2
    · exfalso; exact hA'ne (h1.trans h2.symm)
    · rw [h1, h2, hcl_J₁, hcl_J₂]
    · rw [h1, h2, hcl_J₁, hcl_J₂, min_comm]
    · exfalso; exact hA'ne (h1.trans h2.symm)
  rw [hmin_eq]
  let r := (D'.V ∩ F').ncard
  let r₁ := (J₁ ∩ D'.V).ncard
  let r₂ := (J₂ ∩ D'.V).ncard
  let n := ({a', b'} ∩ D'.V).ncard
  have hfin_V : D'.V.Finite := D'.finite_V
  have hr_sum : r₁ + r₂ = r + n := by
    have hu : (J₁ ∩ D'.V) ∪ (J₂ ∩ D'.V) = D'.V ∩ F' := by
      rw [← union_inter_distrib_right, hJ_union, inter_comm]
    have hi : (J₁ ∩ D'.V) ∩ (J₂ ∩ D'.V) = {a', b'} ∩ D'.V := by
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun ⟨⟨hx1, hxV⟩, ⟨hx2, _⟩⟩ => ⟨hJ_inter ▸ ⟨hx1, hx2⟩, hxV⟩,
        fun ⟨hxab, hxV⟩ => ⟨⟨(hJ_inter ▸ hxab).1, hxV⟩, ⟨(hJ_inter ▸ hxab).2, hxV⟩⟩⟩
    have hcard := Set.ncard_union_add_ncard_inter (J₁ ∩ D'.V) (J₂ ∩ D'.V)
      (hfin_V.subset inter_subset_right) (hfin_V.subset inter_subset_right)
    rw [hu, hi] at hcard
    exact hcard.symm
  -- Trivial case `r = 0`.
  by_cases hr0 : r = 0
  · have hJ₁_sub : J₁ ∩ D'.V ⊆ D'.V ∩ F' := fun x ⟨hxJ, hxV⟩ =>
      ⟨hxV, hJ_union ▸ Or.inl hxJ⟩
    have hr₁_le : r₁ ≤ r := Set.ncard_le_ncard hJ₁_sub (hfin_V.subset inter_subset_left)
    change min r₁ r₂ ≤ (I' ∩ D'.V).ncard
    omega
  have hr_pos : 0 < r := Nat.pos_of_ne_zero hr0
  let s := (r + 1) / 2
  have hs : 0 < s := by dsimp [s]; omega
  -- Inside disc `D_F` of `F'` in `Δ'` and sleeve `sd` for `F'`.
  obtain ⟨D_F, hD_F, _⟩ := disc_oArc Δ' F' hΔ' hF'Δ hF'o
  have hDF_disc : IsClosedDisc D_F := hD_F.2.1
  have hDF_bd : discBd D_F = F' := hD_F.2.2.1
  have hinf_DF : (OnePoint.infty : SphereSurf) ∉ D_F := fun h => hinf (hD_F.1 h)
  have hI'_sub_DF : I' ⊆ D_F := by
    intro x hx
    by_cases hxab : x ∈ ({a', b'} : Set SphereSurf)
    · rcases hxab with rfl | rfl
      · exact Surface.discBd_subset D_F (hDF_bd.symm ▸ ha'F)
      · exact Surface.discBd_subset D_F (hDF_bd.symm ▸ hb'F)
    · exact ((insideOArc_iff_mem_discInt hΔ' hD_F).mp (hI'in x ⟨hx, hxab⟩)).1
  obtain ⟨sd⟩ := theorem_8_1_sphere hΔ' hD'U hinf hc'
  let E_B : Fin s → Set SphereSurf := fun j => (sd.nest.circuit j).ins
  have hEB_disc : ∀ j, IsClosedDisc (E_B j) := fun j => (sd.nest.circuit j).isInside.2.1
  have hEB_bd : ∀ j, discBd (E_B j) = (sd.nest.circuit j).U :=
    fun j => (sd.nest.circuit j).isInside.2.2.1
  have hinf_EB : ∀ j, (OnePoint.infty : SphereSurf) ∉ E_B j :=
    fun j h => hinf ((sd.nest.circuit j).isInside.1 h)
  have hEB_in_DF : ∀ j, E_B j ⊆ discInt D_F := by
    intro j
    refine insideDisc_subset_discInt_of_bd_subset_sphere (hEB_disc j) hDF_disc
      (hinf_EB j) hinf_DF ?_
    rw [hEB_bd j]
    intro x hx
    exact (insideOArc_iff_mem_discInt hΔ' hD_F).mp (sd.circuit_inside j x hx)
  have hEB_strict : ∀ j j' : Fin s, j < j' → E_B j ⊆ discInt (E_B j') := by
    intro j j' hlt
    refine insideDisc_subset_discInt_of_bd_subset_sphere (hEB_disc j) (hEB_disc j')
      (hinf_EB j) (hinf_EB j') ?_
    rw [hEB_bd j]
    intro x hx
    exact (insideOArc_iff_mem_discInt hΔ' (sd.nest.circuit j').isInside).mp
      (sd.nest.inside_of_lt hlt x hx)
  have hC_disj : ∀ j j' : Fin s, j ≠ j' →
      Disjoint (sd.nest.circuit j).U (sd.nest.circuit j').U := by
    intro j j' hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Set.disjoint_left.mpr fun x hxj hxj' =>
        (hEB_strict j j' hlt (Surface.discBd_subset _ ((hEB_bd j).symm ▸ hxj))).2
          ((hEB_bd j').symm ▸ hxj')
    · exact Set.disjoint_left.mpr fun x hxj hxj' =>
        (hEB_strict j' j hgt (Surface.discBd_subset _ ((hEB_bd j').symm ▸ hxj'))).2
          ((hEB_bd j).symm ▸ hxj)
  -- Case split on whether `I'` meets `(sd.nest.circuit 0).U`.
  by_cases hmeet0 : (I' ∩ (sd.nest.circuit ⟨0, hs⟩).U).Nonempty
  · -- Case 1: `I'` meets `C_0`, so `I'` meets each `C_j` (`j > 0`) in at least two points.
    obtain ⟨z₀, hz₀I, hz₀C0⟩ := hmeet0
    have hF'_dis_EB : ∀ j, Disjoint F' (E_B j) := by
      intro j
      refine Set.disjoint_left.mpr fun x hxF hxEB => ?_
      exact (hEB_in_DF j hxEB).2 (hDF_bd.symm ▸ hxF)
    have ha'_not_EB : ∀ j, a' ∉ E_B j := fun j h => Set.disjoint_left.mp (hF'_dis_EB j) ha'F h
    have hb'_not_EB : ∀ j, b' ∉ E_B j := fun j h => Set.disjoint_left.mp (hF'_dis_EB j) hb'F h
    obtain ⟨φ, hφ0, hφ1⟩ := hI'line
    let t₀ : unitInterval := φ.symm ⟨z₀, hz₀I⟩
    have hφ_t₀ : (φ t₀).1 = z₀ := by simp [t₀]
    have hz₀_ne_a : z₀ ≠ a' := fun h =>
      ha'_not_EB ⟨0, hs⟩ (h ▸ Surface.discBd_subset _ ((hEB_bd ⟨0, hs⟩).symm ▸ hz₀C0))
    have hz₀_ne_b : z₀ ≠ b' := fun h =>
      hb'_not_EB ⟨0, hs⟩ (h ▸ Surface.discBd_subset _ ((hEB_bd ⟨0, hs⟩).symm ▸ hz₀C0))
    have ht₀_pos : (0 : ℝ) < (t₀ : ℝ) := by
      rcases eq_or_lt_of_le t₀.2.1 with h0 | hpos
      · exfalso
        have ht0_eq : t₀ = 0 := Subtype.ext h0.symm
        exact hz₀_ne_a (hφ_t₀ ▸ ht0_eq ▸ hφ0)
      · exact hpos
    have ht₀_lt1 : (t₀ : ℝ) < 1 := by
      rcases lt_or_eq_of_le t₀.2.2 with hlt | h1
      · exact hlt
      · exfalso
        have ht1_eq : t₀ = 1 := Subtype.ext h1
        exact hz₀_ne_b (hφ_t₀ ▸ ht1_eq ▸ hφ1)
    let γ : ℝ → SphereSurf := fun x => (φ (Set.projIcc 0 1 zero_le_one x)).1
    have hγ_cont : Continuous γ :=
      continuous_subtype_val.comp (φ.continuous.comp continuous_projIcc)
    have hγ_mem_I : ∀ x, γ x ∈ I' := fun x => (φ _).2
    have htwo_C : ∀ j : Fin s, (⟨0, hs⟩ : Fin s) < j →
        ∃ y₁ y₂ : SphereSurf,
          y₁ ∈ (I' \ {a', b'}) ∩ (sd.nest.circuit j).U ∧
          y₂ ∈ (I' \ {a', b'}) ∩ (sd.nest.circuit j).U ∧ y₁ ≠ y₂ := by
      intro j hj
      have hz₀_int_j : z₀ ∈ discInt (E_B j) :=
        hEB_strict ⟨0, hs⟩ j hj (Surface.discBd_subset _ ((hEB_bd ⟨0, hs⟩).symm ▸ hz₀C0))
      -- Left half `[0, t₀]` meets `discBd (E_B j)`.
      have hK₁_pre : IsPreconnected (γ '' Icc 0 (t₀ : ℝ)) :=
        isPreconnected_Icc.image γ hγ_cont.continuousOn
      have ha'_K₁ : a' ∈ γ '' Icc 0 (t₀ : ℝ) := by
        refine ⟨0, ⟨ le_refl 0, le_of_lt ht₀_pos⟩, ?_⟩
        change (φ (Set.projIcc 0 1 zero_le_one 0)).1 = a'
        have hp0 : Set.projIcc (0 : ℝ) 1 zero_le_one 0 = 0 := by ext; simp
        rw [hp0, hφ0]
      have hz₀_K₁ : z₀ ∈ γ '' Icc 0 (t₀ : ℝ) := by
        refine ⟨(t₀ : ℝ), ⟨le_of_lt ht₀_pos, le_refl _⟩, ?_⟩
        change (φ (Set.projIcc 0 1 zero_le_one (t₀ : ℝ))).1 = z₀
        have hpt0 : Set.projIcc (0 : ℝ) 1 zero_le_one (t₀ : ℝ) = t₀ :=
          Set.projIcc_of_mem zero_le_one t₀.2
        rw [hpt0, hφ_t₀]
      have hmeet_K₁ : ¬ Disjoint (γ '' Icc 0 (t₀ : ℝ)) (discBd (E_B j)) := by
        intro hdis
        rcases (hEB_disc j).side hman hK₁_pre hdis with hin | hout
        · exact ha'_not_EB j (hin ha'_K₁).1
        · exact Set.disjoint_left.mp hout hz₀_K₁ hz₀_int_j.1
      obtain ⟨y₁, ⟨x₁, hx₁_Icc, rfl⟩, hy₁_bd⟩ := Set.not_disjoint_iff.mp hmeet_K₁
      rw [hEB_bd j] at hy₁_bd
      -- Right half `[t₀, 1]` meets `discBd (E_B j)`.
      have hK₂_pre : IsPreconnected (γ '' Icc (t₀ : ℝ) 1) :=
        isPreconnected_Icc.image γ hγ_cont.continuousOn
      have hb'_K₂ : b' ∈ γ '' Icc (t₀ : ℝ) 1 := by
        refine ⟨1, ⟨le_of_lt ht₀_lt1, le_refl 1⟩, ?_⟩
        change (φ (Set.projIcc 0 1 zero_le_one 1)).1 = b'
        have hp1 : Set.projIcc (0 : ℝ) 1 zero_le_one 1 = 1 := by ext; simp
        rw [hp1, hφ1]
      have hz₀_K₂ : z₀ ∈ γ '' Icc (t₀ : ℝ) 1 := by
        refine ⟨(t₀ : ℝ), ⟨le_refl _, le_of_lt ht₀_lt1⟩, ?_⟩
        change (φ (Set.projIcc 0 1 zero_le_one (t₀ : ℝ))).1 = z₀
        have hpt0 : Set.projIcc (0 : ℝ) 1 zero_le_one (t₀ : ℝ) = t₀ :=
          Set.projIcc_of_mem zero_le_one t₀.2
        rw [hpt0, hφ_t₀]
      have hmeet_K₂ : ¬ Disjoint (γ '' Icc (t₀ : ℝ) 1) (discBd (E_B j)) := by
        intro hdis
        rcases (hEB_disc j).side hman hK₂_pre hdis with hin | hout
        · exact hb'_not_EB j (hin hb'_K₂).1
        · exact Set.disjoint_left.mp hout hz₀_K₂ hz₀_int_j.1
      obtain ⟨y₂, ⟨x₂, hx₂_Icc, rfl⟩, hy₂_bd⟩ := Set.not_disjoint_iff.mp hmeet_K₂
      rw [hEB_bd j] at hy₂_bd
      have hy₁_not_ab : γ x₁ ∉ ({a', b'} : Set SphereSurf) := by
        rintro (h | h)
        · exact ha'_not_EB j (h ▸ Surface.discBd_subset _ ((hEB_bd j).symm ▸ hy₁_bd))
        · exact hb'_not_EB j (h ▸ Surface.discBd_subset _ ((hEB_bd j).symm ▸ hy₁_bd))
      have hy₂_not_ab : γ x₂ ∉ ({a', b'} : Set SphereSurf) := by
        rintro (h | h)
        · exact ha'_not_EB j (h ▸ Surface.discBd_subset _ ((hEB_bd j).symm ▸ hy₂_bd))
        · exact hb'_not_EB j (h ▸ Surface.discBd_subset _ ((hEB_bd j).symm ▸ hy₂_bd))
      have hx₁_lt_t0 : x₁ < (t₀ : ℝ) := by
        rcases lt_or_eq_of_le hx₁_Icc.2 with hlt | rfl
        · exact hlt
        · exfalso
          have hγt0 : γ (t₀ : ℝ) = z₀ := by
            change (φ (Set.projIcc 0 1 zero_le_one (t₀ : ℝ))).1 = z₀
            have hpt0 : Set.projIcc (0 : ℝ) 1 zero_le_one (t₀ : ℝ) = t₀ :=
              Set.projIcc_of_mem zero_le_one t₀.2
            rw [hpt0, hφ_t₀]
          exact Set.disjoint_left.mp (hC_disj ⟨0, hs⟩ j (ne_of_lt hj)) hz₀C0 (hγt0 ▸ hy₁_bd)
      have ht0_lt_x₂ : (t₀ : ℝ) < x₂ := by
        rcases eq_or_lt_of_le hx₂_Icc.1 with heq | hlt
        · exfalso
          have hγt0 : γ x₂ = z₀ := by
            rw [← heq]
            change (φ (Set.projIcc 0 1 zero_le_one (t₀ : ℝ))).1 = z₀
            have hpt0 : Set.projIcc (0 : ℝ) 1 zero_le_one (t₀ : ℝ) = t₀ :=
              Set.projIcc_of_mem zero_le_one t₀.2
            rw [hpt0, hφ_t₀]
          exact Set.disjoint_left.mp (hC_disj ⟨0, hs⟩ j (ne_of_lt hj)) hz₀C0 (hγt0 ▸ hy₂_bd)
        · exact hlt
      have hy_ne : γ x₁ ≠ γ x₂ := by
        intro heq
        have hp₁_mem : x₁ ∈ Icc (0 : ℝ) 1 := ⟨hx₁_Icc.1, le_trans hx₁_Icc.2 t₀.2.2⟩
        have hp₂_mem : x₂ ∈ Icc (0 : ℝ) 1 := ⟨le_trans t₀.2.1 hx₂_Icc.1, hx₂_Icc.2⟩
        have hinj_eq := φ.injective (Subtype.ext heq)
        have hp₁_val : (Set.projIcc 0 1 zero_le_one x₁ : ℝ) = x₁ :=
          congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hp₁_mem)
        have hp₂_val : (Set.projIcc 0 1 zero_le_one x₂ : ℝ) = x₂ :=
          congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hp₂_mem)
        have hval_eq : (Set.projIcc 0 1 zero_le_one x₁ : ℝ) =
            (Set.projIcc 0 1 zero_le_one x₂ : ℝ) := congrArg Subtype.val hinj_eq
        rw [hp₁_val, hp₂_val] at hval_eq
        linarith
      exact ⟨γ x₁, γ x₂, ⟨⟨hγ_mem_I x₁, hy₁_not_ab⟩, hy₁_bd⟩,
        ⟨⟨hγ_mem_I x₂, hy₂_not_ab⟩, hy₂_bd⟩, hy_ne⟩
    -- Inject `Fin (1 + 2 * (s - 1))` into `(I' \ {a', b'}) ∩ D'.V`.
    let sh : Fin (s - 1) → Fin s := fun m => ⟨1 + m.1, by have := m.2; omega⟩
    have hsh_pos : ∀ m, (⟨0, hs⟩ : Fin s) < sh m := fun m => Fin.lt_def.mpr (by dsimp [sh]; omega)
    choose y₁ y₂ hy₁ hy₂ hy_ne using fun m => htwo_C (sh m) (hsh_pos m)
    let g : Fin (1 + 2 * (s - 1)) → SphereSurf := fun idx =>
      if h0 : idx.1 = 0 then z₀
      else
        let t := idx.1 - 1
        let m : Fin (s - 1) := ⟨t / 2, by have := idx.2; dsimp [t]; omega⟩
        if t % 2 = 0 then y₁ m else y₂ m
    have hg_mem_C : ∀ idx : Fin (1 + 2 * (s - 1)),
        (idx.1 = 0 ∧ g idx ∈ (I' \ {a', b'}) ∩ (sd.nest.circuit ⟨0, hs⟩).U) ∨
        (∃ hpos : 0 < idx.1,
          g idx ∈ (I' \ {a', b'}) ∩ (sd.nest.circuit (sh ⟨(idx.1 - 1) / 2, by have := idx.2; omega⟩)).U) := by
      intro idx
      by_cases h0 : idx.1 = 0
      · refine Or.inl ⟨h0, ?_⟩
        dsimp only [g]
        split_ifs
        exact ⟨⟨hz₀I, by rintro (rfl | rfl); exacts [hz₀_ne_a rfl, hz₀_ne_b rfl]⟩, hz₀C0⟩
      · refine Or.inr ⟨Nat.pos_of_ne_zero h0, ?_⟩
        dsimp only [g]
        split_ifs
        · exact hy₁ _
        · exact hy₂ _
    have hg_target : range g ⊆ (I' \ {a', b'}) ∩ D'.V := by
      rintro _ ⟨idx, rfl⟩
      rcases hg_mem_C idx with ⟨_, hmem⟩ | ⟨_, hmem⟩
      · exact ⟨hmem.1, hI'norm ⟨hmem.1.1, (sd.nest.circuit ⟨0, hs⟩).U_sub_drawing hmem.2⟩⟩
      · exact ⟨hmem.1, hI'norm ⟨hmem.1.1, (sd.nest.circuit _).U_sub_drawing hmem.2⟩⟩
    have hg_inj : Function.Injective g := by
      intro p q hpq
      have hp2 := p.2
      have hq2 := q.2
      apply Fin.ext
      rcases hg_mem_C p with ⟨hp0, hpmem⟩ | ⟨hppos, hpmem⟩ <;>
        rcases hg_mem_C q with ⟨hq0, hqmem⟩ | ⟨hqpos, hqmem⟩
      · omega
      · exfalso
        exact Set.disjoint_left.mp (hC_disj _ _ (ne_of_lt (hsh_pos _))) hpmem.2 (hpq ▸ hqmem.2)
      · exfalso
        exact Set.disjoint_left.mp (hC_disj _ _ (ne_of_gt (hsh_pos _))) hpmem.2 (hpq ▸ hqmem.2)
      · have hdiv_eq : (p.1 - 1) / 2 = (q.1 - 1) / 2 := by
          by_contra hdiv_ne
          have hsh_ne : sh ⟨(p.1 - 1) / 2, by omega⟩ ≠ sh ⟨(q.1 - 1) / 2, by omega⟩ := by
            intro he
            have := congrArg Fin.val he
            dsimp [sh] at this
            omega
          exact Set.disjoint_left.mp (hC_disj _ _ hsh_ne) hpmem.2 (hpq ▸ hqmem.2)
        have hm_eq : (⟨(p.1 - 1) / 2, by omega⟩ : Fin (s - 1)) = ⟨(q.1 - 1) / 2, by omega⟩ :=
          Fin.ext hdiv_eq
        dsimp only [g] at hpq
        split_ifs at hpq <;>
          first
          | omega
          | (rw [hm_eq] at hpq; exact absurd hpq (hy_ne _))
          | (rw [hm_eq] at hpq; exact absurd hpq.symm (hy_ne _))
    have hcard_int : 1 + 2 * (s - 1) ≤ ((I' \ {a', b'}) ∩ D'.V).ncard := by
      have hle := Set.ncard_le_ncard hg_target (hfin_V.subset inter_subset_right)
      rwa [Set.ncard_range_of_injective hg_inj, Nat.card_fin] at hle
    have hab_sub_I : ({a', b'} : Set SphereSurf) ⊆ I' := by
      rintro x (rfl | rfl)
      · exact hI'l
      · exact hI'r
    have hsplit_I : I' ∩ D'.V = ((I' \ {a', b'}) ∩ D'.V) ∪ ({a', b'} ∩ D'.V) := by
      ext x
      simp only [mem_inter_iff, mem_union, mem_sdiff]
      exact ⟨fun ⟨hxI, hxV⟩ => by
        by_cases hxab : x ∈ ({a', b'} : Set SphereSurf)
        · exact Or.inr ⟨hxab, hxV⟩
        · exact Or.inl ⟨⟨hxI, hxab⟩, hxV⟩,
        fun h => h.elim (fun ⟨⟨hxI, _⟩, hxV⟩ => ⟨hxI, hxV⟩)
          (fun ⟨hxab, hxV⟩ => ⟨hab_sub_I hxab, hxV⟩)⟩
    have hdis_split : Disjoint ((I' \ {a', b'}) ∩ D'.V) ({a', b'} ∩ D'.V) :=
      Set.disjoint_left.mpr fun _ ⟨⟨_, hnot⟩, _⟩ ⟨hab, _⟩ => hnot hab
    have hcard_total : (I' ∩ D'.V).ncard = ((I' \ {a', b'}) ∩ D'.V).ncard + n := by
      rw [hsplit_I, Set.ncard_union_eq hdis_split
        (hfin_V.subset inter_subset_right) (hfin_V.subset inter_subset_right)]
    change min r₁ r₂ ≤ (I' ∩ D'.V).ncard
    dsimp only [r₁, r₂, r, n, s] at hr_sum hr_pos hcard_int hcard_total ⊢
    omega
  · -- Case 2: `I'` is disjoint from `C_0`.
    have hdis_C0 : Disjoint I' (sd.nest.circuit ⟨0, hs⟩).U :=
      Set.not_nonempty_iff_eq_empty.mp hmeet0 |> Set.disjoint_iff_inter_eq_empty.mpr
    by_contra hlt_min
    have hlt_r₁ : (I' ∩ D'.V).ncard < r₁ := (lt_min_iff.mp (not_le.mp hlt_min)).1
    have hlt_r₂ : (I' ∩ D'.V).ncard < r₂ := (lt_min_iff.mp (not_le.mp hlt_min)).2
    -- Extract the spoke endpoints `v_sp : Fin r → SphereSurf` on `F'`.
    choose hs_sp u_sp v_sp hsp_sub hu_sp hv_sp hsp_path hsp_enc hsp_VF using sd.isPath_spoke
    have hv_mem_VF : ∀ i : Fin r, v_sp i ∈ D'.V ∩ F' := by
      intro i
      have hv_in : v_sp i ∈ (sd.spoke i).V ∩ F' := by rw [hsp_VF i]; exact mem_singleton _
      exact ⟨(hsp_sub i).1 hv_in.1, hv_in.2⟩
    have hv_inj : Function.Injective v_sp := by
      intro i j hij
      by_contra hne
      have hi_mem : v_sp i ∈ (sd.spoke i).V := by
        have : v_sp i ∈ (sd.spoke i).V ∩ F' := by rw [hsp_VF i]; exact mem_singleton _
        exact this.1
      have hj_mem : v_sp j ∈ (sd.spoke j).V := by
        have : v_sp j ∈ (sd.spoke j).V ∩ F' := by rw [hsp_VF j]; exact mem_singleton _
        exact this.1
      exact Set.disjoint_left.mp (sd.pairwise_disjoint_spokes hne) hi_mem (hij ▸ hj_mem)
    have hv_range : range v_sp = D'.V ∩ F' := by
      refine Set.eq_of_subset_of_ncard_le (by rintro _ ⟨i, rfl⟩; exact hv_mem_VF i) ?_
        (hfin_V.subset inter_subset_left)
      rw [Set.ncard_range_of_injective hv_inj, Nat.card_fin]
    -- Count spokes ending in `J₁` (`r₁`) and `J₂` (`r₂`), and spokes meeting `I'` (`≤ |I' ∩ D'.V|`).
    let idx₁ : Set (Fin r) := {i : Fin r | v_sp i ∈ J₁}
    let idx₂ : Set (Fin r) := {i : Fin r | v_sp i ∈ J₂}
    let hit : Set (Fin r) := {i : Fin r | ((sd.spoke i).U ∩ I').Nonempty}
    have hidx₁_img : v_sp '' idx₁ = J₁ ∩ D'.V := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hi, (hv_mem_VF i).1⟩
      · rintro ⟨hxJ, hxV⟩
        have hxVF : x ∈ D'.V ∩ F' := ⟨hxV, hJ_union ▸ Or.inl hxJ⟩
        obtain ⟨i, rfl⟩ := hv_range ▸ hxVF
        exact ⟨i, hxJ, rfl⟩
    have hidx₂_img : v_sp '' idx₂ = J₂ ∩ D'.V := by
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hi, (hv_mem_VF i).1⟩
      · rintro ⟨hxJ, hxV⟩
        have hxVF : x ∈ D'.V ∩ F' := ⟨hxV, hJ_union ▸ Or.inr hxJ⟩
        obtain ⟨i, rfl⟩ := hv_range ▸ hxVF
        exact ⟨i, hxJ, rfl⟩
    have hidx₁_card : idx₁.ncard = r₁ := by
      change idx₁.ncard = (J₁ ∩ D'.V).ncard
      rw [← hidx₁_img, Set.ncard_image_of_injective _ hv_inj]
    have hidx₂_card : idx₂.ncard = r₂ := by
      change idx₂.ncard = (J₂ ∩ D'.V).ncard
      rw [← hidx₂_img, Set.ncard_image_of_injective _ hv_inj]
    have hhit_vert : ∀ i : hit, ∃ z : SphereSurf, z ∈ (sd.spoke i.1).V ∧ z ∈ I' ∩ D'.V := by
      intro ⟨i, z, hzU, hzI⟩
      have hzDV : z ∈ D'.V := hI'norm ⟨hzI, (hsp_sub i).U_subset hzU⟩
      have hzPV : z ∈ (sd.spoke i).V := by
        by_contra hnot
        obtain ⟨e, he, hze⟩ := (sd.spoke i).exists_edge_of_mem hzU hnot
        exact (((hsp_sub i).2 he).2.1 hze).2 hzDV
      exact ⟨z, hzPV, hzI, hzDV⟩
    choose z_hit hz_spV hz_IV using hhit_vert
    have hz_hit_inj : Function.Injective z_hit := by
      intro p q hpq
      by_contra hne
      have hne_val : p.1 ≠ q.1 := fun h => hne (Subtype.ext h)
      exact Set.disjoint_left.mp (sd.pairwise_disjoint_spokes hne_val) (hz_spV p) (hpq ▸ hz_spV q)
    have hhit_card : hit.ncard ≤ (I' ∩ D'.V).ncard := by
      have hle := Set.ncard_le_ncard (s := range z_hit) (t := I' ∩ D'.V)
        (by rintro _ ⟨p, rfl⟩; exact hz_IV p) (hfin_V.subset inter_subset_right)
      rwa [Set.ncard_range_of_injective hz_hit_inj, Nat.card_coe_set_eq] at hle
    -- Pick a spoke `i₁ ∈ idx₁ \ hit` and a spoke `i₂ ∈ idx₂ \ hit`.
    have hex₁ : (idx₁ \ hit).Nonempty := by
      by_contra hempty
      have hsub : idx₁ ⊆ hit := sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hempty)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite hit)
      omega
    have hex₂ : (idx₂ \ hit).Nonempty := by
      by_contra hempty
      have hsub : idx₂ ⊆ hit := sdiff_eq_empty.mp (Set.not_nonempty_iff_eq_empty.mp hempty)
      have hle := Set.ncard_le_ncard hsub (Set.toFinite hit)
      omega
    obtain ⟨i₁, hi₁_J, hi₁_not_hit⟩ := hex₁
    obtain ⟨i₂, hi₂_J, hi₂_not_hit⟩ := hex₂
    have hdis_P₁ : Disjoint I' (sd.spoke i₁).U :=
      (Set.not_nonempty_iff_eq_empty.mp hi₁_not_hit |>
        Set.disjoint_iff_inter_eq_empty.mpr).symm
    have hdis_P₂ : Disjoint I' (sd.spoke i₂).U :=
      (Set.not_nonempty_iff_eq_empty.mp hi₂_not_hit |>
        Set.disjoint_iff_inter_eq_empty.mpr).symm
    have hv₁_spU : v_sp i₁ ∈ (sd.spoke i₁).U :=
      (sd.spoke i₁).V_subset_U (by
        have : v_sp i₁ ∈ (sd.spoke i₁).V ∩ F' := by rw [hsp_VF i₁]; exact mem_singleton _
        exact this.1)
    have hv₂_spU : v_sp i₂ ∈ (sd.spoke i₂).U :=
      (sd.spoke i₂).V_subset_U (by
        have : v_sp i₂ ∈ (sd.spoke i₂).V ∩ F' := by rw [hsp_VF i₂]; exact mem_singleton _
        exact this.1)
    have hv₁_not_ab : v_sp i₁ ∉ ({a', b'} : Set SphereSurf) := by
      rintro (h | h)
      · exact Set.disjoint_left.mp hdis_P₁ hI'l (h ▸ hv₁_spU)
      · exact Set.disjoint_left.mp hdis_P₁ hI'r (h ▸ hv₁_spU)
    have hv₂_not_ab : v_sp i₂ ∉ ({a', b'} : Set SphereSurf) := by
      rintro (h | h)
      · exact Set.disjoint_left.mp hdis_P₂ hI'l (h ▸ hv₂_spU)
      · exact Set.disjoint_left.mp hdis_P₂ hI'r (h ▸ hv₂_spU)
    have hv₁_mem_comp₁ : v_sp i₁ ∈ J₁ \ {a', b'} := ⟨hi₁_J, hv₁_not_ab⟩
    have hv₂_mem_comp₂ : v_sp i₂ ∈ J₂ \ {a', b'} := ⟨hi₂_J, hv₂_not_ab⟩
    -- Form the compact connected tree-plus-circuit set `B = C_0 ∪ P_{i₁} ∪ P_{i₂} ⊆ D_F`.
    let C₀_U := (sd.circuitDraw ⟨0, hs⟩).U
    have hC₀_eq : C₀_U = (sd.nest.circuit ⟨0, hs⟩).U := (sd.isCircuit_draw ⟨0, hs⟩).2.2
    let B : Set SphereSurf := C₀_U ∪ (sd.spoke i₁).U ∪ (sd.spoke i₂).U
    have hB_sub_DF : B ⊆ D_F := by
      refine union_subset (union_subset ?_ ?_) ?_
      · rw [hC₀_eq]
        exact fun x hx =>
          (hEB_in_DF ⟨0, hs⟩ (Surface.discBd_subset _ ((hEB_bd ⟨0, hs⟩).symm ▸ hx))).1
      · exact (oArcEncloses_iff_subset hΔ' hD_F).mp (hsp_enc i₁)
      · exact (oArcEncloses_iff_subset hΔ' hD_F).mp (hsp_enc i₂)
    have hB_comp : IsCompact B :=
      ((sd.circuitDraw ⟨0, hs⟩).isClosed_U.isCompact.union
        (sd.spoke i₁).isClosed_U.isCompact).union (sd.spoke i₂).isClosed_U.isCompact
    have hC₀_conn : IsConnected C₀_U := by
      rw [hC₀_eq]
      exact IsOArc.isConnected' (sd.nest.circuit ⟨0, hs⟩).isOArc_U
    have hu₁_spU : u_sp i₁ ∈ (sd.spoke i₁).U := by
      obtain ⟨W, _, hPV, _⟩ := hsp_path i₁
      exact (sd.spoke i₁).V_subset_U (by rw [hPV]; exact W.start_mem_support)
    have hu₂_spU : u_sp i₂ ∈ (sd.spoke i₂).U := by
      obtain ⟨W, _, hPV, _⟩ := hsp_path i₂
      exact (sd.spoke i₂).V_subset_U (by rw [hPV]; exact W.start_mem_support)
    have hC₀P₁_pre : IsPreconnected (C₀_U ∪ (sd.spoke i₁).U) :=
      hC₀_conn.isPreconnected.union (u_sp i₁) (hC₀_eq ▸ hu_sp i₁) hu₁_spU
        (isPreconnected_U_of_isPathBetween (hsp_path i₁))
    have hB_pre : IsPreconnected B :=
      hC₀P₁_pre.union (u_sp i₂) (Or.inl (hC₀_eq ▸ hu_sp i₂)) hu₂_spU
        (isPreconnected_U_of_isPathBetween (hsp_path i₂))
    have hB_conn : IsConnected B := ⟨⟨u_sp i₁, Or.inl (Or.inl (hC₀_eq ▸ hu_sp i₁))⟩, hB_pre⟩
    -- `{a', b'}` and `{v_sp i₁, v_sp i₂}` cross on `discBd D_F = F'`.
    have hcc₁ : connectedComponentIn (F' \ {a', b'}) (v_sp i₁) = J₁ \ {a', b'} := by
      have hmem_c : J₁ \ {a', b'} ∈ componentsIn (F' \ {a', b'}) :=
        hcomp_J ▸ mem_insert _ _
      obtain ⟨w, _, hw_eq⟩ := hmem_c
      have hv_in_w : v_sp i₁ ∈ connectedComponentIn (F' \ {a', b'}) w :=
        hw_eq.symm ▸ hv₁_mem_comp₁
      exact (connectedComponentIn_eq hv_in_w).symm.trans hw_eq
    have hcc₂ : connectedComponentIn (F' \ {a', b'}) (v_sp i₂) = J₂ \ {a', b'} := by
      have hmem_c : J₂ \ {a', b'} ∈ componentsIn (F' \ {a', b'}) :=
        hcomp_J ▸ mem_insert_of_mem _ (mem_singleton _)
      obtain ⟨w, _, hw_eq⟩ := hmem_c
      have hv_in_w : v_sp i₂ ∈ connectedComponentIn (F' \ {a', b'}) w :=
        hw_eq.symm ▸ hv₂_mem_comp₂
      exact (connectedComponentIn_eq hv_in_w).symm.trans hw_eq
    have hcc_ne : connectedComponentIn (F' \ {a', b'}) (v_sp i₁) ≠
        connectedComponentIn (F' \ {a', b'}) (v_sp i₂) := by
      rw [hcc₁, hcc₂]
      intro heq
      exact Set.disjoint_left.mp (hJ12_dis.mono_left subset_closure) hv₁_mem_comp₁
        (heq ▸ hv₁_mem_comp₁)
    have hv12_ne : v_sp i₁ ≠ v_sp i₂ := fun h => hcc_ne (h ▸ rfl)
    have hcross : PairsCrossOn (discBd D_F) a' b' (v_sp i₁) (v_sp i₂) := by
      rw [hDF_bd]
      refine ⟨ha'F, hv_sp i₁, hb'F, hv_sp i₂, ha'b', hv12_ne, ?_, ?_, ?_, ?_, hcc_ne⟩
      · exact fun h => hv₁_not_ab (Or.inl h.symm)
      · exact fun h => hv₂_not_ab (Or.inl h.symm)
      · exact fun h => hv₁_not_ab (Or.inr h.symm)
      · exact fun h => hv₂_not_ab (Or.inr h.symm)
    have hI'comp : IsCompact I' := by
      obtain ⟨φ, _, _⟩ := hI'line
      have hr : range (Subtype.val ∘ φ) = I' := by
        ext z; exact ⟨fun ⟨t, ht⟩ => ht ▸ (φ t).2, fun hz => ⟨φ.symm ⟨z, hz⟩, by simp⟩⟩
      exact hr ▸ isCompact_range (continuous_subtype_val.comp φ.continuous)
    obtain ⟨z, hzI, hzB⟩ := Surface.disc_crossing D_F I' B a' b' (v_sp i₁) (v_sp i₂)
      hDF_disc hI'_sub_DF hB_sub_DF hI'comp hB_comp
      (GM07.isConnected_line hI'line) hB_conn
      hI'l hI'r (Or.inl (Or.inr hv₁_spU)) (Or.inr hv₂_spU) hcross
    rcases hzB with (hzC0 | hzP1) | hzP2
    · exact Set.disjoint_left.mp hdis_C0 hzI (hC₀_eq ▸ hzC0)
    · exact Set.disjoint_left.mp hdis_P₁ hzI hzP1
    · exact Set.disjoint_left.mp hdis_P₂ hzI hzP2

end SphereModel83

/-- **(8.3)** *Let $F$ be a $\Gamma$-normal centred $O$-arc. Let $I$ be a $\Gamma$-normal $[0, 1]$-arc with ends in $F$ and with all its other points inside $F$. Then*
$$|I \cap V(\Gamma)| \ge \min(|F_1 \cap V(\Gamma)|, |F_2 \cap V(\Gamma)|),$$
*where $F_1, F_2$ are the closures of the two components into which the ends of $I$ divide $F$.*
(GM VIII Section 8, page 268.) -/
theorem theorem_8_3_proof {S : Type u} [TopologicalSpace S] {D : Drawing S} {Δ F I : Set S}
    {a b : S} {A₁ A₂ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ)
    (hc : IsCentredOArc D Δ F)
    (hInorm : D.IsNormal I) (hIline : IsLineWithEnds I a b)
    (haF : a ∈ F) (hbF : b ∈ F)
    (hIin : SetInsideOArc Δ F (I \ {a, b}))
    (hcomp : componentsIn (F \ {a, b}) = {A₁, A₂}) (hAne : A₁ ≠ A₂) :
    min (closure A₁ ∩ D.V).ncard (closure A₂ ∩ D.V).ncard ≤ (I ∩ D.V).ncard := by
  have hFΔ : F ⊆ Δ := hc.1
  have hFo : IsOArc F := hc.2.1
  have hIΔ : I ⊆ Δ := by
    intro x hx
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl
      · exact hFΔ haF
      · exact hFΔ hbF
    · obtain ⟨D₀, hD₀, hx₀⟩ := hIin x ⟨hx, hxab⟩
      exact hD₀.1 hx₀.1
  obtain ⟨f, f', sc⟩ := exists_sphereDiscChart hΔ
  obtain ⟨D', _, hD'U, hD'V, hD'E, _, _, _⟩ := sc.exists_transport_drawing hΔ D hDU
  obtain ⟨hΔ', _⟩ := sc.disc_f Subset.rfl hΔ
  have hD'U_sub : D'.U ⊆ f '' Δ := hD'U ▸ image_mono hDU
  have hc' : IsCentredOArc D' (f '' Δ) (f '' F) :=
    sc.push_isCentredOArc hΔ hDU hD'U hD'V hD'E hc
  have hI'norm : D'.IsNormal (f '' I) := (sc.isNormal_f_iff hDU hD'U hD'V hIΔ).mpr hInorm
  have hI'line : IsLineWithEnds (f '' I) (f a) (f b) := by
    obtain ⟨φ, h0, h1⟩ := hIline
    have hc₁ : Continuous fun t => f (φ t).1 :=
      (sc.fc.mono hIΔ).comp_continuous (continuous_subtype_val.comp φ.continuous) fun t => (φ t).2
    have hi₁ : Function.Injective fun t => f (φ t).1 := fun x y h =>
      φ.injective (Subtype.ext (sc.injOn_f (hIΔ (φ x).2) (hIΔ (φ y).2) h))
    have hr : range (fun t => f (φ t).1) = f '' I := by
      ext y
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨(φ t).1, (φ t).2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨φ.symm ⟨x, hx⟩, by simp⟩
    let ψ := (hc₁.isClosedEmbedding hi₁).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
    refine ⟨ψ, ?_, ?_⟩
    · change f (φ 0).1 = f a
      rw [h0]
    · change f (φ 1).1 = f b
      rw [h1]
  have hf_ab_Δ : ({a, b} : Set S) ⊆ Δ := by
    rintro x (rfl | rfl)
    · exact hFΔ haF
    · exact hFΔ hbF
  have hfI_sdiff : f '' I \ {f a, f b} = f '' (I \ {a, b}) := by
    rw [← image_pair, ← sc.f_sdiff hIΔ hf_ab_Δ]
  have hI'in : SetInsideOArc (f '' Δ) (f '' F) (f '' I \ {f a, f b}) := by
    rw [hfI_sdiff]
    exact (sc.setInsideOArc_f_iff hΔ hFΔ hFo (sdiff_subset.trans hIΔ)).mpr hIin
  have hfF_sdiff : f '' F \ {f a, f b} = f '' (F \ {a, b}) := by
    rw [← image_pair, ← sc.f_sdiff hFΔ hf_ab_Δ]
  have hFsdiff_Δ : F \ {a, b} ⊆ Δ := sdiff_subset.trans hFΔ
  have hcomp' : componentsIn (f '' F \ {f a, f b}) = {f '' A₁, f '' A₂} := by
    rw [hfF_sdiff, componentsIn_image_gen (sc.fc.mono hFsdiff_Δ)
      (sc.f'c.mono (image_mono hFsdiff_Δ)) (fun x hx => sc.f'f (hFsdiff_Δ hx)), hcomp, image_pair]
  have hA₁_sub : A₁ ⊆ F \ {a, b} := by
    have hmem : A₁ ∈ componentsIn (F \ {a, b}) := hcomp ▸ mem_insert _ _
    obtain ⟨w, _, rfl⟩ := hmem
    exact connectedComponentIn_subset _ _
  have hA₂_sub : A₂ ⊆ F \ {a, b} := by
    have hmem : A₂ ∈ componentsIn (F \ {a, b}) := hcomp ▸ mem_insert_of_mem _ (mem_singleton _)
    obtain ⟨w, _, rfl⟩ := hmem
    exact connectedComponentIn_subset _ _
  have hA'ne : f '' A₁ ≠ f '' A₂ := by
    intro heq
    apply hAne
    rw [← sc.f'_f (hA₁_sub.trans hFsdiff_Δ), ← sc.f'_f (hA₂_sub.trans hFsdiff_Δ), heq]
  have hbound := theorem_8_3_sphere hΔ' sc.infty_notMem hD'U_sub hc' hI'norm hI'line
    (mem_image_of_mem f haF) (mem_image_of_mem f hbF) hI'in hcomp' hA'ne
  have hDV_Δ : D.V ⊆ Δ := D.V_subset_U.trans hDU
  have hcard_A₁ : (closure (f '' A₁) ∩ D'.V).ncard = (closure A₁ ∩ D.V).ncard := by
    rw [hD'V, ← image_closure_inter_eq_of_subset_disc sc (hA₁_sub.trans hFsdiff_Δ) hDV_Δ,
      (sc.injOn_f.mono (inter_subset_right.trans hDV_Δ)).ncard_image]
  have hcard_A₂ : (closure (f '' A₂) ∩ D'.V).ncard = (closure A₂ ∩ D.V).ncard := by
    rw [hD'V, ← image_closure_inter_eq_of_subset_disc sc (hA₂_sub.trans hFsdiff_Δ) hDV_Δ,
      (sc.injOn_f.mono (inter_subset_right.trans hDV_Δ)).ncard_image]
  have hcard_I : (f '' I ∩ D'.V).ncard = (I ∩ D.V).ncard := by
    rw [hD'V, ← InjOn.image_inter sc.injOn_f hIΔ hDV_Δ,
      (sc.injOn_f.mono (inter_subset_right.trans hDV_Δ)).ncard_image]
  rwa [hcard_A₁, hcard_A₂, hcard_I] at hbound

end GM08
end GraphMinor
