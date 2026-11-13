module

public import GraphMinor.GM21.Section3
public import GraphMinor.GM07.GoodEdge
public import GraphMinor.GM11.PaintingRegions
public import GraphMinor.GM11.RadialBasics
public import GraphMinor.GM19.CapModel
public import GraphMinor.GM19.FragmentSides
public import GraphMinor.GM19.Section4c
public import GraphMinor.GM19.Section5o
public import GraphMinor.GM19.Section6a
public import GraphMinor.GM19.Section6Six
public import GraphMinor.Surface.AddCrosscap
public import GraphMinor.Surface.CutIArc
public import GraphMinor.Surface.CutOArc
public import GraphMinor.Surface.Epstein
public import GraphMinor.Surface.HoleDisc
public import GraphMinor.Surface.OpenDisc
public import GraphMinor.Surface.PasteModel
public import GraphMinor.Surface.SphereDisc

/-!
# Graph Minors XXI, Section 4: Surfaces

Formalization of Section 4 (pages 10–12 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Proves:
- `theorem_4_1` (Graph Minors XXI, (4.1)): effect on `Ŝ` and `c(Σ)` of cutting a surface along a
  proper line or O-arc.
- `theorem_4_2` (Graph Minors XXI, (4.2)): subsurfaces `Σ₁, Σ₂ ⊆ Σ` with `Σ₁ ∪ Σ₂ = Σ` and
  `Σ₁ ∩ Σ₂ = F` when `F` separates `Σ`.
- `theorem_4_3` (Graph Minors XXI, (4.3)): characterization of 2-cell drawings in a surface with
  null boundary.
- `theorem_4_4` (Graph Minors XXI, (4.4)): an O-arc in a surface with null boundary bounds a
  closed disc if and only if it is null-homotopic.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM19

/-! ## Proper lines and cutting maps -/

/-- A line `F ⊆ S` with ends `s, t` is *proper* in `S` if its ends lie in `bd S` and no internal
point of `F` lies in `bd S` (Graph Minors XXI, Section 4, page 10 of the preprint:
"A line in $\Sigma$ is *proper* if its ends are in $bd(\Sigma)$ and it has no internal point in
$bd(\Sigma)$."). -/
def IsProperLineInSurface {S : Type*} [TopologicalSpace S]
    (F : Set S) (s t : S) : Prop :=
  IsLineWithEnds F s t ∧
  s ∈ bd S ∧ t ∈ bd S ∧
  Disjoint (F \ {s, t}) (bd S)

theorem IsProperLineInSurface.ne {S : Type*} [TopologicalSpace S] {F : Set S} {s t : S}
    (h : IsProperLineInSurface F s t) : s ≠ t :=
  h.1.ne'

theorem IsProperLineInSurface.inter_bd_eq {S : Type*} [TopologicalSpace S] {F : Set S} {s t : S}
    (h : IsProperLineInSurface F s t) : F ∩ bd S = {s, t} := by
  apply Subset.antisymm
  · rintro x ⟨hxF, hxb⟩
    by_contra hne
    exact disjoint_left.mp h.2.2.2 ⟨hxF, hne⟩ hxb
  · rintro x (rfl | hx)
    · exact ⟨h.1.left_mem, h.2.1⟩
    · rw [mem_singleton_iff] at hx
      subst hx
      exact ⟨h.1.right_mem, h.2.2.1⟩

section CutInterior

variable {S Y : Type} [TopologicalSpace S] [TopologicalSpace Y]

/-- A cutting map restricts to a bijection between the interior of the cut surface and the
complement of the boundary and cut locus. -/
private theorem preimage_compl_bd_union (hS : IsSurface S) (hY : IsSurface Y)
    {F : Set S} {ψ : Y → S} (hF : IsClosed F) (hψ : IsCutMap ψ F) :
    ψ ⁻¹' (bd S ∪ F)ᶜ = (bd Y)ᶜ ∧ ψ '' (bd Y)ᶜ = (bd S ∪ F)ᶜ := by
  have : T2Space S := hS.2.1
  have : T2Space Y := hY.2.1
  have : CompactSpace Y := hY.1
  have hpre : ψ ⁻¹' (bd S ∪ F)ᶜ = (bd Y)ᶜ := by
    ext y
    simp only [mem_preimage, mem_compl_iff, mem_union, not_or]
    constructor
    · rintro ⟨hbs, hyF⟩ hyb
      exact hbs (bd_of_bd_cutMap hψ hF hyb hyF)
    · intro hyb
      have hyF : ψ y ∉ F := fun h ↦ hyb (hψ.2.2.2.2 h)
      have hint : IsInteriorPoint y := by
        by_contra hn
        exact hyb hn
      exact ⟨fun hbs ↦ hbs (isInteriorPoint_image hψ hF hint hyF), hyF⟩
  refine ⟨hpre, ?_⟩
  apply Subset.antisymm
  · rintro _ ⟨y, hy, rfl⟩
    change y ∈ ψ ⁻¹' (bd S ∪ F)ᶜ
    rwa [hpre]
  · intro x hx
    obtain ⟨y, rfl⟩ := hψ.2.1 x
    refine ⟨y, ?_, rfl⟩
    rw [← hpre]
    exact hx

/-- The interior of a cut surface is partially homeomorphic to `(bd S ∪ F)ᶜ` via `ψ`. -/
private theorem exists_oph_of_isCutMap [Nonempty Y] (hS : IsSurface S) (hY : IsSurface Y)
    {F : Set S} {ψ : Y → S} (hF : IsClosed F) (hψ : IsCutMap ψ F) :
    ∃ e : OpenPartialHomeomorph Y S, e.source = (bd Y)ᶜ ∧ e.target = (bd S ∪ F)ᶜ ∧
      EqOn e ψ (bd Y)ᶜ := by
  have : T2Space S := hS.2.1
  have : CompactSpace Y := hY.1
  obtain ⟨hpre, himg⟩ := preimage_compl_bd_union hS hY hF hψ
  have hoff : (bd Y)ᶜ ⊆ ψ ⁻¹' Fᶜ := fun y hy hyF ↦ hy (hψ.2.2.2.2 hyF)
  refine GM19.exists_oph (cuff_statement Y hY).1.isOpen_compl hψ.1.continuousOn
    (hψ.2.2.1.mono hoff) (fun u hu huo ↦ isOpen_image_of_isCutMap hψ (hu.trans hoff) huo) himg

/-- Any two cut surfaces for the same closed set `F` have homeomorphic interiors, so one is
connected if and only if the other is. -/
private theorem connectedSpace_of_isCutMap {Y₁ Y₂ : Type}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    (hS : IsSurface S) (hY₁ : IsSurface Y₁) (hY₂ : IsSurface Y₂)
    {F : Set S} {ψ₁ : Y₁ → S} {ψ₂ : Y₂ → S}
    (hF : IsClosed F) (hψ₁ : IsCutMap ψ₁ F) (hψ₂ : IsCutMap ψ₂ F)
    [ConnectedSpace Y₁] : ConnectedSpace Y₂ := by
  have : T2Space Y₁ := hY₁.2.1
  have : T2Space Y₂ := hY₂.2.1
  obtain ⟨-, himg₁⟩ := preimage_compl_bd_union hS hY₁ hF hψ₁
  obtain ⟨hpre₂, -⟩ := preimage_compl_bd_union hS hY₂ hF hψ₂
  have hconn₁ : IsConnected (bd Y₁)ᶜ := isConnected_interior hY₁
  have hconn_mid : IsConnected (bd S ∪ F)ᶜ := himg₁ ▸ hconn₁.image ψ₁ hψ₁.1.continuousOn
  obtain ⟨x₀, hx₀⟩ := hconn_mid.nonempty
  obtain ⟨y₀, rfl⟩ := hψ₂.2.1 x₀
  have : Nonempty Y₂ := ⟨y₀⟩
  obtain ⟨e₂, hs₂, ht₂, -⟩ := exists_oph_of_isCutMap hS hY₂ hF hψ₂
  have hsymm_img : e₂.symm '' (bd S ∪ F)ᶜ = (bd Y₂)ᶜ := by
    rw [← hs₂, ← ht₂]
    exact e₂.symm_image_target_eq_source
  have hconn₂ : IsConnected (bd Y₂)ᶜ :=
    hsymm_img ▸ hconn_mid.image e₂.symm (ht₂ ▸ e₂.continuousOn_symm)
  have hcl : closure (bd Y₂)ᶜ = univ := (dense_interior' hY₂).closure_eq
  exact connectedSpace_iff_univ.mpr (hcl ▸ hconn₂.closure)

/-- Any two cut surfaces for the same closed set `F` have homeomorphic cappings and the same
number of cuffs. -/
private theorem capping_homeo_of_isCutMap {Y₁ Y₂ Yhat₁ Yhat₂ : Type}
    [TopologicalSpace Y₁] [TopologicalSpace Y₂]
    [TopologicalSpace Yhat₁] [TopologicalSpace Yhat₂]
    [Nonempty Y₁] [Nonempty Y₂]
    (hS : IsSurface S) (hY₁ : IsSurface Y₁) (hY₂ : IsSurface Y₂)
    {F : Set S} {ψ₁ : Y₁ → S} {ψ₂ : Y₂ → S}
    (hF : IsClosed F) (hψ₁ : IsCutMap ψ₁ F) (hψ₂ : IsCutMap ψ₂ F)
    (cap₁ : IsCappedSurface Y₁ Yhat₁) (cap₂ : IsCappedSurface Y₂ Yhat₂) :
    Nonempty (Yhat₁ ≃ₜ Yhat₂) ∧ (cuffs Y₁).ncard = (cuffs Y₂).ncard := by
  have : T2Space Y₁ := hY₁.2.1
  have : T2Space Y₂ := hY₂.2.1
  obtain ⟨e₁, hs₁, ht₁, -⟩ := exists_oph_of_isCutMap hS hY₁ hF hψ₁
  obtain ⟨e₂, hs₂, ht₂, -⟩ := exists_oph_of_isCutMap hS hY₂ hF hψ₂
  obtain ⟨ec, P, hP, hsc, htc, hPcard⟩ := exists_cap_chart hY₂ cap₂
  let e₁₂ : OpenPartialHomeomorph Y₁ Y₂ := e₁.trans' e₂.symm (by simp [ht₁, ht₂])
  have hs₁₂ : e₁₂.source = (bd Y₁)ᶜ := hs₁
  have ht₁₂ : e₁₂.target = (bd Y₂)ᶜ := by simp [e₁₂, hs₂]
  let e : OpenPartialHomeomorph Y₁ Yhat₂ := e₁₂.trans' ec (ht₁₂.trans hsc.symm)
  obtain ⟨hhomeo, hnum⟩ :=
    capping_homeo hY₁ cap₁ cap₂.isClosedSurface hP e hs₁₂ htc
  refine ⟨hhomeo, ?_⟩
  change numCuffs Y₁ = numCuffs Y₂
  omega

end CutInterior

/-! ## Proof of (4.1) -/

/-- If two points lie in a cuff `C`, their connected components in `bd S` equal `C`. -/
private theorem connectedComponentIn_bd_eq_of_mem_cuff {S : Type*} [TopologicalSpace S]
    {C : Set S} (hC : C ∈ cuffs S) {x : S} (hx : x ∈ C) :
    connectedComponentIn (bd S) x = C := by
  obtain ⟨z, hz, rfl⟩ := hC
  exact (connectedComponentIn_eq hx).symm

/-- In `arc_one_aux`, the case `σ = false` cannot occur when the two ends of the proper line `F`
lie in the same cuff of `S`, because the arc of the cuff of `Y` between `p` and `q` projects to a
simple closed curve in `bd S` through one end of `F` that misses the other end of `F`. -/
private theorem not_sigma_false_of_same_cuff {S Y : Type}
    [TopologicalSpace S] [TopologicalSpace Y] [T2Space S] [T2Space Y] [CompactSpace Y]
    (hS : IsSurface S) {F : Set S} {ψ : Y → S} (hψ : IsCutting ψ F) (hFc : IsClosed F)
    {a' : ℝ → S} {ξ' η' : ℝ → Y} (L' : ArcLift ψ F a' ξ' η')
    (ha'ne : a' 0 ≠ a' 1) (ha'0_bd : a' 0 ∈ bd S) (ha'1_bd : a' 1 ∈ bd S)
    (hsame : connectedComponentIn (bd S) (a' 0) = connectedComponentIn (bd S) (a' 1))
    (hub' : ψ ⁻¹' F = ξ' '' Icc 0 1 ∪ η' '' Icc 0 1)
    {C : Set Y} (hCb : C ⊆ bd Y) (φ : Circle ≃ₜ C)
    {p q : ℝ} (hpq : p < q)
    (e1 : (φ (ee p)).1 = ξ' 1) (e2 : (φ (ee q)).1 = η' 1)
    (e3 : ∀ v ∈ Ioo p q, ∀ u ∈ Icc (0 : ℝ) 1, (φ (ee v)).1 ≠ ξ' u ∧ (φ (ee v)).1 ≠ η' u) :
    False := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hqp1 : q ≤ p + 1 := by
    by_contra hlt
    push Not at hlt
    have hp1 : p + 1 ∈ Ioo p q := ⟨by linarith, hlt⟩
    have hee : (φ (ee (p + 1))).1 = ξ' 1 := by rw [ee_add_one, e1]
    exact (e3 (p + 1) hp1 1 h1).1 hee
  have hv_notF : ∀ v ∈ Ioo p q, ψ (φ (ee v)).1 ∉ F := by
    intro v hv hmem
    have hm' : (φ (ee v)).1 ∈ ψ ⁻¹' F := hmem
    rw [hub'] at hm'
    rcases hm' with ⟨u, hu, hu'⟩ | ⟨u, hu, hu'⟩
    · exact (e3 v hv u hu).1 hu'.symm
    · exact (e3 v hv u hu).2 hu'.symm
  have hp_val : ψ (φ (ee p)).1 = a' 1 := by rw [e1, L'.hξ 1 h1]
  have hq_val : ψ (φ (ee q)).1 = a' 1 := by rw [e2, L'.hη 1 h1]
  let ρ : ℝ → S := fun u ↦ ψ (φ (ee (lin p q u))).1
  have hcρ : ContinuousOn ρ (Icc 0 1) := by
    refine hψ.1.comp_continuousOn (continuous_subtype_val.comp_continuousOn ?_)
    exact φ.continuous.comp_continuousOn (continuous_ee.comp_continuousOn (continuousOn_lin p q))
  have hρ0 : ρ 0 = a' 1 := by simp [ρ, lin_zero, hp_val]
  have hρ1 : ρ 1 = a' 1 := by simp [ρ, lin_one, hq_val]
  have hρ_notF : ∀ u ∈ Ioo (0 : ℝ) 1, ρ u ∉ F := fun u hu ↦
    hv_notF (lin p q u) (lin_mem hpq.le hu hpq)
  have hρ_bd : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ bd S := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with rfl | hu0
    · exact hρ0 ▸ ha'1_bd
    · rcases eq_or_lt_of_le hu.2 with rfl | hu1
      · exact hρ1 ▸ ha'1_bd
      · exact bd_of_bd_cutMap (Y := Y) (IsCutting.isCutMap hψ) hFc (hCb (φ _).2) (hρ_notF u ⟨hu0, hu1⟩)
  let CS : Set S := connectedComponentIn (bd S) (a' 1)
  have hCS_cuff : CS ∈ cuffs S := ⟨a' 1, ha'1_bd, rfl⟩
  have hρ_CS : ∀ u ∈ Icc (0 : ℝ) 1, ρ u ∈ CS := by
    have hsub := (isPreconnected_Icc.image ρ hcρ).subset_connectedComponentIn
      ⟨0, h0, hρ0⟩ (by rintro _ ⟨u, hu, rfl⟩; exact hρ_bd u hu)
    exact fun u hu ↦ hsub (mem_image_of_mem ρ hu)
  have ha'1_F : a' 1 ∈ F := L'.img ▸ ⟨1, h1, rfl⟩
  have ha'0_F : a' 0 ∈ F := L'.img ▸ ⟨0, h0, rfl⟩
  have hinj_ρ : InjOn ρ (Ico 0 1) := by
    intro u₁ hu₁ u₂ hu₂ heq
    rcases lt_trichotomy u₁ u₂ with hlt | rfl | hlt
    · exfalso
      have hu₂_oo : u₂ ∈ Ioo (0 : ℝ) 1 := ⟨ lt_of_le_of_lt hu₁.1 hlt, hu₂.2⟩
      rcases eq_or_lt_of_le hu₁.1 with rfl | hu₁_pos
      · exact hρ_notF u₂ hu₂_oo (heq ▸ hρ0 ▸ ha'1_F)
      · have hu₁_oo : u₁ ∈ Ioo (0 : ℝ) 1 := ⟨hu₁_pos, hlt.trans hu₂.2⟩
        have hψ_eq : (φ (ee (lin p q u₁))).1 = (φ (ee (lin p q u₂))).1 :=
          hψ.2.2.1 (hρ_notF u₁ hu₁_oo) (hρ_notF u₂ hu₂_oo) heq
        have hee_eq : ee (lin p q u₁) = ee (lin p q u₂) :=
          φ.injective (Subtype.ext hψ_eq)
        have hlin_lt : lin p q u₁ < lin p q u₂ := strictMonoOn_lin hpq ⟨hu₁.1, hu₁.2.le⟩ ⟨hu₂.1, hu₂.2.le⟩ hlt
        have hlin_ub : lin p q u₂ < lin p q u₁ + 1 := by
          have h_p : p < lin p q u₁ := (lin_mem hpq.le hu₁_oo hpq).1
          have h_q : lin p q u₂ < q := (lin_mem hpq.le hu₂_oo hpq).2
          linarith
        exact ee_ne hlin_lt hlin_ub hee_eq
    · rfl
    · exfalso
      have hu₁_oo : u₁ ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hu₂.1 hlt, hu₁.2⟩
      rcases eq_or_lt_of_le hu₂.1 with rfl | hu₂_pos
      · exact hρ_notF u₁ hu₁_oo (heq.symm ▸ hρ0 ▸ ha'1_F)
      · have hu₂_oo : u₂ ∈ Ioo (0 : ℝ) 1 := ⟨hu₂_pos, hlt.trans hu₁.2⟩
        have hψ_eq : (φ (ee (lin p q u₂))).1 = (φ (ee (lin p q u₁))).1 :=
          hψ.2.2.1 (hρ_notF u₂ hu₂_oo) (hρ_notF u₁ hu₁_oo) heq.symm
        have hee_eq : ee (lin p q u₂) = ee (lin p q u₁) :=
          φ.injective (Subtype.ext hψ_eq)
        have hlin_lt : lin p q u₂ < lin p q u₁ := strictMonoOn_lin hpq ⟨hu₂.1, hu₂.2.le⟩ ⟨hu₁.1, hu₁.2.le⟩ hlt
        have hlin_ub : lin p q u₁ < lin p q u₂ + 1 := by
          have h_p : p < lin p q u₂ := (lin_mem hpq.le hu₂_oo hpq).1
          have h_q : lin p q u₁ < q := (lin_mem hpq.le hu₁_oo hpq).2
          linarith
        exact ee_ne hlin_lt hlin_ub hee_eq
  obtain ⟨φS⟩ := (cuff_statement S hS).2.2 CS hCS_cuff
  have himg_CS : ρ '' Icc 0 1 = CS :=
    loop_image φS hcρ hρ_CS hinj_ρ (hρ0.trans hρ1.symm)
  have ha'0_CS : a' 0 ∈ CS := by
    rw [show CS = connectedComponentIn (bd S) (a' 0) from hsame.symm]
    exact mem_connectedComponentIn ha'0_bd
  rw [← himg_CS] at ha'0_CS
  obtain ⟨u, hu, hu_eq⟩ := ha'0_CS
  rcases eq_or_lt_of_le hu.1 with rfl | hu0
  · exact ha'ne (hu_eq.symm.trans hρ0)
  · rcases eq_or_lt_of_le hu.2 with rfl | hu1
    · exact ha'ne (hu_eq.symm.trans hρ1)
    · exact hρ_notF u ⟨hu0, hu1⟩ (hu_eq ▸ ha'0_F)

/-- **Graph Minors XXI, (4.1)** (page 11 of the preprint):
"Let $\Sigma$ be a surface, and let $\Sigma'$ be obtained by cutting along $F \subseteq \Sigma$.
1. If $F$ is a proper line with ends in different cuffs then $\hat{\Sigma}'$ is homeomorphic to
$\hat{\Sigma}$ and $c(\hat{\Sigma}') = c(\hat{\Sigma}) - 1$.
2. If $F$ is a proper line with ends in the same cuff and $\Sigma'$ is connected then
$\hat{\Sigma}'$ is simpler than $\hat{\Sigma}$.
3. If $bd(\Sigma) = \emptyset$ and $F$ is an $O$-arc and $\Sigma'$ is connected then
$\hat{\Sigma}'$ is simpler than $\Sigma$."

Note: in (1), `c(Σ)` is the number of cuffs of `Σ`, which the paper writes `c(\hat{\Sigma})` by a
typographical slip for `c(\Sigma)`. -/
theorem theorem_4_1_proof {S Shat S' Shat' : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace S'] [TopologicalSpace Shat']
    (hS : IsSurface S) [ConnectedSpace S] (hS' : IsSurface S')
    {F : Set S} {ψ : S' → S} (hcut : IsCutting ψ F)
    (cap : IsCappedSurface S Shat) (cap' : IsCappedSurface S' Shat') :
    (∀ (s t : S) (C₁ C₂ : Set S),
      C₁ ∈ cuffs S → C₂ ∈ cuffs S → C₁ ≠ C₂ →
      s ∈ C₁ → t ∈ C₂ → IsProperLineInSurface F s t →
      Nonempty (Shat' ≃ₜ Shat) ∧
        (cuffs S').ncard + 1 = (cuffs S).ncard) ∧
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      ConnectedSpace S' →
      IsSimplerThan Shat' Shat) ∧
    (bd S = ∅ → IsOArc F → ConnectedSpace S' →
      IsSimplerThan Shat' S) := by
  have : T2Space S := hS.2.1
  have : T2Space S' := hS'.2.1
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: proper line with ends in different cuffs
    intro s t C₁ C₂ hC₁ hC₂ hC_ne hs ht hL
    have hcomp_s := connectedComponentIn_bd_eq_of_mem_cuff hC₁ hs
    have hcomp_t := connectedComponentIn_bd_eq_of_mem_cuff hC₂ ht
    have hdiff : connectedComponentIn (bd S) s ≠ connectedComponentIn (bd S) t := by
      rw [hcomp_s, hcomp_t]
      exact hC_ne
    obtain ⟨Y, tY, ψ₀, hY, hcut₀, h_iarc, -, -⟩ :=
      cutIArc S F s t hS inferInstance hL.ne hL.inter_bd_eq hL.1
    obtain ⟨hY_conn, a, b, c, ⟨eS⟩, ⟨eY⟩⟩ := h_iarc hdiff
    have : T2Space Y := hY.2.1
    obtain ⟨y₀, -⟩ := hcut.2.1 s
    have : Nonempty S' := ⟨y₀⟩
    obtain ⟨Yhat, _, ⟨capY⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
    have hFc : IsClosed F := hL.1.isCompact.isClosed
    obtain ⟨⟨e_S'Y⟩, hc_S'Y⟩ :=
      capping_homeo_of_isCutMap hS hS' hY hFc (IsCutting.isCutMap hcut) (IsCutting.isCutMap hcut₀) cap' capY
    obtain ⟨e_YM⟩ := capModel a b c Yhat (capY.ofHomeo eY.symm)
    obtain ⟨e_SM⟩ := capModel a b (c + 1) Shat (cap.ofHomeo eS.symm)
    have hcY : (cuffs Y).ncard = c := by
      have h := numCuffs_eq eY
      rw [numCuffs_model] at h
      exact h
    have hcS : (cuffs S).ncard = c + 1 := by
      have h := numCuffs_eq eS
      rw [numCuffs_model] at h
      exact h
    exact ⟨⟨e_S'Y.trans (e_YM.trans e_SM.symm)⟩, by omega⟩
  · -- Part 2: proper line with ends in the same cuff and `S'` connected
    intro s t C hC hs ht hL hS'_conn
    have hsame : connectedComponentIn (bd S) s = connectedComponentIn (bd S) t := by
      rw [connectedComponentIn_bd_eq_of_mem_cuff hC hs,
        connectedComponentIn_bd_eq_of_mem_cuff hC ht]
    obtain ⟨Y, tY, t2Y, ψ₀, hY, hcut₀, X, X', hP⟩ :=
      exists_cut_arc hS hL.ne hL.inter_bd_eq hL.1
    have hFc : IsClosed F := hL.1.isCompact.isClosed
    have : ConnectedSpace Y :=
      connectedSpace_of_isCutMap hS hS' hY hFc (IsCutting.isCutMap hcut) (IsCutting.isCutMap hcut₀)
    have : CompactSpace Y := hY.1
    obtain ⟨Yhat, _, ⟨capY⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
    obtain ⟨⟨e_S'Y⟩, -⟩ :=
      capping_homeo_of_isCutMap hS hS' hY hFc (IsCutting.isCutMap hcut) (IsCutting.isCutMap hcut₀) cap' capY
    obtain ⟨a, b, c, ⟨eY⟩⟩ := classification Y hY inferInstance
    obtain ⟨e_YM⟩ := capModel a b c Yhat (capY.ofHomeo eY.symm)
    have hS'M : Nonempty (Shat' ≃ₜ SurfaceModel a b 0) := ⟨e_S'Y.trans e_YM⟩
    have hPc := hP
    obtain ⟨x0, x1, y0, y1, l1, l2, hd, hun, b1, b2, h7, h8, h9, h10⟩ := hP
    obtain ⟨a₀, ξ, η, L, ha0, ha1, himξ, himη, hiξ, hiη⟩ := exists_arcLift hPc hcut₀
    have hsb : s ∈ bd S := hL.2.1
    have htb : t ∈ bd S := hL.2.2.1
    have hub : ψ₀ ⁻¹' F = ξ '' Icc 0 1 ∪ η '' Icc 0 1 := by rw [himξ, himη, hun]
    have hXb : X ⊆ bd Y := fun z hz ↦ hcut₀.2.2.2.2 (hun ▸ Or.inl hz)
    have hXb' : X' ⊆ bd Y := fun z hz ↦ hcut₀.2.2.2.2 (hun ▸ Or.inr hz)
    have pX : IsPreconnected X := himξ ▸ isPreconnected_Icc.image _ L.cξ
    have pX' : IsPreconnected X' := himη ▸ isPreconnected_Icc.image _ L.cη
    have hex : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    have hx : ξ 0 ∈ X := himξ ▸ ⟨0, hex, rfl⟩
    have hy : η 0 ∈ X' := himη ▸ ⟨0, hex, rfl⟩
    have hξm : ∀ u ∈ Icc (0 : ℝ) 1, ξ u ∈ X := fun u hu ↦ himξ ▸ ⟨u, hu, rfl⟩
    have hηm : ∀ u ∈ Icc (0 : ℝ) 1, η u ∈ X' := fun u hu ↦ himη ▸ ⟨u, hu, rfl⟩
    have hdcuff := cuff_statement Y hY
    have hdc : ∀ {CY : Set Y}, CY ∈ cuffs Y → CY ⊆ bd Y := fun hCY ↦ by
      obtain ⟨z, -, rfl⟩ := hCY
      exact connectedComponentIn_subset _ _
    have hCY : connectedComponentIn (bd Y) (ξ 0) ∈ cuffs Y := ⟨_, hXb hx, rfl⟩
    have hCY' : connectedComponentIn (bd Y) (η 0) ∈ cuffs Y := ⟨_, hXb' hy, rfl⟩
    have hXC := pX.subset_connectedComponentIn hx hXb
    have hXC' := pX'.subset_connectedComponentIn hy hXb'
    by_cases hCC : connectedComponentIn (bd Y) (ξ 0) = connectedComponentIn (bd Y) (η 0)
    · obtain ⟨i, hi, φ, g, hg, hs_side⟩ := exists_one_hole eY hCY
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
        orient_lift L φ (fun u hu ↦ hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_facts c i
      have hξ' : ∀ u ∈ Icc (0 : ℝ) 1, ξ' u ∈ X := fun u hu ↦ by
        rw [← himξ, ← hxim]
        exact ⟨u, hu, rfl⟩
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu ↦ by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      have hub' : ψ₀ ⁻¹' F = ξ' '' Icc 0 1 ∪ η' '' Icc 0 1 := by rw [hxim, heim, hub]
      obtain ⟨σ, g', hp, -, p, q, hpq, e1, e2, e3⟩ :=
        arc_one_aux hY L' hcut₀.1 hcut₀.2.1 hCY φ hi hLf hg hs_side hmc hmm hmξ
          (fun u hu ↦ hCC ▸ hXC' (hη' u hu)) hix hie
          (fun u hu v hv he ↦ Set.disjoint_left.mp hd (hξ' u hu) (he ▸ hη' v hv))
      have hn := nf_blkB (a := a) (b := b) (c := c) hi hN hLf σ
      have hlen := length_erase_range hi
      cases σ with
      | false =>
        exfalso
        rw [ofs_false, sub_zero] at e2
        have ha'ne : a' 0 ≠ a' 1 := by
          rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3, ha0, ha1]
          · exact hL.ne
          · exact hL.ne.symm
        have ha'0_bd : a' 0 ∈ bd S := by
          rcases ha' with ⟨h2, -⟩ | ⟨h2, -⟩ <;> rw [h2]
          · exact ha0 ▸ hsb
          · exact ha1 ▸ htb
        have ha'1_bd : a' 1 ∈ bd S := by
          rcases ha' with ⟨-, h3⟩ | ⟨-, h3⟩ <;> rw [h3]
          · exact ha1 ▸ htb
          · exact ha0 ▸ hsb
        have hsame' : connectedComponentIn (bd S) (a' 0) = connectedComponentIn (bd S) (a' 1) := by
          rcases ha' with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> rw [h2, h3, ha0, ha1]
          · exact hsame
          · exact hsame.symm
        exact not_sigma_false_of_same_cuff hS hcut₀ hFc L' ha'ne ha'0_bd ha'1_bd hsame'
          hub' (hdc hCY) φ hpq e1 e2 e3
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨eS⟩ := homeo_of_nf hp h5 h6
        rw [hlen, show c - 1 + 1 = c by omega] at eS
        obtain ⟨e_SM⟩ := capModel a (b + 1) c Shat (cap.ofHomeo eS.symm)
        exact ⟨a, b, 0, a, b + 1, 0, hS'M, ⟨e_SM⟩, le_rfl, by omega, by omega⟩
    · have hdis := Surface.cuffs_disjoint hCY hCY' hCC
      obtain ⟨i, hi, j, hj, hij, φ, φ', g, hg, hs_side, hs'_side⟩ := exists_two_holes eY hCY hCY' hCC
      obtain ⟨a', ξ', η', m, L', ha', hxim, heim, hix, hie, hmc, hmm, hmξ⟩ :=
        orient_lift L φ (fun u hu ↦ hXC (hξm u hu)) hiξ hiη
      obtain ⟨hN, hLf⟩ := erase_erase_facts c i j
      have hη' : ∀ u ∈ Icc (0 : ℝ) 1, η' u ∈ X' := fun u hu ↦ by
        rw [← himη, ← heim]
        exact ⟨u, hu, rfl⟩
      obtain ⟨σ, g', hp, -⟩ :=
        arc_two_aux hY L' hcut₀.1 hcut₀.2.1 hCY hCY' (hdcuff.2.2 _ hCY).isCompact.isClosed
          (hdcuff.2.2 _ hCY').isCompact.isClosed hdis φ φ' hij hi hj hLf hg hs_side hs'_side
          hmc hmm hmξ (fun u hu ↦ hXC' (hη' u hu)) hix hie
      have hn := nf_blkA (a := a) (b := b) (c := c) hij hi hj hN hLf σ
      have hlen := length_erase_erase hij hi hj
      cases σ with
      | false =>
        obtain ⟨w, h5, h6⟩ := hn.1 rfl
        obtain ⟨eS⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at eS
        obtain ⟨e_SM⟩ := capModel (a + 1) b (c - 2 + 1) Shat (cap.ofHomeo eS.symm)
        exact ⟨a, b, 0, a + 1, b, 0, hS'M, ⟨e_SM⟩, by omega, le_rfl, by omega⟩
      | true =>
        obtain ⟨w, h5, h6⟩ := hn.2 rfl
        obtain ⟨eS⟩ := homeo_of_nf hp h5 h6
        rw [hlen] at eS
        obtain ⟨e_SM⟩ := capModel a (b + 2) (c - 2 + 1) Shat (cap.ofHomeo eS.symm)
        exact ⟨a, b, 0, a, b + 2, 0, hS'M, ⟨e_SM⟩, le_rfl, by omega, by omega⟩
  · -- Part 3: `bd S = ∅`, `F` is an O-arc, and `S'` is connected
    intro hbd hF hS'_conn
    obtain ⟨Y, tY, ψ₀, hY, hcut₀, hcase, -⟩ :=
      cutOArc S F hS inferInstance hF (by rw [hbd]; exact disjoint_empty _)
    have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
    have : ConnectedSpace Y :=
      connectedSpace_of_isCutMap hS hS' hY hFc (IsCutting.isCutMap hcut) (IsCutting.isCutMap hcut₀)
    have : T2Space Y := hY.2.1
    have hcompY : spaceComponents Y = {univ} := by
      rw [spaceComponents_eq]
      ext C
      simp only [mem_range, mem_singleton_iff]
      constructor
      · rintro ⟨x, rfl⟩
        exact PreconnectedSpace.connectedComponent_eq_univ x
      · rintro rfl
        obtain ⟨x⟩ : Nonempty Y := inferInstance
        exact ⟨x, PreconnectedSpace.connectedComponent_eq_univ x⟩
    have hsimpler : CutIsSimpler Y S := by
      rcases hcase with h | ⟨C₁, C₂, hne, hc, -⟩ | ⟨C₁, C₂, hne, hc, -⟩
      · exact h
      · exfalso
        rw [hcompY] at hc
        have h1 : C₁ = univ := by
          have : C₁ ∈ ({univ} : Set (Set Y)) := hc ▸ mem_insert _ _
          exact this
        have h2 : C₂ = univ := by
          have : C₂ ∈ ({univ} : Set (Set Y)) := hc ▸ mem_insert_of_mem _ rfl
          exact this
        exact hne (h1.trans h2.symm)
      · exfalso
        rw [hcompY] at hc
        have h1 : C₁ = univ := by
          have : C₁ ∈ ({univ} : Set (Set Y)) := hc ▸ mem_insert _ _
          exact this
        have h2 : C₂ = univ := by
          have : C₂ ∈ ({univ} : Set (Set Y)) := hc ▸ mem_insert_of_mem _ rfl
          exact this
        exact hne (h1.trans h2.symm)
    have huniv_mem : (univ : Set Y) ∈ spaceComponents Y := by rw [hcompY]; rfl
    obtain ⟨a, b, c, a', b', c', ⟨eY_univ⟩, ⟨eS⟩, ha, hb, hlt⟩ := hsimpler.2 univ huniv_mem
    have eY : Y ≃ₜ SurfaceModel a b c := (Homeomorph.Set.univ Y).symm.trans eY_univ
    have hc'0 : c' = 0 := by
      have h := numCuffs_eq eS
      rw [numCuffs_model] at h
      rw [← h, numCuffs, cuffs, hbd, componentsIn, image_empty, ncard_empty]
    subst hc'0
    obtain ⟨Yhat, _, ⟨capY⟩⟩ := exists_cappedSurface _ Y hY inferInstance rfl
    obtain ⟨⟨e_S'Y⟩, -⟩ :=
      capping_homeo_of_isCutMap hS hS' hY hFc (IsCutting.isCutMap hcut) (IsCutting.isCutMap hcut₀) cap' capY
    obtain ⟨e_YM⟩ := capModel a b c Yhat (capY.ofHomeo eY.symm)
    exact ⟨a, b, 0, a', b', 0, ⟨e_S'Y.trans e_YM⟩, ⟨eS⟩, ha, hb, by omega⟩

/-! ## Proof of (4.2) -/

/-- No closed disc can be contained in a line or an `O`-arc. -/
private theorem not_isClosedDisc_subset_line_or_oArc {S : Type*} [TopologicalSpace S] [T2Space S]
    {F E : Set S} (hE : IsClosedDisc E) (hsub : E ⊆ F)
    (hF : (∃ s t, IsLineWithEnds F s t) ∨ IsOArc F) : False := by
  have hbd_oArc : IsOArc (discBd E) := hE.isOArc_discBd
  have hbd_sub : discBd E ⊆ F := (Surface.discBd_subset E).trans hsub
  rcases hF with ⟨s, t, hL⟩ | hO
  · obtain ⟨f, -, -⟩ := hL
    exact not_isOArc_of_subset_line ⟨f⟩ hbd_oArc hbd_sub
  · have heq : discBd E = F := eq_of_oArc_subset hbd_oArc hO hbd_sub
    obtain ⟨z, hzE, hzb⟩ := hE.nonempty_discInt
    exact hzb (heq ▸ hsub hzE)

/-- When `S₁, S₂ ⊆ S` are surfaces with `S₁ ∩ S₂ = F` and `F` contains no closed disc, the
intersection `F` lies in the boundary of both `S₁` and `S₂`. -/
private theorem preimage_inter_subset_bd {S : Type} [TopologicalSpace S]
    (hS : IsSurface S) {S₁ S₂ F : Set S} (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂)
    (hint : S₁ ∩ S₂ = F) (hno_disc : ∀ E : Set S, IsClosedDisc E → ¬ E ⊆ F) :
    Subtype.val ⁻¹' F ⊆ bd S₁ := by
  have : T2Space S := hS.2.1
  have : T2Space S₁ := hS₁.2.1
  have : T2Space S₂ := hS₂.2.1
  intro x hxF
  by_contra hnb
  have hxi : IsInteriorPoint x := by
    by_contra hn
    exact hnb hn
  obtain ⟨D₁, hD₁, hxD₁, -⟩ := GM07.exists_disc_in_open hxi isOpen_univ (mem_univ x)
  obtain ⟨hD, hD_bd⟩ := isClosedDisc_image hD₁ IsEmbedding.subtypeVal
  set D : Set S := Subtype.val '' D₁
  have hxD : x.1 ∈ discInt D := by
    refine ⟨mem_image_of_mem Subtype.val hxD₁.1, ?_⟩
    rw [hD_bd]
    rintro ⟨y, hy, hxy⟩
    exact hxD₁.2 (Subtype.ext hxy ▸ hy)
  have hDo : IsOpen (discInt D) := hD.isOpen_discInt hS.2.2
  have hx₂ : x.1 ∈ S₂ := (hint ▸ hxF).2
  let x₂ : S₂ := ⟨x.1, hx₂⟩
  have hUo : IsOpen (Subtype.val ⁻¹' discInt D : Set S₂) := hDo.preimage continuous_subtype_val
  obtain ⟨y₂, hy₂D, hy₂b⟩ :=
    (dense_interior' hS₂).inter_open_nonempty _ hUo ⟨x₂, hxD⟩
  have hy₂i : IsInteriorPoint y₂ := by
    by_contra hn
    exact hy₂b hn
  obtain ⟨E₂, hE₂, -, hE₂_sub⟩ := GM07.exists_disc_in_open hy₂i hUo hy₂D
  obtain ⟨hE, -⟩ := isClosedDisc_image hE₂ IsEmbedding.subtypeVal
  refine hno_disc (Subtype.val '' E₂) hE ?_
  rintro _ ⟨z, hz, rfl⟩
  rw [← hint]
  have hzD : z.1 ∈ discInt D := hE₂_sub hz
  obtain ⟨w, -, hwz⟩ := hzD.1
  exact ⟨hwz ▸ w.2, z.2⟩

/-- The disjoint union `S₁ ⊕ S₂` of two subsurfaces `S₁, S₂ ⊆ S` meeting along `F` is a cutting of
`S` along `F`. -/
private theorem isCutting_sum_of_subsurfaces {S : Type} [TopologicalSpace S]
    {S₁ S₂ F : Set S} (hS₁ : IsSurface S₁) (hS₂ : IsSurface S₂)
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (hb₁ : Subtype.val ⁻¹' F ⊆ bd S₁) (hb₂ : Subtype.val ⁻¹' F ⊆ bd S₂) :
    IsSurface (S₁ ⊕ S₂) ∧
      IsCutting (Sum.elim (Subtype.val : S₁ → S) (Subtype.val : S₂ → S)) F := by
  have : CompactSpace S₁ := hS₁.1
  have : CompactSpace S₂ := hS₂.1
  have : T2Space S₁ := hS₁.2.1
  have : T2Space S₂ := hS₂.2.1
  let ψ : S₁ ⊕ S₂ → S := Sum.elim Subtype.val Subtype.val
  have hY : IsSurface (S₁ ⊕ S₂) := ⟨inferInstance, inferInstance, fun x ↦ by
    rcases x with x | x
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inl (hS₁.2.2 x)
    · exact isManifoldPoint_of_isOpenEmbedding IsOpenEmbedding.inr (hS₂.2.2 x)⟩
  refine ⟨hY, continuous_subtype_val.sumElim continuous_subtype_val, ?_, ?_, ?_, ?_⟩
  · intro x
    rcases (hun ▸ mem_univ x : x ∈ S₁ ∪ S₂) with hx | hx
    · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
    · exact ⟨Sum.inr ⟨x, hx⟩, rfl⟩
  · intro a ha b hb hab
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (Subtype.ext hab)
    · exfalso
      have hab' : a.1 = b.1 := hab
      have : a.1 ∈ F := by rw [← hint]; exact ⟨a.2, hab' ▸ b.2⟩
      exact ha this
    · exfalso
      have hab' : a.1 = b.1 := hab
      have : b.1 ∈ F := by rw [← hint]; exact ⟨b.2, hab' ▸ a.2⟩
      exact hb this
    · exact congrArg Sum.inr (Subtype.ext hab)
  · intro x hx
    obtain ⟨hx₁, hx₂⟩ : x ∈ S₁ ∧ x ∈ S₂ := by rwa [← mem_inter_iff, hint]
    have hfib : ψ ⁻¹' {x} = {Sum.inl ⟨x, hx₁⟩, Sum.inr ⟨x, hx₂⟩} := by
      ext y
      rcases y with y | y <;> simp [ψ, Subtype.ext_iff]
    rw [hfib, ncard_pair (by simp)]
  · rintro (x | x) hx
    · exact bd_of_isOpenEmbedding IsOpenEmbedding.inl (hb₁ hx)
    · exact bd_of_isOpenEmbedding IsOpenEmbedding.inr (hb₂ hx)

/-- **Graph Minors XXI, (4.2)** (page 11 of the preprint):
"Let $\Sigma$ be a surface, and let $\Sigma_1, \Sigma_2 \subseteq \Sigma$ be surfaces with
$\Sigma_1 \cup \Sigma_2 = \Sigma$ and $\Sigma_1 \cap \Sigma_2 = F$.
1. If $F$ is a proper line in $\Sigma$ with both ends in the same cuff, then either $\hat{\Sigma}_2$
is simpler than $\hat{\Sigma}$ or $\hat{\Sigma}_1$ is a sphere.
2. If $F$ is a proper line in $\Sigma$ with both ends in the same cuff, and $\hat{\Sigma}_1$ is a
sphere, then $\hat{\Sigma}_2$ is homeomorphic to $\hat{\Sigma}$; and either $c(\Sigma_2) < c(\Sigma)$,
or $c(\Sigma_2) = c(\Sigma)$ and there is a closed disc $\Delta \subseteq \Sigma$ with
$F \subseteq bd(\Delta) \subseteq F \cup bd(\Sigma)$.
3. If $bd(\Sigma) = \emptyset$ and $F$ is an $O$-arc in $\Sigma$, then either $\hat{\Sigma}_2$ is
simpler than $\hat{\Sigma}$ or $\Sigma_1$ is a closed disc." -/
theorem theorem_4_2_proof {S Shat Shat₁ Shat₂ : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace Shat₁] [TopologicalSpace Shat₂]
    (hS : IsSurface S) [ConnectedSpace S]
    {S₁ S₂ F : Set S}
    (hS₁ : IsSurface S₁) [ConnectedSpace S₁]
    (hS₂ : IsSurface S₂) [ConnectedSpace S₂]
    (hun : S₁ ∪ S₂ = univ) (hint : S₁ ∩ S₂ = F)
    (cap : IsCappedSurface S Shat)
    (cap₁ : IsCappedSurface S₁ Shat₁)
    (cap₂ : IsCappedSurface S₂ Shat₂) :
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      IsSimplerThan Shat₂ Shat ∨ IsSphere Shat₁) ∧
    (∀ (s t : S) (C : Set S),
      C ∈ cuffs S → s ∈ C → t ∈ C → IsProperLineInSurface F s t →
      IsSphere Shat₁ →
      Nonempty (Shat₂ ≃ₜ Shat) ∧
        ((cuffs S₂).ncard < (cuffs S).ncard ∨
          ((cuffs S₂).ncard = (cuffs S).ncard ∧
            ∃ Δ : Set S, IsClosedDisc Δ ∧ F ⊆ discBd Δ ∧ discBd Δ ⊆ F ∪ bd S))) ∧
    (bd S = ∅ → IsOArc F →
      IsSimplerThan Shat₂ Shat ∨ IsClosedDisc S₁) := by
  have : T2Space S := hS.2.1
  have : T2Space S₁ := hS₁.2.1
  have : T2Space S₂ := hS₂.2.1
  obtain ⟨a₁, b₁, c₁, ⟨e₁⟩⟩ := classification S₁ hS₁ inferInstance
  obtain ⟨a₂, b₂, c₂, ⟨e₂⟩⟩ := classification S₂ hS₂ inferInstance
  obtain ⟨e_hat₁⟩ := capModel a₁ b₁ c₁ Shat₁ (cap₁.ofHomeo e₁.symm)
  obtain ⟨e_hat₂⟩ := capModel a₂ b₂ c₂ Shat₂ (cap₂.ofHomeo e₂.symm)
  have h_line_model :
      ∀ {s t : S}, IsProperLineInSurface F s t →
        0 < c₁ ∧ 0 < c₂ ∧
          Nonempty (S ≃ₜ SurfaceModel (a₂ + a₁) (b₂ + b₁) ((c₂ - 1) + (c₁ - 1) + 1)) ∧
          Subtype.val ⁻¹' F ⊆ bd S₁ ∧ discBd S₁ ⊆ F ∪ bd S := by
    intro s t hL
    have hno_disc : ∀ E : Set S, IsClosedDisc E → ¬ E ⊆ F := fun E hE hEF ↦
      not_isClosedDisc_subset_line_or_oArc hE hEF (Or.inl ⟨s, t, hL.1⟩)
    have hb₁ : Subtype.val ⁻¹' F ⊆ bd S₁ :=
      preimage_inter_subset_bd hS hS₁ hS₂ hint hno_disc
    have hb₂ : Subtype.val ⁻¹' F ⊆ bd S₂ :=
      preimage_inter_subset_bd hS hS₂ hS₁ (by rw [inter_comm, hint]) hno_disc
    obtain ⟨hY, hcut⟩ := isCutting_sum_of_subsurfaces hS₁ hS₂ hun hint hb₁ hb₂
    let ψ : S₁ ⊕ S₂ → S := Sum.elim Subtype.val Subtype.val
    obtain ⟨b, hb_arc, hbr, hb0, hb1⟩ := hL.1.exists_arc
    let a₀ : ℝ → S := extI b
    have ha₀_mem : ∀ u : ℝ, a₀ u ∈ F := fun u ↦ by
      rw [← hbr]
      exact mem_range_self _
    have ha₀_S₁ : ∀ u : ℝ, a₀ u ∈ S₁ := fun u ↦ (hint ▸ ha₀_mem u).1
    have ha₀_S₂ : ∀ u : ℝ, a₀ u ∈ S₂ := fun u ↦ (hint ▸ ha₀_mem u).2
    let ξ : ℝ → S₁ ⊕ S₂ := fun u ↦ Sum.inl ⟨a₀ u, ha₀_S₁ u⟩
    let η : ℝ → S₁ ⊕ S₂ := fun u ↦ Sum.inr ⟨a₀ u, ha₀_S₂ u⟩
    have ha₀_cont : Continuous a₀ := continuous_extI hb_arc.1
    have hcξ : ContinuousOn ξ (Icc 0 1) :=
      (continuous_inl.comp (ha₀_cont.subtype_mk ha₀_S₁)).continuousOn
    have hcη : ContinuousOn η (Icc 0 1) :=
      (continuous_inr.comp (ha₀_cont.subtype_mk ha₀_S₂)).continuousOn
    have ha₀_img : a₀ '' Icc 0 1 = F := by rw [image_extI, hbr]
    have hinj_a₀ : InjOn a₀ (Icc 0 1) := extI_injOn hb_arc.2
    have hiξ : InjOn ξ (Icc 0 1) := fun u hu v hv he ↦
      hinj_a₀ hu hv (congrArg Subtype.val (Sum.inl.inj he))
    have hiη : InjOn η (Icc 0 1) := fun u hu v hv he ↦
      hinj_a₀ hu hv (congrArg Subtype.val (Sum.inr.inj he))
    have hL₀ : ArcLift ψ F a₀ ξ η := by
      refine ⟨hcξ, hcη, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ha₀_img, ?_⟩
      intro y y' he hne
      rcases y with y | y <;> rcases y' with y' | y'
      · exact absurd (congrArg Sum.inl (Subtype.ext he)) hne
      · have he' : y.1 = y'.1 := he
        have hyF : y.1 ∈ F := by rw [← hint]; exact ⟨y.2, he' ▸ y'.2⟩
        rw [← ha₀_img] at hyF
        obtain ⟨u, hu, hu_eq⟩ := hyF
        refine ⟨u, hu, Or.inl ⟨?_, ?_⟩⟩
        · exact congrArg Sum.inl (Subtype.ext hu_eq.symm)
        · exact congrArg Sum.inr (Subtype.ext (he'.symm.trans hu_eq.symm))
      · have he' : y.1 = y'.1 := he
        have hyF : y'.1 ∈ F := by rw [← hint]; exact ⟨y'.2, he' ▸ y.2⟩
        rw [← ha₀_img] at hyF
        obtain ⟨u, hu, hu_eq⟩ := hyF
        refine ⟨u, hu, Or.inr ⟨?_, ?_⟩⟩
        · exact congrArg Sum.inl (Subtype.ext hu_eq.symm)
        · exact congrArg Sum.inr (Subtype.ext (he'.trans hu_eq.symm))
      · exact absurd (congrArg Sum.inr (Subtype.ext he)) hne
    let W₁ : Set (S₁ ⊕ S₂) := range Sum.inl
    let W₂ : Set (S₁ ⊕ S₂) := range Sum.inr
    have hW₁ : IsClopen W₁ := ⟨isClosed_range_inl, isOpen_range_inl⟩
    have hW₂ : IsClopen W₂ := ⟨isClosed_range_inr, isOpen_range_inr⟩
    have hdW : Disjoint W₁ W₂ := isCompl_range_inl_range_inr.disjoint
    have hUW : W₁ ∪ W₂ = univ := isCompl_range_inl_range_inr.sup_eq_top
    let eW₁ : W₁ ≃ₜ SurfaceModel a₁ b₁ c₁ :=
      (IsOpenEmbedding.inl.isEmbedding.toHomeomorph).symm.trans e₁
    let eW₂ : W₂ ≃ₜ SurfaceModel a₂ b₂ c₂ :=
      (IsOpenEmbedding.inr.isEmbedding.toHomeomorph).symm.trans e₂
    have hξW₁ : ξ '' Icc 0 1 ⊆ W₁ := by rintro _ ⟨u, -, rfl⟩; exact mem_range_self _
    have hηW₂ : η '' Icc 0 1 ⊆ W₂ := by rintro _ ⟨u, -, rfl⟩; exact mem_range_self _
    have hξbd : ξ '' Icc 0 1 ⊆ bd (S₁ ⊕ S₂) := by
      rintro _ ⟨u, -, rfl⟩
      exact bd_of_isOpenEmbedding IsOpenEmbedding.inl (hb₁ (ha₀_mem u))
    have hηbd : η '' Icc 0 1 ⊆ bd (S₁ ⊕ S₂) := by
      rintro _ ⟨u, -, rfl⟩
      exact bd_of_isOpenEmbedding IsOpenEmbedding.inr (hb₂ (ha₀_mem u))
    have : T2Space (S₁ ⊕ S₂) := hY.2.1
    obtain ⟨i, j, σ, a', f, hi, hj, -, -, hf, -⟩ :=
      arc_comps_aux hY hL₀ hcut.1 hcut.2.1 hW₁ hW₂ hdW hUW eW₁ eW₂
        hξW₁ hηW₂ hξbd hηbd hiξ hiη
    obtain ⟨hN₁, hL₁⟩ := erase_facts c₁ i
    obtain ⟨hN₂, hL₂⟩ := erase_facts c₂ j
    obtain ⟨eS⟩ := homeo_of_two_arc hi hj hN₁ hN₂ hL₁ hL₂ hf
    rw [length_erase_range hi, length_erase_range hj] at eS
    have hFc : IsClosed F := hL.1.isCompact.isClosed
    have : CompactSpace (S₁ ⊕ S₂) := hY.1
    have hbd_S₁ : discBd S₁ ⊆ F ∪ bd S := by
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxF : x.1 ∈ F
      · exact Or.inl hxF
      · have h_inl : Sum.inl x ∈ bd (S₁ ⊕ S₂) :=
          bd_of_isOpenEmbedding IsOpenEmbedding.inl hx
        exact Or.inr (bd_of_bd_cutMap (IsCutting.isCutMap hcut) hFc h_inl hxF)
    exact ⟨by omega, by omega, ⟨eS⟩, hb₁, hbd_S₁⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    intro s t C _ _ _ hL
    obtain ⟨-, -, ⟨eS⟩, -, -⟩ := h_line_model hL
    obtain ⟨e_hat⟩ := capModel (a₂ + a₁) (b₂ + b₁) ((c₂ - 1) + (c₁ - 1) + 1) Shat
      (cap.ofHomeo eS.symm)
    by_cases hab₁ : a₁ = 0 ∧ b₁ = 0
    · obtain ⟨rfl, rfl⟩ := hab₁
      obtain ⟨g⟩ := Surface.isSphere_model
      exact Or.inr ⟨e_hat₁.trans g⟩
    · refine Or.inl ⟨a₂, b₂, 0, a₂ + a₁, b₂ + b₁, 0, ⟨e_hat₂⟩, ⟨e_hat⟩, by omega, by omega, ?_⟩
      omega
  · -- Part 2
    intro s t C _ _ _ hL hsph₁
    obtain ⟨hc₁_pos, hc₂_pos, ⟨eS⟩, hb₁, hbd_S₁⟩ := h_line_model hL
    obtain ⟨e_hat⟩ := capModel (a₂ + a₁) (b₂ + b₁) ((c₂ - 1) + (c₁ - 1) + 1) Shat
      (cap.ofHomeo eS.symm)
    obtain ⟨e_sph⟩ := nonempty_homeomorph_of_isSphere hsph₁
    obtain ⟨-, h_genus, -⟩ := (modelCriterion.2 a₁ b₁ 0 0 0 0).mp ⟨e_hat₁.symm.trans e_sph⟩
    have ha₁ : a₁ = 0 := by omega
    have hb₁_zero : b₁ = 0 := by omega
    subst ha₁ hb₁_zero
    rw [Nat.add_zero, Nat.add_zero] at e_hat eS
    have hcS₂ : (cuffs S₂).ncard = c₂ := by
      have h := numCuffs_eq e₂
      rw [numCuffs_model] at h
      exact h
    have hcS : (cuffs S).ncard = (c₂ - 1) + (c₁ - 1) + 1 := by
      have h := numCuffs_eq eS
      rw [numCuffs_model] at h
      exact h
    refine ⟨⟨e_hat₂.trans e_hat.symm⟩, ?_⟩
    rcases lt_or_eq_of_le (show 1 ≤ c₁ by omega) with hc₁_gt | rfl
    · exact Or.inl (by omega)
    · refine Or.inr ⟨by omega, S₁, ?_, ?_, hbd_S₁⟩
      · obtain ⟨d⟩ := nonempty_disc_homeo
        have e_univ : ClosedUnitDisc ≃ₜ (univ : Set S₁) :=
          d.symm.trans (e₁.symm.trans (Homeomorph.Set.univ S₁).symm)
        obtain ⟨hD, -⟩ := isClosedDisc_image ⟨e_univ⟩ IsEmbedding.subtypeVal
        simpa using hD
      · intro x hx
        have hx₁ : x ∈ S₁ := (hint ▸ hx).1
        exact ⟨⟨x, hx₁⟩, hb₁ hx, rfl⟩
  · -- Part 3: `bd S = ∅` and `F` is an O-arc
    intro hbd hF
    have hno_disc : ∀ E : Set S, IsClosedDisc E → ¬ E ⊆ F := fun E hE hEF ↦
      not_isClosedDisc_subset_line_or_oArc hE hEF (Or.inr hF)
    have hb₁ : Subtype.val ⁻¹' F ⊆ bd S₁ :=
      preimage_inter_subset_bd hS hS₁ hS₂ hint hno_disc
    have hb₂ : Subtype.val ⁻¹' F ⊆ bd S₂ :=
      preimage_inter_subset_bd hS hS₂ hS₁ (by rw [inter_comm, hint]) hno_disc
    obtain ⟨hY, hcut⟩ := isCutting_sum_of_subsurfaces hS₁ hS₂ hun hint hb₁ hb₂
    have hFc : IsClosed F := (isCompact_of_isOArc hF).isClosed
    have : CompactSpace (S₁ ⊕ S₂) := hY.1
    have hbd₁_eq : bd S₁ = Subtype.val ⁻¹' F := by
      apply Subset.antisymm _ hb₁
      intro x hx
      by_contra hxF
      have h_inl : Sum.inl x ∈ bd (S₁ ⊕ S₂) :=
        bd_of_isOpenEmbedding IsOpenEmbedding.inl hx
      have h_in_bd : x.1 ∈ bd S := bd_of_bd_cutMap (IsCutting.isCutMap hcut) hFc h_inl hxF
      rw [hbd] at h_in_bd
      exact h_in_bd
    have hF_sub₁ : F ⊆ S₁ := hint ▸ inter_subset_left
    have himg_bd₁ : Subtype.val '' bd S₁ = F := by
      rw [hbd₁_eq, Subtype.image_preimage_coe, inter_eq_right.mpr hF_sub₁]
    have hO_bd₁ : IsOArc (bd S₁) := by
      obtain ⟨φ⟩ := hF
      let e_sub : (bd S₁ : Set S₁) ≃ₜ F :=
        (IsEmbedding.subtypeVal.homeomorphImage (bd S₁)).trans (Homeomorph.setCongr himg_bd₁)
      exact ⟨φ.trans e_sub.symm⟩
    have hC₁ : IsCuff (bd S₁) := isCuff_of_oArc hO_bd₁
    have hS₁_closed : IsClosed S₁ := (isCompact_iff_compactSpace.mpr hS₁.1).isClosed
    have hι : IsClosedEmbedding (Subtype.val : S₁ → S) := hS₁_closed.isClosedEmbedding_subtypeVal
    have hu_glue : range (Subtype.val : S₁ → S) ∪ S₂ = univ := by
      rwa [Subtype.range_coe]
    have hm_glue : range (Subtype.val : S₁ → S) ∩ S₂ = Subtype.val '' bd S₁ := by
      rw [Subtype.range_coe, hint, himg_bd₁]
    have hOF_glue : IsOArc (Subtype.val '' bd S₁) := himg_bd₁ ▸ hF
    have hBb_glue : Subtype.val ⁻¹' (Subtype.val '' bd S₁) ⊆ bd S₂ := by
      rwa [himg_bd₁]
    obtain ⟨hc₁_pos, hc₂_pos, ⟨eS⟩⟩ :=
      glue_model hS₁ hC₁ hS₂ hS.2.1 hι hu_glue hm_glue hOF_glue hBb_glue e₁ e₂
    have hc_sum : c₂ - 1 + (c₁ - 1) = 0 := by
      have h := numCuffs_eq eS
      rw [numCuffs_model] at h
      rw [← h, numCuffs, cuffs, hbd, componentsIn, image_empty, ncard_empty]
    have hc₁_eq : c₁ = 1 := by omega
    have hc₂_eq : c₂ = 1 := by omega
    subst hc₁_eq hc₂_eq
    obtain ⟨e_hat⟩ := capModel (a₂ + a₁) (b₂ + b₁) 0 Shat (cap.ofHomeo eS.symm)
    by_cases hab₁ : a₁ = 0 ∧ b₁ = 0
    · obtain ⟨rfl, rfl⟩ := hab₁
      obtain ⟨d⟩ := nonempty_disc_homeo
      have e_univ : ClosedUnitDisc ≃ₜ (univ : Set S₁) :=
        d.symm.trans (e₁.symm.trans (Homeomorph.Set.univ S₁).symm)
      obtain ⟨hD, -⟩ := isClosedDisc_image ⟨e_univ⟩ IsEmbedding.subtypeVal
      exact Or.inr (by simpa using hD)
    · refine Or.inl ⟨a₂, b₂, 0, a₂ + a₁, b₂ + b₁, 0, ⟨e_hat₂⟩, ⟨e_hat⟩, by omega, by omega, ?_⟩
      omega

/-! ## Proof of (4.3) and (4.4) -/

/-- A closed disc is preconnected. -/
private theorem isPreconnected_of_isClosedDisc {S : Type*} [TopologicalSpace S] {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : IsPreconnected Δ :=
  (IsClosedDisc.isPathConnected hΔ).isConnected.isPreconnected

/-- **Graph Minors XXI, (4.3)** (page 12 of the preprint):
"If $bd(\Sigma) = \emptyset$, a drawing $\Gamma$ in $\Sigma$ is 2-cell if and only if
$V(\Gamma) \ne \emptyset$, $\Gamma$ is connected, and for every $O$-arc $F \subseteq \Sigma$ with
$F \cap U(\Gamma) = \emptyset$, there is a closed disc $\Delta \subseteq \Sigma$ with
$bd(\Delta) = F$." -/
theorem theorem_4_3_proof {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) (Γ : Surface.Drawing S) :
    Γ.IsTwoCell ↔
      (Γ.V.Nonempty ∧ IsPreconnected Γ.U ∧
       ∀ F : Set S, IsOArc F → Disjoint F Γ.U →
         ∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x ↦ by
    by_contra hx
    have : x ∈ bd S := hx
    rw [hbd] at this
    exact this⟩
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hcl
  constructor
  · intro htwo
    have hVne : Γ.V.Nonempty := by
      by_contra hV_empty
      rw [not_nonempty_iff_eq_empty] at hV_empty
      have hU_empty : Γ.U = ∅ := by
        by_contra hU_ne
        obtain ⟨x, hxU⟩ := nonempty_iff_ne_empty.mpr hU_ne
        have hxdiff : x ∈ Γ.U \ Γ.V := ⟨hxU, by simp [hV_empty]⟩
        obtain ⟨e, he, -⟩ : ∃ e ∈ Γ.E, x ∈ e :=
          ⟨_, GM20.mem_arcComponentsIn_pathComponentIn hxdiff, mem_pathComponentIn_self hxdiff⟩
        rcases Γ.edge_cond e he with ⟨u, v, -, huV, -⟩ | ⟨u, huV, -⟩
        · have : u ∈ Γ.V := (huV ▸ mem_insert u _).2
          simp [hV_empty] at this
        · have : u ∈ Γ.V := (huV ▸ mem_singleton u).2
          simp [hV_empty] at this
      have huniv_R : (univ : Set S) ∈ Γ.R := by
        obtain ⟨x₀⟩ : Nonempty S := inferInstance
        refine ⟨x₀, by simp [hU_empty], ?_⟩
        rw [hU_empty, sdiff_empty, connectedComponentIn_univ,
          PreconnectedSpace.connectedComponent_eq_univ]
      exact not_isOpenDisc_univ (htwo.2 univ huniv_R)
    have hU_conn : IsPreconnected Γ.U := by
      apply isPreconnected_closed_iff.mpr
      intro C₁ C₂ hc₁ hc₂ hcover hne₁ hne₂
      by_contra hn
      have hdis : Disjoint (Γ.U ∩ C₁) (Γ.U ∩ C₂) :=
        disjoint_left.mpr fun x hx hy ↦ hn ⟨x, hx.1, hx.2, hy.2⟩
      have heq : (Γ.U ∩ C₁) ∪ (Γ.U ∩ C₂) = Γ.U := by
        apply Subset.antisymm (union_subset inter_subset_left inter_subset_left)
        intro x hx
        exact (hcover hx).elim (fun h ↦ Or.inl ⟨hx, h⟩) (fun h ↦ Or.inr ⟨hx, h⟩)
      have hempty := eq_empty_of_split hcl htwo.2 (Γ.isClosed_U.inter hc₁)
        (Γ.isClosed_U.inter hc₂) hdis heq hne₁
      exact hne₂.ne_empty hempty
    refine ⟨hVne, hU_conn, ?_⟩
    intro F hF hdis
    obtain ⟨φ⟩ := id hF
    have hxF : (φ 1).1 ∈ F := (φ 1).2
    have hxU : (φ 1).1 ∉ Γ.U := disjoint_left.mp hdis hxF
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxU
    have hFr : F ⊆ r := subset_region hr hF.isConnected'.isPreconnected hdis hxF hxr
    obtain ⟨Δ, -, hΔ, hbΔ⟩ := exists_disc_in_openDisc (htwo.2 r hr) hF hFr
    exact ⟨Δ, hΔ, hbΔ⟩
  · rintro ⟨⟨v₀, hv₀⟩, hU_conn, hF_disc⟩
    refine ⟨inferInstance, fun r hr ↦ ?_⟩
    have hr_conn : IsConnected r := ⟨region_nonempty hr, region_isPreconnected hr⟩
    have hr_open : IsOpen r := region_isOpen hr
    have hv₀_not_r : v₀ ∉ r := fun hvr ↦ region_subset hr hvr (Γ.V_subset_U hv₀)
    have h_open_disc := open_disc S r hcl inferInstance hr_conn hr_open
    suffices h_bound : ∀ F : Set S, F ⊆ r → IsOArc F →
        ∃ Δ : Set S, Δ ⊆ r ∧ IsClosedDisc Δ ∧ discBd Δ = F by
      rcases h_open_disc h_bound with ⟨-, rfl⟩ | h_disc
      · exact (hv₀_not_r (mem_univ v₀)).elim
      · exact h_disc
    intro F hFr hF
    by_contra hno
    have hdis_FU : Disjoint F Γ.U :=
      disjoint_left.mpr fun x hxF hxU ↦ region_subset hr (hFr hxF) hxU
    obtain ⟨Δ, hΔ, hbΔ⟩ := hF_disc F hF hdis_FU
    obtain ⟨φ⟩ := id hF
    have hzF : (φ 1).1 ∈ F := (φ 1).2
    have hzΔ : (φ 1).1 ∈ Δ := Surface.discBd_subset Δ (hbΔ ▸ hzF)
    have hzr : (φ 1).1 ∈ r := hFr hzF
    have hΔU_ne : (Δ ∩ Γ.U).Nonempty := by
      by_contra hdis_ΔU
      rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at hdis_ΔU
      have hΔr : Δ ⊆ r :=
        subset_region hr (isPreconnected_of_isClosedDisc hΔ) hdis_ΔU hzΔ hzr
      exact hno ⟨Δ, hΔr, hΔ, hbΔ⟩
    obtain ⟨x₀, hx₀Δ, hx₀U⟩ := hΔU_ne
    have hdis_U_bd : Disjoint Γ.U (discBd Δ) := by
      rw [hbΔ]
      exact hdis_FU.symm
    have hU_sub_Δ : Γ.U ⊆ Δ := fun y hyU ↦
      side_const hcl hΔ hU_conn hdis_U_bd hx₀U hyU hx₀Δ
    have hU_sub_int : Γ.U ⊆ discInt Δ := fun y hyU ↦
      ⟨hU_sub_Δ hyU, disjoint_left.mp hdis_U_bd hyU⟩
    by_cases hsph : IsSphere S
    · obtain ⟨Δ₁, Δ₂, hne12, hΔ₁, hΔ₂, hb₁, hb₂, -, hcap, -, huniq⟩ :=
        sphere_disc S hsph F hF
      rcases huniq Δ hΔ hbΔ with rfl | rfl
      · have hdis_Δ₂U : Disjoint Δ₂ Γ.U := by
          refine disjoint_left.mpr fun y hy₂ hyU ↦ ?_
          have hyF : y ∈ F := hcap ▸ ⟨hU_sub_Δ hyU, hy₂⟩
          exact disjoint_left.mp hdis_FU hyF hyU
        have hΔ₂r : Δ₂ ⊆ r :=
          subset_region hr (isPreconnected_of_isClosedDisc hΔ₂) hdis_Δ₂U
            (Surface.discBd_subset Δ₂ (hb₂ ▸ hzF)) hzr
        exact hno ⟨Δ₂, hΔ₂r, hΔ₂, hb₂⟩
      · have hdis_Δ₁U : Disjoint Δ₁ Γ.U := by
          refine disjoint_left.mpr fun y hy₁ hyU ↦ ?_
          have hyF : y ∈ F := hcap ▸ ⟨hy₁, hU_sub_Δ hyU⟩
          exact disjoint_left.mp hdis_FU hyF hyU
        have hΔ₁r : Δ₁ ⊆ r :=
          subset_region hr (isPreconnected_of_isClosedDisc hΔ₁) hdis_Δ₁U
            (Surface.discBd_subset Δ₁ (hb₁ ▸ hzF)) hzr
        exact hno ⟨Δ₁, hΔ₁r, hΔ₁, hb₁⟩
    · obtain ⟨F₀, hF₀, hnn₀⟩ := exists_not_nullHomotopic hS hbd hsph
      obtain ⟨F', hF', hnn', hdis_F'_int⟩ := exists_curve_off_disc hcl hΔ hF₀ hnn₀
      have hdis_F'U : Disjoint F' Γ.U := hdis_F'_int.mono_right hU_sub_int
      obtain ⟨D, hD, hbD⟩ := hF_disc F' hF' hdis_F'U
      have hnull' : IsNullHomotopicOArc F' :=
        (epstein S univ F' hS inferInstance hF' (subset_univ _)
          (by rw [hbd]; exact disjoint_empty _)).2.1
          ⟨D, subset_univ _, hD, hbD ▸ Surface.discBd_subset D⟩
      exact hnn' hnull'

/-- **Graph Minors XXI, (4.4)** (page 12 of the preprint):
"If $bd(\Sigma) = \emptyset$, an $O$-arc $F \subseteq \Sigma$ bounds a closed disc in $\Sigma$ if
and only if $F$ is null-homotopic in $\Sigma$." -/
theorem theorem_4_4_proof {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) {F : Set S} (hF : IsOArc F) :
    (∃ Δ : Set S, IsClosedDisc Δ ∧ discBd Δ = F) ↔ IsNullHomotopicOArc F := by
  have hep := epstein S univ F hS inferInstance hF (subset_univ F)
    (by rw [hbd]; exact disjoint_empty F)
  constructor
  · rintro ⟨Δ, hΔ, hbΔ⟩
    exact hep.2.1 ⟨Δ, subset_univ Δ, hΔ, hbΔ ▸ Surface.discBd_subset Δ⟩
  · intro hnull
    obtain ⟨Δ, -, hΔ, hbΔ⟩ := hep.1 hnull
    exact ⟨Δ, hΔ, hbΔ⟩

end GM21
end GraphMinor
