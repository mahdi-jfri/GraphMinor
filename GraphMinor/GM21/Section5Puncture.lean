module

public import GraphMinor.GM21.Section5Enlarge
public import GraphMinor.GM21.Section5Linkage
import GraphMinor.GM12.Section4SingletonDiscs
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM19.OrientOfHomeos
import GraphMinor.Surface.ModelCriterion

/-!
# Graph Minors XXI, Section 5: Puncturing at Terminals and Uniform Inductive Hypotheses for (5.2)

This file formalizes Step 1 of the proof of Graph Minors XXI, `(5.2)` (page 17 of the preprint)
and the homeomorphism-invariance reductions that turn pointwise statements into the uniform
inductive hypotheses `(1)`, `(2)`, and `(3)` of `(5.2)`:

1. **Homeomorphism invariance (`no_vitalPLinkage_of_homeomorph`, `no_vitalLinkage_bd_of_homeomorph`)**:
   Transporting a drawing, its tangle, and its vital linkage along a surface homeomorphism
   `e : S' ≃ₜ S` via `mapDrawingInjOn`.
2. **Uniform inductive hypotheses (`exists_theta1_of_simpler`, `exists_theta_of_cuffs_le`)**:
   Using the classification of surfaces (`GM19.classification`, `modelCriterion`, and
   `homeo_of_capped_homeo_and_cuffs_ncard_eq_sec5`) to obtain a single threshold `θ` across all
   surfaces in finitely many homeomorphism classes.
3. **Puncturing at terminals (`exists_punctured_surface_at_terminals`, `reduce_5_2_to_star`)**:
   Given a drawing `Γ` in a closed surface `S₀` (`bd S₀ = ∅`) and a vital `p`-linkage `L` in `Γ`,
   cutting at most `p` small open discs out of `S₀` (one at each terminal of `L`, via
   `GM12.exists_disjoint_single_vertex_discs`, `Surface.remove_discs`, and
   `GM19.nonempty_capped_of_removal`) produces a connected surface `S = ↥W` with `Ŝ ≅ S₀`,
   `c(S) ≤ p`, and a drawing `Γ_W` in `S` with `|V(Γ_W) ∩ bd(S)| ≤ p`, a tangle of the same order,
   and a vital linkage `L_W` with all terminals in `bd(S)`. This reduces `(5.2)` for `(S₀, p)` to
   statement `(*)` of the proof.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Topology Metric Hypergraph GraphMinor.Surface GraphMinor.GM10 Classical
open GraphMinor.GM19

set_option linter.style.haveILetI false

/-! ## Section 1: Homeomorphism Invariance of Vital Linkages and Tangles in Drawings -/

/-- A homeomorphism `e : S' ≃ₜ S` maps `bd S'` onto `bd S`: `e '' bd S' = bd S`. -/
theorem image_bd_of_homeomorph {S' S : Type} [TopologicalSpace S'] [TopologicalSpace S]
    (e : S' ≃ₜ S) :
    e '' bd S' = bd S := by
  ext y
  simp only [mem_image, bd, mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩ hy_int
    exact hx ((isInteriorPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mp hy_int)
  · intro hy
    refine ⟨e.symm y, fun hx_int => hy ?_, e.apply_symm_apply y⟩
    have h := (isInteriorPoint_iff_of_isOpenEmbedding e.isOpenEmbedding).mpr hx_int
    rwa [e.apply_symm_apply] at h

/-- Transporting `(5.2)` across a homeomorphism `e : S' ≃ₜ S`: if every drawing in `S` with a
tangle of order `≥ θ` has no vital `p`-linkage, then the same holds in `S'`. -/
theorem no_vitalPLinkage_of_homeomorph
    {S' S : Type} [TopologicalSpace S'] [TopologicalSpace S]
    (hS : IsSurface S) (e : S' ≃ₜ S) {p θ : ℕ}
    (h_prop : ∀ (Γ : Surface.Drawing S) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
      θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p)
    (Γ' : Surface.Drawing S') (θ_G : ℕ)
    (𝒯' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
    (hθ : θ ≤ θ_G) (h𝒯' : IsTangle Γ'.toHypergraph θ_G 𝒯') :
    ¬ HasVitalPLinkage Γ'.toHypergraph p := by
  rintro ⟨L', hL'_p⟩
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  haveI : CompactSpace S' := e.symm.compactSpace
  have hcont : ContinuousOn e Γ'.U := e.continuous.continuousOn
  have hinj : InjOn e Γ'.U := e.injective.injOn
  have h𝒯 := isTangle_mapDrawingInjOn Γ' e hcont hinj h𝒯'
  obtain ⟨hL_p, -⟩ := isVitalPLinkage_mapDrawingInjOn Γ' e hcont hinj hL'_p
  exact h_prop (mapDrawingInjOn Γ' e hcont hinj) θ_G _ hθ h𝒯
    ⟨mapSubH e L', hL_p⟩

/-- Transporting `(*)` across a homeomorphism `e : S' ≃ₜ S`: if every drawing `Γ` in `S` with
`|V(Γ) ∩ bd(S)| ≤ p` and a tangle of order `≥ θ` has no vital linkage with all terminals in
`bd(S)`, then the same holds in `S'`. -/
theorem no_vitalLinkage_bd_of_homeomorph
    {S' S : Type} [TopologicalSpace S'] [TopologicalSpace S]
    (hS : IsSurface S) (e : S' ≃ₜ S) {p θ : ℕ}
    (h_prop : ∀ (Γ : Surface.Drawing S) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (L : Hypergraph S (Set S)),
      Γ.IsProper →
      (Γ.V ∩ bd S).ncard ≤ p →
      θ ≤ θ_G →
      IsTangle Γ.toHypergraph θ_G 𝒯 →
      IsVitalLinkage Γ.toHypergraph L →
      terminals L ⊆ bd S →
      False)
    (Γ' : Surface.Drawing S') (θ_G : ℕ)
    (𝒯' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
    (L' : Hypergraph S' (Set S'))
    (hprop' : Γ'.IsProper)
    (hbd' : (Γ'.V ∩ bd S').ncard ≤ p)
    (hθ : θ ≤ θ_G)
    (h𝒯' : IsTangle Γ'.toHypergraph θ_G 𝒯')
    (hL' : IsVitalLinkage Γ'.toHypergraph L')
    (hterm' : terminals L' ⊆ bd S') :
    False := by
  haveI : CompactSpace S := hS.1
  haveI : T2Space S := hS.2.1
  haveI : CompactSpace S' := e.symm.compactSpace
  have hcont : ContinuousOn e Γ'.U := e.continuous.continuousOn
  have hinj : InjOn e Γ'.U := e.injective.injOn
  set Γ := mapDrawingInjOn Γ' e hcont hinj
  have h𝒯 := isTangle_mapDrawingInjOn Γ' e hcont hinj h𝒯'
  obtain ⟨hL, hterm_eq⟩ := isVitalLinkage_mapDrawingInjOn Γ' e hcont hinj hL'
  have hprop : Γ.IsProper := by
    rintro y ⟨hy_bd, hy_U⟩
    rw [← image_bd_of_homeomorph e] at hy_bd
    rcases hy_bd with ⟨x, hx_bd, rfl⟩
    rcases hy_U with ⟨x', hx'_U, hxx'⟩
    have hxx'_eq : x' = x := e.injective hxx'
    exact ⟨x, hprop' ⟨hx_bd, hxx'_eq ▸ hx'_U⟩, rfl⟩
  have hV_bd : Γ.V ∩ bd S = e '' (Γ'.V ∩ bd S') := by
    change e '' Γ'.V ∩ bd S = e '' (Γ'.V ∩ bd S')
    rw [← image_bd_of_homeomorph e, image_inter e.injective]
  have hbd : (Γ.V ∩ bd S).ncard ≤ p := by
    rw [hV_bd, ncard_image_of_injective _ e.injective]
    exact hbd'
  have hterm : terminals (mapSubH e L') ⊆ bd S := by
    rw [hterm_eq, ← image_bd_of_homeomorph e]
    exact image_mono hterm'
  exact h_prop Γ θ_G _ (mapSubH e L') hprop hbd hθ h𝒯 hL hterm

/-! ## Section 2: Uniform Inductive Hypotheses (1), (2), and (3) -/

/-- A closed surface (`IsSurface S` with `bd S = ∅`) satisfies `IsClosedSurface S`. -/
theorem isClosedSurface_of_bd_eq_empty {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (hbd : bd S = ∅) :
    IsClosedSurface S := by
  refine ⟨hS.1, hS.2.1, fun x => ?_⟩
  by_contra hx
  have hx_bd : x ∈ bd S := hx
  rw [hbd] at hx_bd
  exact hx_bd

/-- Two connected surfaces with homeomorphic cappings and the same number of cuffs are
homeomorphic. -/
theorem homeo_of_capped_homeo_and_cuffs_ncard_eq_sec5
    {S Shat S' Shat' : Type}
    [TopologicalSpace S] [TopologicalSpace Shat]
    [TopologicalSpace S'] [TopologicalSpace Shat']
    (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') [ConnectedSpace S']
    (cap : GM19.IsCappedSurface S Shat) (cap' : GM19.IsCappedSurface S' Shat')
    (hhat : Nonempty (Shat' ≃ₜ Shat))
    (hcuffs : (cuffs S').ncard = (cuffs S).ncard) :
    Nonempty (S' ≃ₜ S) := by
  obtain ⟨a, b, c, ⟨eS⟩⟩ := classification S hS inferInstance
  obtain ⟨a', b', c', ⟨eS'⟩⟩ := classification S' hS' inferInstance
  obtain ⟨e_SM⟩ := GM19.capModel a b c Shat (GM19.IsCappedSurface.ofHomeo eS.symm cap)
  obtain ⟨e_S'M⟩ := GM19.capModel a' b' c' Shat' (GM19.IsCappedSurface.ofHomeo eS'.symm cap')
  obtain ⟨e_hat⟩ := hhat
  have hM0 : Nonempty (SurfaceModel a' b' 0 ≃ₜ SurfaceModel a b 0) :=
    ⟨e_S'M.symm.trans (e_hat.trans e_SM)⟩
  obtain ⟨-, hab, hb0⟩ := (modelCriterion.2 a' b' 0 a b 0).mp hM0
  have hcS : (cuffs S).ncard = c := by
    have h := GM19.numCuffs_eq eS
    rw [numCuffs_model] at h
    exact h
  have hcS' : (cuffs S').ncard = c' := by
    have h := GM19.numCuffs_eq eS'
    rw [numCuffs_model] at h
    exact h
  have hcc' : c' = c := by omega
  obtain ⟨e_M⟩ := (modelCriterion.2 a' b' c' a b c).mpr ⟨hcc', hab, hb0⟩
  exact ⟨eS'.trans (e_M.trans eS.symm)⟩

/-- If `S' ≃ₜ SurfaceModel a b c` and `bd S' = ∅`, then `bd (SurfaceModel a b c) = ∅`. -/
theorem bd_surfaceModel_eq_empty_of_homeomorph
    {S' : Type} [TopologicalSpace S'] {a b c : ℕ}
    (e : S' ≃ₜ SurfaceModel a b c) (hbd : bd S' = ∅) :
    bd (SurfaceModel a b c) = ∅ := by
  rw [← image_bd_of_homeomorph e, hbd, image_empty]

/-- **Uniform Inductive Hypothesis (1) of `(5.2)`** (page 17 of the preprint):
If `(5.2)` holds for every closed connected surface `S'` simpler than `S₀`, then for every
integer `p' ≥ 0` there exists a single `θ₁ ≥ 1` that works simultaneously for all closed
connected surfaces `S'` simpler than `S₀`. -/
theorem exists_theta1_of_simpler
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀)
    (h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
      IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
      ∀ (p' : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p')
    (p' : ℕ) :
    ∃ θ₁ : ℕ, 1 ≤ θ₁ ∧
      ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          θ₁ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p' := by
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification S₀ hS₀ inferInstance
  let M : ℕ := 2 * (2 * a₀ + b₀) + c₀ + 1
  -- For each triple `(a, b, c) : Fin M × Fin M × Fin M`, if `SurfaceModel a b c` has empty boundary
  -- and is simpler than `S₀`, choose a valid `θ` for it; otherwise use `1`.
  have hex : ∀ idx : Fin M × Fin M × Fin M, ∃ θ : ℕ, 1 ≤ θ ∧
      (bd (SurfaceModel idx.1.1 idx.2.1 idx.2.2) = ∅ →
        IsSimplerThan (SurfaceModel idx.1.1 idx.2.1 idx.2.2) S₀ →
        ∀ (Γ : Surface.Drawing (SurfaceModel idx.1.1 idx.2.1 idx.2.2)) (θ_G : ℕ) (𝒯 : _),
          θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p') := by
    intro idx
    by_cases hcond : bd (SurfaceModel idx.1.1 idx.2.1 idx.2.2) = ∅ ∧
        IsSimplerThan (SurfaceModel idx.1.1 idx.2.1 idx.2.2) S₀
    · have hsurf := (modelCriterion.1 idx.1.1 idx.2.1 idx.2.2).1
      haveI hconn := (modelCriterion.1 idx.1.1 idx.2.1 idx.2.2).2
      obtain ⟨θ, hθ_pos, hθ⟩ :=
        h_simpler (SurfaceModel idx.1.1 idx.2.1 idx.2.2) hsurf hcond.1 hcond.2 p'
      exact ⟨θ, hθ_pos, fun _ _ => hθ⟩
    · exact ⟨1, le_rfl, fun hbd hsimp => (hcond ⟨hbd, hsimp⟩).elim⟩
  choose θ_fn hθ_pos hθ_prop using hex
  let θ₁ : ℕ := 1 + ∑ idx : Fin M × Fin M × Fin M, θ_fn idx
  refine ⟨θ₁, by omega, ?_⟩
  intro S' _ _ _ hbd' hsimp' Γ' θ_G 𝒯' hθ_G h𝒯'
  rcases hsimp' with ⟨a, b, c, a', b', c', ⟨e'⟩, ⟨e₀'⟩, ha, hb, hlt⟩
  have hmc : c' = c₀ ∧ 2 * a' + b' = 2 * a₀ + b₀ ∧ (b' = 0 ↔ b₀ = 0) :=
    (modelCriterion.2 a' b' c' a₀ b₀ c₀).mp ⟨e₀'.symm.trans e₀⟩
  have hbound : 4 * a + 2 * b + c < M := by
    dsimp only [M]
    omega
  have ha_lt : a < M := by omega
  have hb_lt : b < M := by omega
  have hc_lt : c < M := by omega
  let idx : Fin M × Fin M × Fin M := (⟨a, ha_lt⟩, ⟨b, hb_lt⟩, ⟨c, hc_lt⟩)
  have hbd_model : bd (SurfaceModel a b c) = ∅ :=
    bd_surfaceModel_eq_empty_of_homeomorph e' hbd'
  have hsimp_model : IsSimplerThan (SurfaceModel a b c) S₀ :=
    ⟨a, b, c, a', b', c', ⟨Homeomorph.refl _⟩, ⟨e₀'⟩, ha, hb, hlt⟩
  have hle_sum : θ_fn idx ≤ θ₁ := by
    have hmem : idx ∈ (Finset.univ : Finset (Fin M × Fin M × Fin M)) := Finset.mem_univ idx
    have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (θ_fn i)) hmem
    dsimp only [θ₁]
    omega
  have hsurf_model : IsSurface (SurfaceModel a b c) := (modelCriterion.1 a b c).1
  exact no_vitalPLinkage_of_homeomorph hsurf_model e'
    (hθ_prop idx hbd_model hsimp_model) Γ' θ_G 𝒯' (hle_sum.trans hθ_G) h𝒯'

/-- **Uniform bound over surfaces with `≤ c₀` cuffs** (`exists_theta_of_cuffs_le`):
If for every `t ≤ c₀` and every connected surface `S'` with `Nonempty (IsCappedSurface S' S₀)`
and `(cuffs S').ncard = t`, there exists `θ ≥ 1` such that `(*)` holds for `(S', p')`, then there
exists a single `θ ≥ 1` that works simultaneously for all connected surfaces `S'` with
`Nonempty (IsCappedSurface S' S₀)` and `(cuffs S').ncard ≤ c₀`. -/
theorem exists_theta_of_cuffs_le
    {S₀ : Type} [TopologicalSpace S₀]
    (c₀ p' : ℕ)
    (h_cuffs : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
      IsSurface S' → Nonempty (IsCappedSurface S' S₀) → (cuffs S').ncard ≤ c₀ →
      ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L : Hypergraph S' (Set S')),
          Γ.IsProper →
          (Γ.V ∩ bd S').ncard ≤ p' →
          θ ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S' →
          False) :
    ∃ θ₂ : ℕ, 1 ≤ θ₂ ∧
      ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → Nonempty (IsCappedSurface S' S₀) → (cuffs S').ncard ≤ c₀ →
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L : Hypergraph S' (Set S')),
          Γ.IsProper →
          (Γ.V ∩ bd S').ncard ≤ p' →
          θ₂ ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S' →
          False := by
  have hex : ∀ t : Fin (c₀ + 1), ∃ θ_t : ℕ, 1 ≤ θ_t ∧
      ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → Nonempty (IsCappedSurface S' S₀) → (cuffs S').ncard = t.1 →
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
          (L : Hypergraph S' (Set S')),
          Γ.IsProper →
          (Γ.V ∩ bd S').ncard ≤ p' →
          θ_t ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S' →
          False := by
    intro t
    by_cases h_ex : ∃ (S_t : Type) (_ : TopologicalSpace S_t) (_ : ConnectedSpace S_t),
        IsSurface S_t ∧ Nonempty (IsCappedSurface S_t S₀) ∧ (cuffs S_t).ncard = t.1
    · rcases h_ex with ⟨S_t, tS_t, cS_t, hsurf_t, hcap_t, hcuffs_t⟩
      have ht_le : (cuffs S_t).ncard ≤ c₀ := by omega
      obtain ⟨θ_t, hθ_pos, hθ_t⟩ := h_cuffs S_t hsurf_t hcap_t ht_le
      refine ⟨θ_t, hθ_pos, ?_⟩
      intro S' _ _ hsurf' ⟨cap'⟩ hcuffs' Γ' θ_G 𝒯' L' hprop' hbd' hθ_G h𝒯' hL' hterm'
      rcases hcap_t with ⟨cap_t⟩
      have hhomeo : Nonempty (S' ≃ₜ S_t) :=
        homeo_of_capped_homeo_and_cuffs_ncard_eq_sec5 hsurf_t hsurf' cap_t cap'
          ⟨Homeomorph.refl S₀⟩ (hcuffs'.trans hcuffs_t.symm)
      rcases hhomeo with ⟨e⟩
      exact no_vitalLinkage_bd_of_homeomorph hsurf_t e hθ_t Γ' θ_G 𝒯' L' hprop' hbd' hθ_G h𝒯' hL' hterm'
    · refine ⟨1, le_rfl, ?_⟩
      intro S' tS' cS' hsurf' hcap' hcuffs'
      exact (h_ex ⟨S', tS', cS', hsurf', hcap', hcuffs'⟩).elim
  choose θ_fn hθ_pos hθ_prop using hex
  let θ₂ : ℕ := 1 + ∑ t : Fin (c₀ + 1), θ_fn t
  refine ⟨θ₂, by omega, ?_⟩
  intro S' _ _ hsurf' hcap' hcuffs' Γ' θ_G 𝒯' L' hprop' hbd' hθ_G h𝒯' hL' hterm'
  let t : Fin (c₀ + 1) := ⟨(cuffs S').ncard, Nat.lt_succ_of_le hcuffs'⟩
  have hle_sum : θ_fn t ≤ θ₂ := by
    have hmem : t ∈ (Finset.univ : Finset (Fin (c₀ + 1))) := Finset.mem_univ t
    have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (θ_fn i)) hmem
    dsimp only [θ₂]
    omega
  exact hθ_prop t S' hsurf' hcap' rfl Γ' θ_G 𝒯' L' hprop' hbd' (hle_sum.trans hθ_G) h𝒯' hL' hterm'

/-! ## Section 3: Puncturing `S₀` at Terminals to Reduce `(5.2)` to `(*)` -/

/-- When a drawing `Γ : Drawing S₀` has `Γ.U ⊆ W`, pushing `drawingInSubspace Γ W hUW` forward
along `Subtype.val : ↥W → S₀` recovers `Γ`. -/
theorem mapDrawingInjOn_drawingInSubspace_eq
    {S₀ : Type} [TopologicalSpace S₀] [T2Space S₀]
    (Γ : Surface.Drawing S₀) (W : Set S₀) [CompactSpace ↥W] (hUW : Γ.U ⊆ W) :
    mapDrawingInjOn (GM12.drawingInSubspace Γ W hUW) Subtype.val
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn = Γ := by
  have hU : (mapDrawingInjOn (GM12.drawingInSubspace Γ W hUW) Subtype.val
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn).U = Γ.U := by
    change (Subtype.val : ↥W → S₀) '' (GM12.drawingInSubspace Γ W hUW).U = Γ.U
    rw [GM12.drawingInSubspace_U, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr hUW
  have hV : (mapDrawingInjOn (GM12.drawingInSubspace Γ W hUW) Subtype.val
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn).V = Γ.V := by
    change (Subtype.val : ↥W → S₀) '' (GM12.drawingInSubspace Γ W hUW).V = Γ.V
    rw [GM12.drawingInSubspace_V, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr (Γ.V_subset_U.trans hUW)
  cases h_lhs : mapDrawingInjOn (GM12.drawingInSubspace Γ W hUW) Subtype.val
    continuous_subtype_val.continuousOn Subtype.val_injective.injOn
  cases Γ
  rw [h_lhs] at hU hV
  dsimp only at hU hV
  subst hU hV
  rfl

/-- **Puncturing `S₀` at the terminals of a vital `p`-linkage `L`** (Step 1 of `(5.2)`, page 17 of
the preprint): "By cutting at most $p$ small holes in $\Sigma_0$, one at each terminal, we deduce
that it suffices to prove the following. (*)"

Given a closed connected surface `S₀` (`bd S₀ = ∅`), a drawing `Γ` in `S₀`, a tangle `𝒯` of order
`θ_G` in `Γ`, and a vital `p`-linkage `L` in `Γ`, cutting small open discs at the `t ≤ p`
terminals of `L` yields a connected surface `S = ↥W` with `Nonempty (IsCappedSurface S S₀)`,
`(cuffs S).ncard ≤ p`, and a drawing `Γ_W` in `S` with `(Γ_W.V ∩ bd S).ncard ≤ p`, a tangle of
order `θ_G`, and a vital linkage `L_W` with `terminals L_W ⊆ bd S`. -/
theorem exists_punctured_surface_at_terminals
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅)
    (Γ : Surface.Drawing S₀) {p θ_G : ℕ}
    {𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))}
    {L : Hypergraph S₀ (Set S₀)}
    (h𝒯 : IsTangle Γ.toHypergraph θ_G 𝒯)
    (hL : IsVitalPLinkage Γ.toHypergraph L p) :
    ∃ (S : Type) (_ : TopologicalSpace S) (_ : ConnectedSpace S),
      IsSurface S ∧
      Nonempty (IsCappedSurface S S₀) ∧
      (cuffs S).ncard ≤ p ∧
      ∃ (Γ_W : Surface.Drawing S)
        (𝒯_W : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (L_W : Hypergraph S (Set S)),
        Γ_W.IsProper ∧
        (Γ_W.V ∩ bd S).ncard ≤ p ∧
        IsTangle Γ_W.toHypergraph θ_G 𝒯_W ∧
        IsVitalLinkage Γ_W.toHypergraph L_W ∧
        terminals L_W ⊆ bd S := by
  haveI : T2Space S₀ := hS₀.2.1
  have hcl₀ : IsClosedSurface S₀ := isClosedSurface_of_bd_eq_empty hS₀ hbd₀
  have hterm_sub_V : terminals L ⊆ Γ.V :=
    fun v hv => hL.1.1.1.vertexSet_subset hv.1
  have hterm_fin : (terminals L).Finite := Γ.finite_V.subset hterm_sub_V
  let t : ℕ := (terminals L).ncard
  have ht_le_p : t ≤ p := hL.2.2
  -- Enumerate `terminals L` by an injective map `z : Fin t → S₀`.
  haveI : Finite ↥(terminals L) := hterm_fin.to_subtype
  have hcard_term : Nat.card ↥(terminals L) = t := Nat.card_coe_set_eq (terminals L)
  let e_fin : Fin t ≃ ↥(terminals L) :=
    (Finite.equivFinOfCardEq hcard_term).symm
  let z : Fin t → S₀ := fun i => (e_fin i).1
  have hz_inj : Function.Injective z :=
    Subtype.val_injective.comp e_fin.injective
  have hz_V : ∀ i : Fin t, z i ∈ Γ.V := fun i => hterm_sub_V (e_fin i).2
  have hz_range : range z = terminals L := by
    ext x
    simp only [z, mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact (e_fin i).2
    · intro hx
      exact ⟨e_fin.symm ⟨x, hx⟩, by simp⟩
  -- Choose `t` pairwise disjoint closed discs `Δ i` at `z i` meeting `Γ.U` only at `z i ∈ discBd (Δ i)`.
  obtain ⟨Δ, hΔ, hdisj⟩ :=
    GM12.exists_disjoint_single_vertex_discs hcl₀ Γ z hz_V hz_inj
  have hΔ_disc : ∀ i, IsClosedDisc (Δ i) := fun i => (hΔ i).1
  have hΔ_pair : Pairwise fun i j => Disjoint (Δ i) (Δ j) := fun i j hij => hdisj i j hij
  -- Puncture `S₀` by removing `⋃ i, discInt (Δ i)`.
  let W : Set S₀ := (⋃ i, discInt (Δ i))ᶜ
  obtain ⟨_, hW_surf, hW_bd, hW_conn, hW_cuffs⟩ :=
    Surface.remove_discs hS₀ hcl₀.2.2 hΔ_disc hΔ_pair
  haveI : ConnectedSpace ↥W := hW_conn
  haveI : CompactSpace ↥W := hW_surf.1
  have hcap : Nonempty (IsCappedSurface ↥W S₀) :=
    GM19.nonempty_capped_of_removal hcl₀ hΔ_disc hΔ_pair
  have hcuffs_le : (cuffs ↥W).ncard ≤ p := by
    rw [hW_cuffs, ← image_univ]
    calc ((fun i : Fin t => (Subtype.val : ↥W → S₀) ⁻¹' discBd (Δ i)) '' univ).ncard
        ≤ (univ : Set (Fin t)).ncard := ncard_image_le finite_univ
      _ = t := by rw [ncard_univ, Nat.card_fin]
      _ ≤ p := ht_le_p
  -- Show `Γ.U ⊆ W`: each `Δ i` meets `Γ.U` only at `z i ∈ discBd (Δ i)`.
  have hUW : Γ.U ⊆ W := by
    intro x hxU hx_int
    obtain ⟨i, hxi_Δ, hxi_not_bd⟩ := mem_iUnion.mp hx_int
    have hxz : x = z i := by
      have hx_inter : x ∈ Γ.U ∩ Δ i := ⟨hxU, hxi_Δ⟩
      rw [(hΔ i).2.1] at hx_inter
      exact hx_inter
    exact hxi_not_bd (hxz ▸ (hΔ i).2.2.1)
  let Γ_W : Surface.Drawing ↥W := GM12.drawingInSubspace Γ W hUW
  have hΓ_W_prop : Γ_W.IsProper := by
    rintro w ⟨hw_bd, hw_U⟩
    rw [hW_bd, mem_preimage, mem_iUnion] at hw_bd
    rcases hw_bd with ⟨i, hwi⟩
    have hw_U' : w.1 ∈ Γ.U := by
      have : w ∈ (Subtype.val : ↥W → S₀) ⁻¹' Γ.U := by
        rwa [← GM12.drawingInSubspace_U Γ W hUW]
      exact this
    have hw_inter : w.1 ∈ Γ.U ∩ Δ i := ⟨hw_U', Surface.discBd_subset (Δ i) hwi⟩
    rw [(hΔ i).2.1] at hw_inter
    have hw_V' : w.1 ∈ Γ.V := hw_inter.symm ▸ hz_V i
    rw [GM12.drawingInSubspace_V Γ W hUW]
    exact hw_V'
  have hmap_eq :
      mapDrawingInjOn Γ_W Subtype.val
        continuous_subtype_val.continuousOn Subtype.val_injective.injOn = Γ :=
    mapDrawingInjOn_drawingInSubspace_eq Γ W hUW
  -- Pull back the tangle `𝒯` to `Γ_W`.
  have h𝒯_W :=
    isTangle_comapDrawingInjOn Γ_W Subtype.val
      continuous_subtype_val.continuousOn Subtype.val_injective.injOn (hmap_eq.symm ▸ h𝒯)
  -- Pull back the vital linkage `L` to `Γ_W`.
  obtain ⟨hinjV, hinjE⟩ := drawing_injOn_V_and_E Γ_W Subtype.val_injective.injOn
  have hG_eq : Γ.toHypergraph =
      mapHypergraph (Subtype.val : ↥W → S₀) (image Subtype.val) Γ_W.toHypergraph := by
    rw [← hmap_eq, toHypergraph_mapDrawingInjOn, mapSubH_eq_mapHypergraph]
  let L_W : Hypergraph ↥W (Set ↥W) :=
    comapHypergraph Subtype.val (image Subtype.val) Γ_W.toHypergraph L
  have hL_le_map : L ≤
      mapHypergraph (Subtype.val : ↥W → S₀) (image Subtype.val) Γ_W.toHypergraph := by
    rw [← hG_eq]
    exact hL.1.1.1
  have hmap_LW :
      mapHypergraph (Subtype.val : ↥W → S₀) (image Subtype.val) L_W = L :=
    mapHypergraph_comapHypergraph hL_le_map
  have hLW_le : L_W ≤ Γ_W.toHypergraph :=
    comapHypergraph_le_self hL_le_map
  have hLW_vital : IsVitalLinkage Γ_W.toHypergraph L_W := by
    rw [← isVitalLinkage_mapHypergraph (fV := (Subtype.val : ↥W → S₀)) (fE := image Subtype.val)
      hLW_le hinjV hinjE, hmap_LW, ← hG_eq]
    exact hL.1
  -- Show `terminals L_W ⊆ bd ↥W` and `(Γ_W.V ∩ bd ↥W).ncard ≤ p`.
  have hterm_LW : (Subtype.val : ↥W → S₀) '' terminals L_W = terminals L := by
    rw [← terminals_mapHypergraph (fV := (Subtype.val : ↥W → S₀)) (fE := image Subtype.val)
      hLW_le hinjV hinjE, hmap_LW]
  have hterm_LW_bd : terminals L_W ⊆ bd ↥W := by
    intro w hw
    rw [hW_bd, mem_preimage, mem_iUnion]
    have hw_term : w.1 ∈ terminals L := hterm_LW ▸ mem_image_of_mem Subtype.val hw
    rw [← hz_range] at hw_term
    rcases hw_term with ⟨i, hi⟩
    exact ⟨i, hi ▸ (hΔ i).2.2.1⟩
  have hV_bd_sub : (Subtype.val : ↥W → S₀) '' (Γ_W.V ∩ bd ↥W) ⊆ terminals L := by
    rintro x ⟨w, ⟨hwV, hwbd⟩, rfl⟩
    rw [hW_bd, mem_preimage, mem_iUnion] at hwbd
    rcases hwbd with ⟨i, hwi⟩
    have hwV' : w.1 ∈ Γ.V := by
      have : w ∈ (Subtype.val : ↥W → S₀) ⁻¹' Γ.V := by
        rwa [← GM12.drawingInSubspace_V Γ W hUW]
      exact this
    have hw_inter : w.1 ∈ Γ.V ∩ discBd (Δ i) := ⟨hwV', hwi⟩
    rw [(hΔ i).2.2.2] at hw_inter
    rw [← hz_range]
    exact ⟨i, hw_inter.symm⟩
  have hV_bd_le : (Γ_W.V ∩ bd ↥W).ncard ≤ p := by
    rw [← ncard_image_of_injective _ Subtype.val_injective]
    exact (ncard_le_ncard hV_bd_sub hterm_fin).trans ht_le_p
  exact ⟨↥W, inferInstance, inferInstance, hW_surf, hcap, hcuffs_le,
    Γ_W, _, L_W,
    hΓ_W_prop, hV_bd_le, h𝒯_W, hLW_vital, hterm_LW_bd⟩

/-- **Reduction of `(5.2)` to `(*)`** (`reduce_5_2_to_star`, page 17 of the preprint):
If statement `(*)` holds for every connected surface `S` with `Nonempty (IsCappedSurface S S₀)`,
then for every `p ≥ 0` there exists `θ ≥ 1` such that every drawing in `S₀` with a tangle of order
`≥ θ` has no vital `p`-linkage. -/
theorem reduce_5_2_to_star
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅)
    (h_star : ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S],
      IsSurface S → Nonempty (IsCappedSurface S S₀) →
      ∀ (p : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S) (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (L : Hypergraph S (Set S)),
          Γ.IsProper →
          (Γ.V ∩ bd S).ncard ≤ p →
          θ ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S →
          False)
    (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Surface.Drawing S₀) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
        θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p := by
  obtain ⟨θ, hθ_pos, hθ_unif⟩ :=
    exists_theta_of_cuffs_le p p (fun S' _ _ hsurf' hcap' _ => h_star S' hsurf' hcap' p)
  refine ⟨θ, hθ_pos, ?_⟩
  rintro Γ θ_G 𝒯 hθ_G h𝒯 ⟨L, hL_vital, _, hL_card⟩
  have hL : IsVitalPLinkage Γ.toHypergraph L p := ⟨hL_vital, hL_vital.1, hL_card⟩
  obtain ⟨S, tS, cS, hS_surf, hcap, hcuffs_le, Γ_W, 𝒯_W, L_W, hprop_W, hbd_le, h𝒯_W, hLW_vital, hLW_bd⟩ :=
    exists_punctured_surface_at_terminals hS₀ hbd₀ Γ h𝒯 hL
  exact hθ_unif S hS_surf hcap hcuffs_le Γ_W θ_G 𝒯_W L_W hprop_W hbd_le hθ_G h𝒯_W hLW_vital hLW_bd

end GM21
end GraphMinor
