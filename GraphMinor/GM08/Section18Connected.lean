module

public import GraphMinor.GM08.Section18Step
import GraphMinor.GM08.Section12
import GraphMinor.GM08.Section16FiniteLabels
import GraphMinor.GM08.Section17
import GraphMinor.GM08.Section17Cylinder
import GraphMinor.GM08.Section18Map
import GraphMinor.Surface.CutIArc
import GraphMinor.GM07.CutBounds

/-!
# `𝒞(Σ, k)` for a connected surface

Page 287 of VIII: "It follows that `𝒞(Σ, k)` is well-rooted. For
`𝒞(Σ, k) = ⋃ 𝒞(Σ; k₁, …, k_c)`, the union being taken over all choices of
`k₁, …, k_c ≥ 0` with `k₁ + ⋯ + k_c ≤ k`. Since there are only finitely many
such choices, `𝒞(Σ, k)` is well-rooted by (4.2)."

For a disc we use the disc case of (6.1) (`theorem_6_1_disc`), and for a
cylinder (17.3), since a graft that embeds in a cylinder is tubular.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v w

/-- Embedding in a surface depends only on the surface up to homeomorphism. -/
theorem embedsGraft_of_homeomorph {S : Type w} {T : Type v} [TopologicalSpace S]
    [TopologicalSpace T] (e : S ≃ₜ T) {α : Type u} {β : Type u} {X : Graft α β}
    (hX : EmbedsGraft S X) : EmbedsGraft T X :=
  let ⟨gd⟩ := hX
  ⟨mapGraftDrawing e gd⟩

/-- `𝒞(Σ, k)` for a disc is well-rooted: the disc case of (6.1). -/
theorem isWellRooted_classCSurface_disc {S : Type w} [TopologicalSpace S]
    (he : Nonempty (S ≃ₜ SurfaceModel 0 0 1)) {α β : Type u} (k : ℕ) :
    IsWellRootedGraftClass (classCSurface (α := α) (β := β) S k) := by
  obtain ⟨e⟩ := he
  obtain ⟨d⟩ := nonempty_disc_homeo
  exact theorem_6_1_disc ⟨(d.symm.trans e.symm).trans (Homeomorph.Set.univ S).symm⟩ k

/-- `𝒞(Σ, k)` for a cylinder lies in `ℬ(k)`, so it is well-rooted by (17.3). -/
theorem isWellRooted_classCSurface_cylinder {S : Type w} [TopologicalSpace S]
    (he : Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {α β : Type u} (k : ℕ) :
    IsWellRootedGraftClass (classCSurface (α := α) (β := β) S k) := by
  obtain ⟨e⟩ := he
  have hcyl : IsCylinder (SurfaceModel 0 0 2) :=
    ⟨(isSurface_model 0 0 2).1, ⟨Homeomorph.refl _⟩⟩
  refine isWellRootedGraftClass_mono ?_ (theorem_17_3_proof (α := α) (β := β) k)
  rintro X ⟨hk, hX⟩
  exact ⟨isTubularGraft_of_embedsGraft_cylinder hcyl (embedsGraft_of_homeomorph e hX),
    by exact_mod_cast hk⟩

/-- **The claim of page 287 for `𝒞(Σ, k)`**, for a connected surface that is
not a sphere, disc or cylinder: the union over the cuff counts. -/
theorem isWellRooted_classCSurface_of_steps (hcut : CutStepStatement.{u, w})
    (hsplit : SplitStepStatement.{u, w}) {h k : ℕ}
    (hlow : ∀ k', ClassCWellRooted.{u, w} (h - 1) k')
    (hprev : 1 ≤ k → ClassCWellRooted.{u, w} h (k - 1))
    {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hg : surfaceComplexity S ≤ h) {a b c : ℕ} (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) {α β : Type u} :
    IsWellRootedGraftClass (classCSurface (α := α) (β := β) S k) := by
  classical
  have : T2Space S := hS.2.1
  rcases finite_or_infinite α with hα | hα
  · exact isWellRootedGraftClass_of_finite _
  have hfin : (cuffs S).Finite := (cuff_statement.{w} S hS).2.1
  have : Fintype (cuffs S) := hfin.fintype
  let κ : (cuffs S → Fin (k + 1)) → Set S → ℕ :=
    fun v C => if hC : C ∈ cuffs S then v ⟨C, hC⟩ else 0
  refine isWellRootedGraftClass_mono ?_ (isWellRootedGraftClass_biUnion_finset Finset.univ
    fun v _ => isWellRooted_classCCuffs_of_steps hcut hsplit hlow hprev hS hg h3 he (κ v))
  rintro X ⟨hXk, ⟨gd⟩⟩
  have hidx := GraftDrawing.index_eq gd
  have hlt : ∀ C : cuffs S, (gd.drawing.V ∩ C.1).ncard < k + 1 := fun C => by
    have := ncard_le_ncard (inter_subset_inter_right gd.drawing.V
      (GM07.connectedComponentIn_subset_of_cuff C.2)) (gd.drawing.finite_V.subset
        inter_subset_left)
    omega
  refine mem_iUnion₂.mpr ⟨fun C => ⟨(gd.drawing.V ∩ C.1).ncard, hlt C⟩, Finset.mem_univ _,
    ⟨gd, fun C hC => by simp [κ, hC]⟩, hXk⟩

end GraphMinor.GM08
