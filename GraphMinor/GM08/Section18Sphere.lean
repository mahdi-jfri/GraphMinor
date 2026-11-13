module

public import GraphMinor.GM08.Section18Classes
import GraphMinor.GM08.Section18Connected
import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM08.Section18Map
import GraphMinor.GM11.EdgeSides
import GraphMinor.GM11.Section4c
import GraphMinor.GM12.Section3Punctured
import GraphMinor.GM12.Section3PuncturedBoundary
import GraphMinor.GM12.Section3PuncturedModel
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.CutBounds

/-!
# `𝒞(Σ, k)` for a sphere

Page 287 of VIII says that for a sphere `𝒞(Σ; k₁, …, k_c) ⊆ ℬ(k)`. We take a
shorter path to the same end: a drawing in a sphere misses some point, since
a drawing contains no open set. Remove a small open disc around that point.
What is left is a closed disc that holds the whole drawing, and the graft has
no roots. So the graft embeds in a disc, and the disc case of (6.1) applies.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u w

/-- A graft that embeds in a sphere embeds in a disc. -/
theorem embedsGraft_disc_of_sphere {S : Type w} [TopologicalSpace S] (hS : IsSurface S)
    (he : Nonempty (S ≃ₜ SurfaceModel 0 0 0)) {α β : Type u} {X : Graft α β}
    (hX : EmbedsGraft S X) : EmbedsGraft (SurfaceModel 0 0 1) X := by
  classical
  obtain ⟨e⟩ := he
  have : T2Space S := hS.2.1
  have : ConnectedSpace S := GM07.connectedSpace_of_model ⟨e⟩
  have : Nonempty S := inferInstance
  have hbd : bd S = ∅ := by
    have hc := GM07.ncard_cuffs_of_homeomorph_surfaceModel ⟨e⟩
    have hfin : (cuffs S).Finite := (cuff_statement.{w} S hS).2.1
    have hcuffs : cuffs S = ∅ := (ncard_eq_zero hfin).mp hc
    rw [← sUnion_cuffs, hcuffs, sUnion_empty]
  have hclosed : IsClosedSurface S := ⟨hS.1, hS.2.1, fun x => by
    by_contra hx
    have hx' : x ∈ bd S := hx
    rw [hbd] at hx'
    exact hx'⟩
  obtain ⟨gd⟩ := hX
  set Γ := gd.drawing with hΓ
  obtain ⟨x, -, hx⟩ := GM11.exists_notMem_U (Γ := Γ) hclosed isOpen_univ univ_nonempty
  obtain ⟨P, -, hP, -, -, -, hPO, -⟩ :=
    GM11.exists_closedDisc_nbhd hclosed Γ.isClosed_U.isOpen_compl hx
  let Δ : Fin 1 → Set S := fun _ => P
  have hΔ : ∀ i, IsClosedDisc (Δ i) := fun _ => hP
  have hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)) := fun i j hij =>
    absurd (Subsingleton.elim i j) hij
  have hPU : ∀ y ∈ P, y ∉ Γ.U := fun y hy => hPO hy
  have havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i) := fun _ => by
    have h1 : Γ.U ∩ P = ∅ := eq_empty_iff_forall_notMem.mpr (fun y hy => hPU y hy.2 hy.1)
    have h2 : Γ.V ∩ discBd P = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun y hy => hPU y (discBd_subset P hy.2) (Γ.V_subset_U hy.1))
    exact h1.trans h2.symm
  let K := GM12.discComplement Δ
  have hUK : Γ.U ⊆ K := GM12.drawing_support_subset_discComplement hclosed Γ Δ hΔ hdisj havoid
  have hKc : IsClosed K := isClosed_closure
  obtain ⟨eK⟩ : Nonempty (K ≃ₜ SurfaceModel 0 0 1) := by
    have h := GM12.discComplement_model_of_closed_model hclosed Δ hΔ hdisj e
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  let J := GM12.drawingInSubspace Γ K hUK
  let i := (isGraphBij_drawingInSubspace Γ hKc hUK).toIso
  have hinv : ∀ (f : E(Γ.toGraph)) (y z : V(Γ.toGraph)),
      Γ.toGraph.IsLink f.1 y.1 z.1 ↔
        J.toGraph.IsLink (i.edgeEquiv.symm f).1 (i.vertexEquiv.symm y).1
          (i.vertexEquiv.symm z).1 := by
    intro f y z
    have h := i.isLink_iff (i.edgeEquiv.symm f) (i.vertexEquiv.symm y) (i.vertexEquiv.symm z)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let b : GraphMinor.Iso X.G J.toGraph := {
    vertexEquiv := gd.iso.vertexEquiv.trans i.vertexEquiv.symm
    edgeEquiv := gd.iso.edgeEquiv.trans i.edgeEquiv.symm
    isLink_iff := fun f y z => (gd.iso.isLink_iff f y z).trans (hinv _ _ _) }
  have hJbd : ∀ y : K, y ∈ J.U → y ∉ bd K := by
    intro y hy hyb
    have h := GM12.discComplement_boundary_subset hclosed Δ hΔ hyb
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    have hy' : (y : S) ∈ Γ.U := by
      rw [GM12.drawingInSubspace_U] at hy
      exact hy
    exact hPU _ (discBd_subset P hj) hy'
  have gdK : GraftDrawing X.G X.T K :=
    { drawing := J
      iso := b
      isProper := GM12.drawingInDiscComplement_isProper hclosed Γ Δ hΔ hdisj havoid
      T_subset_V := X.T_subset
      mem_bd_iff := fun v hv => by
        constructor
        · intro h
          exact absurd h (hJbd _ (J.V_subset_U (b.vertexEquiv ⟨v, hv⟩).2))
        · intro hvT
          have h := (gd.mem_bd_iff v hv).mpr hvT
          rw [hbd] at h
          exact absurd h (notMem_empty _) }
  exact ⟨mapGraftDrawing eK gdK⟩

/-- `𝒞(Σ, k)` for a sphere is well-rooted. -/
theorem isWellRooted_classCSurface_sphere {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) (he : Nonempty (S ≃ₜ SurfaceModel 0 0 0)) {α β : Type u} (k : ℕ) :
    IsWellRootedGraftClass (classCSurface (α := α) (β := β) S k) :=
  isWellRootedGraftClass_mono (fun X hX => (⟨hX.1, embedsGraft_disc_of_sphere hS he hX.2⟩ :
      X ∈ classCSurface (SurfaceModel 0 0 1) k))
    (isWellRooted_classCSurface_disc ⟨Homeomorph.refl _⟩ k)

end GraphMinor.GM08
