module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.PushOff
import GraphMinor.Surface.Collar
import GraphMinor.Surface.Epstein
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.AddCrosscap
import GraphMinor.Surface.DiscUnion
import GraphMinor.GM12.Section3OneDiscComplement
import GraphMinor.GM12.Section3SolidEmbedding
import GraphMinor.GM07.CutBounds

/-!
# Recognizing a closed disc

The converse of Graph Minors VII, (2.1) (page 216), ends with: "Since $\Delta$ is a surface, it
follows that $\Delta$ is a closed disc." Here `Δ` is a connected surface with non-empty boundary in
which every `O`-arc off the boundary bounds a closed disc off the boundary. We prove that such a
surface is a closed disc (`isClosedDisc_univ_of_bounds`).

The proof caps every cuff of `Δ` by a disc, which gives a surface `T` without boundary. Take one cap
`D₁` and a slightly larger closed disc `Δ'` around it that misses the other caps. The boundary `F` of
`Δ'` lies in `Δ` off its boundary, so it also bounds a closed disc `E` that misses all caps. Now `F`
bounds two different closed discs of `T`, so by Epstein's theorem `T` is a sphere, and `E ∪ Δ' = T`.
No point is left for another cap, so `D₁` is the only cap, and `Δ` is the sphere without the inside of
one closed disc, which is a closed disc.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

/-- **A surface in which every `O`-arc bounds a disc is a closed disc.** Let `Y` be a connected
surface with non-empty boundary, such that every `O`-arc of `Y` that misses `bd(Y)` bounds a closed
disc that misses `bd(Y)`. Then `Y` is a closed disc. -/
theorem isClosedDisc_univ_of_bounds {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y)
    [ConnectedSpace Y] (hne : (bd Y).Nonempty)
    (hP : ∀ F : Set Y, F ⊆ (bd Y)ᶜ → IsOArc F →
      ∃ Δ : Set Y, Δ ⊆ (bd Y)ᶜ ∧ IsClosedDisc Δ ∧ discBd Δ = F) :
    IsClosedDisc (univ : Set Y) := by
  classical
  have : T2Space Y := hY.2.1
  obtain ⟨T, tT, j, K, hT, hj, hK, hu, hi, hconn, 𝓓, hfin, hK𝓓, hdiscs, hdisj⟩ :=
    exists_capAll_discs Y hY
  have : ConnectedSpace T := hconn inferInstance
  have : T2Space T := hT.2.1
  have hTs : IsSurface T := ⟨hT.1, hT.2.1, fun x => (hT.2.2 x).isManifoldPoint⟩
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  have hbdT : bd T = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => hx (hT.2.2 x)
  -- A point of `T` in `K` and in the range of `j` comes from `bd(Y)`.
  have hjK : ∀ y : Y, j y ∈ K → y ∈ bd Y := fun y hy => by
    obtain ⟨y', hy', he⟩ := (hi ▸ (⟨⟨y, rfl⟩, hy⟩ : j y ∈ range j ∩ K) : j y ∈ j '' bd Y)
    exact hj.injective he ▸ hy'
  -- the cap `D₁` over a point of `bd(Y)`
  obtain ⟨p, hp⟩ := hne
  have hpK : j p ∈ K := (hi.symm ▸ mem_image_of_mem j hp : j p ∈ range j ∩ K).2
  rw [← hK𝓓] at hpK
  obtain ⟨D₁, hD₁, hpD₁⟩ := hpK
  have hD₁d := (hdiscs D₁ hD₁).1
  -- the other caps
  set O : Set T := ⋃₀ (𝓓 \ {D₁}) with hO
  have hOc : IsClosed O :=
    (hfin.subset sdiff_subset).isClosed_sUnion fun D hD => (hdiscs D hD.1).1.isClosed
  have hD₁O : Disjoint D₁ O := by
    rw [hO, disjoint_sUnion_right]
    exact fun D hD => hdisj D₁ hD₁ D hD.1 (Ne.symm hD.2)
  obtain ⟨Δ', hΔ', hD₁Δ', hΔ'W⟩ := exists_disc_around hman hD₁d (fun x _ => hT.2.2 x)
    hOc.isOpen_compl (fun x hx => disjoint_left.mp hD₁O (discBd_subset D₁ hx))
  set F := discBd Δ' with hF
  have hFO : IsOArc F := hΔ'.isOArc_discBd
  -- `F` misses every cap
  have hFK : Disjoint F K := by
    rw [← hK𝓓, disjoint_sUnion_right]
    intro D hD
    rw [disjoint_left]
    intro x hxF hxD
    by_cases hDD : D = D₁
    · subst hDD
      exact (hD₁Δ' hxD).2 hxF
    · rcases hΔ'W (discBd_subset Δ' hxF) with h1 | h1
      · exact (hD₁Δ' h1).2 hxF
      · exact h1 ⟨D, ⟨hD, hDD⟩, hxD⟩
  have hFr : F ⊆ range j := fun x hx => by
    rcases eq_univ_iff_forall.mp hu x with h | h
    · exact h
    · exact absurd h (disjoint_left.mp hFK hx)
  -- the disc `E` bounded by `F` that misses the caps
  have hF' : IsOArc (j ⁻¹' F) := GM12.isOArc_preimage_isEmbedding hj.isEmbedding hFO hFr
  have hF'bd : j ⁻¹' F ⊆ (bd Y)ᶜ := fun y hy hyb =>
    disjoint_left.mp hFK hy (hi.symm ▸ mem_image_of_mem j hyb : j y ∈ range j ∩ K).2
  obtain ⟨Δ, hΔbd, hΔ, hΔF⟩ := hP _ hF'bd hF'
  obtain ⟨hE, hEbd⟩ := isClosedDisc_image_of_injOn hΔ hj.continuous hj.injective.injOn
  set E := j '' Δ with hEdef
  have hEF : discBd E = F := by
    rw [hEbd, hΔF, image_preimage_eq_of_subset hFr]
  have hEK : Disjoint E K := by
    rw [disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hyK
    exact hΔbd hy (hjK y hyK)
  have hEne : E ≠ Δ' := by
    intro h
    have : j p ∈ E := h ▸ (hD₁Δ' hpD₁).1
    exact disjoint_left.mp hEK this (hK𝓓 ▸ ⟨D₁, hD₁, hpD₁⟩)
  -- `T` is a sphere
  have hsph : IsSphere T := by
    by_contra hns
    exact hEne ((epstein T univ F hTs inferInstance hFO (subset_univ F)
      (by rw [hbdT]; exact disjoint_empty F)).2.2 E Δ' hE hΔ' hEF rfl hns)
  obtain ⟨Δ₁, Δ₂, -, -, -, -, -, hcup, -, -, huniq⟩ := sphere_disc T hsph F hFO
  have hEΔ' : E ∪ Δ' = univ := by
    rcases huniq E hE hEF with h1 | h1 <;> rcases huniq Δ' hΔ' rfl with h2 | h2
    · exact absurd (h1.trans h2.symm) hEne
    · rw [h1, h2, hcup]
    · rw [h1, h2, union_comm, hcup]
    · exact absurd (h1.trans h2.symm) hEne
  -- `D₁` is the only cap
  have hKD : K = D₁ := by
    refine Subset.antisymm ?_ (hK𝓓 ▸ subset_sUnion_of_mem hD₁)
    rw [← hK𝓓]
    rintro x ⟨D, hD, hxD⟩
    by_contra hx
    have hDD : D ≠ D₁ := fun h => hx (h ▸ hxD)
    rcases (hEΔ' ▸ mem_univ x : x ∈ E ∪ Δ') with h1 | h1
    · exact disjoint_left.mp hEK h1 (hK𝓓 ▸ ⟨D, hD, hxD⟩)
    · rcases hΔ'W h1 with h2 | h2
      · exact hx h2
      · exact h2 ⟨D, ⟨hD, hDD⟩, hxD⟩
  -- `Y` is the sphere without the inside of `D₁`
  have hrange : range j = closure (univ \ D₁) := by
    refine Subset.antisymm ?_ (closure_minimal (fun x hx => ?_) hj.isClosed_range)
    · rintro _ ⟨y, rfl⟩
      have h1 : y ∈ closure (bd Y)ᶜ := mem_closure_compl_bd (hY.2.2 y)
      refine closure_mono ?_ (image_closure_subset_closure_image hj.continuous ⟨y, h1, rfl⟩)
      rintro _ ⟨y', hy', rfl⟩
      exact ⟨mem_univ _, fun h => hy' (hjK y' (hKD ▸ h))⟩
    · rcases eq_univ_iff_forall.mp hu x with h | h
      · exact h
      · exact absurd (hKD ▸ h) hx.2
  obtain ⟨hcl, -⟩ := GM12.isClosedDisc_closure_compl_of_sphere hT hsph hD₁d
  rw [← hrange] at hcl
  obtain ⟨φ⟩ := hcl
  exact ⟨φ.trans ((hj.isEmbedding.toHomeomorph).symm.trans (Homeomorph.Set.univ Y).symm)⟩

end GraphMinor.GM07
