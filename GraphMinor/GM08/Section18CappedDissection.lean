module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.Dissection
import GraphMinor.GM08.Section18BoundaryFace
import GraphMinor.GM07.CutBounds
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.Triangulate
import Lean.Elab.Tactic.Omega

/-!
# Capping a dissection

Map the old graph and faces into the capped surface, then add the cap
as one more face. A boundary edge had only one old incident face, so
the new face-incidence bound is still two. Vertices and edges retain
their counts and the face count increases by one. This extends the
Euler formula to surfaces with cuffs for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

/-- Pasting a disc on a cuff adds one face to a dissection. This is the
capping step for the Euler formula used in VIII (18.2), page 286. -/
theorem isDissection_capped_cuff {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {C : Set S} {j : S → T} {D : Set T}
    (hcap : GM07.IsCappedCuff C T j D)
    {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕) :
    IsDissection (j '' V) ((image j) '' E) (insert D ((image j) '' 𝓕)) ∧
      ((((j '' V) ∩ ⋃₀ ((image j) '' E)).ncard : ℤ) -
          ((image j) '' E).ncard + (insert D ((image j) '' 𝓕)).ncard) =
        (((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard) + 1 := by
  classical
  have : T2Space S := hS.2.1
  have : T2Space T := hcap.isSurface.2.1
  have hj := hcap.isEmbedding
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hcap.cuff
    exact connectedComponentIn_subset _ _
  have hgraph := hd.graph.map hj
  have hEU : ⋃₀ ((image j) '' E) = j '' ⋃₀ E := by
    ext z
    constructor
    · rintro ⟨L, ⟨e, he, rfl⟩, x, hx, rfl⟩
      exact ⟨x, ⟨e, he, hx⟩, rfl⟩
    · rintro ⟨x, ⟨e, he, hx⟩, rfl⟩
      exact ⟨j '' e, mem_image_of_mem (image j) he, x, hx, rfl⟩
  have hdiscimage : ∀ Φ ∈ 𝓕, IsClosedDisc (j '' Φ) ∧
      discBd (j '' Φ) = j '' discBd Φ ∧ discInt (j '' Φ) = j '' discInt Φ := by
    intro Φ hΦ
    obtain ⟨hdisc, hbd⟩ := GM07.isClosedDisc_image_of_injOn (hd.disc Φ hΦ) hj.continuous hj.injective.injOn
    refine ⟨hdisc, hbd, ?_⟩
    change j '' Φ \ discBd (j '' Φ) = j '' (Φ \ discBd Φ)
    rw [hbd, image_sdiff hj.injective]
  have hDoff : Disjoint (discInt D) (range j) := by
    apply disjoint_left.mpr
    intro z hz hzj
    have hzC := hcap.inter_eq.subset ⟨hzj, hz.1⟩
    exact hz.2 (hcap.discBd_eq.symm.subset hzC)
  have hOldOff : ∀ Φ ∈ 𝓕, Disjoint (discInt (j '' Φ)) D := by
    intro Φ hΦ
    rw [(hdiscimage Φ hΦ).2.2]
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hxD
    obtain ⟨y, hyC, heq⟩ := hcap.inter_eq.subset ⟨mem_range_self x, hxD⟩
    have hyx : y = x := hj.injective heq
    have hxbd : x ∈ bd S := hCbd (hyx ▸ hyC)
    exact hxbd (isInteriorPoint_of_mem_discInt hS.2.2 (hd.disc Φ hΦ) hx)
  have hImgCover : ⋃₀ ((image j) '' 𝓕) = range j := by
    ext z
    constructor
    · rintro ⟨L, ⟨Φ, hΦ, rfl⟩, x, hx, rfl⟩
      exact mem_range_self x
    · rintro ⟨x, rfl⟩
      obtain ⟨Φ, hΦ, hxΦ⟩ := hd.cover.symm.subset (mem_univ x)
      exact ⟨j '' Φ, mem_image_of_mem (image j) hΦ, x, hxΦ, rfl⟩
  have hDnew : D ∉ (image j) '' 𝓕 := by
    rintro ⟨Φ, hΦ, heq⟩
    obtain ⟨z, hz⟩ := hcap.isClosedDisc.discInt_nonempty
    have hzD : z ∈ j '' Φ := heq.symm.subset hz.1
    exact disjoint_left.mp hDoff hz (image_subset_range _ _ hzD)
  have hdisc : ∀ Φ ∈ insert D ((image j) '' 𝓕), IsClosedDisc Φ := by
    rintro Φ (rfl | ⟨Ψ, hΨ, rfl⟩)
    · exact hcap.isClosedDisc
    · exact (hdiscimage Ψ hΨ).1
  have hbd : ∀ Φ ∈ insert D ((image j) '' 𝓕), discBd Φ ⊆ ⋃₀ ((image j) '' E) := by
    rintro Φ (rfl | ⟨Ψ, hΨ, rfl⟩)
    · rw [hcap.discBd_eq, hEU]
      exact image_mono (hCbd.trans (dissection_boundary_subset_edges hS hd))
    · rw [(hdiscimage Ψ hΨ).2.1, hEU]
      exact image_mono (hd.bd Ψ hΨ)
  have hint : ∀ Φ ∈ insert D ((image j) '' 𝓕),
      Disjoint (discInt Φ) (⋃₀ ((image j) '' E)) := by
    rintro Φ (rfl | ⟨Ψ, hΨ, rfl⟩)
    · rw [hEU]
      exact hDoff.mono_right (image_subset_range _ _)
    · rw [(hdiscimage Ψ hΨ).2.2, hEU]
      apply disjoint_left.mpr
      rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      exact disjoint_left.mp (hd.int Ψ hΨ) hx (hj.injective heq ▸ hy)
  have hdisj : ∀ Φ ∈ insert D ((image j) '' 𝓕),
      ∀ Ψ ∈ insert D ((image j) '' 𝓕), Φ ≠ Ψ → Disjoint (discInt Φ) Ψ := by
    rintro Φ (rfl | ⟨A, hA, rfl⟩) Ψ (rfl | ⟨B, hB, rfl⟩) hne
    · exact (hne rfl).elim
    · exact hDoff.mono_right (image_subset_range _ _)
    · exact hOldOff A hA
    · rw [(hdiscimage A hA).2.2]
      apply disjoint_left.mpr
      rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
      exact disjoint_left.mp (hd.disj A hA B hB (fun hh => hne (congrArg (image j) hh))) hx
        (hj.injective heq ▸ hy)
  have hcount : ∀ z ∉ j '' V, {Φ ∈ insert D ((image j) '' 𝓕) | z ∈ Φ}.encard ≤ 2 := by
    intro z hzV
    by_cases hzD : z ∈ D
    · let K := {Φ ∈ (image j) '' 𝓕 | z ∈ Φ}
      have hK : K.Subsingleton := by
        rintro Φ ⟨⟨A, hA, rfl⟩, x, hxA, hjx⟩ Ψ ⟨⟨B, hB, rfl⟩, y, hyB, hjy⟩
        have hxy : x = y := hj.injective (hjx.trans hjy.symm)
        have hxV : x ∉ V := fun hx => hzV ⟨x, hx, hjx⟩
        have hxC : x ∈ C := by
          obtain ⟨w, hwC, hjw⟩ := hcap.inter_eq.subset ⟨⟨x, hjx⟩, hzD⟩
          exact hj.injective (hjw.trans hjx.symm) ▸ hwC
        have hAB : A = B := dissection_faces_at_boundary_subsingleton hS hd (hCbd hxC) hxV
          ⟨hA, hxA⟩ ⟨hB, hxy.symm ▸ hyB⟩
        exact congrArg (image j) hAB
      have hsub : {Φ ∈ insert D ((image j) '' 𝓕) | z ∈ Φ} ⊆ insert D K := by
        rintro Φ ⟨hΦ, hzΦ⟩
        rcases hΦ with heq | hΦ
        · exact Or.inl heq
        · exact Or.inr ⟨hΦ, hzΦ⟩
      calc
        _ ≤ (insert D K).encard := encard_le_encard hsub
        _ ≤ K.encard + 1 := encard_insert_le K D
        _ ≤ 1 + 1 := add_le_add (encard_le_one_iff_subsingleton.mpr hK) le_rfl
        _ = 2 := by norm_num
    · have hzR : z ∈ range j := (hcap.union_eq.symm.subset (mem_univ z)).resolve_right hzD
      obtain ⟨x, rfl⟩ := hzR
      have hxV : x ∉ V := fun hx => hzV ⟨x, hx, rfl⟩
      have hsub : {Φ ∈ insert D ((image j) '' 𝓕) | j x ∈ Φ} ⊆
          (image j) '' {Φ ∈ 𝓕 | x ∈ Φ} := by
        rintro Φ ⟨(rfl | ⟨A, hA, rfl⟩), hxΦ⟩
        · exact (hzD hxΦ).elim
        · obtain ⟨y, hy, hxy⟩ := hxΦ
          exact ⟨A, ⟨hA, hj.injective hxy ▸ hy⟩, rfl⟩
      exact (encard_le_encard hsub).trans ((encard_image_le (image j) _).trans (hd.count x hxV))
  have hcapDis : IsDissection (j '' V) ((image j) '' E) (insert D ((image j) '' 𝓕)) := by
    refine ⟨hgraph, (hd.fin.image _).insert D, hdisc, ?_, hbd, hint, hdisj, hcount⟩
    rw [sUnion_insert, hImgCover, union_comm, hcap.union_eq]
  refine ⟨hcapDis, ?_⟩
  have hEcard : ((image j) '' E).ncard = E.ncard :=
    ncard_image_of_injective _ (image_injective.mpr hj.injective)
  have hFcard : (insert D ((image j) '' 𝓕)).ncard = 𝓕.ncard + 1 := by
    rw [ncard_insert_of_notMem hDnew (hd.fin.image _),
      ncard_image_of_injective _ (image_injective.mpr hj.injective)]
  have hVcard : ((j '' V) ∩ ⋃₀ ((image j) '' E)).ncard = (V ∩ ⋃₀ E).ncard := by
    rw [hEU, ← image_inter hj.injective, ncard_image_of_injective _ hj.injective]
  rw [hEcard, hFcard, hVcard]
  push_cast
  omega

end GraphMinor.GM08
