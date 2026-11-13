module

public import GraphMinor.GM21.Section6ClaimThreeRegion
import GraphMinor.GM11.RadialAccess
import GraphMinor.GM11.Corners
import GraphMinor.GM07.Section11
import GraphMinor.GM19.Perimeter
import GraphMinor.GM15.Section3Parallel

/-!
# Graph Minors XXI, (6.3), claim (3): a line through a region of `Γ⁺`

Claim (3) of the proof of (6.3) (page 29 of the preprint): "there is a region of $\Gamma$
incident with vertices in two different cuffs, and so there is a proper line $F$ with ends vertices
of $\Gamma$ in different cuffs, and with no internal point in $U(\Gamma)$."

This file proves the step "and so" (`exists_properLine_of_region`). Let `p` be a region of the
drawing `Γ⁺` in the capped surface `Σ̂` that meets the image of `Σ`, and let `x ≠ y` be vertices of `Γ` in
`bd(Σ)` whose images lie in the closure of `p`.
* `p` lies in `Σ`: the pasted discs are regions of `Γ⁺` (`cuffDisc_mem_R_capDrawing_plusDrawing`),
  and `p` is not one of them, since it meets `Σ`. So `p` misses `U(Γ) ∪ bd(Σ)`.
* A path enters `p` from each of `x` and `y` (`GM11.exists_access`; each vertex in `bd(Σ)` is an
  end of a space, which is an edge of `Γ⁺`). The open connected set `p` is path connected.
* The path from `x` to `y` through `p` lies in the image of `Σ`, so it comes from a path in `Σ`, and
  that path contains a line from `x` to `y`. Its inside points lie in `p`, so they miss `U(Γ)` and
  `bd(Σ)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace ClaimThree

open Set Function Topology GraphMinor.Surface GraphMinor.GM19 unitInterval

/-- A path inside the image of an embedding comes from a path in the domain. -/
theorem joinedIn_preimage_of_isEmbedding {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsEmbedding f) {Z : Set Y} (hZ : Z ⊆ range f) {a b : X}
    (h : JoinedIn Z (f a) (f b)) : JoinedIn (f ⁻¹' Z) a b := by
  choose δ hδ using fun t => hZ (h.somePath_mem t)
  have hc : Continuous δ := hf.continuous_iff.mpr (by
    have : f ∘ δ = h.somePath := funext hδ
    rw [this]
    exact h.somePath.continuous)
  have h0 : δ 0 = a := hf.injective ((hδ 0).trans h.somePath.source)
  have h1 : δ 1 = b := hf.injective ((hδ 1).trans h.somePath.target)
  refine ⟨⟨⟨δ, hc⟩, h0, h1⟩, fun t => ?_⟩
  change f (δ t) ∈ Z
  rw [hδ t]
  exact h.somePath_mem t

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-- Every vertex of `Γ` in `bd(Σ)` lies in the closure of a space of `Γ`: in its cuff, the vertices
of `Γ` are `vNode 0, …, vNode (k - 1)`, and the space `vSpaceArc i` starts at `vNode i`. -/
theorem exists_space_of_mem_bd (hS : IsSurface S) {Γ : Surface.Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {x : S} (hx : x ∈ Γ.V ∩ bd S) :
    ∃ s ∈ drawingSpaces Γ, x ∈ closure s := by
  have hC : connectedComponentIn (bd S) x ∈ cuffs S := ⟨x, hx.2, rfl⟩
  have hxC : x ∈ Γ.V ∩ connectedComponentIn (bd S) x := ⟨hx.1, mem_connectedComponentIn hx.2⟩
  rw [← Supports.range_vNode Γ.V Γ.finite_V (Supports.cuffHomeo hS hC)] at hxC
  obtain ⟨i, hi⟩ := hxC
  have h := Supports.spaceHasEnds_vSpaceArc hS hge2 hC (Supports.cuffHomeo hS hC) i
  refine ⟨_, h.1, ?_⟩
  rw [h.2.2.2.2.2, hi]
  exact Or.inr (Or.inl rfl)

/-- **A line through a region of `Γ⁺`** (Graph Minors XXI, proof of (6.3), claim (3), page 29 of the
preprint). Let `p` be a region of `Γ⁺` in `Σ̂` that meets the image of `Σ`, and let `x ≠ y` be
vertices of `Γ` in `bd(Σ)` whose images lie in the closure of `p`. Then there is a proper line in
`Σ` with ends `x, y` and no internal point in `U(Γ)`. -/
theorem exists_properLine_of_region (hS : IsSurface S) (cap : IsCappedSurface S Shat)
    {Γ : Surface.Drawing S} (hprop : Γ.IsProper) (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard)
    {p : Set Shat} (hp : p ∈ (capDrawing hS cap (plusDrawing hS Γ hprop hge2)).R)
    {z : S} (hzp : cap.emb z ∈ p) {x y : S} (hx : x ∈ Γ.V ∩ bd S)
    (hy : y ∈ Γ.V ∩ bd S) (hxy : x ≠ y) (hxp : cap.emb x ∈ closure p)
    (hyp : cap.emb y ∈ closure p) :
    ∃ F : Set S, IsProperLineInSurface F x y ∧ F ∩ Γ.U ⊆ {x, y} := by
  have : T2Space S := hS.2.1
  have hcs := cap.isClosedSurface
  have : T2Space Shat := hcs.2.1
  have : LocallyConnectedSpace Shat := GM11.IsClosedSurface.locallyConnectedSpace hcs
  have : Nonempty Shat := ⟨cap.emb z⟩
  have hinj := cap.isEmbedding.injective
  set D := capDrawing hS cap (plusDrawing hS Γ hprop hge2)
  -- `p` lies in the image of `Σ`, and misses the images of `U(Γ)` and `bd(Σ)`.
  have hprange : p ⊆ range cap.emb := by
    intro w hw
    by_contra hwr
    have hw' : w ∈ (range cap.emb)ᶜ := hwr
    rw [cap.compl_eq] at hw'
    obtain ⟨C, hC, hwC⟩ := mem_iUnion₂.mp hw'
    have hR := cuffDisc_mem_R_capDrawing_plusDrawing hS cap Γ hprop hge2 hC
    have hpC : p = cap.cuffDisc C := GM11.region_eq_of_mem hp hR hw hwC
    exact cap.notMem_range hC (hpC ▸ hzp) (mem_range_self z)
  have hpU : ∀ w, cap.emb w ∈ p → w ∉ Γ.U ∧ w ∉ bd S := by
    intro w hw
    have h := GM11.region_subset hp hw
    rw [capDrawing_U, plusDrawing_U] at h
    exact ⟨fun h' => h ⟨w, Or.inl h', rfl⟩, fun h' => h ⟨w, Or.inr h', rfl⟩⟩
  -- A path enters `p` from each end.
  obtain ⟨γ, hγ⟩ := GM11.exists_edgePar D
  have haccess : ∀ v ∈ Γ.V ∩ bd S, cap.emb v ∈ closure p →
      JoinedIn ({cap.emb v} ∪ p) (cap.emb v) (cap.emb z) := by
    intro v hv hvp
    obtain ⟨s, hs, hvs⟩ := exists_space_of_mem_bd hS hge2 hv
    have hsE := emb_mem_E_of_mem_drawingSpaces hS cap hprop hge2 hs
    have hvD : cap.emb v ∈ D.V := by
      rw [capDrawing_V, plusDrawing_V]
      exact mem_image_of_mem _ hv.1
    have hvcl : cap.emb v ∈ closure (cap.emb '' s) := by
      rw [closure_emb_image hS cap]
      exact mem_image_of_mem _ hvs
    obtain ⟨b, hb⟩ := GM11.exists_end_eq hγ hsE hvD hvcl
    obtain ⟨g, hg, hg0, hgp⟩ := GM11.exists_access hcs D hγ hvD ⟨(_, b), hsE, hb⟩ hp hvp
    have h₁ : JoinedIn ({cap.emb v} ∪ p) (cap.emb v) (g 1) := by
      refine ⟨⟨⟨g, hg⟩, hg0, rfl⟩, fun t => ?_⟩
      rcases eq_or_lt_of_le (t.2.1 : (0 : ℝ) ≤ t) with h | h
      · have : t = 0 := Subtype.ext h.symm
        change g t ∈ _
        rw [this, hg0]
        exact Or.inl rfl
      · exact Or.inr (hgp t h)
    have hpc : IsPathConnected p := GM11.isPathConnected_of_isOpen hcs (GM11.region_isOpen hp)
      (GM11.region_isPreconnected hp) ⟨_, hzp⟩
    exact h₁.trans ((hpc.joinedIn _ (hgp 1 (by simp)) _ hzp).mono subset_union_right)
  have hZ : JoinedIn (p ∪ {cap.emb x, cap.emb y}) (cap.emb x) (cap.emb y) := by
    refine ((haccess x hx hxp).mono ?_).trans ((haccess y hy hyp).mono ?_).symm
    · rintro w (rfl | hw)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hw
    · rintro w (rfl | hw)
      · exact Or.inr (Or.inr rfl)
      · exact Or.inl hw
  have hZr : p ∪ {cap.emb x, cap.emb y} ⊆ range cap.emb := by
    rintro w (hw | rfl | hw)
    · exact hprange hw
    · exact mem_range_self x
    · exact (mem_singleton_iff.mp hw) ▸ mem_range_self y
  have hJ := joinedIn_preimage_of_isEmbedding cap.isEmbedding hZr hZ
  obtain ⟨F, hFZ, hF⟩ := ((GM07.joinedIn_iff_eq_or_exists_isLineWithEnds hJ.source_mem
    hJ.target_mem).mp hJ).resolve_left hxy
  -- The inside points of `F` lie in the preimage of `p`.
  have hin : ∀ w ∈ F, w ∉ ({x, y} : Set S) → cap.emb w ∈ p := by
    intro w hw hwxy
    rcases hFZ hw with h | h | h
    · exact h
    · exact (hwxy (Or.inl (hinj h))).elim
    · exact (hwxy (Or.inr (hinj (mem_singleton_iff.mp h)))).elim
  refine ⟨F, ⟨hF, hx.2, hy.2, disjoint_left.mpr fun w hw hwb => (hpU w (hin w hw.1 hw.2)).2 hwb⟩,
    fun w hw => ?_⟩
  by_contra hwxy
  exact (hpU w (hin w hw.1 hwxy)).1 hw.2

end ClaimThree
end GM21
end GraphMinor
