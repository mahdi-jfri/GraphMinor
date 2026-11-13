module

public import GraphMinor.GM08.Section18CutCounting
public import GraphMinor.GM08.Section18CutSum
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section18Theorem182

/-!
# Two cuts in a row, with lift counts

The cut along a schism of type (iv) or (v) (VIII (18.2), page 286) is made one
arc at a time. Each step is a cut with exactly two lifts over each point of
the arc. Here we put two such steps together:
- two cuts along disjoint sets make one cut with two lifts everywhere
  (`IsCutting.comp_of_disjoint`);
- a cut along `G₁` followed by a cut along a closed set `G₂` over `H` is a cut
  along `G₁ ∪ H` (`isCutAlongSet_comp`, `isCutMap_comp`);
- every point of `G₁ ∪ H` then has at least two lifts, and a finite set `B`
  has at most `|B| + |B ∩ G₁| + |B ∩ H|` lifts (`lifts_comp`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

variable {S T₁ T₂ : Type w} [TopologicalSpace S] [TopologicalSpace T₁] [TopologicalSpace T₂]

/-- **Two cuts along disjoint sets.** A cut along `G₁`, and then a cut along
the lift of a closed set `G` that misses `G₁`, is a cut along `G₁ ∪ G` with two
lifts over each point. -/
theorem IsCutting.comp_of_disjoint [CompactSpace T₂] [T2Space T₁] {ψ₁ : T₁ → S} {ψ₂ : T₂ → T₁}
    {G₁ G : Set S} (h₁ : IsCutting ψ₁ G₁) (h₂ : IsCutting ψ₂ (ψ₁ ⁻¹' G)) (hG : IsClosed G)
    (hdis : Disjoint G₁ G) : IsCutting (ψ₁ ∘ ψ₂) (G₁ ∪ G) := by
  have hGc : IsClosed (ψ₁ ⁻¹' G) := hG.preimage h₁.1
  refine ⟨h₁.1.comp h₂.1, h₁.2.1.comp h₂.2.1, ?_, fun x hx => ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : ψ₁ (ψ₂ a) ∉ G₁ ∪ G := ha
    have hb' : ψ₁ (ψ₂ b) ∉ G₁ ∪ G := hb
    exact h₂.2.2.1 (fun h => ha' (Or.inr h)) (fun h => hb' (Or.inr h))
      (h₁.2.2.1 (fun h => ha' (Or.inl h)) (fun h => hb' (Or.inl h)) hab)
  · have hpre : (ψ₁ ∘ ψ₂) ⁻¹' {x} = ψ₂ ⁻¹' (ψ₁ ⁻¹' {x}) := rfl
    have hfin : (ψ₁ ⁻¹' {x}).Finite := (GM19.IsCutting.isCutMap h₁).2.2.2.1 x
    rw [hpre, IsCutting.ncard_preimage h₂ hfin]
    rcases hx with hx | hx
    · have : ψ₁ ⁻¹' {x} ∩ ψ₁ ⁻¹' G = ∅ := by
        rw [← preimage_inter, (disjoint_left.mp hdis hx |> fun h =>
          (show {x} ∩ G = ∅ from by simpa using h))]
        rfl
      rw [this, h₁.2.2.2.1 x hx, ncard_empty]
    · have hx₁ : x ∉ G₁ := disjoint_right.mp hdis hx
      have hsub : ψ₁ ⁻¹' {x} ∩ ψ₁ ⁻¹' G = ψ₁ ⁻¹' {x} := by
        refine inter_eq_left.mpr fun z hz => ?_
        rw [mem_preimage, mem_singleton_iff.mp hz]
        exact hx
      obtain ⟨z, hz⟩ := h₁.2.1 x
      have hone : ψ₁ ⁻¹' {x} = {z} := by
        ext y
        refine ⟨fun hy => ?_, fun hy => by rw [mem_singleton_iff.mp hy]; exact hz⟩
        exact h₁.2.2.1 (show ψ₁ y ∈ G₁ᶜ by rw [mem_preimage.mp hy]; exact hx₁)
          (show ψ₁ z ∈ G₁ᶜ by rw [hz]; exact hx₁) (hy.trans hz.symm)
      rw [hsub, hone, ncard_singleton]
  · rintro z (hz | hz)
    · by_cases hzG : ψ₂ z ∈ ψ₁ ⁻¹' G
      · exact h₂.2.2.2.2 hzG
      · exact bd_lift_cutMap (GM19.IsCutting.isCutMap h₂) hGc (h₁.2.2.2.2 hz) hzG
    · exact h₂.2.2.2.2 hz

/-- A cut along a set `G` is a cut along any set with the same union with the
boundary. -/
theorem isCutAlongSet_congr_bd {θ : T₁ → S} {G G' : Set S} (h : GM07.IsCutAlongSet G θ)
    (heq : bd S ∪ G = bd S ∪ G') : GM07.IsCutAlongSet G' θ :=
  ⟨h.isSurface, h.quotientMap, heq ▸ h.preimage_bd, h.interior_inj, h.finite_fiber⟩

/-- **A cut along `G₁`, then along `G₂` over `H`.** If the closed set `G₂`
lies over `H`, and covers the lift of `H` off the boundary, the two cuts make
a cut along `G₁ ∪ H`. -/
theorem isCutAlongSet_comp (hS : IsSurface S) (hT₁ : IsSurface T₁) (hT₂ : IsSurface T₂)
    {ψ₁ : T₁ → S} {ψ₂ : T₂ → T₁} {G₁ H : Set S} {G₂ : Set T₁} (h₁ : IsCutting ψ₁ G₁)
    (hG₁ : IsClosed G₁) (h₂ : IsCutting ψ₂ G₂) (hG₂ : IsClosed G₂) (hG₂H : G₂ ⊆ ψ₁ ⁻¹' H)
    (hH : ψ₁ ⁻¹' H ⊆ G₂ ∪ bd T₁) : GM07.IsCutAlongSet (G₁ ∪ H) (ψ₁ ∘ ψ₂) := by
  have hc₁ := isCutAlongSet_of_isCutting hS hT₁ hG₁ h₁
  have hc₂ := isCutAlongSet_of_isCutting hT₁ hT₂ hG₂ h₂
  refine hc₁.comp (isCutAlongSet_congr_bd hc₂ ?_)
  apply subset_antisymm
  · rintro z (hz | hz)
    · exact Or.inl hz
    · exact Or.inr (hG₂H hz)
  · rintro z (hz | hz)
    · exact Or.inl hz
    · exact (hH hz).elim Or.inr Or.inl

/-- The same two cuts make a cut map along `G₁ ∪ H`. -/
theorem isCutMap_comp (hT₁ : IsSurface T₁) (hT₂ : IsSurface T₂)
    {ψ₁ : T₁ → S} {ψ₂ : T₂ → T₁} {G₁ H : Set S} {G₂ : Set T₁} (h₁ : IsCutting ψ₁ G₁)
    (h₂ : IsCutting ψ₂ G₂) (hG₂ : IsClosed G₂) (hG₂H : G₂ ⊆ ψ₁ ⁻¹' H)
    (hH : ψ₁ ⁻¹' H ⊆ G₂ ∪ bd T₁) : GM19.IsCutMap (ψ₁ ∘ ψ₂) (G₁ ∪ H) := by
  have : CompactSpace T₂ := hT₂.1
  have : T2Space T₁ := hT₁.2.1
  exact IsCutMap.comp (GM19.IsCutting.isCutMap h₁) (GM19.IsCutting.isCutMap h₂) hG₂ hG₂H hH

/-- **The lifts of two cuts in a row.** If `ψ₁` is one to one on `G₂`, `G₂`
lies over `H`, and `G₂` holds every lift of a point of `H` off `G₁`, then every
point of `G₁ ∪ H` has at least two lifts, and a finite set `B` has at most
`|B| + |B ∩ G₁| + |B ∩ H|` lifts. -/
theorem lifts_comp {ψ₁ : T₁ → S} {ψ₂ : T₂ → T₁} {G₁ H : Set S} {G₂ : Set T₁}
    (h₁ : IsCutting ψ₁ G₁) (h₂ : IsCutting ψ₂ G₂) (hinj : InjOn ψ₁ G₂) (hG₂H : G₂ ⊆ ψ₁ ⁻¹' H)
    (hHG₂ : ψ₁ ⁻¹' (H \ G₁) ⊆ G₂) :
    (∀ x ∈ G₁ ∪ H, 1 < ((ψ₁ ∘ ψ₂) ⁻¹' {x}).ncard) ∧
      ∀ B : Set S, B.Finite →
        ((ψ₁ ∘ ψ₂) ⁻¹' B).ncard ≤ B.ncard + (B ∩ G₁).ncard + (B ∩ H).ncard := by
  have hfib := (GM19.IsCutting.isCutMap h₁).2.2.2.1
  have hpre : ∀ B : Set S, B.Finite → ((ψ₁ ∘ ψ₂) ⁻¹' B).ncard =
      (ψ₁ ⁻¹' B).ncard + (ψ₁ ⁻¹' B ∩ G₂).ncard := fun B hB =>
    IsCutting.ncard_preimage h₂ (hB.preimage' fun b _ => hfib b)
  refine ⟨fun x hx => ?_, fun B hB => ?_⟩
  · rw [hpre _ (finite_singleton x)]
    by_cases hx₁ : x ∈ G₁
    · rw [h₁.2.2.2.1 x hx₁]
      omega
    · have hxH : x ∈ H := hx.resolve_left hx₁
      obtain ⟨z, hz⟩ := h₁.2.1 x
      have hzG : z ∈ ψ₁ ⁻¹' {x} ∩ G₂ := ⟨hz, hHG₂ (show ψ₁ z ∈ H \ G₁ by rw [hz]; exact ⟨hxH, hx₁⟩)⟩
      have h1 : 0 < (ψ₁ ⁻¹' {x}).ncard :=
        (ncard_pos (hfib x)).mpr ⟨z, hz⟩
      have h2 : 0 < (ψ₁ ⁻¹' {x} ∩ G₂).ncard :=
        (ncard_pos ((hfib x).subset inter_subset_left)).mpr ⟨z, hzG⟩
      omega
  · rw [hpre B hB, IsCutting.ncard_preimage h₁ hB]
    have : (ψ₁ ⁻¹' B ∩ G₂).ncard ≤ (B ∩ H).ncard :=
      ncard_le_ncard_of_injOn ψ₁ (fun z hz => ⟨hz.1, hG₂H hz.2⟩) (hinj.mono inter_subset_right)
        (hB.subset inter_subset_left)
    omega

omit [TopologicalSpace S] in
/-- With `G₁ ∩ H` of at most two points, the bound of
`lifts_comp` is at most `2 |B| + 2`. -/
theorem ncard_bound_of_inter {B G₁ H : Set S} (hB : B.Finite)
    (hGH : (G₁ ∩ H).Finite) (h2 : (G₁ ∩ H).ncard ≤ 2) :
    B.ncard + (B ∩ G₁).ncard + (B ∩ H).ncard ≤ 2 * B.ncard + 2 := by
  have h := ncard_union_add_ncard_inter (B ∩ G₁) (B ∩ H) (hB.subset inter_subset_left)
    (hB.subset inter_subset_left)
  have hu : (B ∩ G₁ ∪ B ∩ H).ncard ≤ B.ncard :=
    ncard_le_ncard (union_subset inter_subset_left inter_subset_left) hB
  have hi : (B ∩ G₁ ∩ (B ∩ H)).ncard ≤ 2 :=
    (ncard_le_ncard (show B ∩ G₁ ∩ (B ∩ H) ⊆ G₁ ∩ H from fun z hz => ⟨hz.1.2, hz.2.2⟩) hGH).trans h2
  omega

end GraphMinor.GM08
