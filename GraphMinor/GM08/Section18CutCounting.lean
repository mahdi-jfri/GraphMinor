module

public import GraphMinor.Surface.TopologyStatements

/-!
# Counting the lifts of a cut along a circle or a line

A cut along `G` with two lifts over each point of `G` is one to one off `G`.
So a finite set `B` has `|B| + |B ∩ G|` lifts (`IsCutting.ncard_preimage`).
The cuts of (18.2) for schisms of types (iv) and (v), page 286, are made one
arc at a time, and adding these counts gives the lift counts that the cut
step of (18.3) needs.
-/

@[expose] public section

namespace GraphMinor.GM08

universe w

open Set GraphMinor.Surface

/-- If every fibre over a finite set `A` has exactly `c > 0` points, the
preimage of `A` has `c |A|` points. -/
theorem ncard_preimage_eq_mul {X Y : Type*} (ψ : Y → X) {A : Set X} (hA : A.Finite) {c : ℕ}
    (hc : 0 < c) (h : ∀ x ∈ A, (ψ ⁻¹' {x}).ncard = c) : (ψ ⁻¹' A).ncard = c * A.ncard := by
  induction A, hA using Set.Finite.induction_on with
  | empty => simp
  | @insert a s ha hs ih =>
    have hfa : (ψ ⁻¹' {a}).Finite :=
      Set.finite_of_ncard_pos ((h a (mem_insert _ _)).symm ▸ hc)
    have hfs : (ψ ⁻¹' s).Finite := hs.preimage' fun x hx =>
      Set.finite_of_ncard_pos ((h x (mem_insert_of_mem _ hx)).symm ▸ hc)
    have hdis : Disjoint (ψ ⁻¹' {a}) (ψ ⁻¹' s) :=
      (disjoint_singleton_left.mpr ha).preimage ψ
    rw [ncard_insert_of_notMem ha hs, insert_eq, preimage_union, ncard_union_eq hdis hfa hfs,
      h a (mem_insert _ _), ih fun x hx => h x (mem_insert_of_mem _ hx)]
    ring

/-- **The lifts of a finite set under a cut.** A finite set `B` has
`|B| + |B ∩ G|` lifts under a cut along `G`. -/
theorem IsCutting.ncard_preimage {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    {ψ : T → S} {G : Set S} (hc : IsCutting ψ G) {B : Set S} (hB : B.Finite) :
    (ψ ⁻¹' B).ncard = B.ncard + (B ∩ G).ncard := by
  have hsplit : ψ ⁻¹' B = ψ ⁻¹' (B \ G) ∪ ψ ⁻¹' (B ∩ G) := by
    rw [← preimage_union, diff_union_inter]
  have hdis : Disjoint (ψ ⁻¹' (B \ G)) (ψ ⁻¹' (B ∩ G)) :=
    (disjoint_sdiff_inter (s := B) (t := G)).preimage ψ
  have hinj : InjOn ψ (ψ ⁻¹' (B \ G)) := fun x hx y hy hxy =>
    hc.2.2.1 (show ψ x ∈ Gᶜ from hx.2) (show ψ y ∈ Gᶜ from hy.2) hxy
  have himg : ψ '' (ψ ⁻¹' (B \ G)) = B \ G := image_preimage_eq _ hc.2.1
  have hf₁ : (ψ ⁻¹' (B \ G)).Finite :=
    Set.Finite.of_finite_image (by rw [himg]; exact hB.diff) hinj
  have h₂ : (ψ ⁻¹' (B ∩ G)).ncard = 2 * (B ∩ G).ncard :=
    ncard_preimage_eq_mul ψ (hB.inter_of_left G) two_pos fun x hx => hc.2.2.2.1 x hx.2
  have hf₂ : (ψ ⁻¹' (B ∩ G)).Finite := (hB.inter_of_left G).preimage' fun x hx =>
    Set.finite_of_ncard_pos ((hc.2.2.2.1 x hx.2).symm ▸ two_pos)
  rw [hsplit, ncard_union_eq hdis hf₁ hf₂, h₂, ← hinj.ncard_image, himg,
    ← ncard_inter_add_ncard_sdiff_eq_ncard B G hB]
  ring

end GraphMinor.GM08
