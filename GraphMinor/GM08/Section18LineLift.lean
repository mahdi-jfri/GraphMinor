module

public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section18CutClosure
import GraphMinor.GM19.PullLift

/-!
# Lifting an edge that is not cut

The open part of an uncut edge lies off the cutting set. An interval is
connected near each end, so the closure of its lift maps homeomorphically
onto the edge. Its two ends are exactly the points over the old ends.
This constructs the uncut edges in the dissection for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM19

private theorem connected_near_line_ends {S : Type w} [TopologicalSpace S] [T2Space S]
    {e : Set S} {u v : S} (he_diff : closure e \ {u, v} = e)
    (hL : IsLineWithEnds (closure e) u v) {w : S} (hw : w ∈ tilde e) :
    GM19.IsConnectedNear e w := by
  obtain ⟨f, hf0, hf1⟩ := hL
  let T : Set (Icc (0 : ℝ) 1) := {(0 : Icc (0 : ℝ) 1), (1 : Icc (0 : ℝ) 1)}
  have hT_fin : T.Finite := (finite_singleton _).insert _
  have himg : (fun t : Icc (0 : ℝ) 1 => (f t).1) '' Tᶜ = e := by
    apply Eq.trans _ he_diff
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(f t).2, ?_⟩
      rintro (hxu | hxv)
      · apply ht; left
        exact f.injective (Subtype.ext (hxu.trans hf0.symm))
      · apply ht; right
        exact f.injective (Subtype.ext (hxv.trans hf1.symm))
    · rintro ⟨hxcl, hxuv⟩
      refine ⟨f.symm ⟨x, hxcl⟩, ?_, by simp⟩
      rintro (h0 | h1)
      · apply hxuv; left
        have := congrArg (fun t => (f t).1) h0
        simpa [hf0] using this
      · apply hxuv; right
        have := congrArg (fun t => (f t).1) (mem_singleton_iff.mp h1)
        simpa [hf1] using this
  have hw_uv : w = u ∨ w = v := by
    by_contra hnot
    have hwe : w ∈ e := by
      rw [← he_diff]
      exact ⟨hw.1, hnot⟩
    exact hw.2 hwe
  rcases hw_uv with rfl | rfl
  · have h0 : ∀ W ∈ 𝓝 (0 : Icc (0 : ℝ) 1),
        ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 (0 : Icc (0 : ℝ) 1), Tᶜ ∩ W' ⊆ B := by
      refine GM19.connected_near_extreme (convex_Icc (0 : ℝ) 1) ?_ hT_fin (Or.inl rfl)
      have h_eq : Icc (0 : ℝ) 1 \ {((0 : Icc (0 : ℝ) 1) : ℝ)} = Ioc (0 : ℝ) 1 := Icc_sdiff_left
      rw [h_eq]
      exact convex_Ioc (0 : ℝ) 1
    have h := GM19.isConnectedNear_of_homeo f h0
    rwa [himg, hf0] at h
  · have h1 : ∀ W ∈ 𝓝 (1 : Icc (0 : ℝ) 1),
        ∃ B ⊆ Tᶜ ∩ W, IsPreconnected B ∧ ∃ W' ∈ 𝓝 (1 : Icc (0 : ℝ) 1), Tᶜ ∩ W' ⊆ B := by
      refine GM19.connected_near_extreme (convex_Icc (0 : ℝ) 1) ?_ hT_fin (Or.inr rfl)
      have h_eq : Icc (0 : ℝ) 1 \ {((1 : Icc (0 : ℝ) 1) : ℝ)} = Ico (0 : ℝ) 1 := Icc_sdiff_right
      rw [h_eq]
      exact convex_Ico (0 : ℝ) 1
    have h := GM19.isConnectedNear_of_homeo f h1
    rwa [himg, hf1] at h

/-- An uncut edge lifts to one line with the corresponding ends. The
open lifted edge is exactly the preimage of the old open edge. This is
the uncut-edge step in the Euler proof of VIII (18.2), page 286. -/
theorem exists_line_closure_lift_of_cutMap {Y S : Type w} [TopologicalSpace Y]
    [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F L : Set S} {u v : S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (hL : IsLineWithEnds L u v) (hoff : Disjoint (L \ {u, v}) F) :
    ∃ x y, ψ x = u ∧ ψ y = v ∧
      IsLineWithEnds (closure (ψ ⁻¹' (L \ {u, v}))) x y ∧
      BijOn ψ (closure (ψ ⁻¹' (L \ {u, v}))) L ∧
      closure (ψ ⁻¹' (L \ {u, v})) \ {x, y} = ψ ⁻¹' (L \ {u, v}) := by
  let A := L \ {u, v}
  let Z := closure (ψ ⁻¹' A)
  have hcl : closure A = L :=
    (closure_minimal sdiff_subset hL.isCompact.isClosed).antisymm hL.subset_closure_diff
  have hAdiff : closure A \ {u, v} = A := by rw [hcl]
  have hline : IsLineWithEnds (closure A) u v := hcl.symm ▸ hL
  have hA : A ⊆ Fᶜ := fun z hz => disjoint_left.mp hoff hz
  obtain ⟨H₀, hH₀⟩ := exists_homeo_closure_lift_of_cutMap hcm hF hA
    (fun w hw => connected_near_line_ends hAdiff hline hw)
  let H : Z ≃ₜ L := H₀.trans (Homeomorph.setCongr hcl)
  have hpoint : ∀ z : Z, (H z).1 = ψ z.1 := hH₀
  obtain ⟨a, ha0, ha1⟩ := hL
  let J : unitInterval ≃ₜ Z := a.trans H.symm
  let x := (J 0).1
  let y := (J 1).1
  have hψx : ψ x = u := by
    rw [← hpoint (J 0)]
    change (H (H.symm (a 0))).1 = u
    rw [H.apply_symm_apply]
    exact ha0
  have hψy : ψ y = v := by
    rw [← hpoint (J 1)]
    change (H (H.symm (a 1))).1 = v
    rw [H.apply_symm_apply]
    exact ha1
  have hinj : InjOn ψ Z := by
    intro z hz w hw heq
    exact congrArg Subtype.val (H.injective (Subtype.ext
      ((hpoint ⟨z, hz⟩).trans (heq.trans (hpoint ⟨w, hw⟩).symm))))
  have hmap : MapsTo ψ Z L := fun z hz => hpoint ⟨z, hz⟩ ▸ (H ⟨z, hz⟩).2
  have hsur : SurjOn ψ Z L := by
    intro z hz
    obtain ⟨w, hw⟩ := H.surjective ⟨z, hz⟩
    exact ⟨w.1, w.2, (hpoint w).symm.trans (congrArg Subtype.val hw)⟩
  have hopen : Z \ {x, y} = ψ ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨hz, hzends⟩
      refine ⟨hmap hz, ?_⟩
      rintro (hzu | hzv)
      · exact hzends (Or.inl (hinj hz (J 0).2 (hzu.trans hψx.symm)))
      · exact hzends (Or.inr (hinj hz (J 1).2 (hzv.trans hψy.symm)))
    · intro hz
      refine ⟨subset_closure hz, ?_⟩
      rintro (rfl | rfl)
      · exact hz.2 (Or.inl hψx)
      · exact hz.2 (Or.inr hψy)
  exact ⟨x, y, hψx, hψy, ⟨J, rfl, rfl⟩, ⟨hmap, hinj, hsur⟩, hopen⟩

end GraphMinor.GM08
