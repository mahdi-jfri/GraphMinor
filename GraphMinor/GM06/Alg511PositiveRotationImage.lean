module

public import GraphMinor.GM06.Alg511PositivePolarReflection
public import GraphMinor.GM06.Alg511PolarTransport
import Mathlib.Tactic

/-!
# Reversed positive rotations in the reflected sphere drawing

The orientation step of VI (5.11), page 134, reverses the order
of the actual edge ends at each vertex. Carry the drawing and edge
curves by the concrete plane reflection. Mirror the parameter disc
of each old chart, choosing its phase from the row's extreme angles.
The resulting chart has positive boundary winding and interprets
the reversed row. Edge indices and parameter directions stay fixed
in this lemma. Reversing the prescribed cuff parameters then changes
only their directed labels, with this same positive chart retained.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Concrete plane reflection realizes the reversed positive row
with exactly the same labelled original edge parameters. Both ends
of a loop remain distinct under the half-edge bijection. -/
theorem alg511_positive_rotation_image (phase : ℝ)
    {Γ : Drawing (OnePoint EuclideanPlane)} {m : ℕ}
    {edge : Fin m ≃ Γ.E} {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) :
    GM06SuccessorRotationRowRep
      (edge.trans (alg511ImageEdgeEquiv (alg511PlaneReflection phase).onePointCongr Γ))
      (alg511ImageEdgePar (alg511PlaneReflection phase).onePointCongr γ)
      ((alg511PlaneReflection phase).onePointCongr v) xs.reverse := by
  let H := (alg511PlaneReflection phase).onePointCongr
  let edge' := edge.trans (alg511ImageEdgeEquiv H Γ)
  let η := alg511ImageHalfEdges H Γ γ v
  have hlabel (a : halfEdges Γ γ v) : halfEdgeLabel edge' (η a) = halfEdgeLabel edge a :=
    alg511ImageHalfEdges_label H edge γ v a
  obtain ⟨hnd, hmem, horder⟩ := hrow
  refine ⟨List.nodup_reverse.mpr hnd, ?_, ?_⟩
  · intro r
    constructor
    · intro hr
      obtain ⟨a, ha⟩ := (hmem r).mp (List.mem_reverse.mp hr)
      exact ⟨η a, (hlabel a).trans ha⟩
    · rintro ⟨a', ha'⟩
      obtain ⟨a, rfl⟩ := η.surjective a'
      exact List.mem_reverse.mpr ((hmem r).mpr ⟨a, (hlabel a).symm.trans ha'⟩)
  · rcases horder with hshort | ⟨Φ, z, hp, hpos, hzi, hs, hspoke, hrim⟩
    · exact Or.inl (by simpa only [List.length_reverse] using hshort)
    · obtain ⟨a, ha⟩ := alg511_exists_row_mirror_phase xs z
      let M := alg511AngularMirror a
      have hMM (w : Circle) : M (M w) = w := (alg511AngularMirror a).left_inv w
      let Φd : C(ClosedUnitDisc, OnePoint EuclideanPlane) :=
        Φ.comp ⟨alg511DiscMirror a, (alg511DiscMirror a).continuous⟩
      let Ψ := alg511ImagePolarChart H Φd
      have hp' : IsPolar (GM07.embedDrawing H.isClosedEmbedding Γ) (H v) Ψ :=
        alg511_isPolar_image H (alg511_isPolar_comp_discMirror hp a)
      have hpos' : GM06PositivePolar Ψ := alg511_positivePolar_reflection hpos hp.inj phase a
      refine Or.inr ⟨Ψ, fun r => M (z r), hp', hpos', ?_,
        alg511_pairwise_reverse_angles xs z a ha hs, ?_, ?_⟩
      · intro r hr s hs heq
        exact hzi (List.mem_reverse.mp hr) (List.mem_reverse.mp hs) (M.injective heq)
      · intro a' t ht
        obtain ⟨e, rfl⟩ := η.surjective a'
        have heq : Ψ (polarDiscPoint t (M (z (halfEdgeLabel edge' (η e))))) =
            H (Φ (polarDiscPoint t (z (halfEdgeLabel edge e)))) := by
          change H (Φ (alg511DiscMirror a (polarDiscPoint t (M (z (halfEdgeLabel edge' (η e))))))) = _
          rw [hlabel, alg511DiscMirror_polarDiscPoint]
          change H (Φ (polarDiscPoint t (M (M (z (halfEdgeLabel edge e)))))) = _
          rw [hMM]
        rw [heq]
        obtain ⟨u, hu⟩ := hspoke e t ht
        refine ⟨u, ?_⟩
        rw [alg511ImageHalfEdges_spoke]
        exact congrArg H hu
      · intro j w
        change H (Φ (alg511DiscMirror a (polarDiscPoint 1 w))) ∈ H '' (edge j).val ↔
          ∃ r ∈ xs.reverse, M (z r) = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1)
        rw [alg511DiscMirror_polarDiscPoint, H.injective.mem_set_image]
        change polarRimMap Φ (M w) ∈ (edge j).val ↔ _
        rw [hrim]
        constructor
        · rintro ⟨r, hr, hz, hend⟩
          exact ⟨r, List.mem_reverse.mpr hr, by rw [hz, hMM], hend⟩
        · rintro ⟨r, hr, hz, hend⟩
          have hh := congrArg M hz
          rw [hMM] at hh
          exact ⟨r, List.mem_reverse.mp hr, hh, hend⟩

end GraphMinor.GM06
