module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Affine
import Mathlib.Tactic.FunProp

/-!
# Intersections in a finite segment arrangement

Part IV, Section 7a of the planarity note splits segments at isolated
intersections and at the ends of collinear overlaps. The intersection of
two segments is empty or another segment, possibly reduced to one point.
This follows by pulling the intersection back to the parameter interval
of one segment. The preimage is compact and convex, hence a closed interval.
-/

public section
namespace GraphMinor.LRPlanarity

open Set

/-- The intersection step in the finite segment arrangement of Part IV,
Section 7a. A nonempty intersection has two ends, allowing coincident ends
when the intersection is an isolated point. -/
theorem segment_inter_eq_segment {a b c d : ℂ}
    (hne : (segment ℝ a b ∩ segment ℝ c d).Nonempty) :
    ∃ x y : ℂ, segment ℝ a b ∩ segment ℝ c d = segment ℝ x y := by
  let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
  have hfc : Continuous f := AffineMap.lineMap_continuous
  have hgc : Continuous (AffineMap.lineMap c d : ℝ →ᵃ[ℝ] ℂ) :=
    AffineMap.lineMap_continuous
  have hsegc : IsClosed (segment ℝ c d) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image hgc).isClosed
  let K : Set ℝ := Icc 0 1 ∩ f ⁻¹' segment ℝ c d
  have hK : IsCompact K := isCompact_Icc.inter_right (hsegc.preimage hfc)
  have hconv : Convex ℝ K :=
    (convex_Icc _ _).inter (Convex.affine_preimage f (convex_segment c d))
  have himg : f '' K = segment ℝ a b ∩ segment ℝ c d := by
    change f '' (Icc 0 1 ∩ f ⁻¹' segment ℝ c d) = _
    rw [image_inter_preimage]
    rw [show f '' Icc 0 1 = segment ℝ a b from
      (segment_eq_image_lineMap ℝ a b).symm]
  have hKn : K.Nonempty := image_nonempty.mp (himg.symm ▸ hne)
  have hinterval : K = Icc (sInf K) (sSup K) :=
    eq_Icc_of_connected_compact ⟨hKn, Real.convex_iff_isPreconnected.mp hconv⟩ hK
  have hle : sInf K ≤ sSup K := csInf_le hK.bddBelow (hK.sSup_mem hKn)
  refine ⟨f (sInf K), f (sSup K), ?_⟩
  calc
    segment ℝ a b ∩ segment ℝ c d = f '' K := himg.symm
    _ = f '' Icc (sInf K) (sSup K) := congrArg (fun T : Set ℝ => f '' T) hinterval
    _ = f '' segment ℝ (sInf K) (sSup K) := by rw [segment_eq_Icc hle]
    _ = segment ℝ (f (sInf K)) (f (sSup K)) := image_segment ℝ f _ _

/-- A compact connected part of a straight segment is another straight
segment. This keeps pieces straight when the arrangement is split at a
new vertex in Part IV, Section 7a. -/
theorem compact_connected_subset_segment {C : Set ℂ} {a b : ℂ}
    (hC : IsCompact C) (hconn : IsPreconnected C) (hne : C.Nonempty)
    (hsub : C ⊆ segment ℝ a b) :
    ∃ x y : ℂ, C = segment ℝ x y := by
  by_cases hab : a = b
  · subst b
    rw [segment_same] at hsub
    obtain ⟨x, hx⟩ := hne
    have hxa : x = a := mem_singleton_iff.mp (hsub hx)
    refine ⟨a, a, ?_⟩
    rw [segment_same]
    exact hsub.antisymm (singleton_subset_iff.mpr (hxa ▸ hx))
  · let f : ℝ →ᵃ[ℝ] ℂ := AffineMap.lineMap a b
    let τ : ℂ → ℝ := fun z => ((z - a) / (b - a)).re
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (fun he => hab he.symm)
    have hτ : Continuous τ := by dsimp only [τ]; fun_prop
    have hτf : ∀ t, τ (f t) = t := by
      intro t
      dsimp only [τ, f]
      simp [AffineMap.lineMap_apply_module', Complex.real_smul, hba]
    have hfτ : ∀ z ∈ C, f (τ z) = z := by
      intro z hz
      have hm := hsub hz
      rw [segment_eq_image_lineMap] at hm
      obtain ⟨t, _, rfl⟩ := hm
      exact congrArg f (hτf t)
    let T := τ '' C
    have hTc : IsCompact T := hC.image hτ
    have hTn : T.Nonempty := hne.image τ
    have hTi : T = Icc (sInf T) (sSup T) :=
      eq_Icc_of_connected_compact ⟨hTn, hconn.image τ hτ.continuousOn⟩ hTc
    have hle : sInf T ≤ sSup T := csInf_le hTc.bddBelow (hTc.sSup_mem hTn)
    have himg : f '' T = C := by
      change f '' (τ '' C) = C
      rw [← image_comp]
      exact (image_congr hfτ).trans (image_id C)
    refine ⟨f (sInf T), f (sSup T), ?_⟩
    calc
      C = f '' T := himg.symm
      _ = f '' Icc (sInf T) (sSup T) := congrArg (fun J : Set ℝ => f '' J) hTi
      _ = f '' segment ℝ (sInf T) (sSup T) := by rw [segment_eq_Icc hle]
      _ = segment ℝ (f (sInf T)) (f (sSup T)) := image_segment ℝ f _ _

/-- Part IV, Section 7a: finitely many cut points suffice for all segment
ends, isolated intersections, and ends of collinear overlaps. -/
theorem exists_segment_arrangement_cut_points (pieces : Finset (ℂ × ℂ)) :
    ∃ V : Set ℂ, V.Finite ∧
      (∀ p ∈ pieces, p.1 ∈ V ∧ p.2 ∈ V) ∧
      ∀ p ∈ pieces, ∀ q ∈ pieces,
        (segment ℝ p.1 p.2 ∩ segment ℝ q.1 q.2).Nonempty →
        ∃ x ∈ V, ∃ y ∈ V,
          segment ℝ p.1 p.2 ∩ segment ℝ q.1 q.2 = segment ℝ x y := by
  classical
  let I := {p // p ∈ pieces}
  have hends : ∀ e : I × I, ∃ x y : ℂ,
      segment ℝ e.1.val.1 e.1.val.2 ∩ segment ℝ e.2.val.1 e.2.val.2 = ∅ ∨
      segment ℝ e.1.val.1 e.1.val.2 ∩ segment ℝ e.2.val.1 e.2.val.2 = segment ℝ x y := by
    intro e
    by_cases hn : (segment ℝ e.1.val.1 e.1.val.2 ∩ segment ℝ e.2.val.1 e.2.val.2).Nonempty
    · obtain ⟨x, y, hxy⟩ := segment_inter_eq_segment hn
      exact ⟨x, y, Or.inr hxy⟩
    · exact ⟨0, 0, Or.inl (not_nonempty_iff_eq_empty.mp hn)⟩
  choose left right hends using hends
  let V : Set ℂ := (⋃ p : I, {p.val.1, p.val.2}) ∪ range left ∪ range right
  have hV : V.Finite :=
    ((finite_iUnion fun p : I => (finite_singleton p.val.2).insert p.val.1).union
      (finite_range left)).union (finite_range right)
  refine ⟨V, hV, ?_, ?_⟩
  · intro p hp
    exact ⟨Or.inl (Or.inl (mem_iUnion.mpr ⟨⟨p, hp⟩, Or.inl rfl⟩)),
      Or.inl (Or.inl (mem_iUnion.mpr ⟨⟨p, hp⟩, Or.inr rfl⟩))⟩
  · intro p hp q hq hn
    let e : I × I := (⟨p, hp⟩, ⟨q, hq⟩)
    refine ⟨left e, Or.inl (Or.inr (mem_range_self e)),
      right e, Or.inr (mem_range_self e), ?_⟩
    rcases hends e with hempty | he
    · exact (hn.ne_empty hempty).elim
    · exact he

end GraphMinor.LRPlanarity
