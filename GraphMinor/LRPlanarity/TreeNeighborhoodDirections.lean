module

public import GraphMinor.HP25.Web
public import Mathlib.Analysis.Convex.Segment
public import GraphMinor.Surface.Lunes
import Mathlib.Algebra.Module.Torsion.Free

/-!
# Distinct directions at a vertex of a straight drawing

Part IV, Section 7b of the planarity note uses distinct incident directions
to choose disjoint polygon facets. If two incident straight edges had the
same direction, the nearer endpoint would lie on the longer edge. The plane
embedding forbids an edge from passing through that third vertex.
-/

public section
namespace GraphMinor.LRPlanarity

open Set

private theorem normalized_eq_mem_segment {z p q : ℂ} (hp : p ≠ z) (hq : q ≠ z)
    (heq : ‖p - z‖⁻¹ • (p - z) = ‖q - z‖⁻¹ • (q - z))
    (hle : ‖p - z‖ ≤ ‖q - z‖) : p ∈ segment ℝ z q := by
  have hpn : ‖p - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)
  have hqn : 0 < ‖q - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  have hscale : p - z = (‖p - z‖ / ‖q - z‖) • (q - z) := by
    calc
      p - z = ‖p - z‖ • (‖p - z‖⁻¹ • (p - z)) := by
        rw [smul_smul, mul_inv_cancel₀ hpn, one_smul]
      _ = ‖p - z‖ • (‖q - z‖⁻¹ • (q - z)) := congrArg (fun x => ‖p - z‖ • x) heq
      _ = (‖p - z‖ / ‖q - z‖) • (q - z) := by rw [smul_smul, div_eq_mul_inv]
  have hmem : p - z ∈ segment ℝ (0 : ℂ) (q - z) := by
    rw [segment_eq_image]
    refine ⟨‖p - z‖ / ‖q - z‖, ⟨div_nonneg (norm_nonneg _) hqn.le,
      (div_le_one hqn).mpr hle⟩, ?_⟩
    simpa only [smul_zero, zero_add] using hscale.symm
  have ht := (mem_segment_translate ℝ z).mpr hmem
  have hleft : z + (p - z) = p := by abel
  have hright : z + (q - z) = q := by abel
  simpa only [hleft, hright, add_zero] using ht

/-- Part IV, Section 7b: at a vertex of a straight plane drawing, the unit
directions toward distinct neighbors are distinct. -/
theorem incident_straight_directions_injective {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v → drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (u : V) : Function.Injective (fun v : {v // G.Adj u v} =>
      ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u)) := by
  intro v w heq
  by_contra hne
  have hvu : drawing.pt v.val ≠ drawing.pt u := by
    intro he
    exact (G.ne_of_adj v.property) (drawing.injOn (mem_univ _) (mem_univ _) he).symm
  have hwu : drawing.pt w.val ≠ drawing.pt u := by
    intro he
    exact (G.ne_of_adj w.property) (drawing.injOn (mem_univ _) (mem_univ _) he).symm
  rcases le_total ‖drawing.pt v.val - drawing.pt u‖ ‖drawing.pt w.val - drawing.pt u‖ with hle | hle
  · have hm := normalized_eq_mem_segment hvu hwu heq hle
    rw [← hstraight u w.val w.property] at hm
    rcases drawing.avoid u (mem_univ _) w.val (mem_univ _) w.property v.val (mem_univ _) hm with he | he
    · exact (G.ne_of_adj v.property) he.symm
    · exact hne (Subtype.ext he)
  · have hm := normalized_eq_mem_segment hwu hvu heq.symm hle
    rw [← hstraight u v.val v.property] at hm
    rcases drawing.avoid u (mem_univ _) v.val (mem_univ _) v.property w.val (mem_univ _) hm with he | he
    · exact (G.ne_of_adj w.property) he.symm
    · exact hne (Subtype.ext he.symm)

/-- Part IV, Section 7b: assign an angle to each incident unit direction.
Distinct neighbors give distinct unit normals for the polygon facets. -/
theorem exists_incident_normal_angles {V : Type*} {G : SimpleGraph V}
    (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v → drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (u : V) :
    ∃ angle : {v // G.Adj u v} → ℝ,
      (∀ v, Surface.eC (angle v) =
        ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u)) ∧
      Function.Injective (fun v => Surface.eC (angle v)) := by
  have hnormal : ∀ v : {v // G.Adj u v}, ∃ θ : ℝ, Surface.eC θ =
      ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u) := by
    intro v
    have hdiff : drawing.pt v.val - drawing.pt u ≠ 0 := by
      apply sub_ne_zero.mpr
      intro he
      exact (G.ne_of_adj v.property) (drawing.injOn (mem_univ _) (mem_univ _) he).symm
    have hunit : ‖‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u)‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hdiff)),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hdiff)]
    obtain ⟨θ, hθ⟩ := Surface.exists_eC hunit
    exact ⟨θ, hθ.symm⟩
  choose angle hangle using hnormal
  refine ⟨angle, hangle, ?_⟩
  intro v w he
  apply incident_straight_directions_injective drawing hstraight u
  dsimp only
  rw [← hangle v, ← hangle w]
  exact he

end GraphMinor.LRPlanarity
