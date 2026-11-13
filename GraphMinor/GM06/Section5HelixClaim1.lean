module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5DeletedEdgeRegion
import GraphMinor.GM06.Section5StripDisjoint
import GraphMinor.GM06.Section5StripCuffs
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section5InitialCuffBacktrack
import GraphMinor.GM06.Section5RegionVisit
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section5RegionPoint

/-!
# Claim (1) in the proof of VI (5.5)

If the helix already meets a vertex before its last visit to the
deleted-edge region, retain it. Otherwise its initial segment stays
in that region. The retained linkage identifies its initial dual
point as the one preceding the deleted edge's initial vertex.
Prepend the full-gap cuff curve. Its winding loss is offset by its
one new vertex contact, which supplies the claim's earlier hit.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- Prepend the full-gap cuff curve. Its one new vertex contact
compensates for its winding −1/k, and that contact precedes the
transported last-region time. -/
private theorem prepend_initial_cuff_curve {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (f : Curve ClosedCylinder) (hf : IsHelix k G f)
    (h0 : f 0 = cylinderN1Point k (finPredCycle i)) {R : Set ClosedCylinder} {z : unitInterval}
    (hz : IsGreatest (closure (f ⁻¹' R)) z) :
    ∃ (g : Curve ClosedCylinder) (z' : unitInterval), IsHelix k G g ∧
      curvePhi k G g = curvePhi k G f ∧ IsGreatest (closure (g ⁻¹' R)) z' ∧
      g z' = f z ∧ range f ⊆ range g ∧
      ∃ t : unitInterval, t < z' ∧ g t ∈ G.V := by
  classical
  let h := initialCuffBacktrackCurve k i
  have hh := initialCuffBacktrackCurve_props hG i
  let p : Path (cylinderN1Point k i) (f 0) :=
    ⟨h, initialCuffBacktrackCurve_zero i, (initialCuffBacktrackCurve_one hG.1 i).trans h0.symm⟩
  let q : Path (f 0) (f 1) := ⟨f, rfl, rfl⟩
  let g : Curve ClosedCylinder := (p.trans q).toContinuousMap
  have hnot : f 0 ∉ G.V := by
    rw [h0]
    exact fun h => cylinderN1Point_not_mem_U hG (finPredCycle i) (G.V_subset_U h)
  have hcount := curveL_path_trans_add p q hh.2.1 hf.2.2.2
  have hlen := hcount.2
  rw [ite_eq_right hnot, Nat.add_zero] at hlen
  change curveL G g = curveL G h + curveL G f at hlen
  rw [hh.2.2] at hlen
  have hhelix : IsHelix k G g := by
    refine ⟨isNormalCurve_path_trans p q hh.1 hf.1, ?_, ?_, hcount.1⟩
    · change (p.trans q) 0 ∈ cylinderN1 k
      rw [Path.source]
      exact ⟨i, rfl⟩
    · change (p.trans q) 1 ∈ cylinderN2 k
      rw [Path.target]
      exact hf.2.2.1
  have hphi : curvePhi k G g = curvePhi k G f := by
    have hw := windingNumber_path_trans p q
    change windingNumber g = windingNumber h + windingNumber f at hw
    rw [curvePhi, hw, windingNumber_initialCuffBacktrackCurve hG.1 i, hlen]
    simp only [Nat.cast_add, Nat.cast_one]
    unfold curvePhi
    ring
  have hlast := last_region_visit_path_trans p q hz
  refine ⟨g, rightHalfTime z, hhelix, hphi, hlast, ?_, ?_, ?_⟩
  · change (p.trans q) (rightHalfTime z) = f z
    rw [path_trans_rightHalfTime]
    rfl
  · rintro x ⟨t, rfl⟩
    refine ⟨rightHalfTime t, ?_⟩
    exact path_trans_rightHalfTime p q t
  · refine ⟨leftHalfTime (leftHalfTime 1), ?_, ?_⟩
    · change (1 / 2 : ℝ) / 2 < ((z : ℝ) + 1) / 2
      linarith only [z.2.1]
    · change (p.trans q) (leftHalfTime (leftHalfTime 1)) ∈ G.V
      rw [path_trans_leftHalfTime]
      change h (leftHalfTime 1) ∈ G.V
      rw [initialCuffBacktrackCurve_mid]
      have hp : cylinderM1Point k i ∈ cylinderM1 k ∪ cylinderM2 k := Or.inl ⟨i, rfl⟩
      exact (show cylinderM1Point k i ∈ G.V ∩ bd ClosedCylinder from hG.2.2.symm ▸ hp).1
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- Graph Minors VI, (5.5), claim (1), pages 130–131:
"There exists $z_1 \in [0, z_2)$ with $f'(z_1) \in V(G')$."
The conclusion makes the permitted normalization explicit: it retains
helix potential, the last region point, and the old curve image while
providing the required earlier vertex contact. -/
theorem lemma_5_5_claim_1 {k : ℕ} {G G' : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (hpaths : L'.pathDrawing = L.pathDrawing) (i : Fin k) {e : Set ClosedCylinder}
    (_he : e ∈ G.E) (_hs : cylinderM1Point k i ∈ closure e)
    (heStrip : e ⊆ cylinderStrip L (finPredCycle i))
    (f' : Curve ClosedCylinder) (hf' : IsHelix k G' f')
    {R' : Set ClosedCylinder} (hR' : R' ∈ G'.R) (heR' : e ⊆ R')
    (hHit : (range f' ∩ e).Nonempty) {z₂ : unitInterval}
    (hz₂ : IsGreatest (closure (f' ⁻¹' R')) z₂) :
    ∃ (f : Curve ClosedCylinder) (z₂' : unitInterval), IsHelix k G' f ∧
      curvePhi k G' f = curvePhi k G' f' ∧ IsGreatest (closure (f ⁻¹' R')) z₂' ∧
      f z₂' = f' z₂ ∧ range f' ⊆ range f ∧
      ∃ z₁ : unitInterval, z₁ < z₂' ∧ f z₁ ∈ G'.V := by
  classical
  by_cases hprior : ∃ t : unitInterval, t < z₂ ∧ f' t ∈ G'.V
  · exact ⟨f', z₂, hf', rfl, hz₂, rfl, Subset.rfl, hprior⟩
  · obtain ⟨x, ⟨u, rfl⟩, hue⟩ := hHit
    have huR : f' u ∈ R' := heR' hue
    have huz : u ≤ z₂ := hz₂.2 (subset_closure (show u ∈ f' ⁻¹' R' from huR))
    have hR0 := initial_point_mem_region_of_no_prior_vertex f' hf'.1 hR' huR huz hprior
    have hRstrip := region_subset_strip_of_retained_linkage L L' hpaths hR'
      (finPredCycle i) ⟨f' u, huR, heStrip hue⟩
    obtain ⟨θ, hθ⟩ := CylinderLinkage.exists_hasTheta hG.1 L
    obtain ⟨j, hj⟩ := hf'.2.1
    have hjstrip : cylinderN1Point k j ∈ closure (cylinderStrip L (finPredCycle i)) ∩ cylinderCuff1 := by
      refine ⟨?_, rfl⟩
      rw [hj]
      exact subset_closure (hRstrip hR0)
    have hjgap := closure_strip_inter_initial_cuff_subset_gap L hG hθ (finPredCycle i) hjstrip
    have hji := index_eq_of_dual_point_mem_initial_gap hG.1 hjgap
    have hstart : f' 0 = cylinderN1Point k (finPredCycle i) :=
      hj.symm.trans (congrArg (cylinderN1Point k) hji)
    exact prepend_initial_cuff_curve hG' i f' hf' hstart hz₂
end GraphMinor.GM06
