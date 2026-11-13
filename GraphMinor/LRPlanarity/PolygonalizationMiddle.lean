module

public import GraphMinor.HP25.Web
public import GraphMinor.Surface.ArcTools
import GraphMinor.LRPlanarity.PolygonalizationDiscs
import GraphMinor.LRPlanarity.PolygonalizationPorts
import GraphMinor.Surface.SurfaceGraph

/-!
# Disjoint middle arcs of the drawing

Part IV, Section 7a of the planarity note cuts each edge at the last exit
from its source disc and the first entry into its target disc. The resulting
middle arcs miss every original vertex. Distinct middle arcs are disjoint
because the original edge images meet only at their common vertex points.
One orientation per undirected edge avoids duplicate middle arcs.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric

/-- Part IV, Section 7a: choose the separated vertex discs and cut every
edge, with the smaller vertex first, into a middle arc between boundary
ports. The middle arcs are disjoint, avoid all original vertices, and avoid
every nonincident vertex disc. -/
theorem exists_drawing_middle_arcs {N : ℕ} {G : SimpleGraph (Fin N)}
    (drawing : HP25.PlaneEmbedding G univ) :
    let E := {e : Fin N × Fin N // G.Adj e.1 e.2 ∧ e.1 < e.2}
    ∃ (r : Fin N → ℝ) (source target : E → ℂ) (middle : E → Set ℂ),
      (∀ w, 0 < r w) ∧
      (∀ u v, u ≠ v → Disjoint (closedBall (drawing.pt u) (r u))
        (closedBall (drawing.pt v) (r v))) ∧
      (∀ e, source e ∈ sphere (drawing.pt e.val.1) (r e.val.1) ∧
        target e ∈ sphere (drawing.pt e.val.2) (r e.val.2) ∧
        Surface.IsLineWithEnds (middle e) (source e) (target e) ∧
        middle e ⊆ drawing.line e.val.1 e.val.2 ∧
        middle e ∩ closedBall (drawing.pt e.val.1) (r e.val.1) = {source e} ∧
        middle e ∩ closedBall (drawing.pt e.val.2) (r e.val.2) = {target e}) ∧
      (∀ e w, drawing.pt w ∉ middle e) ∧
      Pairwise (fun e f => Disjoint (middle e) (middle f)) ∧
      (∀ e w, e.val.1 ≠ w → e.val.2 ≠ w →
        Disjoint (middle e) (closedBall (drawing.pt w) (r w))) := by
  classical
  let E := {e : Fin N × Fin N // G.Adj e.1 e.2 ∧ e.1 < e.2}
  obtain ⟨γ, hγ, r, hr, hdiscs, hnonincident, hsource, htarget⟩ :=
    exists_drawing_vertex_discs drawing
  let directed : E → {e : Fin N × Fin N // G.Adj e.1 e.2} :=
    fun e => ⟨e.val, e.property.1⟩
  let arc : E → unitInterval → ℂ := fun e => γ (directed e)
  let lo : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
  let hi : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
  have hlohi : lo < hi := by change (1 / 3 : ℝ) < 2 / 3; norm_num
  have htrim := fun e : E => exists_trimmed_middle_arc (hγ (directed e)).1
    (hr e.val.1) (hr e.val.2) (hγ (directed e)).2.1 (hγ (directed e)).2.2.1
    lo hi hlohi (hsource (directed e)) (htarget (directed e))
  choose s t hs ht hsphere tsphere hline hS hT hbetween using htrim
  let source : E → ℂ := fun e => arc e (s e)
  let target : E → ℂ := fun e => arc e (t e)
  let middle : E → Set ℂ := fun e => arc e '' Icc (s e) (t e)
  have hsub : ∀ e, middle e ⊆ drawing.line e.val.1 e.val.2 := by
    intro e x hx
    obtain ⟨u, _, rfl⟩ := hx
    exact (hγ (directed e)).2.2.2 ▸ mem_range_self u
  have no_center : ∀ w p, p ∈ sphere (drawing.pt w) (r w) → p ≠ drawing.pt w := by
    intro w p hp he
    have hd := mem_sphere.mp hp
    rw [he, dist_self] at hd
    exact (hr w).ne' hd.symm
  have havoid : ∀ e w, drawing.pt w ∉ middle e := by
    intro e w hw
    rcases drawing.avoid _ (mem_univ _) _ (mem_univ _) e.property.1 w (mem_univ _)
      (hsub e hw) with he | he
    · subst w
      have heq : drawing.pt e.val.1 = source e :=
        mem_singleton_iff.mp (hS e ▸ ⟨hw, mem_closedBall_self (hr e.val.1).le⟩)
      exact no_center _ _ (hsphere e) heq.symm
    · subst w
      have heq : drawing.pt e.val.2 = target e :=
        mem_singleton_iff.mp (hT e ▸ ⟨hw, mem_closedBall_self (hr e.val.2).le⟩)
      exact no_center _ _ (tsphere e) heq.symm
  have hedge : ∀ e f : E, e ≠ f → s(e.val.1, e.val.2) ≠ s(f.val.1, f.val.2) := by
    intro e f hef heq
    rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hef (Subtype.ext (Prod.ext h₁ h₂))
    · have hlt : f.val.2 < f.val.1 := by rw [← h₁, ← h₂]; exact e.property.2
      exact lt_asymm hlt f.property.2
  have hmiddles : Pairwise (fun e f : E => Disjoint (middle e) (middle f)) := by
    intro e f hef
    apply disjoint_left.mpr
    intro x hx hy
    have hm := drawing.inter _ (mem_univ _) _ (mem_univ _) _ (mem_univ _) _ (mem_univ _)
      e.property.1 f.property.1 (hedge e f hef) ⟨hsub e hx, hsub f hy⟩
    obtain ⟨w, _, hw⟩ := hm
    exact havoid e w (hw.symm ▸ hx)
  refine ⟨r, source, target, middle, hr, hdiscs,
    fun e => ⟨hsphere e, tsphere e, hline e, hsub e, hS e, hT e⟩,
    havoid, hmiddles, ?_⟩
  intro e w hs ht
  exact (hnonincident (directed e) w hs ht).symm.mono_left (hsub e)

end GraphMinor.LRPlanarity
