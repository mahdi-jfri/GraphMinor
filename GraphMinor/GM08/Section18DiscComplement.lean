module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.ArcTools

/-!
# The rest of a disc boundary

A line lying on the boundary of a disc has a complementary boundary line
with the same ends. Move to a disc chart, apply the proved complementary-arc
lemma in the plane, and move back. This identifies the old boundary part
of a disc component in the same-cuff arc case of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology Metric GraphMinor.Surface

universe w

/-- The complementary boundary line of a disc. This is a local geometric
step in the disc-side analysis of VIII (18.2), page 286. -/
theorem exists_complementary_boundary_line {S : Type w} [TopologicalSpace S]
    [T2Space S] {Δ F : Set S} {u v : S} (hΔ : IsClosedDisc Δ)
    (hF : IsLineWithEnds F u v) (hsub : F ⊆ discBd Δ) :
    ∃ L : Set S, IsLineWithEnds L u v ∧ F ∪ L = discBd Δ ∧ F ∩ L = {u, v} := by
  obtain ⟨h, g, ch⟩ := hΔ.exists_isChart
  obtain ⟨a, ha, harange, ha0, ha1⟩ := hF.exists_arc
  have haF : ∀ t, a t ∈ F := fun t => harange ▸ mem_range_self t
  have haΔ : ∀ t, a t ∈ Δ := fun t => discBd_subset Δ (hsub (haF t))
  let c : unitInterval → ℂ := h ∘ a
  have hcs : ∀ t, c t ∈ sphere 0 1 := fun t =>
    ch.bd ▸ mem_image_of_mem h (hsub (haF t))
  have hc : IsArcMap c := by
    refine ⟨ch.hc.comp_continuous ha.1 haΔ, ?_⟩
    intro s t he
    apply ha.2
    have he' := congrArg g he
    change g (h (a s)) = g (h (a t)) at he'
    simpa only [ch.gh (haΔ s), ch.gh (haΔ t)] using he'
  have ho := ch.oArc_h (discBd_subset Δ) hΔ.isOArc_discBd
  rw [ch.bd] at ho
  obtain ⟨b, hb, hb0, hb1, hcover, hinter⟩ := exists_other_arc (Classical.choice ho) hc
    (by rintro _ ⟨t, rfl⟩; exact hcs t)
  have hbs : ∀ t, b t ∈ sphere 0 1 := fun t => hcover ▸ Or.inr (mem_range_self t)
  have hbb : ∀ t, b t ∈ closedBall 0 1 := fun t => sphere_subset_closedBall (hbs t)
  let d : unitInterval → S := g ∘ b
  have hd : IsArcMap d := ⟨ch.gc.comp_continuous hb.1 hbb,
    fun s t he => hb.2 (ch.injOn (hbb s) (hbb t) he)⟩
  have hd0 : d 0 = u := by
    change g (b 0) = u
    rw [hb0]
    exact (ch.gh (haΔ 0)).trans ha0
  have hd1 : d 1 = v := by
    change g (b 1) = v
    rw [hb1]
    exact (ch.gh (haΔ 1)).trans ha1
  have hgc : g '' range c = F := by
    rw [← range_comp]
    have he : g ∘ c = a := funext fun t => ch.gh (haΔ t)
    rw [he, harange]
  refine ⟨range d, hd0 ▸ hd1 ▸ hd.isLineWithEnds, ?_, ?_⟩
  · calc
      F ∪ range d = g '' range c ∪ g '' range b := by rw [hgc, range_comp]
      _ = g '' (range c ∪ range b) := (image_union g _ _).symm
      _ = discBd Δ := by rw [hcover, ch.g_sphere]
  · apply Subset.antisymm
    · rintro x ⟨hxF, t, htx⟩
      obtain ⟨s, hsx⟩ := harange.symm ▸ hxF
      have he : c s = b t := by
        change h (a s) = b t
        rw [hsx, ← htx]
        exact ch.hg (hbb t)
      rcases hinter s t he with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl (hsx.symm.trans ha0)
      · exact Or.inr (hsx.symm.trans ha1)
    · rintro x (rfl | rfl)
      · exact ⟨ha0 ▸ haF 0, 0, hd0⟩
      · exact ⟨ha1 ▸ haF 1, 1, hd1⟩

end GraphMinor.GM08
