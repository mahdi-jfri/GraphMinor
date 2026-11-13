module

public import GraphMinor.HP25.Web
public import GraphMinor.Surface.ArcTools
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Tactic.Linarith

/-!
# Small separated vertex discs

Part IV, Section 7a of the planarity note chooses a small closed disc at
each vertex. Each disc must avoid finitely many compact sets missing its
center. Include the other vertex points among the forbidden sets and choose
the radius small enough that even the doubled disc misses them. The resulting
discs are pairwise disjoint by the triangle inequality.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric

private theorem sum_lt_of_twice_lt {r s d : ℝ} (hr : 2 * r < d) (hs : 2 * s < d) :
    r + s < d := by linarith

/-- The compact-separation step of Part IV, Section 7a. A finite family of
distinct centers admits pairwise disjoint positive-radius closed discs,
each avoiding any prescribed compact set missing its center. -/
theorem exists_separated_vertex_discs {ι : Type*} [Finite ι] (pt : ι → ℂ)
    (hinj : Function.Injective pt) (K : ι → Set ℂ)
    (hK : ∀ v, IsCompact (K v)) (hmiss : ∀ v, pt v ∉ K v) :
    ∃ r : ι → ℝ, (∀ v, 0 < r v ∧ Disjoint (closedBall (pt v) (r v)) (K v)) ∧
      ∀ u v, u ≠ v → Disjoint (closedBall (pt u) (r u)) (closedBall (pt v) (r v)) := by
  let F : ι → Set ℂ := fun v => K v ∪ pt '' {w | w ≠ v}
  have hFc : ∀ v, IsClosed (F v) := fun v =>
    ((hK v).union (((Set.toFinite {w | w ≠ v}).image pt).isCompact)).isClosed
  have hFm : ∀ v, pt v ∈ (F v)ᶜ := by
    intro v
    rintro (h | ⟨w, hw, he⟩)
    · exact hmiss v h
    · exact hw (hinj he)
  have hball : ∀ v, ∃ ε : ℝ, 0 < ε ∧ ball (pt v) ε ⊆ (F v)ᶜ :=
    fun v => Metric.mem_nhds_iff.mp ((hFc v).isOpen_compl.mem_nhds (hFm v))
  choose ε hε hεball using hball
  let r : ι → ℝ := fun v => ε v / 3
  have hr : ∀ v, 0 < r v := fun v => div_pos (hε v) (by norm_num)
  have hdouble : ∀ v, closedBall (pt v) (2 * r v) ⊆ (F v)ᶜ := by
    intro v x hx
    apply hεball v
    apply mem_ball.mpr
    exact (mem_closedBall.mp hx).trans_lt (by dsimp [r]; linarith [hε v])
  refine ⟨r, fun v => ⟨hr v, ?_⟩, ?_⟩
  · apply disjoint_left.mpr
    intro x hx hX
    apply hdouble v (closedBall_subset_closedBall (by linarith [hr v]) hx)
    exact Or.inl hX
  · intro u v huv
    have huvF : pt v ∈ F u := Or.inr ⟨v, huv.symm, rfl⟩
    have hvuF : pt u ∈ F v := Or.inr ⟨u, huv, rfl⟩
    have hdU : 2 * r u < dist (pt u) (pt v) := by
      apply lt_of_not_ge
      intro hle
      exact hdouble u (mem_closedBall.mpr (by simpa only [dist_comm] using hle)) huvF
    have hdV : 2 * r v < dist (pt u) (pt v) := by
      apply lt_of_not_ge
      intro hle
      exact hdouble v (mem_closedBall.mpr hle) hvuF
    apply disjoint_left.mpr
    intro x hxu hxv
    have htri : dist (pt u) (pt v) ≤ r u + r v :=
      (dist_triangle (pt u) x (pt v)).trans
        (add_le_add (by simpa only [dist_comm] using mem_closedBall.mp hxu)
          (mem_closedBall.mp hxv))
    exact (sum_lt_of_twice_lt hdU hdV).not_ge htri

/-- Part IV, Section 7a: parameterize all directed edges and choose disjoint
vertex discs. Each disc avoids nonincident edges and the prescribed far
thirds of every incident edge parameterization. -/
theorem exists_drawing_vertex_discs {N : ℕ} {G : SimpleGraph (Fin N)}
    (drawing : HP25.PlaneEmbedding G univ) :
    ∃ γ : {e : Fin N × Fin N // G.Adj e.1 e.2} → unitInterval → ℂ,
      (∀ e, Surface.IsArcMap (γ e) ∧ γ e 0 = drawing.pt e.val.1 ∧
        γ e 1 = drawing.pt e.val.2 ∧ range (γ e) = drawing.line e.val.1 e.val.2) ∧
      ∃ r : Fin N → ℝ,
        (∀ v, 0 < r v) ∧
        (∀ u v, u ≠ v → Disjoint (closedBall (drawing.pt u) (r u))
          (closedBall (drawing.pt v) (r v))) ∧
        (∀ (e : {e : Fin N × Fin N // G.Adj e.1 e.2}) v, e.val.1 ≠ v → e.val.2 ≠ v →
          Disjoint (closedBall (drawing.pt v) (r v)) (drawing.line e.val.1 e.val.2)) ∧
        (∀ e, Disjoint (closedBall (drawing.pt e.val.1) (r e.val.1))
          (γ e '' Ici (⟨1 / 3, by constructor <;> norm_num⟩ : unitInterval))) ∧
        (∀ e, Disjoint (closedBall (drawing.pt e.val.2) (r e.val.2))
          (γ e '' Iic (⟨2 / 3, by constructor <;> norm_num⟩ : unitInterval))) := by
  classical
  let E := {e : Fin N × Fin N // G.Adj e.1 e.2}
  have parameterize : ∀ e : E, ∃ f : unitInterval → ℂ,
      Surface.IsArcMap f ∧ f 0 = drawing.pt e.val.1 ∧
      f 1 = drawing.pt e.val.2 ∧ range f = drawing.line e.val.1 e.val.2 := by
    intro e
    obtain ⟨f, hf, hrange, hzero, hone⟩ :=
      (drawing.isLine _ (mem_univ _) _ (mem_univ _) e.property).exists_arc
    exact ⟨f, hf, hzero, hone, hrange⟩
  choose γ hγ using parameterize
  let lo : unitInterval := ⟨1 / 3, by constructor <;> norm_num⟩
  let hi : unitInterval := ⟨2 / 3, by constructor <;> norm_num⟩
  let K : Fin N → Set ℂ := fun v => ⋃ e : E,
    if e.val.1 = v then γ e '' Ici lo
    else if e.val.2 = v then γ e '' Iic hi
    else drawing.line e.val.1 e.val.2
  have hK : ∀ v, IsCompact (K v) := by
    intro v
    apply isCompact_iUnion
    intro e
    split_ifs
    · exact isClosed_Ici.isCompact.image (hγ e).1.1
    · exact isClosed_Iic.isCompact.image (hγ e).1.1
    · exact (drawing.isLine _ (mem_univ _) _ (mem_univ _) e.property).isCompact
  have hmiss : ∀ v, drawing.pt v ∉ K v := by
    intro v hm
    obtain ⟨e, he⟩ := mem_iUnion.mp hm
    split_ifs at he with hsource htarget
    · obtain ⟨t, ht, he⟩ := he
      have ht0 : t = 0 := (hγ e).1.2
        (he.trans ((hγ e).2.1.trans (congrArg drawing.pt hsource)).symm)
      rw [ht0] at ht
      change (1 / 3 : ℝ) ≤ 0 at ht
      norm_num at ht
    · obtain ⟨t, ht, he⟩ := he
      have ht1 : t = 1 := (hγ e).1.2
        (he.trans ((hγ e).2.2.1.trans (congrArg drawing.pt htarget)).symm)
      rw [ht1] at ht
      change (1 : ℝ) ≤ 2 / 3 at ht
      norm_num at ht
    · rcases drawing.avoid _ (mem_univ _) _ (mem_univ _) e.property v (mem_univ _) he with h | h
      · exact hsource h.symm
      · exact htarget h.symm
  have hinj : Function.Injective drawing.pt := fun u v he =>
    drawing.injOn (mem_univ _) (mem_univ _) he
  obtain ⟨r, hr, hdisj⟩ := exists_separated_vertex_discs drawing.pt hinj K hK hmiss
  refine ⟨γ, hγ, r, fun v => (hr v).1, hdisj, ?_, ?_, ?_⟩
  · intro e v hs ht
    apply (hr v).2.mono_right
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨e, by simpa only [hs, ht, ↓reduceIte] using hx⟩
  · intro e
    apply (hr e.val.1).2.mono_right
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨e, by simpa only [↓reduceIte] using hx⟩
  · intro e
    have hne : e.val.1 ≠ e.val.2 := G.ne_of_adj e.property
    apply (hr e.val.2).2.mono_right
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨e, by simpa only [hne, ↓reduceIte] using hx⟩

end GraphMinor.LRPlanarity
