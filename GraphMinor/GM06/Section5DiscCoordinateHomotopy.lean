module

public import GraphMinor.Surface.DiscGrow

/-!
# The coordinate homotopy of a disc detour

For the attachment-visit argument in VI (5.5), page 130, retain
the actual coordinate formula throughout the disc homotopy. This
lets a straight retraction fibre control the whole homotopy path
over a new attachment contact, which in turn controls its angular
sheet. Off the disc interior the homotopy is fixed.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface

/-- Interpolate a disc retraction in its coordinates and glue it
to the unchanged curve outside the disc interior. The formula is
retained at every homotopy time for attachment-fibre estimates. -/
theorem exists_disc_detour_coordinate_homotopy
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x) {D : Set S} (hD : IsClosedDisc D)
    {h : S → ℂ} {j : ℂ → S} (c : IsChart D h j)
    (f : Curve S) {a : ℂ} (r : ℂ → ℂ)
    (hrcont : ContinuousOn r (closedBall 0 1 \ {a}))
    (hrnorm : ∀ w ∈ closedBall (0 : ℂ) 1 \ {a}, ‖r w‖ = 1)
    (hrfix : ∀ w : ℂ, ‖w‖ = 1 → w ≠ a → r w = w)
    (hfne : ∀ t, f t ∈ D → h (f t) ≠ a) :
    ∃ H : C(unitInterval × unitInterval, S),
      (∀ t, H (t, 0) = f t) ∧
      (∀ t u, f t ∉ discInt D → H (t, u) = f t) ∧
      (∀ t u, f t ∈ D → H (t, u) =
        j ((1 - (u : ℝ)) • h (f t) + (u : ℝ) • r (h (f t)))) ∧
      ∀ t, f t ∈ D → H (t, 1) ∈ discBd D := by
  classical
  let A : Set (unitInterval × unitInterval) := {p | f p.1 ∈ D}
  let B : Set (unitInterval × unitInterval) := {p | f p.1 ∉ discInt D}
  let z : unitInterval × unitInterval → ℂ := fun p =>
    (1 - (p.2 : ℝ)) • h (f p.1) + (p.2 : ℝ) • r (h (f p.1))
  have hz (p : unitInterval × unitInterval) (hp : p ∈ A) :
      z p ∈ closedBall (0 : ℂ) 1 := by
    exact (convex_closedBall (0 : ℂ) 1) (c.hm hp)
      (mem_closedBall_zero_iff.mpr (hrnorm _ ⟨c.hm hp, hfne _ hp⟩).le)
      (sub_nonneg.mpr p.2.2.2) p.2.2.1 (sub_add_cancel 1 (p.2 : ℝ))
  have hret : ContinuousOn (fun p : unitInterval × unitInterval =>
      r (h (f p.1))) A :=
    hrcont.comp (c.hc.comp
      (f.continuous.comp continuous_fst).continuousOn (fun _ hp => hp))
      (fun p hp => ⟨c.hm hp, hfne _ hp⟩)
  have hzcont : ContinuousOn z A :=
    ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).continuousOn.smul
      (c.hc.comp (f.continuous.comp continuous_fst).continuousOn (fun _ hp => hp))).add
      ((continuous_subtype_val.comp continuous_snd).continuousOn.smul hret)
  let H : unitInterval × unitInterval → S := fun p =>
    if p ∈ A then j (z p) else f p.1
  have hbd (p : unitInterval × unitInterval) (hp : p ∈ A) (hq : p ∈ B) :
      j (z p) = f p.1 := by
    have hfb : f p.1 ∈ discBd D := by
      by_contra hb
      exact hq ⟨hp, hb⟩
    have hnorm : ‖h (f p.1)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp (c.bd ▸ mem_image_of_mem h hfb)
    have hfix := hrfix _ hnorm (hfne _ hp)
    dsimp only [z]
    rw [hfix, ← add_smul, sub_add_cancel, one_smul]
    exact c.gh hp
  have hHA (p) (hp : p ∈ A) : H p = j (z p) := ite_eq_left hp
  have hHB (p) (hp : p ∈ B) : H p = f p.1 := by
    by_cases hpa : p ∈ A
    · exact (hHA p hpa).trans (hbd p hpa hp)
    · exact ite_eq_right hpa
  have hcont : Continuous H := by
    have hAB : A ∪ B = univ := by
      apply eq_univ_of_forall
      intro p
      by_cases hp : p ∈ A
      · exact Or.inl hp
      · exact Or.inr (fun hi => hp hi.1)
    rw [← continuousOn_univ, ← hAB]
    exact ContinuousOn.union_of_isClosed
      ((c.gc.comp hzcont hz).congr (fun p hp => hHA p hp))
      ((f.continuous.comp continuous_fst).continuousOn.congr (fun p hp => hHB p hp))
      (hD.isClosed.preimage (f.continuous.comp continuous_fst))
      ((hD.isOpen_discInt hman).isClosed_compl.preimage (f.continuous.comp continuous_fst))
  have hHzero (t) : H (t, 0) = f t := by
    by_cases ht : f t ∈ D
    · rw [hHA _ ht]
      simpa [z] using c.gh ht
    · exact ite_eq_right ht
  refine ⟨⟨H, hcont⟩, hHzero, fun t u ht => hHB (t, u) ht,
    fun t u ht => hHA (t, u) ht, ?_⟩
  intro t ht
  change H (t, 1) ∈ discBd D
  rw [hHA _ ht]
  have he : z (t, 1) = r (h (f t)) := by simp [z]
  rw [he, ← c.g_sphere]
  exact mem_image_of_mem j (mem_sphere_zero_iff_norm.mpr (hrnorm _ ⟨c.hm ht, hfne _ ht⟩))

end GraphMinor.GM06
