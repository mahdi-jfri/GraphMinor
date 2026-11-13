module

public import GraphMinor.GM06.Alg57SourceLoopWinding
import GraphMinor.GM19.Winding
import GraphMinor.Surface.PlaneOrientation

/-!
# Reading the surviving source germs from a positive coordinate loop

For the source comparison in Lemma 8 of the implementation of VI
(5.7), page 133, the rim of a smaller chart gives a loop of directions
in the full source chart. A surviving germ is met exactly once.
Positive winding and the intermediate value theorem then force
these contacts to have their original cyclic order. The proof below
uses angle lifts of that loop and the uniqueness of its contacts.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem lift_bounds_of_unique_contact
    {P : ℝ} (L : ℝ → ℝ) (hc : Continuous L)
    (hpos : L 0 < L P)
    (havoid : ∀ t ∈ Ioo 0 P, L t ≠ L 0 ∧ L t ≠ L P) :
    ∀ t ∈ Ioo 0 P, L 0 < L t ∧ L t < L P := by
  intro t ht
  constructor
  · by_contra hh
    have hle : L t ≤ L 0 := le_of_not_gt hh
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc ht.2.le
      (hc.continuousOn) ⟨hle, hpos.le⟩
    have hr' : r ∈ Ioo 0 P := ⟨ht.1.trans_le hr.1,
      lt_of_le_of_ne hr.2 (fun he => by subst r; exact hpos.ne heq.symm)⟩
    exact (havoid r hr').1 heq
  · by_contra hh
    have hle : L P ≤ L t := le_of_not_gt hh
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc ht.1.le
      (hc.continuousOn) ⟨hpos.le, hle⟩
    have hr' : r ∈ Ioo 0 P := ⟨
      lt_of_le_of_ne hr.1 (fun he => by subst r; exact hpos.ne heq),
      hr.2.trans_lt ht.2⟩
    exact (havoid r hr').2 heq

private theorem exp_ne_at_inner_time {P t : ℝ} (hP : P = 2 * Real.pi)
    (ht : t ∈ Ioo 0 P) : Circle.exp t ≠ Circle.exp 0 := by
  intro heq
  have hi := Circle.exp_injOn_Ico (a := 0) (b := P) (show P - 0 ≤ 2 * Real.pi by rw [sub_zero, hP])
  have hh := hi ⟨ht.1.le, ht.2⟩ ⟨le_rfl, by rw [hP]; exact Real.two_pi_pos⟩ heq
  exact ht.1.ne' hh

private theorem one_turn_lift_of_positive_loop
    (v : C(Circle, Circle)) (a : Circle)
    (hpos : 0 < wind (fun w => (v w : ℂ)) 0)
    (ha : ∀ w, v w = v a → w = a) :
    ∃ L : ℝ → ℝ, Continuous L ∧
      (∀ t, Circle.exp (L t) = v (a * Circle.exp t)) ∧
      L (2 * Real.pi) = L 0 + 2 * Real.pi ∧
      ∀ t ∈ Ioo 0 (2 * Real.pi), L 0 < L t ∧ L t < L (2 * Real.pi) := by
  obtain ⟨L, hLc, hL⟩ := GraphMinor.GM19.exists_circle_lift_map
    ⟨fun t => v (a * Circle.exp t),
      v.continuous.comp (continuous_const.mul Circle.exp.continuous)⟩
  change ∀ t, Circle.exp (L t) = v (a * Circle.exp t) at hL
  have hAngle : GraphMinor.GM19.IsAngle
      (fun t => (v (a * Circle.exp t) : ℂ)) L := by
    refine ⟨hLc, fun t => ?_⟩
    rw [Circle.norm_coe, Complex.ofReal_one, one_mul]
    exact (congrArg (fun w : Circle => (w : ℂ)) (hL t)).symm
  have hvne : ∀ w, (v w : ℂ) ≠ (0 : ℂ) := fun w => Circle.coe_ne_zero _
  have hw := wind_eq_turn_rotate
    (continuous_subtype_val.comp v.continuous) hvne a
  simp only [sub_zero] at hw
  change wind (fun w => (v w : ℂ)) 0 =
    GraphMinor.GM19.turn (fun t => (v (a * Circle.exp t) : ℂ)) 0 (2 * Real.pi) at hw
  rw [hAngle.turn_eq (fun t => hvne _)] at hw
  have hLP : L 0 < L (2 * Real.pi) := by linarith only [hpos, hw]
  have hcontact (t : ℝ) (ht : t ∈ Ioo 0 (2 * Real.pi)) :
      Circle.exp (L t) ≠ Circle.exp (L 0) := by
    intro heq
    rw [hL, hL, Circle.exp_zero, mul_one] at heq
    have hh := ha _ heq
    have he : Circle.exp t = Circle.exp 0 := by
      simpa only [Circle.exp_zero, mul_eq_left] using hh
    exact exp_ne_at_inner_time rfl ht he
  have he : Circle.exp (L (2 * Real.pi)) = Circle.exp (L 0) := by
    rw [hL, hL, Circle.exp_zero, Circle.exp_two_pi]
  obtain ⟨n, hn⟩ := Circle.exp_eq_exp.mp he
  have hnpos : (0 : ℝ) < n := by
    have hp := Real.two_pi_pos
    nlinarith only [hn, hLP, hp]
  have hnposZ : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hn1Z : (1 : ℤ) ≤ n := hnposZ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn1Z
  have hnle : (n : ℝ) ≤ 1 := by
    by_contra hh
    have hgt : (1 : ℝ) < n := lt_of_not_ge hh
    have htop : L 0 + 2 * Real.pi < L (2 * Real.pi) := by
      have hp := Real.two_pi_pos
      nlinarith only [hn, hgt, hp]
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc Real.two_pi_pos.le
      hLc.continuousOn ⟨by linarith [Real.pi_pos], htop.le⟩
    have ht' : t ∈ Ioo 0 (2 * Real.pi) := by
      constructor
      · exact lt_of_le_of_ne ht.1 (fun he => by subst t; linarith only [heq, Real.pi_pos])
      · exact lt_of_le_of_ne ht.2 (fun he => by subst t; linarith only [heq, htop])
    apply hcontact t ht'
    rw [heq, Circle.exp_add_two_pi]
  have hend : L (2 * Real.pi) = L 0 + 2 * Real.pi := by
    have hnval : (n : ℝ) = 1 := le_antisymm hnle hn1
    rw [hnval, one_mul] at hn
    exact hn
  refine ⟨L, hLc, hL, hend, ?_⟩
  apply lift_bounds_of_unique_contact L hLc hLP
  intro t ht
  refine ⟨fun heq => hcontact t ht (congrArg Circle.exp heq), fun heq => ?_⟩
  apply hcontact t ht
  rw [heq, hend, Circle.exp_add_two_pi]

/-- A positive direction loop preserves cyclic order at contacts
whose first two directions each have a unique preimage. This is
the angular comparison used for the surviving source germs. -/
theorem circleCyclic_of_positive_loop_contacts
    (v : C(Circle, Circle)) (hpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {a b c : Circle} (ha : ∀ w, v w = v a → w = a)
    (hb : ∀ w, v w = v b → w = b) (habc : CircleCyclic a b c) :
    CircleCyclic (v a) (v b) (v c) := by
  obtain ⟨s, t, hs, hst, ht, rfl, rfl⟩ := habc
  obtain ⟨L, hLc, hL, hend, hbounds⟩ := one_turn_lift_of_positive_loop v a hpos ha
  have hsP := hbounds s ⟨hs, hst.trans ht⟩
  have htP := hbounds t ⟨hs.trans hst, ht⟩
  have hLt : L s < L t := by
    by_contra hh
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc ht.le hLc.continuousOn
      ⟨le_of_not_gt hh, hsP.2.le⟩
    have hv : v (a * Circle.exp r) = v (a * Circle.exp s) := by
      rw [← hL, ← hL, heq]
    have hsame := hb _ hv
    have hexp : Circle.exp r = Circle.exp s := mul_left_cancel hsame
    have hi := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (show 2 * Real.pi - 0 ≤ 2 * Real.pi by rw [sub_zero])
    have hrP : r < 2 * Real.pi := by
      apply lt_of_le_of_ne hr.2
      intro he
      subst r
      exact hsP.2.ne heq.symm
    have heq' : r = s := hi ⟨(hs.trans hst).le.trans hr.1, hrP⟩
      ⟨hs.le, hst.trans ht⟩ hexp
    linarith only [hr.1, hst, heq']
  have hcyc := circleCyclic_exp_of_lt hsP.1 hLt (by rw [← hend]; exact htP.2)
  simpa only [hL, Circle.exp_zero, mul_one] using hcyc


/-- At three distinct unique contacts the positive loop both
preserves and reflects cyclic order. The reversed order is
excluded by applying the same lift comparison to the swapped pair. -/
theorem circleCyclic_iff_positive_loop_contacts
    (v : C(Circle, Circle)) (hpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {a b c : Circle} (ha : ∀ w, v w = v a → w = a)
    (hb : ∀ w, v w = v b → w = b) (hc : ∀ w, v w = v c → w = c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic a b c ↔ CircleCyclic (v a) (v b) (v c) := by
  refine ⟨circleCyclic_of_positive_loop_contacts v hpos ha hb, fun h => ?_⟩
  rcases circleCyclic_or hab hac hbc with h' | h'
  · exact h'
  · exact False.elim (not_circleCyclic_both h
      (circleCyclic_of_positive_loop_contacts v hpos ha hc h'))


/-- Moving the first point to the end preserves positive cyclic order. -/
theorem circleCyclic_cycle {a b c : Circle} (h : CircleCyclic a b c) :
    CircleCyclic b c a := by
  obtain ⟨s, t, hs, hst, ht, hb, hc⟩ := h
  refine ⟨t - s, 2 * Real.pi - s, by linarith only [hst],
    by linarith only [ht], by linarith only [hs], ?_, ?_⟩
  · rw [hb, hc, mul_assoc, ← Circle.exp_add]
    rw [add_sub_cancel]
  · rw [hb, Circle.exp_sub, Circle.exp_two_pi]
    simp only [one_div, mul_assoc, mul_inv_cancel, mul_one]

/-- A cuff contact may be used as the starting point of the order
comparison without requiring its coordinate direction to have a
unique preimage. Uniqueness is needed only for the two retained
germs whose order is being read. -/
theorem circleCyclic_iff_positive_loop_anchor
    (v : C(Circle, Circle)) (hpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {a b c : Circle} (ha : ∀ w, v w = v a → w = a)
    (hb : ∀ w, v w = v b → w = b)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic c a b ↔ CircleCyclic (v c) (v a) (v b) := by
  constructor
  · intro h
    exact circleCyclic_cycle (circleCyclic_cycle
      (circleCyclic_of_positive_loop_contacts v hpos ha hb (circleCyclic_cycle h)))
  · intro h
    rcases circleCyclic_or hab hac hbc with h' | h'
    · exact circleCyclic_cycle (circleCyclic_cycle h')
    · have hbad := circleCyclic_of_positive_loop_contacts v hpos hb ha
        (circleCyclic_cycle (circleCyclic_cycle h'))
      exact False.elim (not_circleCyclic_both (circleCyclic_cycle h)
        (circleCyclic_cycle hbad))


/-- Two unique outer contacts also determine the side of an
arbitrary third contact in the positive coordinate loop. -/
theorem circleCyclic_iff_positive_loop_outer_contacts
    (v : C(Circle, Circle)) (hpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {a b c : Circle} (ha : ∀ w, v w = v a → w = a)
    (hb : ∀ w, v w = v b → w = b)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    CircleCyclic a c b ↔ CircleCyclic (v a) (v c) (v b) := by
  have hiff := circleCyclic_iff_positive_loop_anchor v hpos hb ha hab.symm hbc hac
  constructor
  · intro h
    exact circleCyclic_cycle (circleCyclic_cycle (hiff.mp (circleCyclic_cycle h)))
  · intro h
    exact circleCyclic_cycle (circleCyclic_cycle (hiff.mpr (circleCyclic_cycle h)))

end GraphMinor.GM06
