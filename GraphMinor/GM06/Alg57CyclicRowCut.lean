module

public import GraphMinor.GM06.Alg57SourceContactOrder
public import GraphMinor.GM06.Section2Dual
public import GraphMinor.GM06.Alg57PersistentRotations
public import Mathlib.Data.List.Rotate
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Choosing the angular cut of the contracted source row

For Lemma 8 in the implementation of VI (5.7), page 133, the
computed row has a fixed first label. Cyclic order of its actual
germs must be converted to increasing arguments in one positive
polar chart. Unwrap the directions starting at that first germ,
then rotate the parameter cut into the gap before it. A finite
maximum leaves a positive gap, so every resulting argument lies
strictly between minus π and π. This changes only the angular
origin, preserving the cyclic order just proved geometrically.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem angle_lt_of_cyclic_same_base {a : Circle} {s t : ℝ}
    (hs0 : 0 < s) (hsP : s < 2 * Real.pi)
    (ht0 : 0 < t) (htP : t < 2 * Real.pi)
    (h : CircleCyclic a (a * Circle.exp s) (a * Circle.exp t)) : s < t := by
  obtain ⟨s', t', hs', hst', ht', hss, htt⟩ := h
  have hse : s = s' := exp_eq_of_angles hs0 hsP hs' (hst'.trans ht')
    (mul_left_cancel hss)
  have hte : t = t' := exp_eq_of_angles ht0 htP (hs'.trans hst') ht'
    (mul_left_cancel htt)
  simpa only [hse, hte] using hst'

/-- Any finite row in its actual cyclic order can be read in
strictly increasing arguments after rotating the angular cut. Its
first label is preserved, with no cyclic shift of the row itself. -/
theorem exists_rotation_pairwise_angle_of_cyclic_order
    (first : ℕ) (tail : List ℕ) (z : ℕ → Circle)
    (hi : InjOn z {r | r ∈ first :: tail})
    (hnd : (first :: tail).Nodup)
    (horder : (first :: tail).Pairwise (fun a b =>
      a = first ∨ CircleCyclic (z first) (z a) (z b))) :
    ∃ w : Circle, (first :: tail).Pairwise (fun a b =>
      circleStdCoord.angle (w⁻¹ * z a) < circleStdCoord.angle (w⁻¹ * z b)) := by
  classical
  let θ : ℕ → ℝ := fun r => if hz : z r = z first then 0 else
    (exists_angle (z := (z first)⁻¹ * z r)
      (fun heq => hz (inv_mul_eq_one.mp heq).symm)).choose
  have hθ0 : θ first = 0 := by simp only [θ, dite_eq_left rfl]
  have hθ (r : ℕ) : 0 ≤ θ r ∧ θ r < 2 * Real.pi ∧
      z r = z first * Circle.exp (θ r) := by
    by_cases hz : z r = z first
    · simp only [θ, dite_eq_left hz, Circle.exp_zero, mul_one]
      exact ⟨le_rfl, Real.two_pi_pos, hz⟩
    · have hh := (exists_angle (z := (z first)⁻¹ * z r)
        (fun heq => hz (inv_mul_eq_one.mp heq).symm)).choose_spec
      simp only [θ, dite_eq_right hz]
      refine ⟨hh.1.le, hh.2.1, ?_⟩
      rw [← hh.2.2]
      simp only [mul_inv_cancel_left]
  have hθpos {r : ℕ} (hr : r ∈ first :: tail) (hrf : r ≠ first) : 0 < θ r := by
    by_contra hh
    have heq : θ r = 0 := le_antisymm (le_of_not_gt hh) (hθ r).1
    have hz : z r = z first := by simpa only [heq, Circle.exp_zero, mul_one] using (hθ r).2.2
    exact hrf (hi hr (by simp) hz)
  have hθsorted : (first :: tail).Pairwise (fun a b => θ a < θ b) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi' hj' hij
    have ha : (first :: tail)[i] ∈ first :: tail := List.getElem_mem hi'
    have hb : (first :: tail)[j] ∈ first :: tail := List.getElem_mem hj'
    have hne : (first :: tail)[i] ≠ (first :: tail)[j] :=
      List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd) i j hi' hj' hij
    have hj0 : j ≠ 0 := by omega
    have hbf : (first :: tail)[j] ≠ first := by
      intro heq
      have hh := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
        0 j (by simp) hj' (Nat.pos_of_ne_zero hj0)
      exact hh (by simpa only [List.getElem_cons_zero] using heq.symm)
    rcases List.pairwise_iff_getElem.mp horder i j hi' hj' hij with hfirst | hcyc
    · rw [hfirst, hθ0]
      exact hθpos hb hbf
    · have haf : (first :: tail)[i] ≠ first := by
        intro heq
        rw [heq] at hcyc
        obtain ⟨s, t, hs, hst, ht, hss, _⟩ := hcyc
        have hse : Circle.exp s = Circle.exp 0 := by
          simpa only [Circle.exp_zero] using (mul_eq_left.mp hss.symm)
        have hh := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
          (show 2 * Real.pi - 0 ≤ 2 * Real.pi by rw [sub_zero])
          ⟨hs.le, hst.trans ht⟩ ⟨le_rfl, Real.two_pi_pos⟩ hse
        exact hs.ne' hh
      rw [(hθ (first :: tail)[i]).2.2, (hθ (first :: tail)[j]).2.2] at hcyc
      exact angle_lt_of_cyclic_same_base (hθpos ha haf) (hθ _).2.1
        (hθpos hb hbf) (hθ _).2.1 hcyc
  let A : Finset ℕ := (first :: tail).toFinset
  have hA : A.Nonempty := ⟨first, by simp [A]⟩
  let M : ℝ := A.sup' hA θ
  have hM : M < 2 * Real.pi := (Finset.sup'_lt_iff _).2 (fun r _ => (hθ r).2.1)
  have hM0 : 0 ≤ M := by
    rw [← hθ0]
    exact Finset.le_sup' θ (by simp [A])
  let ε : ℝ := (2 * Real.pi - M) / 2
  have hε : 0 < ε := by dsimp only [ε]; linarith only [hM]
  have hεM : M - Real.pi + ε < Real.pi := by
    dsimp only [ε]
    linarith only [hM]
  let w : Circle := z first * Circle.exp (Real.pi - ε)
  have hdir (r : ℕ) : w⁻¹ * z r = Circle.exp (θ r - Real.pi + ε) := by
    rw [(hθ r).2.2]
    dsimp only [w]
    rw [mul_inv_rev, mul_assoc, ← mul_assoc (z first)⁻¹, inv_mul_cancel, one_mul,
      ← Circle.exp_neg, ← Circle.exp_add]
    congr 1
    ring
  have harg (r : ℕ) (hr : r ∈ first :: tail) :
      circleStdCoord.angle (w⁻¹ * z r) = θ r - Real.pi + ε := by
    have hle : θ r ≤ M := Finset.le_sup' θ (by simpa only [A, List.mem_toFinset] using hr)
    change Complex.arg (w⁻¹ * z r : Circle) = _
    rw [hdir]
    exact Circle.arg_exp (by linarith only [(hθ r).1, hε])
      ((show θ r - Real.pi + ε ≤ M - Real.pi + ε by linarith only [hle]).trans hεM.le)
  refine ⟨w, ?_⟩
  apply List.pairwise_iff_getElem.mpr
  intro i j hi' hj' hij
  rw [harg _ (List.getElem_mem hi'), harg _ (List.getElem_mem hj')]
  have hh := List.pairwise_iff_getElem.mp hθsorted i j hi' hj' hij
  linarith only [hh]


/-- Changing the angular origin preserves the polar rays and the
full neighbourhood of the chart's centre. -/
theorem isPolar_disc_rotate
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S} {p : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ p Φ) (w : Circle) :
    IsPolar Γ p (Φ.comp ⟨section5RotateDisc w, (section5RotateDisc w).continuous⟩) := by
  have hzero : section5RotateDisc w polarCentre = polarCentre := by
    apply Subtype.ext
    change planeOf ((w : ℂ) * planeOf.symm 0) = 0
    simp
  have hrange : range (Φ.comp ⟨section5RotateDisc w, (section5RotateDisc w).continuous⟩) = range Φ := by
    exact (section5RotateDisc w).surjective.range_comp Φ
  refine ⟨hp.inj.comp (section5RotateDisc w).injective, ?_, ?_, ?_⟩
  · change Φ (section5RotateDisc w polarCentre) = p
    rw [hzero, hp.centre]
  · rw [hrange]
    exact hp.nhd
  · intro x hx r hr
    have hx' : section5RotateDisc w x ≠ polarCentre :=
      fun he => hx ((section5RotateDisc w).injective (he.trans hzero.symm))
    obtain ⟨a, ha, hxA, hrA⟩ := hp.ray (section5RotateDisc w x) hx' r hr
    refine ⟨a, ha, hxA, ?_⟩
    have hcomm : section5RotateDisc w (discScale r x) = discScale r (section5RotateDisc w x) := by
      apply Subtype.ext
      change planeOf ((w : ℂ) * planeOf.symm ((r : ℝ) • x.val)) =
        (r : ℝ) • planeOf ((w : ℂ) * planeOf.symm x.val)
      simp only [map_smul, mul_smul_comm]
    change Φ (section5RotateDisc w (discScale r x)) ∈ a
    rw [hcomm]
    exact hrA

/-- A row whose actual germs have the stated cyclic order has the
permanent positive-row interpretation. Rotate only the chart's
angular cut, keeping the numeric row and its first label fixed. -/
theorem persistent_rotation_row_of_cyclic_order
    {Γ : Drawing (OnePoint EuclideanPlane)} (label : Γ.E ↪ ℕ)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ p Φ) (hpos : GM06PositivePolar Φ)
    (first : ℕ) (tail : List ℕ) (z : ℕ → Circle)
    (hnd : (first :: tail).Nodup)
    (hmem : ∀ r, r ∈ first :: tail ↔ ∃ a : halfEdges Γ γ p,
      gm06PersistentHalfEdgeLabel label a = r)
    (hi : InjOn z {r | r ∈ first :: tail})
    (horder : (first :: tail).Pairwise (fun a b =>
      a = first ∨ CircleCyclic (z first) (z a) (z b)))
    (hspoke : ∀ a : halfEdges Γ γ p, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val))
    (hlabel : ∀ (f : Γ.E) (w : Circle), polarRimMap Φ w ∈ f.val ↔
      ∃ r ∈ first :: tail, z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1)) :
    GM06PersistentRotationRowRep label γ p (first :: tail) := by
  obtain ⟨w, hsorted⟩ := exists_rotation_pairwise_angle_of_cyclic_order first tail z hi hnd horder
  let Φ' := Φ.comp ⟨section5RotateDisc w, (section5RotateDisc w).continuous⟩
  let z' : ℕ → Circle := fun r => w⁻¹ * z r
  have hcancel (r : ℕ) : w * z' r = z r := by simp only [z', mul_inv_cancel_left]
  refine ⟨hnd, hmem, Or.inr ⟨Φ', z', isPolar_disc_rotate hp w, hpos.disc_rotate hp.inj w,
    ?_, hsorted, ?_, ?_⟩⟩
  · intro a ha b hb heq
    exact hi ha hb (mul_left_cancel heq)
  · intro a t ht
    change Φ (section5RotateDisc w (polarDiscPoint t (z' _))) ∈ _
    rw [section5RotateDisc_polarDiscPoint, hcancel]
    exact hspoke a t ht
  · intro f u
    change Φ (section5RotateDisc w (polarDiscPoint 1 u)) ∈ f.val ↔ _
    rw [section5RotateDisc_polarDiscPoint]
    change polarRimMap Φ (w * u) ∈ f.val ↔ _
    rw [hlabel]
    constructor
    · rintro ⟨r, hr, hru, hl⟩
      exact ⟨r, hr, by simp only [z', hru, inv_mul_cancel_left], hl⟩
    · rintro ⟨r, hr, hru, hl⟩
      exact ⟨r, hr, (hcancel r).symm.trans (congrArg (fun u => w * u) hru), hl⟩


/-- Reading the old target row just after its incoming end gives
strictly increasing angles between zero and one full turn. This
is exactly the suffix-then-prefix order used by the finite splice. -/
theorem exists_increasing_angles_after_row_entry
    (ys : List ℕ) (z : ℕ → Circle)
    (hs : ys.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    (q : ℕ) (hq : q < ys.length) :
    ∃ θ : ℕ → ℝ,
      (∀ r ∈ ys.drop (q + 1) ++ ys.take q, 0 < θ r ∧ θ r < 2 * Real.pi ∧
        z r = z ys[q] * Circle.exp (θ r)) ∧
      (ys.drop (q + 1) ++ ys.take q).Pairwise (fun a b => θ a < θ b) := by
  change ys.Pairwise (fun a b => Complex.arg (z a : ℂ) < Complex.arg (z b : ℂ)) at hs
  let A : ℕ → ℝ := fun r => Complex.arg (z r : ℂ)
  let base : ℝ := A ys[q]
  have hafter (a : ℕ) (ha : a ∈ ys.drop (q + 1)) : base < A a := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hj' : q + 1 + j < ys.length := by rw [List.length_drop] at hj; omega
    rw [List.getElem_drop]
    exact List.pairwise_iff_getElem.mp hs q (q + 1 + j) hq hj' (by omega)
  have hbefore (a : ℕ) (ha : a ∈ ys.take q) : A a < base := by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    have hjq : j < q := by rw [List.length_take] at hj; omega
    have hj' : j < ys.length := hjq.trans hq
    rw [List.getElem_take]
    exact List.pairwise_iff_getElem.mp hs j q hj' hq hjq
  let θ : ℕ → ℝ := fun r => if base < A r then A r - base else A r - base + 2 * Real.pi
  have hspan (a b : ℕ) : A a - A b < 2 * Real.pi := by
    have ha := Complex.arg_le_pi (z a : ℂ)
    have hb := Complex.neg_pi_lt_arg (z b : ℂ)
    dsimp only [A]
    linarith only [ha, hb]
  have hrepr (r : ℕ) : z r = z ys[q] * Circle.exp (θ r) := by
    have hh : z ys[q] * Circle.exp (A r - base) = z r := by
      dsimp only [A, base]
      rw [Circle.exp_sub, Circle.exp_arg, Circle.exp_arg]
      simp only [div_eq_mul_inv, mul_left_comm, mul_inv_cancel, mul_one]
    dsimp only [θ]
    split
    · exact hh.symm
    · rw [Circle.exp_add_two_pi]
      exact hh.symm
  refine ⟨θ, ?_, ?_⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have hh := hafter r hr
      have hp := hspan r ys[q]
      refine ⟨?_, ?_, hrepr r⟩
      · simp only [θ, if_pos hh]
        linarith only [hh]
      · simpa only [θ, if_pos hh] using hp
    · have hh := hbefore r hr
      have hp := hspan ys[q] r
      refine ⟨?_, ?_, hrepr r⟩
      · simp only [θ, if_neg (not_lt.mpr hh.le)]
        linarith only [hp]
      · simp only [θ, if_neg (not_lt.mpr hh.le)]
        linarith only [hh]
  · apply List.pairwise_append.mpr
    refine ⟨?_, ?_, ?_⟩
    · apply List.Pairwise.imp_of_mem ?_ (List.Pairwise.sublist (List.drop_sublist _ _) hs)
      intro a b ha hb hab
      simp only [θ, if_pos (hafter a ha), if_pos (hafter b hb)]
      exact sub_lt_sub_right hab base
    · apply List.Pairwise.imp_of_mem ?_ (List.Pairwise.sublist (List.take_sublist _ _) hs)
      intro a b ha hb hab
      simp only [θ, if_neg (not_lt.mpr (hbefore a ha).le), if_neg (not_lt.mpr (hbefore b hb).le)]
      linarith only [hab]
    · intro a ha b hb
      simp only [θ, if_pos (hafter a ha), if_neg (not_lt.mpr (hbefore b hb).le)]
      have hh := hspan a b
      linarith only [hh]


/-- The permanent positive-row interpretation is unchanged by a
cyclic shift of the numeric row. A new angular cut is constructed
inside the same positive chart, preserving every actual end label. -/
theorem GM06PersistentRotationRowRep.rotate
    {Γ : Drawing (OnePoint EuclideanPlane)} {label : Γ.E ↪ ℕ}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v xs) (q : ℕ) :
    GM06PersistentRotationRowRep label γ v (xs.rotate q) := by
  classical
  have hnd : (xs.rotate q).Nodup := List.nodup_rotate.mpr hrow.1
  have hmem : ∀ r, r ∈ xs.rotate q ↔ ∃ a : halfEdges Γ γ v,
      gm06PersistentHalfEdgeLabel label a = r := by
    intro r
    rw [List.mem_rotate]
    exact hrow.2.1 r
  rcases hrow.2.2 with hsmall | ⟨Φ, z, hp, hpos, hi, hs, hspoke, hlabel⟩
  · exact ⟨hnd, hmem, Or.inl (by simpa only [List.length_rotate] using hsmall)⟩
  by_cases hx : xs = []
  · subst xs
    simpa only [List.rotate_nil] using hrow
  have hxpos : 0 < xs.length := List.length_pos_iff.mpr hx
  let p := q % xs.length
  have hp' : p < xs.length := Nat.mod_lt q hxpos
  let tail := xs.drop (p + 1) ++ xs.take p
  have hrot : xs.rotate q = xs[p] :: tail := by
    rw [List.rotate_eq_drop_append_take_mod, List.drop_eq_getElem_cons hp']
    rfl
  have hmem' (r : ℕ) : r ∈ xs[p] :: tail ↔ r ∈ xs := by
    rw [← hrot, List.mem_rotate]
  have hnd' : (xs[p] :: tail).Nodup := hrot ▸ hnd
  have hi' : InjOn z {r | r ∈ xs[p] :: tail} := fun _ ha _ hb heq =>
    hi ((hmem' _).mp ha) ((hmem' _).mp hb) heq
  obtain ⟨θ, hθ, hθsort⟩ := exists_increasing_angles_after_row_entry xs z hs p hp'
  have htail : tail.Pairwise (fun a b => CircleCyclic (z xs[p]) (z a) (z b)) := by
    apply List.Pairwise.imp_of_mem ?_ hθsort
    intro a b ha hb hab
    have hθa := hθ a ha
    have hθb := hθ b hb
    exact ⟨θ a, θ b, hθa.1, hab, hθb.2.1, hθa.2.2, hθb.2.2⟩
  have horder : (xs[p] :: tail).Pairwise (fun a b =>
      a = xs[p] ∨ CircleCyclic (z xs[p]) (z a) (z b)) :=
    List.pairwise_cons.mpr ⟨fun _ _ => Or.inl rfl,
      List.Pairwise.imp (fun h => Or.inr h) htail⟩
  have hlabel' (f : Γ.E) (w : Circle) : polarRimMap Φ w ∈ f.val ↔
      ∃ r ∈ xs[p] :: tail, z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1) := by
    rw [hlabel]
    simp only [hmem']
  rw [hrot]
  exact persistent_rotation_row_of_cyclic_order label hp hpos xs[p] tail z hnd'
    (fun r => (hmem' r).trans (hrow.2.1 r)) hi' horder hspoke hlabel'

end GraphMinor.GM06
