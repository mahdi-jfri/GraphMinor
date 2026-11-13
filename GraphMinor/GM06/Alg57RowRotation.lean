module

public import GraphMinor.GM06.Alg57CornerLabelExists
public import GraphMinor.GM06.Alg57PositiveRotations
import GraphMinor.GM07.StarDisc
import GraphMinor.GM06.Section5PolarHalfedgeEquiv

/-!
# The input rotation rows give the counterclockwise rotation

The input of VI (5.7) gives, at each vertex `v`, a row of dart labels
(`GM06SuccessorRotationRowRep`). A dart of the edge `edge j` with end bit `b` has label
`2 j + b` (`dartLabel`). When the row has at least two entries it comes with a positive polar
chart at `v` in which the labels are sorted by angle.

Here we read the rotation off the rows: the next dart after `d` is the dart whose label follows
the label of `d` cyclically in the row of the vertex of `d` (`List.formPerm`). We show that this
rotation fits the drawing and is counterclockwise in the sense of `IsCcwRotation`
(`exists_ccwRotation_of_rows`). This is the step from the finite input to the topology of
Sections 2 and 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`).

The order part rests on one fact about angles (`not_circleCyclic_of_arg_lt`,
`not_circleCyclic_of_arg_wrap`): if the angles in a row increase, then going counterclockwise
from an entry, no entry of the row comes strictly before the next entry of the row. At a vertex
with at most one dart the row has no chart, so we take any positive polar chart there
(`exists_positive_polar_chart`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval Equiv

/-! ### Angles and the cyclic order -/

/-- Two angles with the same point on the circle and difference less than `2π` are equal. -/
theorem eq_of_circle_exp_eq {x y : ℝ} (h : Circle.exp x = Circle.exp y)
    (habs : |x - y| < 2 * Real.pi) : x = y := by
  by_contra hne
  exact circle_exp_ne hne habs h

/-- If `arg a < arg c`, and `arg b` is not strictly between them, then `b` does not come
strictly between `a` and `c` counterclockwise. -/
theorem not_circleCyclic_of_arg_lt {a b c : Circle} (hac : Complex.arg a < Complex.arg c)
    (hb : Complex.arg b ≤ Complex.arg a ∨ Complex.arg c ≤ Complex.arg b) :
    ¬ CircleCyclic a b c := by
  rintro ⟨s, t, hs, hst, ht, hbs, hct⟩
  have hpi := Real.pi_pos
  have ha1 := Complex.neg_pi_lt_arg (a : ℂ)
  have ha2 := Complex.arg_le_pi (a : ℂ)
  have hb1 := Complex.neg_pi_lt_arg (b : ℂ)
  have hb2 := Complex.arg_le_pi (b : ℂ)
  have hc1 := Complex.neg_pi_lt_arg (c : ℂ)
  have hc2 := Complex.arg_le_pi (c : ℂ)
  have eb : Circle.exp (Complex.arg b) = Circle.exp (Complex.arg a + s) := by
    rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg, hbs]
  have ec : Circle.exp (Complex.arg c) = Circle.exp (Complex.arg a + t) := by
    rw [Circle.exp_add, Circle.exp_arg, Circle.exp_arg, hct]
  have htc : Complex.arg c = Complex.arg a + t :=
    eq_of_circle_exp_eq ec (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
  rcases hb with hb | hb
  · have eb' : Circle.exp (Complex.arg b + 2 * Real.pi) = Circle.exp (Complex.arg a + s) := by
      rw [Circle.exp_add, Circle.exp_two_pi, mul_one, eb]
    have := eq_of_circle_exp_eq eb' (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    linarith
  · have := eq_of_circle_exp_eq eb (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
    linarith

/-- If `arg c < arg a`, and `arg b` lies between them, then `b` does not come strictly between
`a` and `c` counterclockwise: going counterclockwise from `a` one passes the angle `π` and then
meets `c` before any angle in `[arg c, arg a)`. -/
theorem not_circleCyclic_of_arg_wrap {a b c : Circle} (hca : Complex.arg c < Complex.arg a)
    (hcb : Complex.arg c ≤ Complex.arg b) (hba : Complex.arg b ≤ Complex.arg a) :
    ¬ CircleCyclic a b c := by
  rintro ⟨s, t, hs, hst, ht, hbs, hct⟩
  have hpi := Real.pi_pos
  have ha1 := Complex.neg_pi_lt_arg (a : ℂ)
  have ha2 := Complex.arg_le_pi (a : ℂ)
  have hc1 := Complex.neg_pi_lt_arg (c : ℂ)
  have hc2 := Complex.arg_le_pi (c : ℂ)
  have eb : Circle.exp (Complex.arg b + 2 * Real.pi) = Circle.exp (Complex.arg a + s) := by
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one, Circle.exp_add, Circle.exp_arg,
      Circle.exp_arg, hbs]
  have ec : Circle.exp (Complex.arg c + 2 * Real.pi) = Circle.exp (Complex.arg a + t) := by
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one, Circle.exp_add, Circle.exp_arg,
      Circle.exp_arg, hct]
  have htc := eq_of_circle_exp_eq ec (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
  have hsb := eq_of_circle_exp_eq eb (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)
  linarith

/-- No point comes strictly between a point and itself. -/
theorem not_circleCyclic_self (a b : Circle) : ¬ CircleCyclic a b a := by
  rintro ⟨s, t, hs, hst, ht, -, hct⟩
  have h1 : Circle.exp t = Circle.exp 0 := by
    rw [Circle.exp_zero]
    exact (mul_eq_left.mp hct.symm)
  have hpi := Real.pi_pos
  exact circle_exp_ne (by linarith : t ≠ 0)
    (by rw [sub_zero, abs_of_pos (by linarith)]; exact ht) h1

/-- In a row whose angles increase, no entry comes strictly between an entry and the next entry
of the row, counterclockwise. -/
theorem not_circleCyclic_formPerm {xs : List ℕ} (hnd : xs.Nodup) (hlen : 2 ≤ xs.length)
    (z : ℕ → Circle)
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    {x y : ℕ} (hx : x ∈ xs) (hy : y ∈ xs) : ¬ CircleCyclic (z x) (z y) (z (xs.formPerm x)) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  rw [List.formPerm_apply_getElem xs hnd i hi]
  have hlt : ∀ (p q : ℕ) (hp : p < xs.length) (hq : q < xs.length), p < q →
      Complex.arg (z xs[p]) < Complex.arg (z xs[q]) := fun p q hp hq hpq =>
    List.pairwise_iff_getElem.mp hs p q hp hq hpq
  have hle : ∀ (p q : ℕ) (hp : p < xs.length) (hq : q < xs.length), p ≤ q →
      Complex.arg (z xs[p]) ≤ Complex.arg (z xs[q]) := fun p q hp hq hpq => by
    rcases eq_or_lt_of_le hpq with h | h
    · subst h; exact le_rfl
    · exact (hlt p q hp hq h).le
  by_cases hnext : i + 1 < xs.length
  · have hmod : (i + 1) % xs.length = i + 1 := Nat.mod_eq_of_lt hnext
    simp only [hmod]
    refine not_circleCyclic_of_arg_lt (hlt i (i + 1) hi hnext (by omega)) ?_
    rcases le_or_gt j i with hji | hji
    · exact Or.inl (hle j i hj hi hji)
    · exact Or.inr (hle (i + 1) j hnext hj (by omega))
  · have hi1 : i + 1 = xs.length := by omega
    have hmod : (i + 1) % xs.length = 0 := by rw [hi1, Nat.mod_self]
    simp only [hmod]
    exact not_circleCyclic_of_arg_wrap (hlt 0 i (by omega) hi (by omega))
      (hle 0 j (by omega) hj (by omega)) (hle j i hj hi (by omega))

/-! ### Labels of darts -/

variable {Γ : Drawing (OnePoint EuclideanPlane)} {m : ℕ} {edge : Fin m ≃ Γ.E}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}

/-- The label of a dart in the input: twice the index of its edge, plus its end bit. -/
def dartLabel (edge : Fin m ≃ Γ.E) (d : DrawingDart Γ) : ℕ :=
  2 * (edge.symm ⟨d.1.1, d.2⟩).val + d.1.2.toNat

/-- The half-edge at the vertex of a dart, given by the dart. -/
def dartHalfEdge (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (d : DrawingDart Γ) : halfEdges Γ γ (dartVertex γ d) :=
  ⟨d.1, d.2, rfl⟩

theorem halfEdgeLabel_dartHalfEdge (d : DrawingDart Γ) :
    halfEdgeLabel edge (dartHalfEdge γ d) = dartLabel edge d := rfl

/-- The dart of a half-edge at `v`. -/
def halfEdgeDart {v : OnePoint EuclideanPlane} (a : halfEdges Γ γ v) : DrawingDart Γ :=
  ⟨a.1, a.2.1⟩

theorem dartVertex_halfEdgeDart {v : OnePoint EuclideanPlane} (a : halfEdges Γ γ v) :
    dartVertex γ (halfEdgeDart a) = v := a.2.2

theorem dartLabel_halfEdgeDart {v : OnePoint EuclideanPlane} (a : halfEdges Γ γ v) :
    dartLabel edge (halfEdgeDart a) = halfEdgeLabel edge a := rfl

/-- Different darts have different labels. -/
theorem dartLabel_injective (edge : Fin m ≃ Γ.E) : Function.Injective (dartLabel edge) := by
  intro a b hab
  have hba : a.1.2.toNat ≤ 1 := by cases a.1.2 <;> decide
  have hbb : b.1.2.toNat ≤ 1 := by cases b.1.2 <;> decide
  have hi : edge.symm ⟨a.1.1, a.2⟩ = edge.symm ⟨b.1.1, b.2⟩ := by
    apply Fin.ext
    unfold dartLabel at hab
    omega
  have he : a.1.1 = b.1.1 := congrArg Subtype.val (edge.symm.injective hi)
  have hb : a.1.2 = b.1.2 := by
    unfold dartLabel at hab
    rw [hi] at hab
    have hn : a.1.2.toNat = b.1.2.toNat := Nat.add_left_cancel hab
    cases ha : a.1.2 <;> cases hb : b.1.2 <;> simp_all
  exact Subtype.ext (Prod.ext he hb)

/-- The label of a dart at `v` is in the row of `v`. -/
theorem dartLabel_mem_row {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) {d : DrawingDart Γ}
    (hd : dartVertex γ d = v) : dartLabel edge d ∈ xs := by
  subst hd
  exact (hrow.2.1 _).mpr ⟨dartHalfEdge γ d, rfl⟩

/-- Every entry of the row of `v` is the label of a dart at `v`. -/
theorem exists_dart_of_mem_row {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) {r : ℕ} (hr : r ∈ xs) :
    ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ dartLabel edge d = r := by
  obtain ⟨a, ha⟩ := (hrow.2.1 r).mp hr
  exact ⟨halfEdgeDart a, dartVertex_halfEdgeDart a, ha⟩

/-- Two darts at `v` with the same label are the same dart. -/
theorem eq_of_dartLabel_eq {a b : DrawingDart Γ} (h : dartLabel edge a = dartLabel edge b) :
    a = b :=
  dartLabel_injective edge h

/-! ### The rotation read from the rows -/

/-- The reversal of darts, as the rotation data `τ`. -/
def flipRotation (Γ : Drawing (OnePoint EuclideanPlane)) (rot : Perm (DrawingDart Γ)) :
    DartRotation (DrawingDart Γ) where
  rot := rot
  rev := dartFlip Γ
  rev_rev d := by simp
  rev_ne d h := by
    have := congrArg (fun x : DrawingDart Γ => x.1.2) h
    simp at this

/-- A positive polar chart at a finite vertex, with a direction for each half-edge there. This is
`exists_positive_polar_halfedge_chart` without the bound on the number of half-edges. -/
theorem exists_positive_polar_chart (hγ : EdgePar Γ γ) {v : OnePoint EuclideanPlane}
    (hv : v ∈ Γ.V) (hvfinite : v ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane)) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e}),
      IsPolar Γ v Φ ∧ GM06PositivePolar Φ ∧
      ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1) := by
  have hS := IsSphere.isClosedSurface
    (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)
  obtain ⟨Φ, hΦ⟩ := GM07.exists_isPolar_of_vertex hS.1 Γ hv
  obtain ⟨Ψ, hΨ, hfinite, d, hd⟩ := exists_polar_chart_with_halfedge_equiv hS.1 hγ hv hΦ
    OnePoint.isOpen_range_coe hvfinite
  rcases positive_polar_or_mirror Ψ hΨ.inj hfinite with hp | hp
  · exact ⟨Ψ, d, hΨ, hp, hd⟩
  · let Ψ' := Ψ.comp ⟨alg511DiscMirror 0, (alg511DiscMirror 0).continuous⟩
    have hΨ' : IsPolar Γ v Ψ' := alg511_isPolar_comp_discMirror hΨ 0
    have hmirror (t : I) (w : Circle) : Ψ' (polarDiscPoint t w) = Ψ (polarDiscPoint t w⁻¹) := by
      change Ψ (alg511DiscMirror 0 (polarDiscPoint t w)) = _
      rw [alg511DiscMirror_polarDiscPoint]
      congr 2
      change Circle.exp 0 * w⁻¹ = w⁻¹
      rw [Circle.exp_zero, one_mul]
    let W := {w : Circle | ∃ e ∈ Γ.E, polarRimMap Ψ w ∈ e}
    let W' := {w : Circle | ∃ e ∈ Γ.E, polarRimMap Ψ' w ∈ e}
    let eW : W ≃ W' := {
      toFun := fun w => ⟨w.val⁻¹, by
        obtain ⟨e, he, hw⟩ := w.property
        refine ⟨e, he, ?_⟩
        change Ψ' (polarDiscPoint 1 w.val⁻¹) ∈ e
        rw [hmirror, inv_inv]
        exact hw⟩
      invFun := fun w => ⟨w.val⁻¹, by
        obtain ⟨e, he, hw⟩ := w.property
        refine ⟨e, he, ?_⟩
        change Ψ' (polarDiscPoint 1 w.val) ∈ e at hw
        rw [hmirror] at hw
        exact hw⟩
      left_inv := fun w => Subtype.ext (inv_inv w.val)
      right_inv := fun w => Subtype.ext (inv_inv w.val) }
    refine ⟨Ψ', d.trans eW, hΨ', hp, ?_⟩
    intro a t ht
    change Ψ' (polarDiscPoint t (d a).val⁻¹) ∈ _
    rw [hmirror, inv_inv]
    exact hd a t ht

/-- At a finite vertex with at most one dart, any rotation that stays at the vertex is
counterclockwise there. -/
theorem exists_ccwStar_of_subsingleton (hγ : EdgePar Γ γ) {R : DartRotation (DrawingDart Γ)}
    (hvert : ∀ d, dartVertex γ (R.rot d) = dartVertex γ d) {v : OnePoint EuclideanPlane}
    (hv : v ∈ Γ.V) (hvfinite : v ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane))
    (hsub : ∀ a b : DrawingDart Γ, dartVertex γ a = v → dartVertex γ b = v → a = b) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : DrawingDart Γ → Circle),
      IsCcwStar Γ γ R v Φ z := by
  classical
  obtain ⟨Φ, D, hp, hpos, hd⟩ := exists_positive_polar_chart hγ hv hvfinite
  let z : DrawingDart Γ → Circle := fun d =>
    if h : dartVertex γ d = v then (D ⟨d.1, d.2, h⟩).1 else 1
  have hz : ∀ (a : halfEdges Γ γ v), z (halfEdgeDart a) = (D a).1 := by
    intro a
    simp only [z, dartVertex_halfEdgeDart, dite_true]
    rfl
  refine ⟨Φ, z, hp, hpos, fun a b ha hb _ => hsub a b ha hb, ?_, ?_, ?_⟩
  · intro a ha t ht
    have := hz ⟨a.1, a.2, ha⟩
    change z a = _ at this
    rw [this]
    exact hd ⟨a.1, a.2, ha⟩ t ht
  · intro w e he hwe
    obtain ⟨a, ha⟩ := D.surjective ⟨w, e, he, hwe⟩
    refine ⟨halfEdgeDart a, dartVertex_halfEdgeDart a, ?_⟩
    rw [hz, ha]
  · intro a b ha hb
    have h1 : b = a := hsub b a hb ha
    have h2 : R.rot a = a := hsub _ a (by rw [hvert, ha]) ha
    rw [h1, h2]
    exact not_circleCyclic_self _ _

/-- **The rows give the counterclockwise rotation.** Let every vertex of a drawing in the sphere
be a finite point with a row in the sense of `GM06SuccessorRotationRowRep`. Then the rotation
that sends each dart to the dart with the next label in the row of its vertex fits the drawing
and is counterclockwise. -/
theorem exists_ccwRotation_of_rows (hγ : EdgePar Γ γ)
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.V)
    (rows : OnePoint EuclideanPlane → List ℕ)
    (hrows : ∀ v ∈ Γ.V, GM06SuccessorRotationRowRep edge γ v (rows v)) :
    ∃ R : DartRotation (DrawingDart Γ), IsDrawingRotation Γ γ R ∧ IsCcwRotation Γ γ R ∧
      R.rev = dartFlip Γ ∧
      ∀ d, dartLabel edge (R.rot d) = (rows (dartVertex γ d)).formPerm (dartLabel edge d) := by
  classical
  have hrow : ∀ d : DrawingDart Γ, GM06SuccessorRotationRowRep edge γ (dartVertex γ d)
      (rows (dartVertex γ d)) := fun d => hrows _ (dartVertex_mem hγ d)
  -- the dart with the next label
  have hnext : ∀ d : DrawingDart Γ, ∃ d' : DrawingDart Γ, dartVertex γ d' = dartVertex γ d ∧
      dartLabel edge d' = (rows (dartVertex γ d)).formPerm (dartLabel edge d) := fun d =>
    exists_dart_of_mem_row (hrow d)
      (List.formPerm_apply_mem_of_mem (dartLabel_mem_row (hrow d) rfl))
  choose f hfv hfl using hnext
  have hfi : Function.Injective f := by
    intro a b hab
    have hv : dartVertex γ a = dartVertex γ b := by rw [← hfv a, ← hfv b, hab]
    have hl := hfl a
    rw [hab, hfl b, hv] at hl
    exact dartLabel_injective edge ((List.formPerm _).injective hl).symm
  let rot : Perm (DrawingDart Γ) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  have hrot : ∀ d, rot d = f d := fun _ => rfl
  let R := flipRotation Γ rot
  -- powers of the rotation follow powers of `formPerm` on labels
  have hpow : ∀ (n : ℕ) (d : DrawingDart Γ), dartVertex γ ((rot ^ n) d) = dartVertex γ d ∧
      dartLabel edge ((rot ^ n) d) = ((rows (dartVertex γ d)).formPerm ^ n) (dartLabel edge d) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      obtain ⟨h1, h2⟩ := ih d
      rw [pow_succ', Perm.mul_apply, hrot, hfv, h1, hfl, h1, h2, pow_succ', Perm.mul_apply]
      exact ⟨rfl, rfl⟩
  have hreach : ∀ d d', dartVertex γ d = dartVertex γ d' → rot.SameCycle d d' := by
    intro d d' hdd
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (dartLabel_mem_row (hrow d) rfl)
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem (dartLabel_mem_row (hrow d) hdd.symm)
    set xs := rows (dartVertex γ d)
    have hnd : xs.Nodup := (hrow d).1
    refine ⟨((j + xs.length - i : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast]
    apply dartLabel_injective edge
    rw [(hpow _ d).2, ← hix, List.formPerm_pow_apply_getElem xs hnd _ i hi, hjx.symm]
    congr 1
    rw [show i + (j + xs.length - i) = j + xs.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  refine ⟨R, ⟨fun _ => rfl, fun d => hfv d, hreach⟩, ?_, rfl, hfl⟩
  intro v ⟨a, ha⟩
  have hv : v ∈ Γ.V := ha ▸ dartVertex_mem hγ a
  have hvfinite : v ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) := by
    obtain ⟨x, hx⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hinf (h ▸ hv))
    exact ⟨x, hx⟩
  by_cases hlen : 2 ≤ (rows v).length
  swap
  · refine exists_ccwStar_of_subsingleton hγ (R := R) hfv hv hvfinite fun b c hb hc => ?_
    apply dartLabel_injective edge
    have hbm := dartLabel_mem_row (hrows v hv) hb
    have hcm := dartLabel_mem_row (hrows v hv) hc
    match hxs : rows v, hlen with
    | [], _ => rw [hxs] at hbm; simp at hbm
    | [x], _ =>
      rw [hxs, List.mem_singleton] at hbm hcm
      rw [hbm, hcm]
    | _ :: _ :: _, hl => simp at hl
  obtain ⟨hnd, -, hsmall | ⟨Φ, zN, hp, hpos, hzi, hs, hspoke, hlabel⟩⟩ := hrows v hv
  · omega
  · refine ⟨Φ, fun d => zN (dartLabel edge d), hp, hpos, ?_, ?_, ?_, ?_⟩
    · intro b c hb hc hbc
      exact dartLabel_injective edge (hzi (dartLabel_mem_row (hrows v hv) hb)
        (dartLabel_mem_row (hrows v hv) hc) hbc)
    · intro b hb t ht
      subst hb
      exact hspoke (dartHalfEdge γ b) t ht
    · intro w e he hwe
      have hj : polarRimMap Φ w ∈ (edge (edge.symm ⟨e, he⟩)).val := by
        rw [Equiv.apply_symm_apply]; exact hwe
      obtain ⟨r, hr, hzr, -⟩ := (hlabel _ w).mp hj
      obtain ⟨b, hb, hbr⟩ := exists_dart_of_mem_row (hrows v hv) hr
      exact ⟨b, hb, by simp only [hbr, hzr]⟩
    · intro b c hb hc
      have hrb : dartLabel edge (R.rot b) = (rows v).formPerm (dartLabel edge b) := by
        rw [← hb]; exact hfl b
      simp only [hrb]
      exact not_circleCyclic_formPerm hnd hlen zN hs (dartLabel_mem_row (hrows v hv) hb)
        (dartLabel_mem_row (hrows v hv) hc)

end GraphMinor.GM06
