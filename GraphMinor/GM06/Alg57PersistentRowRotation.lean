module

public import GraphMinor.GM06.Alg57PersistentRotations
public import GraphMinor.GM06.Alg57RowRotation

/-!
# The drawing rotation read from permanent-label rows

The current arrays of VI (5.7), page 133, keep gaps in their edge
labels after deletions. The row-to-rotation proof uses injectivity
of directed labels, rather than consecutiveness of the edge labels.
We run that same proof with the permanent edge injection. Positive
polar charts still give the counterclockwise successor in each row.
-/

@[expose] public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval Equiv

/-- The permanent directed word of a drawing dart. -/
def persistentDartLabel {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) (d : DrawingDart Γ) : ℕ :=
  2 * label ⟨d.val.1, d.property⟩ + d.val.2.toNat

/-- The two actual directed ends retain different permanent words. -/
theorem persistentDartLabel_injective {Γ : Drawing (OnePoint EuclideanPlane)}
    (label : Γ.E ↪ ℕ) : Function.Injective (persistentDartLabel label) := by
  intro a b hab
  have hh := gm06PersistentHalfEdgeLabel_data_eq label (dartHalfEdge
    (fun _ _ => (OnePoint.infty : OnePoint EuclideanPlane)) a)
    (dartHalfEdge (fun _ _ => (OnePoint.infty : OnePoint EuclideanPlane)) b) hab
  exact Subtype.ext hh

variable {Γ : Drawing (OnePoint EuclideanPlane)} {label : Γ.E ↪ ℕ}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}

/-- The word of a dart belongs to the row at its vertex. -/
theorem persistentDartLabel_mem_row {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v xs) {d : DrawingDart Γ}
    (hd : dartVertex γ d = v) : persistentDartLabel label d ∈ xs := by
  subst hd
  exact (hrow.2.1 _).mpr ⟨dartHalfEdge γ d, rfl⟩

/-- Every current row word is the permanent label of an actual dart
at that row's vertex. -/
theorem exists_persistentDart_of_mem_row {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v xs) {r : ℕ} (hr : r ∈ xs) :
    ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ persistentDartLabel label d = r := by
  obtain ⟨a, ha⟩ := (hrow.2.1 r).mp hr
  exact ⟨halfEdgeDart a, dartVertex_halfEdgeDart a, ha⟩

/-- The actual counterclockwise drawing rotation and its successor
word are read from the permanent current rows. -/
theorem exists_ccwRotation_of_persistent_rows (hγ : EdgePar Γ γ)
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.V)
    (rows : OnePoint EuclideanPlane → List ℕ)
    (hrows : ∀ v ∈ Γ.V, GM06PersistentRotationRowRep label γ v (rows v)) :
    ∃ R : DartRotation (DrawingDart Γ), IsDrawingRotation Γ γ R ∧ IsCcwRotation Γ γ R ∧
      R.rev = dartFlip Γ ∧
      ∀ d, persistentDartLabel label (R.rot d) = (rows (dartVertex γ d)).formPerm (persistentDartLabel label d) := by
  classical
  have hrow : ∀ d : DrawingDart Γ, GM06PersistentRotationRowRep label γ (dartVertex γ d)
      (rows (dartVertex γ d)) := fun d => hrows _ (dartVertex_mem hγ d)
  -- the dart with the next label
  have hnext : ∀ d : DrawingDart Γ, ∃ d' : DrawingDart Γ, dartVertex γ d' = dartVertex γ d ∧
      persistentDartLabel label d' = (rows (dartVertex γ d)).formPerm (persistentDartLabel label d) := fun d =>
    exists_persistentDart_of_mem_row (hrow d)
      (List.formPerm_apply_mem_of_mem (persistentDartLabel_mem_row (hrow d) rfl))
  choose f hfv hfl using hnext
  have hfi : Function.Injective f := by
    intro a b hab
    have hv : dartVertex γ a = dartVertex γ b := by rw [← hfv a, ← hfv b, hab]
    have hl := hfl a
    rw [hab, hfl b, hv] at hl
    exact persistentDartLabel_injective label ((List.formPerm _).injective hl).symm
  let rot : Perm (DrawingDart Γ) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  have hrot : ∀ d, rot d = f d := fun _ => rfl
  let R := flipRotation Γ rot
  -- powers of the rotation follow powers of `formPerm` on labels
  have hpow : ∀ (n : ℕ) (d : DrawingDart Γ), dartVertex γ ((rot ^ n) d) = dartVertex γ d ∧
      persistentDartLabel label ((rot ^ n) d) = ((rows (dartVertex γ d)).formPerm ^ n) (persistentDartLabel label d) := by
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
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem (persistentDartLabel_mem_row (hrow d) rfl)
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem (persistentDartLabel_mem_row (hrow d) hdd.symm)
    set xs := rows (dartVertex γ d)
    have hnd : xs.Nodup := (hrow d).1
    refine ⟨((j + xs.length - i : ℕ) : ℤ), ?_⟩
    rw [zpow_natCast]
    apply persistentDartLabel_injective label
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
    apply persistentDartLabel_injective label
    have hbm := persistentDartLabel_mem_row (hrows v hv) hb
    have hcm := persistentDartLabel_mem_row (hrows v hv) hc
    match hxs : rows v, hlen with
    | [], _ => rw [hxs] at hbm; simp at hbm
    | [x], _ =>
      rw [hxs, List.mem_singleton] at hbm hcm
      rw [hbm, hcm]
    | _ :: _ :: _, hl => simp at hl
  obtain ⟨hnd, -, hsmall | ⟨Φ, zN, hp, hpos, hzi, hs, hspoke, hlabel⟩⟩ := hrows v hv
  · omega
  · refine ⟨Φ, fun d => zN (persistentDartLabel label d), hp, hpos, ?_, ?_, ?_, ?_⟩
    · intro b c hb hc hbc
      exact persistentDartLabel_injective label (hzi (persistentDartLabel_mem_row (hrows v hv) hb)
        (persistentDartLabel_mem_row (hrows v hv) hc) hbc)
    · intro b hb t ht
      subst hb
      exact hspoke (dartHalfEdge γ b) t ht
    · intro w e he hwe
      obtain ⟨r, hr, hzr, -⟩ := (hlabel ⟨e, he⟩ w).mp hwe
      obtain ⟨b, hb, hbr⟩ := exists_persistentDart_of_mem_row (hrows v hv) hr
      exact ⟨b, hb, by simp only [hbr, hzr]⟩
    · intro b c hb hc
      have hrb : persistentDartLabel label (R.rot b) = (rows v).formPerm (persistentDartLabel label b) := by
        rw [← hb]; exact hfl b
      simp only [hrb]
      exact not_circleCyclic_formPerm hnd hlen zN hs (persistentDartLabel_mem_row (hrows v hv) hb)
        (persistentDartLabel_mem_row (hrows v hv) hc)


end GraphMinor.GM06
