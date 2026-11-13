module

public import GraphMinor.GM12.Section4SubdivisionCrossingModel
public import GraphMinor.GM12.Section4ProtectedCrossDiscFamily
import GraphMinor.Surface.SurfaceGraph

/-!
# Protected crossing discs for the actual subdivision

In XII (4.5), claim (1), page 253, choose a disc around every
crossing of the subdivided source. The chord construction gives
a local coordinate model at each old meeting. The new drawing
has no triple meeting away from its vertices, so every other
new edge misses that meeting. The protected-disc construction
then excludes all vertices and unrelated new edges while
retaining the four opposite boundary marks.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric

/-- The subdivision metadata supplies all the protected small
crossing discs of XII (4.5), claim (1), page 253. Their two
crossing edges, local coordinates, and avoidance properties
are constructed rather than supplied as extra proof steps. -/
theorem exists_subdivision_crossing_discs {α β : Type*} [Finite β] {n : ℕ}
    (V : α → ℂ) (E : Fin n → Set ℂ) (s : Fin n × Bool → ℝ)
    (hinj : Function.Injective (fun q => (ee (s q) : ℂ)))
    (hchord : ∀ e, E e ∩ closedBall 0 1 =
      segment ℝ (ee (s (e, false)) : ℂ) (ee (s (e, true)) : ℂ))
    (hEinter : ∀ e f, e ≠ f → E e ∩ E f ⊆
      (segment ℝ (ee (s (e, false)) : ℂ) (ee (s (e, true)) : ℂ) ∩
        segment ℝ (ee (s (f, false)) : ℂ) (ee (s (f, true)) : ℂ)) ∪ range V)
    (hfinite : ∀ e f, e ≠ f → (E e ∩ E f).Finite)
    (k : Fin n → ℕ) (w : ∀ e, Fin (k e + 1) → ℂ) (P : ∀ e, Fin (k e) → Set ℂ)
    (hline : ∀ e i, IsLineWithEnds (P e i) (w e i.castSucc) (w e i.succ))
    (hcover : ∀ e, (⋃ i, P e i) = E e)
    (havoid : ∀ e i, w e i ∉ E e ∩ edgeMeetingPoints V E)
    (hinter : ∀ e i j, i ≠ j → P e i ∩ P e j ⊆ range (w e))
    (v : β → ℂ) (hvM : Disjoint (range v) (edgeMeetingPoints V E))
    (htriple : ∀ q r t : Σ e : Fin n, Fin (k e), q ≠ r → r ≠ t → q ≠ t →
      P q.1 q.2 ∩ P r.1 r.2 ∩ P t.1 t.2 ⊆ range v) :
    ∃ (left right : edgeMeetingPoints V E → Σ e : Fin n, Fin (k e))
      (A : edgeMeetingPoints V E → ℂ ≃L[ℝ] ℂ)
      (r : edgeMeetingPoints V E → ℝ) (D : edgeMeetingPoints V E → Set ℂ),
      (∀ x, left x ≠ right x ∧ x.val ∈ P (left x).1 (left x).2 ∩ P (right x).1 (right x).2) ∧
      (∀ x, 0 < r x) ∧ (∀ x, IsClosedDisc (D x)) ∧
      (∀ x y, x ≠ y → Disjoint (D x) (D y)) ∧
      (∀ x, x.val ∈ interior (D x)) ∧ (∀ x, Disjoint (D x) (range v)) ∧
      (∀ x q, q ≠ left x → q ≠ right x → Disjoint (D x) (P q.1 q.2)) ∧
      (∀ x, P (left x).1 (left x).2 ∩ discBd (D x) =
        {x.val + A x (r x • (1 : ℂ)), x.val + A x ((-r x) • (1 : ℂ))}) ∧
      (∀ x, P (right x).1 (right x).2 ∩ discBd (D x) =
        {x.val + A x (r x • Complex.I), x.val + A x ((-r x) • Complex.I)}) ∧
      (∀ x, D x = (fun z => x.val + A x z) '' closedBall 0 (r x)) := by
  classical
  let X := edgeMeetingPoints V E
  let Q := Σ e : Fin n, Fin (k e)
  let P' : Q → Set ℂ := fun q => P q.1 q.2
  have hX : X.Finite := finite_edgeMeetingPoints V E hfinite
  let : Fintype X := hX.fintype
  have hlocal : ∀ x : X, ∃ (q t : Q), q ≠ t ∧ x.val ∈ P' q ∩ P' t ∧
      ∃ (A : ℂ ≃L[ℝ] ℂ) (U : Set ℂ), IsOpen U ∧ x.val ∈ U ∧
        P' q ∩ U = (line[ℝ, x.val, x.val + A 1] : Set ℂ) ∩ U ∧
        P' t ∩ U = (line[ℝ, x.val, x.val + A Complex.I] : Set ℂ) ∩ U := by
    intro x
    obtain ⟨e, f, i, j, hef, hx, A, U, hU, hxU, hleft, hright⟩ :=
      exists_subdivision_crossing_model V E s hinj hchord hEinter k w P hline hcover havoid hinter x.property
    exact ⟨⟨e, i⟩, ⟨f, j⟩, (fun h => hef (congrArg Sigma.fst h)), hx, A, U, hU, hxU, hleft, hright⟩
  choose left right hne hx A U hU hxU hleft hright using hlocal
  have hxV : ∀ x : X, x.val ∉ range v := fun x h => disjoint_left.mp hvM h x.property
  have hother : ∀ x : X, ∀ q : Q, q ≠ left x → q ≠ right x → x.val ∉ P' q := by
    intro x q hql hqr hxq
    have heq := edge_eq_of_mem_pair_meeting v P' htriple (hne x)
      (show x.val ∈ (P' (left x) ∩ P' (right x)) \ range v from ⟨hx x, hxV x⟩) hxq
    exact heq.elim hql hqr
  obtain ⟨r, D, hr, hd, -, hdd, hcentre, hDv, hDP, hDL, hDR, hcoord⟩ :=
    exists_protected_cross_disc_family v P' (fun q => (hline q.1 q.2).isCompact.isClosed)
      Subtype.val Subtype.val_injective left right hxV hother A U hU hxU hleft hright
  exact ⟨left, right, A, r, D, (fun x => ⟨hne x, hx x⟩), hr, hd, hdd, hcentre, hDv, hDP, hDL, hDR, hcoord⟩

end GraphMinor.GM12
