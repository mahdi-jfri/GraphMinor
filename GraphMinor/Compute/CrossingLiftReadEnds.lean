module

public import GraphMinor.Compute.CrossingLiftCutEnds
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the two reverse-search endpoints

Once the path scan has found its first boundary position and the position just after its
last boundary visit, two array reads load the endpoints. The last read subtracts one from
the second cut. The endpoint identities ensure that both reads lie inside the path.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Read the first and last boundary vertices from the cut registers. -/
def liftReadSearchEndsProg (path r_lo r_hi r_u r_v : ℕ) : Cmd :=
  .seq (.assign r_u (.read path (.reg r_lo)))
    (.assign r_v (.read path (.op .sub (.reg r_hi) (.const 1))))

/-- The cut reads return exactly the endpoints specified by `firstIn` and `lastIn`.
The assumptions specify the path, cuts, existing endpoint visits, layout and word bound. -/
theorem liftReadSearchEndsProg_exec {w N : ℕ} (path r_lo r_hi r_u r_v : ℕ)
    (huh : r_hi ≠ r_u) (huv : r_u ≠ r_v)
    (B L : List (Fin N)) (S : Finset (Fin N)) (hB : ∀ x, x ∈ B ↔ x ∈ S)
    (u v : Fin N) (hu : firstIn S L = some u) (hv : lastIn S L = some v)
    (s : State) (hs : s.arrs path = L.map Fin.val)
    (hlo : s.regs r_lo = liftFirstBoundaryIndex B L)
    (hhi : s.regs r_hi = liftAfterLastBoundaryIndex B L)
    (hw : N + L.length + 2 < 2 ^ w) :
    ∃ s', Exec w (liftReadSearchEndsProg path r_lo r_hi r_u r_v) s s' 8 ∧
      s'.regs r_u = u.val ∧ s'.regs r_v = v.val ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ r_u → q ≠ r_v → s'.regs q = s.regs q) := by
  obtain ⟨hloL, hhi0, hup, hvp⟩ := liftBoundaryCuts_endpoints B L S hB u v hu hv
  have hhiL := (liftBoundaryIndices_le_length B L).2
  have hgetU : (s.arrs path)[liftFirstBoundaryIndex B L]? = some u.val := by
    simp only [hs, List.getElem?_map, hup, Option.map_some]
  have hgetV : (s.arrs path)[liftAfterLastBoundaryIndex B L - 1]? = some v.val := by
    simp only [hs, List.getElem?_map, hvp, Option.map_some]
  have heU : (Expr.read path (.reg r_lo)).eval w s = some u.val := by
    obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.mp hgetU
    rw [← heq]
    exact eval_read (eval_reg hlo (by omega)) hb (by rw [heq]; exact u.isLt.trans (by omega))
  let s1 := s.setReg r_u u.val
  have hhi1 : s1.regs r_hi = liftAfterLastBoundaryIndex B L := by simp [s1, huh, hhi]
  have heV : (Expr.read path (.op .sub (.reg r_hi) (.const 1))).eval w s1 = some v.val := by
    obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.mp hgetV
    rw [← heq]
    exact eval_read (s := s1) (eval_sub (eval_reg hhi1 (by omega)) (eval_const (by omega))) hb
      (by simpa only [s1, State.setReg_arrs, heq] using v.isLt.trans (by omega : N < 2 ^ w))
  refine ⟨s1.setReg r_v v.val, .seq (.assign heU) (.assign heV), ?_, by simp, fun _ => rfl, ?_⟩
  · simp [s1, huv]
  · intro q hqu hqv; simp [s1, hqu, hqv]

end GraphMinor.Compute.Crossing
