module

public import GraphMinor.Compute.GM06Alg511ReadDart
import Mathlib.Tactic

/-!
# A selected dart trace is a labelled walk

The output invariant of the edge-selection loop for VI (5.11),
page 134, lists a directed edge for every consecutive vertex pair.
Join those edges in order. This produces a finite labelled walk with
exactly the stored vertex and dart lists, so the signed accumulator
computes its turn sum.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Surface

/-- Distinct path vertices and matching directed edges give a walk
with exactly those vertex and dart lists. This is an output
interpretation theorem, not a supplied input certificate. -/
theorem gm06Alg511SelectedDarts_exists_walk {n : ℕ} (pairs : List (Fin n × Fin n))
    (a : Fin n) (tail : List (Fin n)) (darts : List ℕ)
    (hnd : (a :: tail).Nodup) (hlen : darts.length = tail.length)
    (hend : ∀ j (hj : j < darts.length), darts[j] < 2 * pairs.length ∧
      (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD darts[j] 0 =
        ((a :: tail).map Fin.val).getD j 0 ∧
      (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD
        (gm06DartMate darts[j]) 0 = ((a :: tail).map Fin.val).getD (j + 1) 0) :
    ∃ (b : Fin n) (W : GraphWalk (gm06Alg511LabelGraph pairs) a b),
      W.support = a :: tail ∧ gm06Alg511LabelWalkDarts pairs W = darts := by
  induction tail generalizing a darts with
  | nil =>
    have hd : darts = [] := List.length_eq_zero_iff.mp hlen
    subst darts
    exact ⟨a, .nil (by trivial), rfl, rfl⟩
  | cons b rest ih =>
    cases darts with
    | nil => simp at hlen
    | cons d ds =>
      have hab : a ≠ b := fun heq => (List.nodup_cons.mp hnd).1 (by simp [heq])
      have hfirst := hend 0 (by simp)
      simp only [List.getElem_cons_zero, List.map_cons, List.getD_cons_zero,
        Nat.zero_add, List.getD_cons_succ] at hfirst
      obtain ⟨e, he, hde⟩ := gm06Alg511LabelEdge_of_dart pairs a b hab d
        hfirst.1 hfirst.2.1 hfirst.2.2
      have htail : ∀ j (hj : j < ds.length), ds[j] < 2 * pairs.length ∧
          (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD ds[j] 0 =
            ((b :: rest).map Fin.val).getD j 0 ∧
          (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).getD
            (gm06DartMate ds[j]) 0 = ((b :: rest).map Fin.val).getD (j + 1) 0 := by
        intro j hj
        have hh := hend (j + 1) (by simpa using Nat.succ_lt_succ hj)
        simpa only [List.getElem_cons_succ, List.map_cons, List.getD_cons_succ,
          Nat.add_assoc] using hh
      obtain ⟨finish, W, hsupport, hdarts⟩ := ih b ds (List.nodup_cons.mp hnd).2
        (by simpa using hlen) htail
      refine ⟨finish, .cons he W, ?_, ?_⟩
      · change a :: W.support = a :: b :: rest
        rw [hsupport]
      · change gm06Alg511LabelDart pairs he :: gm06Alg511LabelWalkDarts pairs W = d :: ds
        rw [hde, hdarts]

end GraphMinor.Compute
