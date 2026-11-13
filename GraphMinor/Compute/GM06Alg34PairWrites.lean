module

public import GraphMinor.Compute.GM06Alg34EndsLoop

/-!
# Consecutive pair writes fill an endpoint section

Numbering pairs consecutively makes their two writes fill a reserved
word list in order. The proof removes the first pair and moves the
written prefix forward by two words. Earlier and later sections are
preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write a pair at two consecutive positions of a word list. -/
def gm06PairWrite (dst : List ℕ) (k : ℕ) (p : ℕ × ℕ) : List ℕ :=
  (dst.set k p.1).set (k + 1) p.2

/-- Filling consecutive pair positions produces their flattened word
list between the preserved front and remaining suffix. -/
theorem gm06PairWrite_fold {n : ℕ} (f : Fin n → ℕ × ℕ) (front suffix : List ℕ)
    (hcap : 2 * n ≤ suffix.length) :
    (List.finRange n).foldl (fun dst i => gm06PairWrite dst (front.length + 2 * i.val) (f i))
      (front ++ suffix) =
      front ++ (List.ofFn f).flatMap (fun p => [p.1, p.2]) ++ suffix.drop (2 * n) := by
  induction n generalizing front suffix with
  | zero => simp [List.finRange_zero]
  | succ n ih =>
    cases suffix with
    | nil => simp at hcap
    | cons a suffix =>
      cases suffix with
      | nil => simp at hcap; omega
      | cons b suffix =>
        have hcap' : 2 * n ≤ suffix.length := by simp only [List.length_cons] at hcap; omega
        let p := f 0
        let front' := front ++ [p.1, p.2]
        have hfirst : gm06PairWrite (front ++ a :: b :: suffix) front.length p = front' ++ suffix := by
          simp only [gm06PairWrite]
          rw [List.set_append_right _ _ (by omega)]
          simp only [Nat.sub_self, List.set_cons_zero]
          rw [List.set_append_right _ _ (by omega)]
          simp [front', List.append_assoc]
        rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
        simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero]
        rw [hfirst]
        have heq : (fun dst (i : Fin n) => gm06PairWrite dst
            (front.length + 2 * i.succ.val) (f i.succ)) =
            (fun dst (i : Fin n) => gm06PairWrite dst
              (front'.length + 2 * i.val) (f i.succ)) := by
          funext dst i
          congr 1
          simp only [front', List.length_append, List.length_cons, List.length_nil, Fin.val_succ]
          omega
        rw [heq, ih (fun i => f i.succ) front' suffix hcap']
        simp [front', p, List.ofFn_succ, List.append_assoc, Nat.mul_add, List.drop_cons]

end GraphMinor.Compute
