module

public import GraphMinor.Compute.GM06Alg34EdgeMaskLoop

/-!
# The completed surviving-edge mask

Consecutive writes into a reserved table fill its next entries in the
same order as the supplied edge list. Applied to the full finite edge
list, the endpoint scan therefore produces exactly the zero-one mask
of edges retained by induced deletion.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- One zero-one entry for each supplied edge label. -/
def gm06EdgeMask (x : GM06DrawingData) (vs : List (Fin x.n)) : List ℕ :=
  List.ofFn (fun e => if x.activeCell vs (.inr (.inl e)) then 1 else 0)

/-- Sequential mask writes fill the next part of a reserved list and
preserve its preceding and following entries. -/
theorem gm06EdgeMaskWrites_append (x : GM06DrawingData) (vs : List (Fin x.n))
    (L : List (Fin x.ends.length)) (front suffix : List ℕ)
    (hcap : L.length ≤ suffix.length) :
    gm06EdgeMaskWrites x vs L front.length (front ++ suffix) =
      front ++ L.map (fun e => if x.activeCell vs (.inr (.inl e)) then 1 else 0) ++
        suffix.drop L.length := by
  induction L generalizing front suffix with
  | nil => simp [gm06EdgeMaskWrites]
  | cons e L ih =>
    cases suffix with
    | nil => simp at hcap
    | cons a suffix =>
      let bit : ℕ := if x.activeCell vs (.inr (.inl e)) then 1 else 0
      have hcap' : L.length ≤ suffix.length := by simpa using hcap
      have hh := ih (front ++ [bit]) suffix hcap'
      simp only [List.length_append, List.length_cons, List.length_nil] at hh
      simp only [gm06EdgeMaskWrites]
      rw [List.set_append_right _ _ (by omega)]
      simp only [Nat.sub_self, List.set_cons_zero]
      convert hh using 1 <;> simp [bit, List.append_assoc]

/-- Scanning all supplied labels into a table of the right length
produces the exact finite edge mask, regardless of old table entries. -/
theorem gm06EdgeMaskWrites_all (x : GM06DrawingData) (vs : List (Fin x.n))
    (dst : List ℕ) (hlen : dst.length = x.ends.length) :
    gm06EdgeMaskWrites x vs (List.finRange x.ends.length) 0 dst = gm06EdgeMask x vs := by
  have hh := gm06EdgeMaskWrites_append x vs (List.finRange x.ends.length) [] dst
    (by simpa only [List.length_finRange] using hlen.ge)
  simp only [List.length_finRange] at hh
  rw [List.drop_eq_nil_of_le hlen.le] at hh
  simpa [gm06EdgeMask, List.ofFn_eq_map] using hh

end GraphMinor.Compute
