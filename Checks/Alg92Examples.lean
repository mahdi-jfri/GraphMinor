module

import GraphMinor.Compute.Algorithm92Main

/-!
# Examples for the program of (9.2) after `F` (`Checks/Alg92Examples.lean`)

1. `starProg_example`: a run of the star lift `starProg 1` on concrete arrays. The graph has the
   vertices `0, 1, 2`; the layout `[3, 0, 1, 2]` holds one path `0 1 2`, whose middle `1` is a run
   of its own. The compressed copy has the same three vertices, and the stored answer is the star
   with center `0` and the one ray `0 1 2`. The program writes the lifted star
   `[0, 0, 3, 0, 1, 2]`: the center `0`, then the ray of length `3`.
2. `algorithm_9_2_example`: the statement of (9.2) follows from `F92ProgClaim`.
-/

namespace GraphMinor.Compute.Alg92.Examples

/-- The arrays read by `starProg` on the example. -/
def starState : State where
  regs := fun _ => 0
  arrs := fun a =>
    if a = aE then tab 3 (fun c => [0, 1, 2].getD c 0)
    else if a = aN then tab 4 (fun u => if (fun v => decide (v ≠ 1)) u then 1 else 0)
    else if a = aRS then tab 4 (fun v => if v = 1 then 2 else 0)
    else if a = aEn then tab 4 (fun j => if j = 2 then 2 else 0)
    else if a = aL then [3, 0, 1, 2]
    else if a = aRank then tab 3 id
    else if a = aAns then [0, 0, 3, 0, 1, 2]
    else []

/-- **A run of the star lift.** -/
theorem starProg_example :
    ∃ s' t, Exec 8 (starProg 1) starState s' t ∧ t ≤ 1420 ∧
      s'.arrs outArr = [0, 0, 3, 0, 1, 2] := by
  obtain ⟨s', t, ex, ht, hout, -⟩ := starProg_exec (w := 8) (l := 1) (s := starState) (n := 3)
    (E := [0, 1, 2]) (L := [3, 0, 1, 2]) (nd := fun v => decide (v ≠ 1))
    (rsA := fun v => if v = 1 then 2 else 0) (enA := fun j => if j = 2 then 2 else 0)
    (rankA := id) (c := 0) (rays := [[0, 1, 2]])
    rfl rfl rfl rfl rfl rfl rfl rfl (by decide) (by decide)
    (fun r hr v hv => by
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> (unfold GoodV; decide))
    (by decide) (by decide) (fun u hu => by simp; omega) (by decide) (by decide)
  exact ⟨s', t, ex, ht.trans (by decide), by rw [hout]; rfl⟩

/-- The statement of (9.2), from the claim on the program that finds `F`. -/
theorem algorithm_9_2_example (hF : F92ProgClaim) : Algorithm92Statement :=
  algorithm_9_2_of_F92 hF

end GraphMinor.Compute.Alg92.Examples
