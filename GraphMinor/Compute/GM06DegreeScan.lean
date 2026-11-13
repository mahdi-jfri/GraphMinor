module

public import GraphMinor.Compute.GM02CountBits

/-!
# Incidence counting for the cylinder reductions

Reduction 3 of VI, page 128, tests the valency of a vertex. Scan the
endpoint labels of the current edge list and count occurrences of that
vertex. Each edge contributes its two ends, so a loop contributes twice.
The scan preserves all arrays and takes linear time.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Count occurrences of the vertex in register 22 in an endpoint array. -/
def gm06DegreeProg (ends : Arr) : Cmd :=
  gm02CountBitsProg 20 21 (.len ends) (.op .eq (.read ends (.reg 20)) (.reg 22))

/-- Summing equality bits counts the occurrences of a label. -/
theorem gm06EqualityBits_sum (xs : List ℕ) (v : ℕ) :
    (xs.map (fun x => if x = v then 1 else 0)).sum = xs.count v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    by_cases h : x = v <;> simp [List.count_cons, h, eq_comm, Nat.add_comm]

/-- The endpoint scan returns the valency count in register 21 in linear time. -/
theorem gm06DegreeProg_exec {w : ℕ} (a : Arr) (xs : List ℕ) (v : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : xs.length < 2 ^ w)
    (hxs : ∀ x ∈ xs, x < 2 ^ w) (hv : v < 2 ^ w)
    (ha : s.arrs a = xs) (hr : s.regs 22 = v) :
    ∃ s' t, Exec w (gm06DegreeProg a) s s' t ∧
      t ≤ 7 + 14 * xs.length ∧ Keeps [20, 21] [] s s' ∧
      s'.regs 21 = xs.count v := by
  let bits := xs.map (fun x => if x = v then 1 else 0)
  have hlen : bits.length = xs.length := List.length_map _
  obtain ⟨s', t, he, ht, hk, hc⟩ := gm02CountBitsProg_exec 20 21 (by decide)
    (.len a) (.op .eq (.read a (.reg 20)) (.reg 22)) bits s hw (hlen ▸ hn)
    (by
      intro b hb
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hb
      split <;> omega)
    (fun st hk => by
      simpa only [hlen] using eval_len ((hk.2 a (by simp)).trans ha) hn)
    (fun st i hi hk hiReg => by
      have hi' : i < xs.length := hlen ▸ hi
      have ha' : st.arrs a = xs := (hk.2 a (by simp)).trans ha
      have heval : (Expr.read a (.reg 20)).eval w st = some xs[i] := by
        have hh := eval_read (a := a) (eval_reg hiReg (hi'.trans hn))
          (by simpa only [ha'] using hi')
          (by simpa only [ha'] using hxs xs[i] (List.getElem_mem hi'))
        simpa only [ha'] using hh
      have hh := eval_eq heval (eval_reg ((hk.1 22 (by decide)).trans hr) hv) hw
      simpa only [bits, List.getElem_map] using hh)
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · simpa only [Expr.cost, hlen, Nat.mul_comm] using ht
  · exact hc.trans (gm06EqualityBits_sum xs v)

end GraphMinor.Compute
