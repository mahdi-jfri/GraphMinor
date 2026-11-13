module

public import GraphMinor.Compute.GM02CountBits

/-!
# Valency scans with deleted edges

Keep the original directed-end labels during the cylinder reductions.
A separate array marks which original edges remain. A directed end
contributes to valency exactly when its edge is active and its endpoint
is the queried vertex. This scan supports deletions without renumbering
rotations or boundary walks.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Contribution of each directed end to the active valency of a vertex. -/
def gm06ActiveEndpointBits (xs mask : List ℕ) (v : ℕ) : List ℕ :=
  List.ofFn fun j : Fin xs.length =>
    (if mask[j.val / 2]?.getD 0 = 1 then 1 else 0) * (if xs[j.val] = v then 1 else 0)

/-- Scan endpoint labels and their edge-activity flags. -/
def gm06ActiveDegreeProg (ends active : Arr) : Cmd :=
  gm02CountBitsProg 20 21 (.len ends)
    (.op .mul
      (.op .eq (.read active (.op .div (.reg 20) (.const 2))) (.const 1))
      (.op .eq (.read ends (.reg 20)) (.reg 22)))

/-- The active-edge valency scan preserves all arrays and has a linear time bound. -/
theorem gm06ActiveDegreeProg_exec {w : ℕ} (ends active : ℕ)
    (xs mask : List ℕ) (v : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hlen : xs.length = 2 * mask.length) (hn : xs.length < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hm : ∀ x ∈ mask, x < 2 ^ w)
    (hv : v < 2 ^ w) (ha : s.arrs ends = xs) (hb : s.arrs active = mask)
    (hr : s.regs 22 = v) :
    ∃ s' t, Exec w (gm06ActiveDegreeProg ends active) s s' t ∧
      t ≤ 7 + 21 * xs.length ∧ Keeps [20, 21] [] s s' ∧
      s'.regs 21 = (gm06ActiveEndpointBits xs mask v).sum := by
  let bits := gm06ActiveEndpointBits xs mask v
  have hbits : bits.length = xs.length := List.length_ofFn
  obtain ⟨s', t, he, ht, hk, hd⟩ := gm02CountBitsProg_exec 20 21 (by decide)
    (.len ends)
    (.op .mul
      (.op .eq (.read active (.op .div (.reg 20) (.const 2))) (.const 1))
      (.op .eq (.read ends (.reg 20)) (.reg 22))) bits s (by omega) (hbits ▸ hn)
    (by
      intro b hb'
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb'
      split <;> split <;> omega)
    (fun st hk => by
      simpa only [hbits] using eval_len ((hk.2 ends (by simp)).trans ha) hn)
    (fun st i hi hk hiReg => by
      have hi' : i < xs.length := hbits ▸ hi
      have hiw := hi'.trans hn
      have him : i / 2 < mask.length := by omega
      have hid : i / 2 < 2 ^ w := (Nat.div_le_self i 2).trans_lt hiw
      have ha' : st.arrs ends = xs := (hk.2 ends (by simp)).trans ha
      have hb' : st.arrs active = mask := (hk.2 active (by simp)).trans hb
      have hediv : (Expr.op .div (.reg 20) (.const 2)).eval w st = some (i / 2) := by
        simp [Expr.eval, hiReg, checkWord, hiw, hw, BinOp.eval, BinOp.raw, hid]
      have hem := eval_read (a := active) hediv (by simpa only [hb'] using him)
        (by simpa only [hb'] using hm mask[i / 2] (List.getElem_mem him))
      have hex := eval_read (a := ends) (eval_reg hiReg hiw)
        (by simpa only [ha'] using hi')
        (by simpa only [ha'] using hx xs[i] (List.getElem_mem hi'))
      simp only [ha', hb'] at hem hex
      have hbval := eval_eq hem (eval_const (by omega : 1 < 2 ^ w)) (by omega)
      have hxval := eval_eq hex (eval_reg ((hk.1 22 (by decide)).trans hr) hv) (by omega)
      have hfit : (if mask[i / 2] = 1 then 1 else 0) * (if xs[i] = v then 1 else 0) < 2 ^ w := by
        split <;> split <;> omega
      have hh := eval_mul hbval hxval hfit
      simpa only [bits, gm06ActiveEndpointBits, List.getElem_ofFn,
        List.getElem?_eq_getElem him, Option.getD_some] using hh)
  refine ⟨s', t, he, ?_, hk, hd⟩
  simpa only [Expr.cost, hbits, Nat.mul_comm] using ht

end GraphMinor.Compute
