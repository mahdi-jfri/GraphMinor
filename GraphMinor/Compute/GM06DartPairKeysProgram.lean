module

public import GraphMinor.Compute.GM06PathDarts

/-!
# Endpoint-pair keys for actual directed edge recovery

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) retain
the permanent ordinary edge labels behind the BFS neighbour lists. The
program computes one endpoint-pair key per permanent dart. Excluded
darts receive zero. A positive pair query can therefore find only an
actual retained directed dart. All origins and activity bits are read
from the computed candidate representation.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Encode two evaluated vertices in the positive ordered-pair key space. -/
def gm06PairKeyExpr (u v : Expr) : Expr :=
  .op .add (.const 1) (.op .add (.op .mul u (.reg 620)) v)

/-- Pair-key arithmetic is exact, including each intermediate word. -/
theorem gm06PairKeyExpr_eval {w n u v : ℕ} (U V : Expr) (s : State)
    (hw : 1 < 2 ^ w) (hfit : 1 + n * n < 2 ^ w) (hu : u < n) (hv : v < n)
    (hU : U.eval w s = some u) (hV : V.eval w s = some v) (h620 : s.regs 620 = n) :
    (gm06PairKeyExpr U V).eval w s = some (gm06PairKey n u v) := by
  have hbound := gm06PairKey_lt hu hv
  have hn : n < 2 ^ w := by
    have hmul : n ≤ n * n := Nat.le_mul_self n
    omega
  have hprod : u * n < 2 ^ w := by unfold gm06PairKey at hbound; omega
  have hsum : u * n + v < 2 ^ w := by unfold gm06PairKey at hbound; omega
  have he := GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_const hw)
    (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_mul hU (GraphMinor.Compute.Crossing.eval_reg h620 hn) hprod)
      hV hsum) (by unfold gm06PairKey at hbound; omega)
  simpa only [gm06PairKeyExpr, gm06PairKey, Nat.add_assoc] using he

/-- Multiply the actual activity bit by the actual ordered endpoint key. -/
def gm06DartPairKeysExpr : Expr :=
  .op .mul (.read 627 (.reg 650))
    (gm06PairKeyExpr (.read 626 (.reg 650)) (.read 626 (gm06DartMateExpr (.reg 650))))

/-- Reading activity and both directed ends gives the exact finite key. -/
theorem gm06DartPairKeysExpr_eval {w n m d : ℕ} (origins active : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : 1 + n * n < 2 ^ w) (hd : d < 2 * m)
    (hlen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h620 : s.regs 620 = n) (h650 : s.regs 650 = d) :
    gm06DartPairKeysExpr.eval w s = some
      (if d ∈ active then gm06PairKey n (origins[d]?.getD 0) (gm06CutNeighbourHead origins d) else 0) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hdm : gm06DartMate d < 2 * m := gm06DartMate_lt hd
  have hi : d < origins.length := hlen ▸ hd
  have him : gm06DartMate d < origins.length := hlen ▸ hdm
  have hu : origins[d]?.getD 0 < n := by
    simpa only [List.getElem?_eq_getElem hi, Option.getD_some] using hvalues _ (List.getElem_mem hi)
  have hv : gm06CutNeighbourHead origins d < n := by
    simpa only [gm06CutNeighbourHead, List.getElem?_eq_getElem him, Option.getD_some] using
      hvalues _ (List.getElem_mem him)
  have hx := GraphMinor.Compute.Crossing.eval_reg (w := w) h650 (hd.trans hm)
  have hmate := gm06DartMateExpr_eval hw hm hd hx
  have hreadU : (Expr.read 626 (.reg 650)).eval w s = some (origins[d]?.getD 0) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 626) hx
      (by simpa only [h626] using hi)
      (by simpa only [h626, List.getElem?_eq_getElem hi, Option.getD_some] using hu.trans hn)
    simpa only [h626, List.getElem?_eq_getElem hi, Option.getD_some] using he
  have hreadV : (Expr.read 626 (gm06DartMateExpr (.reg 650))).eval w s =
      some (gm06CutNeighbourHead origins d) := by
    have he := GraphMinor.Compute.Crossing.eval_read (a := 626) hmate
      (by simpa only [h626] using him)
      (by simpa only [h626, gm06CutNeighbourHead, List.getElem?_eq_getElem him, Option.getD_some] using hv.trans hn)
    simpa only [h626, gm06CutNeighbourHead, List.getElem?_eq_getElem him, Option.getD_some] using he
  have hkey := gm06PairKeyExpr_eval _ _ s hw1 hfit hu hv hreadU hreadV h620
  have hbit := gm06ReadBits_eval active s (.reg 650) hw1 hd hx h627
  have hb := (gm06PairKey_lt hu hv).trans hfit
  have he := GraphMinor.Compute.Crossing.eval_mul hbit hkey
    (by split <;> simp_all only [Nat.one_mul, Nat.zero_mul, Nat.two_pow_pos])
  by_cases hactive : d ∈ active <;>
    simpa only [gm06DartPairKeysExpr, hactive, ↓reduceIte, Nat.one_mul, Nat.zero_mul] using he

/-- Compute the ordered endpoint key for every permanent dart in array 616. -/
def gm06DartPairKeysProg : Cmd := gm13TabulateProg 650 (.len 626) gm06DartPairKeysExpr 616

/-- Exact linear-time key construction, preserving the BFS result. -/
theorem gm06DartPairKeysProg_exec {w n m : ℕ} (origins active : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : 1 + n * n < 2 ^ w) (hlen : origins.length = 2 * m)
    (hvalues : ∀ v ∈ origins, v < n)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h620 : s.regs 620 = n) :
    ∃ sf t, Exec w gm06DartPairKeysProg s sf t ∧ t ≤ 6 + 100 * (2 * m) ∧
      Keeps [650] [616] s sf ∧ sf.arrs 616 = gm06DartPairKeys n origins active := by
  let out := gm06DartPairKeys n origins active
  have houtlen : out.length = 2 * m := (gm06DartPairKeys_length n origins active).trans hlen
  obtain ⟨sf, t, he, ht, hk, hd⟩ := gm13TabulateProg_exec
    650 (.len 626) gm06DartPairKeysExpr 616 out s (by omega) (houtlen ▸ hm)
    (fun st hk => by
      simpa only [out, gm06DartPairKeys_length] using
        GraphMinor.Compute.Crossing.eval_len ((hk.2 626 (by decide)).trans h626) (hlen ▸ hm))
    (fun st i hi hk hr => by
      have hi' : i < 2 * m := houtlen ▸ hi
      have he := gm06DartPairKeysExpr_eval origins active st hw hn hm hfit hi' hlen hvalues
        ((hk.2 626 (by decide)).trans h626) ((hk.2 627 (by decide)).trans h627)
        ((hk.1 620 (by decide)).trans h620) hr
      have hout := gm06DartPairKeys_get (n := n) origins active (hlen ▸ hi')
      rw [List.getElem?_eq_getElem hi] at hout
      simpa only [Option.getD_some, ← hout] using he)
  refine ⟨sf, t, he, ?_, hk, hd⟩
  have hcost : gm06DartPairKeysExpr.cost ≤ 80 := by decide
  simp only [Expr.cost, houtlen, Nat.mul_add, Nat.mul_one] at ht
  have hmul := Nat.mul_le_mul_left (2 * m) hcost
  omega

end GraphMinor.Compute
