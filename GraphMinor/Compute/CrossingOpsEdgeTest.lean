module

public import GraphMinor.Compute.CrossingOpsEdgePrefix
public import GraphMinor.Compute.CrossingOpsReplFilter
public import GraphMinor.Compute.CrossingOpsBool

/-!
# Constant-time tests for the extra retained edge set

The test compares the smaller endpoint with the saved cutoff row and reads one mark
for its larger endpoint. Two gated orientations make the expression symmetric.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The cutoff/mark test for an increasing pair of endpoint indices. -/
def orderedPrefixTest (a_mark r_cut r_x r_y : ℕ) : Expr :=
  boolOr (.op .lt (.reg r_x) (.reg r_cut))
    (boolAnd (.op .eq (.reg r_x) (.reg r_cut)) (.read a_mark (.reg r_y)))

/-- A symmetric test using the increasing orientation of the endpoints. -/
def edgePrefixTest (a_mark r_cut r_x r_y : ℕ) : Expr :=
  boolOr (boolAnd (.op .lt (.reg r_x) (.reg r_y)) (orderedPrefixTest a_mark r_cut r_x r_y))
    (boolAnd (.op .lt (.reg r_y) (.reg r_x)) (orderedPrefixTest a_mark r_cut r_y r_x))

/-- The ordered expression reads exactly the cutoff and chosen-neighbour marks. -/
theorem eval_orderedPrefixTest {w N a r_cut r_x r_y : ℕ} {s : State}
    (cut u v : Fin N) (selected : List ℕ)
    (hm : s.arrs a = setAt (List.replicate N 0) selected 1)
    (hc : s.regs r_cut = cut.val) (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (orderedPrefixTest a r_cut r_x r_y).eval w s =
      some (if u.val < cut.val ∨ (u = cut ∧ v.val ∈ selected) then 1 else 0) := by
  have hcut := eval_reg hc (cut.isLt.trans hN)
  have hroot := eval_reg hx (u.isLt.trans hN)
  have hmark := eval_membershipMark a r_y hm hy v.isLt hN hw
  have hh := eval_boolOr (eval_lt hroot hcut hw)
    (eval_boolAnd (eval_eq hroot hcut hw) hmark hw) hw
  simpa only [orderedPrefixTest, Fin.val_injective.eq_iff] using hh

/-- On an original edge, the symmetric word test is one exactly on the selected prefix. -/
theorem eval_edgePrefixTest {w N a r_cut r_x r_y : ℕ} {s : State}
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (cut u v : Fin N) (q k : ℕ)
    [Decidable (s(u, v) ∈ edgePrefixSet lists k)]
    (hq : q ≤ (edgeRow lists cut).length) (hk : (edgeRowsBefore lists cut.val).length + q = k)
    (hadj : G.Adj u v)
    (hm : s.arrs a = setAt (List.replicate N 0) (edgeBoundaryList lists cut q) 1)
    (hc : s.regs r_cut = cut.val) (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (edgePrefixTest a r_cut r_x r_y).eval w s =
      some (if s(u, v) ∈ edgePrefixSet lists k then 1 else 0) := by
  have hxy := eval_lt (eval_reg hx (u.isLt.trans hN)) (eval_reg hy (v.isLt.trans hN)) hw
  have hyx := eval_lt (eval_reg hy (v.isLt.trans hN)) (eval_reg hx (u.isLt.trans hN)) hw
  have hu := eval_orderedPrefixTest cut u v (edgeBoundaryList lists cut q) hm hc hx hy hN hw
  have hv := eval_orderedPrefixTest cut v u (edgeBoundaryList lists cut q) hm hc hy hx hN hw
  have hh := eval_boolOr (eval_boolAnd hxy hu hw) (eval_boolAnd hyx hv hw) hw
  have hne : u.val ≠ v.val := fun he => hadj.ne (Fin.ext he)
  by_cases hlt : u.val < v.val
  · have hgt : ¬ v.val < u.val := by omega
    have hmemb := mem_edgePrefixSet_rows h cut u v q k hq hk hadj hlt
    simpa only [edgePrefixTest, hlt, hgt, true_and, false_and, or_false, ← hmemb] using hh
  · have hgt : v.val < u.val := by omega
    have hmemb := mem_edgePrefixSet_rows h cut v u q k hq hk hadj.symm hgt
    have hmemb' : s(u, v) ∈ edgePrefixSet lists k ↔
        v.val < cut.val ∨ (v = cut ∧ u.val ∈ edgeBoundaryList lists cut q) := by
      simpa only [Sym2.eq_swap (a := u) (b := v)] using hmemb
    simpa only [edgePrefixTest, hlt, hgt, true_and, false_and, false_or, ← hmemb'] using hh

end GraphMinor.Compute.Crossing
