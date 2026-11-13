module

public import GraphMinor.Compute.GM06SelectRow
public import GraphMinor.Compute.GM06DartMate
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the initial path neighbour

At a valency-one initial vertex in VI (5.7), page 133, the given
path's first directed edge is its sole incident end. Load that end
from the supplied path row, swap its two consecutive endpoint
positions and read the other vertex. This computes the neighbour
needed by Reduction 3 without supplying an edge chosen by a proof.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the first directed edge of path 295, put its opposite end
in 24 and the opposite vertex label in 301. -/
def gm06InitialNeighbourProg : Cmd :=
  .seq (.assign 31 (.reg 295)) (.seq (gm06SelectRowProg 8 24)
    (.seq (.assign 23 (.read 24 (.const 0)))
      (.seq gm06DartMateProg (.assign 301 (.read 3 (.reg 24))))))

/-- The neighbour query reads exactly the other endpoint of the
first supplied path edge, preserving every instance array. -/
theorem gm06InitialNeighbourProg_exec {w m : ℕ}
    (xs : List ℕ) (paths : List (List ℕ)) (i : ℕ) (hi : i < paths.length)
    (hne : 0 < paths[i].length) (s : State) (hw : 2 < 2 ^ w)
    (hm : 2 * m < 2 ^ w) (hlen : xs.length = 2 * m)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hfirst : paths[i][0] < 2 * m)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (h3 : s.arrs 3 = xs) (h8 : s.arrs 8 = gm06EncodeRows paths) (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06InitialNeighbourProg s s' t ∧
      t ≤ 33 + 17 * i + 22 * paths[i].length ∧
      Keeps [7, 8, 9, 11, 31, 23, 24, 301] [24] s s' ∧
      s'.regs 23 = paths[i][0] ∧ s'.regs 24 = gm06DartMate paths[i][0] ∧
      s'.regs 301 = xs[gm06DartMate paths[i][0]]'(hlen ▸ gm06DartMate_lt hfirst) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hcount : paths.length < 2 ^ w := hpWords _ (by simp [gm06EncodeRows])
  have hiw : i < 2 ^ w := hi.trans hcount
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 295)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h295 hiw)
  obtain ⟨s₁, t₁, he₁, ht₁, hpath, _, _, hk₁⟩ := gm06SelectRowProg_exec
    8 24 (by decide) paths i hi s₀ hw1 (by simpa [s₀] using h8) hpLen hpWords (by simp [s₀])
  let R := [7, 8, 9, 11, 31, 23, 24, 301]
  have hk₀ : Keeps R [24] s s₀ := (Keeps.refl R [24] s).setReg (by simp [R]) _
  have hk₁' : Keeps R [24] s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp)
  let s₂ := s₁.setReg 23 paths[i][0]
  have he₂ : Exec w (.assign 23 (.read 24 (.const 0))) s₁ s₂ 3 := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 24) (s := s₁)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by simpa only [hpath] using hne) (by simpa only [hpath] using hfirst.trans hm)
    simpa only [hpath, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 23) hh
  let s₃ := s₂.setReg 24 (gm06DartMate paths[i][0])
  have he₃ : Exec w gm06DartMateProg s₂ s₃ 9 :=
    gm06DartMateProg_exec s₂ hw hm hfirst (by simp [s₂])
  have hk₃ : Keeps R [24] s s₃ :=
    (hk₁'.setReg (by simp [R]) _).setReg (by simp [R]) _
  have hxs : s₃.arrs 3 = xs := (hk₃.2 3 (by decide)).trans h3
  have hmate : gm06DartMate paths[i][0] < xs.length := hlen ▸ gm06DartMate_lt hfirst
  have hval : xs[gm06DartMate paths[i][0]] < 2 ^ w := hx _ (List.getElem_mem hmate)
  let s₄ := s₃.setReg 301 xs[gm06DartMate paths[i][0]]
  have he₄ : Exec w (.assign 301 (.read 3 (.reg 24))) s₃ s₄ 3 := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 3) (s := s₃)
      (GraphMinor.Compute.Crossing.eval_reg (r := 24) (by simp [s₃]) ((gm06DartMate_lt hfirst).trans hm))
      (by simpa only [hxs] using hmate) (by simpa only [hxs] using hval)
    simpa only [hxs, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 301) hh
  refine ⟨s₄, 2 + (t₁ + (3 + (9 + 3))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))),
    by omega, hk₃.setReg (by simp [R]) _, ?_, ?_, ?_⟩
  · simp [s₄, s₃, s₂]
  · simp [s₄, s₃]
  · simp [s₄]

end GraphMinor.Compute
