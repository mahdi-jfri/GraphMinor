module

public import GraphMinor.GM01.RootedGraphs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Interval.Set.Defs
import Lean.Elab.Tactic.Omega

/-!
# Connected index intervals along a path

The spine pieces in the page-60 contraction of Graph Minors I are
intervals of the covering path. Consecutive vertices give the edges
joining an interval. Induction on the last index joins every vertex
in an interval to its first vertex. This proves connectivity of the
induced interval directly, without assuming a path-piece conclusion.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Consecutive vertex steps make every nonempty index interval
connected, as needed for the spine pieces on page 60 of GM01. -/
theorem graphConnected_induce_index_interval {α β : Type*} {N : ℕ} {G : Graph α β}
    (v : Fin N → α)
    (hAdj : ∀ i j, j.val = i.val + 1 → G.Adj (v i) (v j))
    (lo hi : Fin N) (hlohi : lo ≤ hi) :
    GraphConnected (G.induce (v '' Icc lo hi)) := by
  have hreach : ∀ k, lo.val ≤ k → ∀ hkhi : k ≤ hi.val,
      Relation.ReflTransGen (G.induce (v '' Icc lo hi)).Adj
        (v lo) (v ⟨k, Nat.lt_of_le_of_lt hkhi hi.isLt⟩) := by
    intro k hklo
    induction k, hklo using Nat.le_induction with
    | base =>
      intro hkhi
      exact .refl
    | succ k hklo ih =>
      intro hkhi
      have hk : k ≤ hi.val := Nat.le_trans (Nat.le_succ k) hkhi
      let i : Fin N := ⟨k, Nat.lt_of_le_of_lt hk hi.isLt⟩
      let j : Fin N := ⟨k + 1, Nat.lt_of_le_of_lt hkhi hi.isLt⟩
      have hiI : i ∈ Icc lo hi := ⟨hklo,hk⟩
      have hjI : j ∈ Icc lo hi := ⟨Nat.le_trans hklo (Nat.le_succ k),hkhi⟩
      obtain ⟨e,he⟩ := hAdj i j rfl
      exact (ih hk).tail ⟨e,he,⟨i,hiI,rfl⟩,⟨j,hjI,rfl⟩⟩
  refine ⟨⟨v lo,⟨lo,⟨le_rfl,hlohi⟩,rfl⟩⟩, ?_⟩
  rintro x ⟨i,hi,rfl⟩ y ⟨j,hj,rfl⟩
  exact (Std.Symm.symm _ _ (hreach i.val hi.1 hi.2)).trans (hreach j.val hj.1 hj.2)

end GraphMinor.GM01
