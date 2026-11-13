module

public import GraphMinor.GM05.ChordalDefs
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel

/-!
# Chordless closed walks in chordal graphs

Enumerate the vertices of a simple closed walk, omitting the final repeat
of its start. For a chordless walk, this enumeration is an induced cycle
embedding. Thus the definition by forbidden induced cycles also rules out
chordless simple closed walks of length at least four.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set Fin.NatCast

private lemma cycle_adj_succ_iff {n : ℕ} [NeZero n] (hn : 2≤n) (i j : Fin n) :
    (cycleGraph n).Adj i j ↔ j=i+1 ∨ i=j+1 := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+2 := ⟨n-2,by omega⟩
  rw [cycleGraph_adj]
  constructor
  · rintro (h|h)
    · right
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
    · left
      exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  · rintro (h|h)
    · right
      simp only [h,add_sub_cancel_left]
    · left
      simp only [h,add_sub_cancel_left]

/-- Enumerating a chordless simple circuit gives an induced embedding
of the cycle graph with the same length. -/
noncomputable def chordlessCycleEmbedding {V : Type*} {G : SimpleGraph V} {a : V}
    {p : G.Walk a a} (hp : p.IsCycle) (hc : p.IsChordless) :
    cycleGraph p.length ↪g G := by
  classical
  have hn := hp.three_le_length
  let : NeZero p.length := ⟨by omega⟩
  let f : Fin p.length → V := fun i ↦ p.getVert i.val
  have hf : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn' (show i.val≤p.length-1 by omega)
      (show j.val≤p.length-1 by omega) h
  have hnext (i : Fin p.length) : f (i+1) = p.getVert (i.val+1) := by
    dsimp [f]
    rw [Fin.val_add_eq_ite]
    have h1 : (1 : Fin p.length).val=1 := by
      change 1 % p.length=1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h1]
    split_ifs with h
    · have he : i.val+1=p.length := by have := i.isLt; omega
      rw [he,Nat.sub_self,p.getVert_zero,p.getVert_length]
    · rfl
  have hedge (i : Fin p.length) : G.Adj (f i) (f (i+1)) := by
    rw [hnext]
    exact p.adj_getVert_succ i.isLt
  refine { toFun:=f, inj':=hf, map_rel_iff':=?_ }
  intro i j
  constructor
  · intro hij
    have he := hc.mem_edges (p.getVert_mem_support i.val) (p.getVert_mem_support j.val) hij
    obtain ⟨k,hk,hke⟩ := p.mk_mem_edges_iff_exists.mp he
    let q : Fin p.length := ⟨k,hk⟩
    have hq : p.getVert k=f q := rfl
    have hq' : p.getVert (k+1)= f (q+1) := (hnext q).symm
    rw [hq,hq'] at hke
    apply (cycle_adj_succ_iff (by omega) i j).mpr
    rcases Sym2.eq_iff.mp hke with ⟨h1,h2⟩|⟨h1,h2⟩
    · have hi : q=i := hf h1
      have hj : q+1=j := hf h2
      exact Or.inl (hj.symm.trans (congrArg (fun z ↦ z+1) hi))
    · have hj : q=j := hf h1
      have hi : q+1=i := hf h2
      exact Or.inr (hi.symm.trans (congrArg (fun z ↦ z+1) hj))
  · intro hij
    rcases (cycle_adj_succ_iff (by omega) i j).mp hij with h|h
    · rw [h]
      exact hedge i
    · rw [h]
      exact (hedge j).symm

/-- A chordless simple circuit in a chordal graph has at most three edges. -/
theorem IsChordal.chordless_cycle_length_le {V : Type*} {G : SimpleGraph V}
    (hG : IsChordal G) {a : V} {p : G.Walk a a}
    (hp : p.IsCycle) (hc : p.IsChordless) : p.length≤3 := by
  by_contra hn
  exact (hG p.length (by omega)).false (chordlessCycleEmbedding hp hc)

end GraphMinor.GM05
