module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.SubtreePoint
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Abel

/-!
# Subtree intersection graphs are chordal

A leaf-deletion argument gives a subtree whose neighbors all meet at one
point, hence a simplicial vertex in the intersection graph. Restrict the
representing family to any induced cycle. A cycle on at least four
vertices has no simplicial vertex, which rules out such a cycle.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set Fin.NatCast

universe u w

variable {V : Type u} {W : Type w} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Restricting the representing family along an induced embedding retains
its subtree intersection representation. -/
theorem IsSubtreeIntersectionGraph.of_embedding (hG : IsSubtreeIntersectionGraph G)
    (f : H ↪g G) : IsSubtreeIntersectionGraph H := by
  obtain ⟨ι,inst,T,hT,A,hA,hadj⟩ := hG
  exact ⟨ι,inst,T,hT,A ∘ f,fun v ↦ hA (f v),fun v w hne ↦
    f.map_adj_iff.symm.trans (hadj (f v) (f w) (fun he ↦ hne (f.injective he)))⟩

/-- A nonempty subtree intersection graph has a vertex with pairwise
adjacent neighbors. This is the leaf-deletion argument for its representing tree. -/
theorem IsSubtreeIntersectionGraph.exists_simplicial [Nonempty V]
    (hG : IsSubtreeIntersectionGraph G) : ∃ v, IsSimplicial G v := by
  obtain ⟨ι,inst,T,hT,A,hA,hadj⟩ := hG
  let := inst
  have hN : ∀ v, (A v).Nonempty := by
    intro v
    obtain ⟨t⟩ := (hA v).nonempty
    exact ⟨t.1,t.2⟩
  have hconv : ∀ v a, a ∈ A v → ∀ b, b ∈ A v → ∀ c,
      OnTreePath T a b c → c ∈ A v := by
    intro v a ha b hb c hp
    obtain ⟨p,hp'⟩ := (hA v).exists_isPath ⟨a,ha⟩ ⟨b,hb⟩
    let f : T.induce (A v) →g T := ⟨Subtype.val,fun h ↦ h⟩
    have hc := hp (p.map f) (hp'.map Subtype.val_injective)
    rw [Walk.support_map] at hc
    obtain ⟨q,hq,hqc⟩ := List.mem_map.mp hc
    exact hqc ▸ q.2
  obtain ⟨v,t,ht,hm⟩ := exists_subtree_meeting_point hT A hN hconv
  refine ⟨v,?_⟩
  intro x hx y hy hxy
  have hx' := hm x ((hadj v x hx.ne).mp hx)
  have hy' := hm y ((hadj v y hy.ne).mp hy)
  exact (hadj x y hxy).mpr ⟨t,hx',hy'⟩

private lemma fin_small_ne {m a b : ℕ} (ha : a<m) (hb : b<m) (hne : a≠b)
    [NeZero m] : (↑a : Fin m) ≠ (↑b : Fin m) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hv
  exact hne hv

/-- An induced cycle on at least four vertices has no vertex with pairwise
adjacent neighbors. -/
theorem cycleGraph_not_simplicial {n : ℕ} (hn : 4≤n) (i : Fin n) :
    ¬ IsSimplicial (cycleGraph n) i := by
  obtain ⟨m,rfl⟩ : ∃ m, n=m+4 := ⟨n-4,by omega⟩
  intro hs
  have hne : i-1 ≠ i+1 := by
    intro he
    have h2 : (2 : Fin (m+4)) = 0 := by
      calc
        2 = (i+1)-(i-1) := by abel
        _ = 0 := by rw [he]; exact sub_self _
    exact fin_small_ne (a:=2) (b:=0) (by omega) (by omega) (by omega) h2
  have hm : (cycleGraph (m+4)).Adj i (i-1) := by
    rw [←mem_neighborSet,cycleGraph_neighborSet]
    exact Or.inl rfl
  have hp : (cycleGraph (m+4)).Adj i (i+1) := by
    rw [←mem_neighborSet,cycleGraph_neighborSet]
    exact Or.inr rfl
  have hAdj := hs hm hp hne
  rcases cycleGraph_adj.mp hAdj with h|h
  · have h3 : (3 : Fin (m+4)) = 0 := by
      calc
        3 = ((i+1)-(i-1))+1 := by abel
        _ = ((i+1)-(i-1))+((i-1)-(i+1)) := by rw [h]
        _ = 0 := by abel
    exact fin_small_ne (a:=3) (b:=0) (by omega) (by omega) (by omega) h3
  · have h2 : (2 : Fin (m+4)) = 1 := by
      calc
        2 = (i+1)-(i-1) := by abel
        _ = 1 := h
    exact fin_small_ne (a:=2) (b:=1) (by omega) (by omega) (by omega) h2

/-- The forward direction of Graph Minors V, (8.3), page 110:
a subtree intersection graph has no induced circuit of length at least four. -/
theorem IsSubtreeIntersectionGraph.isChordal (hG : IsSubtreeIntersectionGraph G) :
    IsChordal G := by
  intro n hn
  refine ⟨fun f ↦ ?_⟩
  have : NeZero n := ⟨by omega⟩
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  obtain ⟨i,hi⟩ := (hG.of_embedding f).exists_simplicial
  exact cycleGraph_not_simplicial hn i hi

end GraphMinor.GM05
