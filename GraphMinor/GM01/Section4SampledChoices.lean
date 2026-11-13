module

public import GraphMinor.GM01.Section4MinimalChoice

/-!
# Choosing all sampled small separators

Graph Minors I, pages 56–57, samples the minimal separators at
multiples of `ν = θ^(2θ)`. The left and right index maps describe
these actual windows. Choose each small minimal separator as after
(4.2), and rewrite its early endpoint set into the left-index form used
by (4.3)–(4.14).
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The simultaneous sampled choices preceding GM01 (4.5), page 56.
The minimal separators are those chosen after (4.2), whose late
endpoint set begins at the right boundary block, as printed. -/
theorem exists_sampled_minimal_comb_separators {α : Type u} {β : Type v} {γ δ L n θ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β) (hfin : V(G.graph).Finite)
    (hθ : 6 ≤ θ) (heven : Even θ) (hGrid : ¬ IsIsoMinor (gridGraph θ) G.graph)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    {T : ℕ} (hn : n = θ ^ (2 * θ) * T + 1) :
    ∃ left right : Fin T → Fin n,
      (∀ i, (left i).val = θ ^ (2 * θ) * i.val) ∧
      (∀ i, (right i).val + 1 = θ ^ (2 * θ) * (i.val + 1)) ∧
      ∃ Y : Fin T → Set α, (∀ i, Y i ⊆ V(G.graph)) ∧
        (∀ i, (Y i).ncard < θ ^ 2 / 2) ∧
        ∀ i, IsMinimalGraphSeparator G.graph (Y i)
          (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
          (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k) := by
  classical
  let ν := θ ^ (2 * θ)
  have hνpos : 0 < ν := Nat.pow_pos (by omega : 0 < θ)
  let left : Fin T → Fin n := fun i ↦ ⟨ν * i.val, by
    have hh := Nat.mul_le_mul_left ν (Nat.le_of_lt i.isLt)
    change n = ν * T + 1 at hn
    omega⟩
  let right : Fin T → Fin n := fun i ↦ ⟨ν * (i.val + 1) - 1, by
    have hh := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt i.isLt)
    change ν * (i.val + 1) ≤ ν * T at hh
    change n = ν * T + 1 at hn
    omega⟩
  have hleft : ∀ i, (left i).val = ν * i.val := fun _ ↦ rfl
  have hright : ∀ i, (right i).val + 1 = ν * (i.val + 1) := by
    intro i
    have hprod : 0 < ν * (i.val + 1) := Nat.mul_pos hνpos (Nat.succ_pos _)
    change ν * (i.val + 1) - 1 + 1 = ν * (i.val + 1)
    omega
  have hwindow : ∀ i, (left i).val + ν = (right i).val + 1 := by
    intro i
    rw [hleft, hright, Nat.mul_add, Nat.mul_one]
  have hChoices : ∀ i : Fin T, ∃ X ⊆ V(G.graph), X.ncard < θ ^ 2 / 2 ∧
      IsMinimalGraphSeparator G.graph X
        (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
        (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k) := by
    intro i
    have hνright : ν ≤ (right i).val + 1 := by
      have hh := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le i.val))
      change ν * 1 ≤ ν * (i.val + 1) at hh
      simp only [Nat.mul_one] at hh
      rw [hright]
      exact hh
    obtain ⟨X, hXG, hcard, hmin⟩ := exists_small_minimal_block_separator hγ hδ hL htail G hfin
      hθ heven hGrid hno hN hc hV hE hPaths hInter hR hmeetR (right i) hνright
    have hEarly :
        (⋃ k : Fin n, ⋃ (_ : k.val < (right i).val + 2 - θ ^ (2 * θ)),
          combBlock hL (subgraphUnion G.graph N R) c k) =
        (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k) := by
      have hw := hwindow i
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨k, hk, hx⟩
        exact ⟨k, by change k.val ≤ (left i).val; change k.val < (right i).val + 2 - ν at hk; omega, hx⟩
      · rintro ⟨k, hk, hx⟩
        refine ⟨k, ?_, hx⟩
        change k.val ≤ (left i).val at hk
        change k.val < (right i).val + 2 - ν
        omega
    rw [hEarly] at hmin
    exact ⟨X, hXG, hcard, hmin⟩
  choose Y hYG hcard hmin using hChoices
  exact ⟨left, right, hleft, hright, Y, hYG, hcard, hmin⟩

end GraphMinor.GM01
