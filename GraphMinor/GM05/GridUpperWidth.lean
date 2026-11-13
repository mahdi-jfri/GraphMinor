module

public import GraphMinor.GM05.Defs
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A path-decomposition of the square grid

Number the vertices row by row. A bag contains a consecutive interval of
`n + 1` numbers. Moving the interval one step at a time covers every edge.
The bags containing a fixed vertex form an interval of the decomposition
path, and each bag has at most `n + 1` vertices.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

private lemma pathGraph_tree_succ (m : ℕ) : (pathGraph (m + 1)).IsTree := by
  induction m with
  | zero =>
    let : Subsingleton (Fin (0 + 1)) := ⟨fun x y ↦ Fin.ext (by omega)⟩
    exact IsTree.of_subsingleton
  | succ m ih =>
    let e : GM10.attachLeaf (pathGraph (m + 1)) (0 : Fin (m + 1)) ≃g pathGraph (m + 2) := {
      (finSuccEquiv (m + 1)).symm with
      map_rel_iff' := by
        intro a b
        cases a <;> cases b <;>
          simp only [finSuccEquiv_symm_none, finSuccEquiv_symm_some, pathGraph_adj,
            Fin.val_zero, Fin.val_succ, GM10.attachLeaf, Fin.ext_iff]
        all_goals first | omega | simp }
    exact e.isTree_iff.mp (GM10.isTree_attachLeaf ih _)

private lemma bounded_path_walk {L : ℕ} (a b : Fin L) (hab : a.1 ≤ b.1) :
    ∃ p : (pathGraph L).Walk a b, ∀ c ∈ p.support, a.1 ≤ c.1 ∧ c.1 ≤ b.1 := by
  have main : ∀ d, ∀ a b : Fin L, a.1 ≤ b.1 → b.1 - a.1 = d →
      ∃ p : (pathGraph L).Walk a b, ∀ c ∈ p.support, a.1 ≤ c.1 ∧ c.1 ≤ b.1 := by
    intro d
    induction d with
    | zero =>
      intro a b hab hd
      have he : a = b := Fin.ext (by omega)
      subst b
      refine ⟨.nil, ?_⟩
      intro c hc
      have he : c = a := by simpa using hc
      subst c
      exact ⟨le_rfl, le_rfl⟩
    | succ d ih =>
      intro a b hab hd
      let a' : Fin L := ⟨a.1 + 1, by omega⟩
      have hab' : a'.1 ≤ b.1 := by dsimp [a']; omega
      have hd' : b.1 - a'.1 = d := by dsimp [a']; omega
      obtain ⟨p, hp⟩ := ih a' b hab' hd'
      refine ⟨.cons (pathGraph_adj.mpr (Or.inl rfl)) p, ?_⟩
      intro c hc
      simp only [Walk.support_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨le_rfl, hab⟩
      · have h := hp c hc
        exact ⟨by dsimp [a'] at h; omega, h.2⟩
  exact main _ a b hab rfl

private lemma path_index_bounds {L : ℕ} {a b c : Fin L}
    (hab : a.1 ≤ b.1) (hp : OnTreePath (pathGraph L) a b c) :
    a.1 ≤ c.1 ∧ c.1 ≤ b.1 := by
  obtain ⟨p, hb⟩ := bounded_path_walk a b hab
  exact hb c (GM10.mem_support_of_onTreePath hp p)

private def gridRank {n : ℕ} (v : Fin n × Fin n) : ℕ :=
  v.2.1 + n * v.1.1

private lemma gridRank_injective {n : ℕ} : Function.Injective (@gridRank n) := by
  intro x y h
  apply finProdFinEquiv.injective
  exact Fin.ext h

private lemma gridRank_lt {n : ℕ} (v : Fin n × Fin n) : gridRank v < n * n :=
  (finProdFinEquiv v).isLt

private lemma gridRank_adj {n : ℕ} {x y : Fin n × Fin n}
    (h : (pathGraph n □ pathGraph n).Adj x y) :
    gridRank x ≤ gridRank y + n ∧ gridRank y ≤ gridRank x + n := by
  simp only [boxProd_adj, pathGraph_adj] at h
  rcases h with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · have hcol := congrArg Fin.val hj
    rcases hi with hi | hi
    · have hm := congrArg (fun z : ℕ ↦ n * z) hi
      simp only [Nat.mul_add, Nat.mul_one] at hm
      dsimp [gridRank]
      omega
    · have hm := congrArg (fun z : ℕ ↦ n * z) hi
      simp only [Nat.mul_add, Nat.mul_one] at hm
      dsimp [gridRank]
      omega
  · have hrow := congrArg (fun z : Fin n ↦ n * z.1) hi
    have hn : 1 ≤ n := by have := x.1.isLt; omega
    rcases hj with hj | hj <;> dsimp [gridRank] <;> omega

/-- The upper bound for the grid in Graph Minors V, (1.4), page 93.
Consecutive intervals in row-by-row numbering form bags of size at most
`n + 1`, indexed by a path. -/
theorem grid_treeWidthLE {n : ℕ} (hn : 2 ≤ n) :
    TreeWidthLE (SimpleGraph.toSubgraph (pathGraph n □ pathGraph n) le_top) n := by
  classical
  let L := (n - 1) * n
  have hL : 0 < L := Nat.mul_pos (by omega) (by omega)
  have hcount : n * n = L + n := by
    have h := congrArg (fun z : ℕ ↦ z * n) (Nat.sub_add_cancel (show 1 ≤ n by omega))
    simpa only [Nat.add_mul, Nat.one_mul, L] using h.symm
  let χ : Fin L → Set (Fin n × Fin n) :=
    fun r ↦ {v | r.1 ≤ gridRank v ∧ gridRank v ≤ r.1 + n}
  have htree : (pathGraph L).IsTree := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    rw [hm]
    exact pathGraph_tree_succ m
  have htd : IsTreeDecomposition
      (SimpleGraph.toSubgraph (pathGraph n □ pathGraph n) le_top) (pathGraph L) χ := by
    refine ⟨htree, ?_, ?_, ?_⟩
    · ext v
      simp only [mem_iUnion, SimpleGraph.toSubgraph_verts, mem_univ, iff_true]
      let r : Fin L := ⟨min (gridRank v) (L - 1), by omega⟩
      refine ⟨r, ?_⟩
      have hv := gridRank_lt v
      dsimp [χ, r]
      omega
    · intro x y hxy
      have hd := gridRank_adj hxy
      have hx := gridRank_lt x
      have hy := gridRank_lt y
      let r : Fin L := ⟨min (min (gridRank x) (gridRank y)) (L - 1), by omega⟩
      refine ⟨r, ?_, ?_⟩ <;> dsimp [χ, r] <;> omega
    · intro a c b hp v hv
      by_cases hab : a.1 ≤ b.1
      · have hc := path_index_bounds hab hp
        change (a.1 ≤ gridRank v ∧ gridRank v ≤ a.1 + n) ∧
          (b.1 ≤ gridRank v ∧ gridRank v ≤ b.1 + n) at hv
        change c.1 ≤ gridRank v ∧ gridRank v ≤ c.1 + n
        omega
      · have hc := path_index_bounds (show b.1 ≤ a.1 by omega) (GM10.onTreePath_comm.mp hp)
        change (a.1 ≤ gridRank v ∧ gridRank v ≤ a.1 + n) ∧
          (b.1 ≤ gridRank v ∧ gridRank v ≤ b.1 + n) at hv
        change c.1 ≤ gridRank v ∧ gridRank v ≤ c.1 + n
        omega
  apply treeWidthLE_of_isTreeDecomposition htd
  intro r
  let f : χ r → Fin (n + 1) := fun v ↦ ⟨gridRank v.1 - r.1, by
    have hv := v.2
    dsimp [χ] at hv
    omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply gridRank_injective
    have he := congrArg Fin.val hxy
    have hx := x.2
    have hy := y.2
    dsimp [f, χ] at he hx hy
    omega
  exact (Nat.card_le_card_of_injective f hf).trans (by simp)

end GraphMinor.GM05
