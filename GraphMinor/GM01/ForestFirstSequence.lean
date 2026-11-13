module

public import GraphMinor.GM01.ForestGraphs
import GraphMinor.GM01.MainReduction
import GraphMinor.GM01.PathWidth
import GraphMinor.GM03.Section1
import GraphMinor.GM04.Main
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# A sequence whose first graph is a forest

This proves Graph Minors I, (1.3), page 40, as the paper does: (1.1) "dovetails nicely with the
main theorem of [3]; the two results together yield the following". The main theorem of [3] is
Graph Minors IV, (1.5): graphs of bounded tree-width are well-quasi-ordered by minors
(`GM04.theorem_1_5_proved`).

If some later graph has a minor isomorphic to the forest `G 0`, we are done. Otherwise, by (1.1)
(`theorem_1_1`), every later graph has path-width at most some `w`. A path-decomposition is a
tree-decomposition whose tree is a path, so the later graphs have tree-width at most `w`
(`treeWidthLE_of_hasPathWidthLE`), and IV (1.5) gives a comparable pair among them.

A path-decomposition in I, Section 1, need not cover vertices of valency zero, while a
tree-decomposition must. We add a bag `{v}` at the end of the path for each vertex `v` in no bag,
and one empty bag so that the path is never empty.
-/

namespace GraphMinor.GM01

open Graph SimpleGraph Set

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

/-- A node on the path of `pathGraph L` between `a` and `b` has its index between theirs. -/
private lemma path_index_bounds {L : ℕ} {a b c : Fin L}
    (hp : GM10.OnTreePath (pathGraph L) a b c) :
    min a.1 b.1 ≤ c.1 ∧ c.1 ≤ max a.1 b.1 := by
  by_cases hab : a.1 ≤ b.1
  · obtain ⟨p, hb⟩ := bounded_path_walk a b hab
    have := hb c (GM10.mem_support_of_onTreePath hp p)
    omega
  · obtain ⟨p, hb⟩ := bounded_path_walk b a (by omega)
    have := hb c (GM10.mem_support_of_onTreePath (GM10.onTreePath_comm.mp hp) p)
    omega

/-- Graph Minors I, Section 1, page 39, with III, Section 1: a graph with finitely many vertices
and path-width at most `w` has tree-width at most `w`. The bags of a path-decomposition, indexed
by a path, form a tree-decomposition once the vertices in no bag get bags of their own. -/
theorem treeWidthLE_of_hasPathWidthLE {α β : Type*} {G : Graph α β} (hV : V(G).Finite)
    {w : ℕ} (h : HasPathWidthLE G w) : GM03.TreeWidthLE G w := by
  classical
  obtain ⟨D, hD⟩ := h
  let L := D.length
  let _ : Fintype V(G) := hV.fintype
  let n := Fintype.card V(G)
  let e : Fin n ≃ V(G) := (Fintype.equivFin V(G)).symm
  let covered : Set α := ⋃ j, D.bag j
  -- The bag of node `i` of the path on `L + n + 1` nodes.
  let X : Fin (L + n + 1) → Set α := fun i =>
    if h₁ : i.1 < L then D.bag ⟨i.1, h₁⟩
    else if h₂ : i.1 - L < n then
      (if (e ⟨i.1 - L, h₂⟩).1 ∈ covered then ∅ else {(e ⟨i.1 - L, h₂⟩).1})
    else ∅
  have hX_lt : ∀ (i : Fin (L + n + 1)) (h₁ : i.1 < L), X i = D.bag ⟨i.1, h₁⟩ := by
    intro i h₁
    simp only [X, dite_eq_left h₁]
  have hX_ge : ∀ (i : Fin (L + n + 1)), ¬ i.1 < L → ∀ v ∈ X i,
      ∃ h₂ : i.1 - L < n, v = (e ⟨i.1 - L, h₂⟩).1 ∧ v ∉ covered := by
    intro i h₁ v hv
    simp only [X, dite_eq_right h₁] at hv
    by_cases h₂ : i.1 - L < n
    · rw [dite_eq_left h₂] at hv
      by_cases hc : (e ⟨i.1 - L, h₂⟩).1 ∈ covered
      · rw [ite_eq_left hc] at hv
        exact absurd hv (notMem_empty v)
      · rw [ite_eq_right hc, mem_singleton_iff] at hv
        exact ⟨h₂, hv, hv ▸ hc⟩
    · rw [dite_eq_right h₂] at hv
      exact absurd hv (notMem_empty v)
  have hsub : ∀ i, X i ⊆ V(G) := by
    intro i v hv
    by_cases h₁ : i.1 < L
    · rw [hX_lt i h₁] at hv
      exact D.bag_subset _ hv
    · obtain ⟨h₂, rfl, -⟩ := hX_ge i h₁ v hv
      exact (e _).2
  have htd : GM03.IsTreeDecomposition G (pathGraph (L + n + 1)) X := by
    refine ⟨pathGraph_tree_succ _, hsub, ?_, ?_, ?_⟩
    · -- (W1): every vertex is in a bag
      refine Subset.antisymm (iUnion_subset hsub) fun v hv => ?_
      by_cases hc : v ∈ covered
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hc
        refine mem_iUnion.mpr ⟨⟨j.1, by omega⟩, ?_⟩
        rw [hX_lt _ j.2]
        exact hj
      · let k := e.symm ⟨v, hv⟩
        have hk : (e k).1 = v := by simp [k]
        refine mem_iUnion.mpr ⟨⟨L + k.1, by omega⟩, ?_⟩
        have h₁ : ¬ (L + k.1) < L := by omega
        have h₂ : L + k.1 - L < n := by omega
        have hk' : (⟨L + k.1 - L, h₂⟩ : Fin n) = k := Fin.ext (by simp)
        simp only [X, dite_eq_right h₁, dite_eq_left h₂, hk', hk, ite_eq_right hc,
          mem_singleton_iff]
    · -- (W2): every edge is in a bag
      intro f x y hl
      obtain ⟨j, hx, hy⟩ := D.edge_covered f x y hl
      refine ⟨⟨j.1, by omega⟩, ?_, ?_⟩ <;> rw [hX_lt _ j.2]
      · exact hx
      · exact hy
    · -- (W3): the bags containing a vertex form an interval
      intro a c b hp v ⟨hva, hvb⟩
      have hc := path_index_bounds (L := L + n + 1) hp
      by_cases ha : a.1 < L <;> by_cases hb : b.1 < L
      · have hcL : c.1 < L := by omega
        rw [hX_lt _ ha] at hva
        rw [hX_lt _ hb] at hvb
        rw [hX_lt _ hcL]
        rcases le_total a.1 b.1 with hab | hab
        · exact D.interval ⟨a.1, ha⟩ ⟨c.1, hcL⟩ ⟨b.1, hb⟩ (by simp; omega) (by simp; omega)
            ⟨hva, hvb⟩
        · exact D.interval ⟨b.1, hb⟩ ⟨c.1, hcL⟩ ⟨a.1, ha⟩ (by simp; omega) (by simp; omega)
            ⟨hvb, hva⟩
      · rw [hX_lt _ ha] at hva
        obtain ⟨-, -, hcov⟩ := hX_ge b hb v hvb
        exact absurd (mem_iUnion.mpr ⟨_, hva⟩) hcov
      · rw [hX_lt _ hb] at hvb
        obtain ⟨-, -, hcov⟩ := hX_ge a ha v hva
        exact absurd (mem_iUnion.mpr ⟨_, hvb⟩) hcov
      · obtain ⟨h₂a, hva', -⟩ := hX_ge a ha v hva
        obtain ⟨h₂b, hvb', -⟩ := hX_ge b hb v hvb
        have hk : (⟨a.1 - L, h₂a⟩ : Fin n) = ⟨b.1 - L, h₂b⟩ :=
          e.injective (Subtype.ext (hva'.symm.trans hvb'))
        have hab : a = b := Fin.ext (by have := congrArg Fin.val hk; simp at this; omega)
        subst hab
        have hca : c = a := Fin.ext (by omega)
        subst hca
        exact hva
  refine (GM03.treeWidthLE_iff_exists_isTreeDecomposition G w).mpr
    ⟨Fin (L + n + 1), inferInstance, pathGraph (L + n + 1), X, htd, fun i => ?_⟩
  by_cases h₁ : i.1 < L
  · rw [hX_lt i h₁]
    exact (hD _).2
  · have : Finite (X i) := (hV.subset (hsub i)).to_subtype
    have hle : (X i).ncard ≤ 1 := by
      rw [ncard_le_one]
      intro x hx y hy
      obtain ⟨h₂, rfl, -⟩ := hX_ge i h₁ x hx
      obtain ⟨-, rfl, -⟩ := hX_ge i h₁ y hy
      rfl
    omega

/-- Graph Minors I, (1.3), page 40: "Let $G_1, G_2, ..., $ be a
countable sequence of graphs, such that $G_1$ is a forest. Then there
exist $j > i \ge 1$ such that $G_i$ is isomorphic to a minor of $G_j$."
The proof is the paper's: (1.1) (`theorem_1_1`) bounds the path-width of the later graphs that
exclude the forest, and Graph Minors IV, (1.5) (`GM04.theorem_1_5_proved`) applies to them.
The sequence is indexed from zero, so its first graph is `G 0`. -/
public theorem theorem_1_3_proof {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hForest : IsForest (G 0)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  by_cases h : ∃ j, IsIsoMinor (G 0) (G (j + 1))
  · obtain ⟨j, hj⟩ := h
    exact ⟨0, j + 1, Nat.succ_pos j, hj⟩
  · simp only [not_exists] at h
    obtain ⟨w, hw⟩ := theorem_1_1_proof (G 0) (hV 0) hForest
    obtain ⟨i, j, hij, hm⟩ := GM04.theorem_1_5_proved w (fun n => G (n + 1))
      (fun n => hV (n + 1)) (fun n => hE (n + 1)) fun n =>
        GM03.treeWidthLE_gm04_of_treeWidthLE (hV (n + 1)) (hE (n + 1))
          (treeWidthLE_of_hasPathWidthLE (hV (n + 1))
            (hw (G (n + 1)) (hV (n + 1)) (hE (n + 1)) (h n)))
    exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, hm⟩

end GraphMinor.GM01
