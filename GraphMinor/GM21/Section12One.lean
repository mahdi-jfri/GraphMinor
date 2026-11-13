module

public import GraphMinor.GM21.Section12Fam

/-!
# Graph Minors XXI, (12.1): a path-decomposition along a unique set of disjoint paths

The path-decomposition of (12.1) is built from a chain of separations
`(A, B) = (a 0, b 0), (a 1, b 1), …, (a m, b m) = (A', B')`, each of order `k`, where `a` grows and
`b` shrinks. Its bags are `a 0`, `b j ∩ a (j + 1)` for `j < m`, and `b m`, on the path with
`m + 2` vertices (`isTreeDecomp21_chain`). The proof of (12.1) is the paper's induction on
`|E(B ∩ A')|`: steps (1) and (2) of the paper each add one separation to the front of the chain,
and steps (3) and (4) show that otherwise `B ∩ A'` has no edges, so that the chain has length `0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph SimpleGraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## The path with `m + 1` vertices -/

theorem isTree_pathGraph (m : ℕ) : (pathGraph (m + 1)).IsTree := by
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

theorem exists_bounded_walk_pathGraph {L : ℕ} (a b : Fin L) (hab : a.1 ≤ b.1) :
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
      obtain ⟨p, hp⟩ := ih a' b (by dsimp [a']; omega) (by dsimp [a']; omega)
      refine ⟨.cons (pathGraph_adj.mpr (Or.inl rfl)) p, ?_⟩
      intro c hc
      simp only [Walk.support_cons, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ⟨le_rfl, hab⟩
      · have h := hp c hc
        exact ⟨by dsimp [a'] at h; omega, h.2⟩
  exact main _ a b hab rfl

/-- A vertex on the path of `pathGraph L` between `a` and `b` lies between them. -/
theorem le_of_onTreePath_pathGraph {L : ℕ} {a b c : Fin L} (hab : a.1 ≤ b.1)
    (hp : GM10.OnTreePath (pathGraph L) a b c) : a.1 ≤ c.1 ∧ c.1 ≤ b.1 := by
  obtain ⟨p, hb⟩ := exists_bounded_walk_pathGraph a b hab
  exact hb c (GM10.mem_support_of_onTreePath hp p)

/-! ## Chains of separations -/

/-- One step of the chain: from `(A, B)` to `(A₁, B₁)`. The bag `B ∩ A₁` between them has exactly
one edge `g`, and either (a) `V(A ∩ B) = V(A₁ ∩ B₁) = V(B ∩ A₁)`, or (b) `V(A ∩ B) = X ∪ {v}` and
`V(A₁ ∩ B₁) = X ∪ {v'}` where `X` is their intersection, `|X| = k - 1`, and `g` has ends `v, v'`.
These are (iii)(a) and (iii)(b) of (12.1). -/
def IsChainStep (k : ℕ) (A B A₁ B₁ : Hypergraph α β) : Prop :=
  ∃ g, (B ∩ A₁).edgeSet = {g} ∧
    (((A ∩ B).vertexSet = (B ∩ A₁).vertexSet ∧ (A₁ ∩ B₁).vertexSet = (B ∩ A₁).vertexSet) ∨
      ∃ X : Set α, ∃ v v' : α, (A ∩ B).vertexSet ∩ (A₁ ∩ B₁).vertexSet = X ∧ X.ncard = k - 1 ∧
        (B ∩ A₁).ends g = {v, v'} ∧ (A ∩ B).vertexSet = insert v X ∧
        (A₁ ∩ B₁).vertexSet = insert v' X)

/-- Separations `(a j, b j)` of `G` of order `k`, where `a` grows, `b` shrinks, each of the first
`m` steps is as in `IsChainStep`, and nothing changes after step `m`. -/
structure IsSepChain (G : Hypergraph α β) (k : ℕ) (a b : ℕ → Hypergraph α β) (m : ℕ) : Prop where
  sep : ∀ j, G.IsSeparation (a j) (b j)
  ord : ∀ j, (a j ∩ b j).vertexSet.ncard = k
  amono : ∀ j, a j ≤ a (j + 1)
  bmono : ∀ j, b (j + 1) ≤ b j
  step : ∀ j < m, IsChainStep k (a j) (b j) (a (j + 1)) (b (j + 1))
  stop : ∀ j, m ≤ j → a j = a m ∧ b j = b m

/-- The bags of the path-decomposition given by a chain: `a 0`, then `b j ∩ a (j + 1)` for `j < m`,
then `b m`. -/
def chainBag (a b : ℕ → Hypergraph α β) (m : ℕ) : ℕ → Hypergraph α β
  | 0 => a 0
  | j + 1 => if j < m then b j ∩ a (j + 1) else b m

/-- The sequence `x, s 0, s 1, …`. -/
def consSeq {γ : Type*} (x : γ) (s : ℕ → γ) : ℕ → γ
  | 0 => x
  | j + 1 => s j

section Chain

variable {G : Hypergraph α β} {k m : ℕ} {a b : ℕ → Hypergraph α β}

theorem chainBag_succ_of_lt {j : ℕ} (hj : j < m) : chainBag a b m (j + 1) = b j ∩ a (j + 1) := by
  simp [chainBag, hj]

theorem chainBag_last : chainBag a b m (m + 1) = b m := by
  simp [chainBag]

variable (h : IsSepChain G k a b m)
include h

theorem IsSepChain.a_le (j : ℕ) : a j ≤ G := (h.sep j).left_le

theorem IsSepChain.b_le (j : ℕ) : b j ≤ G := (h.sep j).right_le

theorem IsSepChain.a_mono {i j : ℕ} (hij : i ≤ j) : a i ≤ a j :=
  monotone_nat_of_le_succ h.amono hij

theorem IsSepChain.b_anti {i j : ℕ} (hij : i ≤ j) : b j ≤ b i :=
  antitone_nat_of_succ_le h.bmono hij

theorem IsSepChain.bag_le (j : ℕ) : chainBag a b m j ≤ G := by
  rcases j with _ | j
  · exact h.a_le 0
  · by_cases hj : j < m
    · rw [chainBag_succ_of_lt hj]
      exact GM10.inter_le (h.b_le j) (h.a_le _)
    · simp only [chainBag, hj, ite_false]
      exact h.b_le m

theorem IsSepChain.bag_le_a {j : ℕ} (hj : j ≤ m) : chainBag a b m j ≤ a j := by
  rcases j with _ | j
  · exact le_rfl
  · rw [chainBag_succ_of_lt (by omega)]
    exact GM10.inter_le_right (h.b_le j) (h.a_le _)

theorem IsSepChain.bag_succ_le_b {j : ℕ} (hj : j ≤ m) : chainBag a b m (j + 1) ≤ b j := by
  rcases eq_or_lt_of_le hj with rfl | hj
  · rw [chainBag_last]
  · rw [chainBag_succ_of_lt hj]
    exact GM10.inter_le_left (h.b_le j) (h.a_le _)

/-- Consecutive bags meet in the middle of the separation between them. -/
theorem IsSepChain.inter_bag {j : ℕ} (hj : j ≤ m) :
    (chainBag a b m j).vertexSet ∩ (chainBag a b m (j + 1)).vertexSet = (a j ∩ b j).vertexSet := by
  apply Subset.antisymm
  · rintro x ⟨h1, h2⟩
    exact ⟨(h.bag_le_a hj).vertexSet_subset h1, (h.bag_succ_le_b hj).vertexSet_subset h2⟩
  · rintro x ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rcases j with _ | j
      · exact h1
      · rw [chainBag_succ_of_lt (by omega)]
        exact ⟨(h.bmono j).vertexSet_subset h2, h1⟩
    · rcases eq_or_lt_of_le hj with rfl | hj
      · rw [chainBag_last]; exact h2
      · rw [chainBag_succ_of_lt hj]
        exact ⟨h2, (h.amono j).vertexSet_subset h1⟩

/-- Everything in `a i` is in a bag with index `≤ i`. -/
theorem IsSepChain.cover_a {γ : Type*} (p : Hypergraph α β → Set γ)
    (hp : ∀ H₁ H₂, p (H₁ ∩ H₂) = p H₁ ∩ p H₂) (hpu : ∀ j, p (a j) ∪ p (b j) = p G) {x : γ} :
    ∀ i ≤ m, x ∈ p (a i) → ∃ j ≤ i, x ∈ p (chainBag a b m j) := by
  intro i
  induction i with
  | zero => exact fun _ hx ↦ ⟨0, le_rfl, hx⟩
  | succ i ih =>
    intro hi hx
    have hxG : x ∈ p G := hpu (i + 1) ▸ Or.inl hx
    rw [← hpu i] at hxG
    rcases hxG with hx' | hx'
    · obtain ⟨j, hj, hxj⟩ := ih (by omega) hx'
      exact ⟨j, by omega, hxj⟩
    · refine ⟨i + 1, le_rfl, ?_⟩
      rw [chainBag_succ_of_lt (by omega), hp]
      exact ⟨hx', hx⟩

/-- Everything in `b i` is in a bag with index `> i`. -/
theorem IsSepChain.cover_b {γ : Type*} (p : Hypergraph α β → Set γ)
    (hp : ∀ H₁ H₂, p (H₁ ∩ H₂) = p H₁ ∩ p H₂) (hpu : ∀ j, p (a j) ∪ p (b j) = p G) {x : γ} :
    ∀ i ≤ m, x ∈ p (b i) → ∃ j, i < j ∧ j ≤ m + 1 ∧ x ∈ p (chainBag a b m j) := by
  suffices H : ∀ d i, i + d = m → x ∈ p (b i) → ∃ j, i < j ∧ j ≤ m + 1 ∧
      x ∈ p (chainBag a b m j) from fun i hi ↦ H (m - i) i (by omega)
  intro d
  induction d with
  | zero =>
    intro i hi hx
    subst hi
    exact ⟨i + 1, by omega, by omega, by rw [add_zero, chainBag_last]; exact hx⟩
  | succ d ih =>
    intro i hi hx
    have hxG : x ∈ p G := hpu i ▸ Or.inr hx
    rw [← hpu (i + 1)] at hxG
    rcases hxG with hx' | hx'
    · refine ⟨i + 1, by omega, by omega, ?_⟩
      rw [chainBag_succ_of_lt (by omega), hp]
      exact ⟨hx, hx'⟩
    · obtain ⟨j, hj, hjm, hxj⟩ := ih (i + 1) (by omega) hx'
      exact ⟨j, by omega, hjm, hxj⟩

theorem IsSepChain.bag_inter_le {i j l : ℕ} (hij : i ≤ j) (hjl : j ≤ l) (hl : l ≤ m + 1) :
    chainBag a b m i ∩ chainBag a b m l ≤ chainBag a b m j := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact GM10.inter_le_left (h.bag_le _) (h.bag_le _)
  rcases eq_or_lt_of_le hjl with rfl | hjl
  · exact GM10.inter_le_right (h.bag_le _) (h.bag_le _)
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [chainBag_succ_of_lt (by omega)]
  have hil := GM10.inter_le (h.bag_le i) (h.bag_le l)
  refine DiscCut.le_inter' ?_ ?_
  · refine (GM10.inter_le_right (h.bag_le i) (h.bag_le l)).trans ?_
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    exact (h.bag_succ_le_b (by omega)).trans (h.b_anti (by omega))
  · exact (GM10.inter_le_left (h.bag_le i) (h.bag_le l)).trans
      ((h.bag_le_a (by omega)).trans (h.a_mono (by omega)))

/-- **A chain of separations gives a path-decomposition.** -/
theorem IsSepChain.isTreeDecomp21 :
    IsTreeDecomp21 G (pathGraph (m + 2)) (fun t : Fin (m + 2) ↦ chainBag a b m t) := by
  classical
  have hV : ∀ j, (a j).vertexSet ∪ (b j).vertexSet = G.vertexSet :=
    fun j ↦ (h.sep j).vertexSet_union
  have hE : ∀ j, (a j).edgeSet ∪ (b j).edgeSet = G.edgeSet := fun j ↦ (h.sep j).edgeSet_union
  refine ⟨isTree_pathGraph (m + 1), fun t ↦ h.bag_le t, ?_, ?_⟩
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (GM10.biUnion_le_of_le fun t _ ↦ h.bag_le t) le_rfl ?_ ?_
    · apply Subset.antisymm
      · intro x hx
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hx
        obtain ⟨t, hx⟩ := hx
        exact (h.bag_le t).vertexSet_subset hx
      · intro x hx
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
        rw [← hV 0] at hx
        rcases hx with hx | hx
        · exact ⟨0, hx⟩
        · obtain ⟨j, -, hj, hxj⟩ := h.cover_b (fun H ↦ H.vertexSet) (fun _ _ ↦ rfl) hV 0
            (Nat.zero_le _) hx
          exact ⟨⟨j, by omega⟩, hxj⟩
    · apply Subset.antisymm
      · intro x hx
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hx
        obtain ⟨t, hx⟩ := hx
        exact (h.bag_le t).edgeSet_subset hx
      · intro x hx
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion]
        rw [← hE 0] at hx
        rcases hx with hx | hx
        · exact ⟨0, hx⟩
        · obtain ⟨j, -, hj, hxj⟩ := h.cover_b (fun H ↦ H.edgeSet) (fun _ _ ↦ rfl) hE 0
            (Nat.zero_le _) hx
          exact ⟨⟨j, by omega⟩, hxj⟩
  · intro t t' t'' hp
    rcases le_total t.1 t''.1 with hle | hle
    · obtain ⟨h1, h2⟩ := le_of_onTreePath_pathGraph hle hp
      exact h.bag_inter_le h1 h2 (by omega)
    · obtain ⟨h1, h2⟩ := le_of_onTreePath_pathGraph hle (GM10.onTreePath_comm.1 hp)
      rw [GM10.inter_comm]
      exact h.bag_inter_le h1 h2 (by omega)

/-- `W(e)` for the edge `e` of the path between `j` and `j + 1` is the middle of `(a j, b j)`. -/
theorem IsSepChain.treeEdgeSet_eq {t u : Fin (m + 2)} (hadj : (pathGraph (m + 2)).Adj t u) :
    treeEdgeSet (pathGraph (m + 2)) (fun t : Fin (m + 2) ↦ chainBag a b m t) t u =
      (a (min t.1 u.1) ∩ b (min t.1 u.1)).vertexSet := by
  rw [h.isTreeDecomp21.treeEdgeSet_eq hadj]
  rcases pathGraph_adj.1 hadj with h' | h'
  · rw [min_eq_left (by omega), ← h', h.inter_bag (by omega)]
  · rw [min_eq_right (by omega), ← h', Set.inter_comm, h.inter_bag (by omega)]

end Chain

section Build

variable {G : Hypergraph α β} {k m : ℕ} {a b : ℕ → Hypergraph α β}

/-- The chain with one separation. -/
theorem isSepChain_single {A B : Hypergraph α β} (hs : G.IsSeparation A B)
    (ho : (A ∩ B).vertexSet.ncard = k) : IsSepChain G k (fun _ ↦ A) (fun _ ↦ B) 0 :=
  ⟨fun _ ↦ hs, fun _ ↦ ho, fun _ ↦ le_rfl, fun _ ↦ le_rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _),
    fun _ _ ↦ ⟨rfl, rfl⟩⟩

/-- Putting one more separation in front of a chain. -/
theorem IsSepChain.cons (h : IsSepChain G k a b m) {A B : Hypergraph α β}
    (hs : G.IsSeparation A B) (ho : (A ∩ B).vertexSet.ncard = k) (hA : A ≤ a 0) (hB : b 0 ≤ B)
    (hstep : IsChainStep k A B (a 0) (b 0)) :
    IsSepChain G k (consSeq A a) (consSeq B b) (m + 1) where
  sep j := by cases j; exacts [hs, h.sep _]
  ord j := by cases j; exacts [ho, h.ord _]
  amono j := by cases j; exacts [hA, h.amono _]
  bmono j := by cases j; exacts [hB, h.bmono _]
  step j hj := by cases j; exacts [hstep, h.step _ (by omega)]
  stop j hj := by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact h.stop j (by omega)

end Build

/-! ## The induction of (12.1) -/

/-- In `K` there is a unique set of `k` disjoint paths between `Y` and `Z`, and every vertex of `K`
is on one of them. -/
def UniqSystem (K : Hypergraph α β) (Y Z : Set α) (k : ℕ) : Prop :=
  ∃ M, IsPathSystem K Y Z k M ∧ (∀ M', IsPathSystem K Y Z k M' → M' = M) ∧
    M.vertexSet = K.vertexSet

section Steps

variable {G A B A' B' : Hypergraph α β} {k : ℕ}

/-- **Step (1) of the proof of (12.1).** An edge `g` of `B ∩ A'` with both ends in `V(A ∩ B)` moves
from `B` to `A`. The print takes "a path-decomposition $(P_1, W_1)$ of $B \cap A_1$" and sets
"$W(t) = W'(t)$". These are misprints for a path-decomposition of $G$ and $W(t) = W_1(t)$ (see the
correction to the proof of (12.1) in `corrections/GM21.md`). We build the chain of separations
instead of the path-decomposition. -/
theorem step_one (hG : G.IsGraph) (hs : G.IsSeparation A B) (hs' : G.IsSeparation A' B')
    (hAA' : A ≤ A') (hBB' : B' ≤ B) (hk : (A ∩ B).vertexSet.ncard = k)
    (hU : UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k) {g : β}
    (hg : g ∈ (B ∩ A').edgeSet) (hgY : (B ∩ A').ends g ⊆ (A ∩ B).vertexSet) :
    ∃ A₁ B₁ : Hypergraph α β, G.IsSeparation A₁ B₁ ∧ (A₁ ∩ B₁).vertexSet.ncard = k ∧
      A ≤ A₁ ∧ B₁ ≤ B ∧ A₁ ≤ A' ∧ B' ≤ B₁ ∧
      (B₁ ∩ A').edgeSet.ncard < (B ∩ A').edgeSet.ncard ∧
      UniqSystem (B₁ ∩ A') (A₁ ∩ B₁).vertexSet (A' ∩ B').vertexSet k ∧
      IsChainStep k A B A₁ B₁ := by
  classical
  have hA := hs.left_le
  have hB := hs.right_le
  have hA' := hs'.left_le
  have hB' := hs'.right_le
  have hKG : B ∩ A' ≤ G := GM10.inter_le hB hA'
  have hgG : g ∈ G.edgeSet := hKG.edgeSet_subset hg
  have hends : G.ends g ⊆ A.vertexSet := by
    rw [hKG.ends_eq g hg]; exact fun x hx ↦ (hgY hx).1
  have hEH : GM10.edgeHypergraph G g ≤ G := GM10.edgeHypergraph_le hgG
  set A₁ := A ∪ GM10.edgeHypergraph G g with hA₁
  set B₁ := B.deleteEdges {g} with hB₁
  have hA₁G : A₁ ≤ G := GM10.union_le hA hEH
  have hB₁B : B₁ ≤ B := GM10.deleteEdges_le B {g}
  have hB₁G : B₁ ≤ G := hB₁B.trans hB
  have hV₁ : A₁.vertexSet = A.vertexSet ∪ G.ends g := rfl
  have hE₁ : A₁.edgeSet = A.edgeSet ∪ {g} := rfl
  have hVB₁ : B₁.vertexSet = B.vertexSet := rfl
  have hEB₁ : B₁.edgeSet = B.edgeSet \ {g} := rfl
  have hVA₁ : A₁.vertexSet = A.vertexSet := by rw [hV₁, union_eq_left.2 hends]
  have hsep : G.IsSeparation A₁ B₁ := by
    rw [GM10.isSeparation_iff_of_le hA₁G hB₁G, hVA₁, hVB₁, hE₁, hEB₁]
    refine ⟨hs.vertexSet_union, ?_, ?_⟩
    · rw [← hs.edgeSet_union]
      ext e
      by_cases he : e = g
      · subst he; simp [hg.1]
      · simp [he]
    · ext e
      simp only [mem_inter_iff, mem_union, mem_singleton_iff, mem_sdiff, mem_empty_iff_false,
        iff_false, not_and]
      rintro (he | rfl) heB hne
      · exact hs.notMem_edgeSet_right he heB
      · exact hne rfl
  have hmid : (A₁ ∩ B₁).vertexSet = (A ∩ B).vertexSet := by
    change A₁.vertexSet ∩ B₁.vertexSet = A.vertexSet ∩ B.vertexSet
    rw [hVA₁, hVB₁]
  have hK₁ : (B₁ ∩ A').edgeSet = (B ∩ A').edgeSet \ {g} := by
    change (B.edgeSet \ {g}) ∩ A'.edgeSet = (B.edgeSet ∩ A'.edgeSet) \ {g}
    rw [inter_sdiff_right_comm]
  have hK₁K : B₁ ∩ A' ≤ B ∩ A' :=
    (GM10.le_iff_of_le (GM10.inter_le hB₁G hA') hKG).2 ⟨subset_rfl, by rw [hK₁]; exact sdiff_subset⟩
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  -- `g` is not an edge of `M`, since each vertex of `V(A ∩ B)` is the first vertex of its path.
  have hgM : g ∉ M.edgeSet := by
    intro hgM
    have : Nonempty β := ⟨g⟩
    obtain ⟨x, -⟩ := (hG g hgG).1
    have : Nonempty α := ⟨x⟩
    have hYf : (A ∩ B).vertexSet.Finite := (A ∩ B).vertexSet_finite
    obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hk ▸ hM)
    rw [← hfam, famGraph_edgeSet hF.1] at hgM
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_famEdges.1 hgM
    have h1 : c y (a + 1) ∈ (B ∩ A').ends (f y a) := by
      rw [hF.1.ends y hy a ha]; exact mem_insert_of_mem _ rfl
    have h2 := hgY h1
    have h3 := hF.1.eq_of_eq hy h2 ha (Nat.zero_le _) (hc0 _ h2).symm
    omega
  have hMK₁ : M ≤ B₁ ∩ A' :=
    (GM10.le_iff_of_le (hM.1.1.trans hKG) (GM10.inter_le hB₁G hA')).2
      ⟨hM.1.1.vertexSet_subset, by
        rw [hK₁]; exact fun e he ↦ ⟨hM.1.1.edgeSet_subset he, fun h ↦ hgM (h ▸ he)⟩⟩
  refine ⟨A₁, B₁, hsep, hmid ▸ hk, GM10.le_union_left hA hEH, hB₁B, ?_, ?_, ?_, ?_, ?_⟩
  · refine (GM10.le_iff_of_le hA₁G hA').2 ⟨by rw [hVA₁]; exact hAA'.vertexSet_subset, ?_⟩
    rw [hE₁]
    exact union_subset hAA'.edgeSet_subset (singleton_subset_iff.2 hg.2)
  · refine (GM10.le_iff_of_le hB' hB₁G).2 ⟨hBB'.vertexSet_subset, fun e he ↦ ⟨hBB'.edgeSet_subset he,
      fun h ↦ hs'.notMem_edgeSet_left he ((mem_singleton_iff.1 h) ▸ hg.2)⟩⟩
  · rw [hK₁]
    exact ncard_sdiff_singleton_lt_of_mem hg (B ∩ A').edgeSet_finite
  · rw [hmid]
    refine ⟨M, ⟨hM.1.mono_ambient hMK₁, hM.2⟩, fun M' hM' ↦
      hMu M' ⟨hM'.1.mono_ambient (hM'.1.1.trans hK₁K), hM'.2⟩, hMV⟩
  · refine ⟨g, ?_, Or.inl ⟨?_, ?_⟩⟩
    · change B.edgeSet ∩ (A.edgeSet ∪ {g}) = {g}
      ext e
      simp only [mem_inter_iff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨heB, he | rfl⟩
        · exact absurd heB (hs.notMem_edgeSet_right he)
        · rfl
      · rintro rfl; exact ⟨hg.1, Or.inr rfl⟩
    · change A.vertexSet ∩ B.vertexSet = B.vertexSet ∩ A₁.vertexSet
      rw [hVA₁, Set.inter_comm]
    · change A₁.vertexSet ∩ B₁.vertexSet = B.vertexSet ∩ A₁.vertexSet
      rw [hVB₁, Set.inter_comm]

end Steps

section StepTwo

variable {G A B A' B' : Hypergraph α β} {k : ℕ}

theorem insert_sdiff_singleton_eq {x : α} {Y : Set α} (h : x ∈ Y) : insert x (Y \ {x}) = Y := by
  ext y
  by_cases hy : y = x
  · subst hy; simp [h]
  · simp [hy]

/-- **Step (2) of the proof of (12.1).** A vertex `v ∈ V(A ∩ B) - V(A' ∩ B')` with exactly one edge
`g = vv₁` in `B ∩ A'` moves, with `g`, from `B` to `A`, and `v₁` takes its place in the middle. -/
theorem step_two (hG : G.IsGraph) (hs : G.IsSeparation A B) (hs' : G.IsSeparation A' B')
    (hAA' : A ≤ A') (hBB' : B' ≤ B) (hk : (A ∩ B).vertexSet.ncard = k)
    (hU : UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k)
    (hno : ∀ g ∈ (B ∩ A').edgeSet, ¬ (B ∩ A').ends g ⊆ (A ∩ B).vertexSet) {v : α}
    (hvY : v ∈ (A ∩ B).vertexSet) (hvZ : v ∉ (A' ∩ B').vertexSet)
    (hv1 : (incidentEdges (B ∩ A') v).ncard = 1) :
    ∃ A₁ B₁ : Hypergraph α β, G.IsSeparation A₁ B₁ ∧ (A₁ ∩ B₁).vertexSet.ncard = k ∧
      A ≤ A₁ ∧ B₁ ≤ B ∧ A₁ ≤ A' ∧ B' ≤ B₁ ∧
      (B₁ ∩ A').edgeSet.ncard < (B ∩ A').edgeSet.ncard ∧
      UniqSystem (B₁ ∩ A') (A₁ ∩ B₁).vertexSet (A' ∩ B').vertexSet k ∧
      IsChainStep k A B A₁ B₁ := by
  classical
  set Y := (A ∩ B).vertexSet with hYdef
  set Z := (A' ∩ B').vertexSet with hZdef
  set K := B ∩ A' with hKdef
  have hA := hs.left_le
  have hB := hs.right_le
  have hA' := hs'.left_le
  have hB' := hs'.right_le
  have hKG : K ≤ G := GM10.inter_le hB hA'
  have hYK : ∀ y ∈ Y, y ∈ K.vertexSet := fun y hy ↦ ⟨hy.2, hAA'.vertexSet_subset hy.1⟩
  obtain ⟨g, hgeq⟩ := ncard_eq_one.1 hv1
  have hgK : g ∈ K.edgeSet ∧ K.Inc g v := by
    have : g ∈ incidentEdges K v := hgeq ▸ mem_singleton g
    exact this
  have hgG : g ∈ G.edgeSet := hKG.edgeSet_subset hgK.1
  have hKe : G.ends g = K.ends g := hKG.ends_eq g hgK.1
  obtain ⟨v₁, hv₁K, hv₁Y⟩ := not_subset.1 (hno g hgK.1)
  have hvv₁ : v ≠ v₁ := fun h ↦ hv₁Y (h ▸ hvY)
  have hends : G.ends g = {v, v₁} := by
    have hsub : ({v, v₁} : Set α) ⊆ G.ends g := by
      rw [hKe]; rintro x (rfl | rfl); exacts [hgK.2, hv₁K]
    exact (eq_of_subset_of_ncard_le hsub (by rw [ncard_pair hvv₁]; exact (hG g hgG).2)
      (G.vertexSet_finite.subset fun x hx ↦ G.vertex_mem_of_inc hx)).symm
  have hv₁KV : v₁ ∈ K.vertexSet := K.vertex_mem_of_inc hv₁K
  have hvA : v ∈ A.vertexSet := hvY.1
  -- The only edge of `B` at `v` is `g`.
  have hBv : ∀ e ∈ B.edgeSet, B.Inc e v → e = g := by
    intro e heB hinc
    have hinG : G.Inc e v := GM10.inc_of_le hB hinc
    have heA' : e ∈ A'.edgeSet := by
      have heG : e ∈ G.edgeSet := hB.edgeSet_subset heB
      rw [← hs'.edgeSet_union] at heG
      rcases heG with h | h
      · exact h
      · exact absurd ⟨hAA'.vertexSet_subset hvA, B'.vertex_mem_of_inc
          ((GM10.inc_iff_of_le hB' h).2 hinG)⟩ hvZ
    have : e ∈ incidentEdges K v := ⟨⟨heB, heA'⟩, hinc, (GM10.inc_iff_of_le hA' heA').2 hinG⟩
    rw [hgeq] at this
    exact this
  have hEH : GM10.edgeHypergraph G g ≤ G := GM10.edgeHypergraph_le hgG
  set A₁ := A ∪ GM10.edgeHypergraph G g with hA₁
  set B₁ := B.deleteVertices {v} with hB₁
  have hA₁G : A₁ ≤ G := GM10.union_le hA hEH
  have hB₁B : B₁ ≤ B := GM10.deleteVertices_le B {v}
  have hB₁G : B₁ ≤ G := hB₁B.trans hB
  have hVA₁ : A₁.vertexSet = insert v₁ A.vertexSet := by
    change A.vertexSet ∪ G.ends g = _
    rw [hends]
    ext x
    simp only [mem_union, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (h | rfl | rfl)
      exacts [Or.inr h, Or.inr hvA, Or.inl rfl]
    · rintro (rfl | h)
      exacts [Or.inr (Or.inr rfl), Or.inl h]
  have hE₁ : A₁.edgeSet = A.edgeSet ∪ {g} := rfl
  have hVB₁ : B₁.vertexSet = B.vertexSet \ {v} := rfl
  have hEB₁ : B₁.edgeSet = B.edgeSet \ {g} := by
    ext e
    change (e ∈ B.edgeSet ∧ ∀ w ∈ ({v} : Set α), ¬ B.Inc e w) ↔ _
    simp only [mem_singleton_iff, forall_eq, mem_sdiff]
    constructor
    · rintro ⟨heB, hn⟩
      exact ⟨heB, fun h ↦ hn (h ▸ hgK.2.1)⟩
    · rintro ⟨heB, hne⟩
      exact ⟨heB, fun h ↦ hne (hBv e heB h)⟩
  have hsep : G.IsSeparation A₁ B₁ := by
    rw [GM10.isSeparation_iff_of_le hA₁G hB₁G, hVA₁, hVB₁, hE₁, hEB₁]
    refine ⟨?_, ?_, ?_⟩
    · rw [← hs.vertexSet_union]
      ext x
      simp only [mem_union, mem_insert_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ((rfl | h) | ⟨h, -⟩)
        exacts [Or.inr hv₁KV.1, Or.inl h, Or.inr h]
      · rintro (h | h)
        · exact Or.inl (Or.inr h)
        · by_cases hx : x = v
          · subst hx; exact Or.inl (Or.inr hvA)
          · exact Or.inr ⟨h, hx⟩
    · rw [← hs.edgeSet_union]
      ext e
      by_cases he : e = g
      · subst he; simp [hgK.1.1]
      · simp [he]
    · ext e
      simp only [mem_inter_iff, mem_union, mem_singleton_iff, mem_sdiff, mem_empty_iff_false,
        iff_false, not_and]
      rintro (he | rfl) heB hne
      · exact hs.notMem_edgeSet_right he heB
      · exact hne rfl
  set Y₁ := insert v₁ (Y \ {v}) with hY₁
  have hmid : (A₁ ∩ B₁).vertexSet = Y₁ := by
    change A₁.vertexSet ∩ B₁.vertexSet = _
    rw [hVA₁, hVB₁]
    ext x
    simp only [mem_inter_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff, Y₁, hYdef]
    constructor
    · rintro ⟨rfl | hxA, hxB, hxv⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hxA, hxB⟩, hxv⟩
    · rintro (rfl | ⟨⟨hxA, hxB⟩, hxv⟩)
      · exact ⟨Or.inl rfl, hv₁KV.1, hvv₁.symm⟩
      · exact ⟨Or.inr hxA, hxB, hxv⟩
  have hYf : Y.Finite := (A ∩ B).vertexSet_finite
  have hkpos : 1 ≤ k := by
    rw [← hk]; exact Nat.one_le_iff_ne_zero.2 (ncard_ne_zero_of_mem hvY hYf)
  have hY₁k : Y₁.ncard = k := by
    rw [hY₁, ncard_insert_of_notMem (fun h ↦ hv₁Y h.1) (hYf.subset sdiff_subset),
      ncard_sdiff_singleton_of_mem hvY, hk]
    omega
  have hY₁f : Y₁.Finite := (hYf.subset sdiff_subset).insert v₁
  have hK₁E : (B₁ ∩ A').edgeSet = K.edgeSet \ {g} := by
    change B₁.edgeSet ∩ A'.edgeSet = (B.edgeSet ∩ A'.edgeSet) \ {g}
    rw [hEB₁, inter_sdiff_right_comm]
  have hK₁V : (B₁ ∩ A').vertexSet = K.vertexSet \ {v} := by
    change B₁.vertexSet ∩ A'.vertexSet = (B.vertexSet ∩ A'.vertexSet) \ {v}
    rw [hVB₁, inter_sdiff_right_comm]
  have hK₁K : B₁ ∩ A' ≤ K :=
    (GM10.le_iff_of_le (GM10.inter_le hB₁G hA') hKG).2
      ⟨by rw [hK₁V]; exact sdiff_subset, by rw [hK₁E]; exact sdiff_subset⟩
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  have : Nonempty β := ⟨g⟩
  have : Nonempty α := ⟨v⟩
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hk ▸ hM)
  have hFp := hF.1
  -- The path of `v` starts with `g` and then `v₁`.
  have hnv : 1 ≤ n v := by
    by_contra h0
    have h0' : n v = 0 := by omega
    have := (hF.2.2.2 v hvY).2
    rw [h0', hc0 v hvY] at this
    exact hvZ this
  have hfv : f v 0 = g := by
    have : f v 0 ∈ incidentEdges K v := ⟨hFp.edge_mem v hvY 0 hnv,
      (hFp.inc_iff hvY hnv).2 (Or.inl (hc0 v hvY).symm)⟩
    rw [hgeq] at this
    exact this
  have hcv1 : c v 1 = v₁ := by
    have h1 : c v 1 ∈ G.ends g := by
      rw [hKe, ← hfv, hFp.ends v hvY 0 hnv]; exact mem_insert_of_mem _ rfl
    rw [hends] at h1
    rcases h1 with h1 | h1
    · have := hFp.inj v hvY (show 1 ∈ Iic (n v) from hnv) (show 0 ∈ Iic (n v) from Nat.zero_le _)
        (h1.trans (hc0 v hvY).symm)
      omega
    · exact h1
  obtain ⟨hF₁, hV₁, hvF₁, hE₁', hgF₁⟩ := hFp.shift hvY hnv
  rw [hc0 v hvY] at hV₁ hvF₁
  rw [hfv] at hE₁' hgF₁
  have hFV : famVerts Y c n = M.vertexSet := by rw [← hfam, famGraph_vertexSet hFp]
  have hFE : famEdges Y n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hFp]
  have hF₁K₁ : IsPathFam (B₁ ∩ A') Y (shiftC v c) (shiftN v n) (shiftF v f) := by
    refine hF₁.of_le hK₁K ?_ ?_
    · intro x hx
      rw [hK₁V]
      refine ⟨famVerts_subset hFp (hV₁ ▸ mem_insert_of_mem _ hx), fun h ↦ hvF₁ (h ▸ hx)⟩
    · intro e he
      rw [hK₁E]
      refine ⟨(famGraph_edgeSet hFp ▸ (famGraph_le hFp).edgeSet_subset) (hE₁' ▸ mem_insert_of_mem _ he),
        fun h ↦ hgF₁ (h ▸ he)⟩
  have hgood₁ : IsGoodFam (B₁ ∩ A') Y₁ (A' ∩ B').vertexSet Y (shiftC v c) (shiftN v n)
      (shiftF v f) := by
    refine ⟨hF₁K₁, hYf, by rw [hY₁k, hk], fun y hy ↦ ?_⟩
    by_cases hyv : y = v
    · subst hyv
      rw [shiftC_self, shiftC_self, shiftN_self, Nat.sub_add_cancel hnv, hcv1]
      exact ⟨mem_insert _ _, (hF.2.2.2 y hy).2⟩
    · rw [shiftC_of_ne hyv, shiftC_of_ne hyv, shiftN_of_ne hyv, hc0 y hy]
      exact ⟨mem_insert_of_mem _ ⟨hy, hyv⟩, (hc0 y hy ▸ (hF.2.2.2 y hy).2)⟩
  set M₁ := famGraph (B₁ ∩ A') Y (shiftC v c) (shiftN v n) (shiftF v f)
  have hM₁ : IsPathSystem (B₁ ∩ A') Y₁ Z k M₁ := hY₁k ▸ isPathSystem_famGraph hgood₁
  refine ⟨A₁, B₁, hsep, by rw [hmid, hY₁k], GM10.le_union_left hA hEH, hB₁B, ?_, ?_, ?_, ?_, ?_⟩
  · refine (GM10.le_iff_of_le hA₁G hA').2 ⟨?_, ?_⟩
    · rw [hVA₁]; exact insert_subset hv₁KV.2 hAA'.vertexSet_subset
    · rw [hE₁]; exact union_subset hAA'.edgeSet_subset (singleton_subset_iff.2 hgK.1.2)
  · refine (GM10.le_iff_of_le hB' hB₁G).2 ⟨?_, ?_⟩
    · rw [hVB₁]
      intro x hx
      refine ⟨hBB'.vertexSet_subset hx, fun h ↦ hvZ ?_⟩
      rw [mem_singleton_iff] at h
      subst h
      exact ⟨hAA'.vertexSet_subset hvA, hx⟩
    · rw [hEB₁]
      exact fun e he ↦ ⟨hBB'.edgeSet_subset he,
        fun h ↦ hs'.notMem_edgeSet_left he ((mem_singleton_iff.1 h) ▸ hgK.1.2)⟩
  · rw [hK₁E]
    exact ncard_sdiff_singleton_lt_of_mem hgK.1 K.edgeSet_finite
  · rw [hmid]
    refine ⟨M₁, hM₁, fun M' hM' ↦ ?_, ?_⟩
    · obtain ⟨c', n', f', hF', hc0', hfam'⟩ := exists_goodFam_of_isPathSystem hY₁f (hY₁k ▸ hM')
      have hv₁Y₁ : v₁ ∈ Y₁ := mem_insert _ _
      have hF'K := hF'.1.mono hK₁K
      have hvF' : v ∉ famVerts Y₁ c' n' := fun h ↦ by
        have := famVerts_subset hF'.1 h
        rw [hK₁V] at this
        exact this.2 rfl
      obtain ⟨hF'', hV'', hE''⟩ := hF'K.extend hv₁Y₁ (hYK v hvY) hvF' hgK.1
        (by rw [← hKe, hends, hc0' v₁ hv₁Y₁])
      have hgood'' : IsGoodFam K Y Z Y₁ (extC v₁ v c') (extN v₁ n') (extF v₁ g f') := by
        refine ⟨hF'', hY₁f, by rw [hY₁k, hk], fun y hy ↦ ?_⟩
        by_cases hyv : y = v₁
        · subst hyv
          rw [extC_self_zero, extN_self, extC_self_succ]
          exact ⟨hvY, (hF'.2.2.2 y hy).2⟩
        · rw [extC_of_ne hyv, extC_of_ne hyv, extN_of_ne hyv]
          refine ⟨?_, (hF'.2.2.2 y hy).2⟩
          rw [hc0' y hy]
          rcases hy with rfl | hy
          · exact absurd rfl hyv
          · exact hy.1
      have hM'' := hMu _ (hk ▸ isPathSystem_famGraph hgood'')
      have hV' : famVerts Y₁ c' n' = famVerts Y (shiftC v c) (shiftN v n) := by
        have h1 : insert v (famVerts Y₁ c' n') = insert v (famVerts Y (shiftC v c) (shiftN v n)) := by
          rw [← hV'', ← hV₁, hFV, ← famGraph_vertexSet hF'', hM'']
        rw [← insert_sdiff_self_of_notMem hvF', h1, insert_sdiff_self_of_notMem hvF₁]
      have hgF' : g ∉ famEdges Y₁ n' f' := fun h ↦ by
        have := (famGraph_edgeSet hF'.1 ▸ (famGraph_le hF'.1).edgeSet_subset) h
        rw [hK₁E] at this
        exact this.2 rfl
      have hE' : famEdges Y₁ n' f' = famEdges Y (shiftN v n) (shiftF v f) := by
        have h1 : insert g (famEdges Y₁ n' f') = insert g (famEdges Y (shiftN v n) (shiftF v f)) := by
          rw [← hE'', ← hE₁', hFE, ← famGraph_edgeSet hF'', hM'']
        rw [← insert_sdiff_self_of_notMem hgF', h1, insert_sdiff_self_of_notMem hgF₁]
      rw [← hfam']
      change subOn _ (famVerts Y₁ c' n') (famEdges Y₁ n' f') =
        subOn _ (famVerts Y (shiftC v c) (shiftN v n)) (famEdges Y (shiftN v n) (shiftF v f))
      rw [hV', hE']
    · rw [famGraph_vertexSet hF₁K₁, hK₁V, ← hMV, ← hFV, hV₁, insert_sdiff_self_of_notMem hvF₁]
  · refine ⟨g, ?_, Or.inr ⟨Y \ {v}, v, v₁, ?_, ?_, ?_, ?_, ?_⟩⟩
    · change B.edgeSet ∩ (A.edgeSet ∪ {g}) = {g}
      ext e
      simp only [mem_inter_iff, mem_union, mem_singleton_iff]
      constructor
      · rintro ⟨heB, he | rfl⟩
        · exact absurd heB (hs.notMem_edgeSet_right he)
        · rfl
      · rintro rfl; exact ⟨hgK.1.1, Or.inr rfl⟩
    · rw [hmid]
      ext x
      simp only [mem_inter_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff, Y₁]
      constructor
      · rintro ⟨hx, rfl | h⟩
        · exact absurd hx hv₁Y
        · exact h
      · intro h; exact ⟨h.1, Or.inr h⟩
    · rw [ncard_sdiff_singleton_of_mem hvY, hk]
    · have hle : B ∩ A₁ ≤ G := GM10.inter_le hB hA₁G
      have hgBA : g ∈ (B ∩ A₁).edgeSet := ⟨hgK.1.1, Or.inr rfl⟩
      rw [← hle.ends_eq g hgBA, hends]
    · exact (insert_sdiff_singleton_eq hvY).symm
    · exact hmid

end StepTwo

section StepFour

variable {G A B A' B' : Hypergraph α β} {k : ℕ}

/-- **Steps (3) and (4) of the proof of (12.1).** If no edge of `B ∩ A'` has both ends in
`V(A ∩ B)`, and no vertex of `V(A ∩ B) - V(A' ∩ B')` has exactly one edge in `B ∩ A'`, then
`B ∩ A'` has no edges. Otherwise each path that is not a single vertex has, at its first vertex, an
edge into another path (3); following these edges gives a cycle, and rerouting the paths along it
gives a second set of paths (4). -/
theorem edgeSet_eq_empty_of_no_step (hG : G.IsGraph) (hs : G.IsSeparation A B)
    (hs' : G.IsSeparation A' B') (hk : (A ∩ B).vertexSet.ncard = k)
    (hk' : (A' ∩ B').vertexSet.ncard = k)
    (hU : UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k)
    (hno : ∀ g ∈ (B ∩ A').edgeSet, ¬ (B ∩ A').ends g ⊆ (A ∩ B).vertexSet)
    (hno2 : ∀ v ∈ (A ∩ B).vertexSet, v ∉ (A' ∩ B').vertexSet →
      (incidentEdges (B ∩ A') v).ncard ≠ 1) :
    (B ∩ A').edgeSet = ∅ := by
  classical
  set Y := (A ∩ B).vertexSet with hYdef
  set Z := (A' ∩ B').vertexSet with hZdef
  set K := B ∩ A' with hKdef
  have hKG : K ≤ G := GM10.inter_le hs.right_le hs'.left_le
  by_contra hne
  obtain ⟨g₀, hg₀⟩ := nonempty_iff_ne_empty.2 hne
  obtain ⟨M, hM, hMu, hMV⟩ := hU
  have : Nonempty β := ⟨g₀⟩
  obtain ⟨x₀, -⟩ := (hG g₀ (hKG.edgeSet_subset hg₀)).1
  have : Nonempty α := ⟨x₀⟩
  have hYf : Y.Finite := (A ∩ B).vertexSet_finite
  have hZf : Z.Finite := (A' ∩ B').vertexSet_finite
  obtain ⟨c, n, f, hF, hc0, hfam⟩ := exists_goodFam_of_isPathSystem hYf (hk ▸ hM)
  have hFp := hF.1
  have hFV : famVerts Y c n = K.vertexSet := by rw [← hMV, ← hfam, famGraph_vertexSet hFp]
  have hFE : famEdges Y n f = M.edgeSet := by rw [← hfam, famGraph_edgeSet hFp]
  -- Every vertex of `Z` is the last vertex of a path.
  have hZsurj : ∀ z ∈ Z, ∃ y ∈ Y, c y (n y) = z := by
    have hinj : InjOn (fun y ↦ c y (n y)) Y := fun y hy y' hy' h ↦
      (hFp.eq_of_eq hy hy' le_rfl le_rfl h).1
    have himg : (fun y ↦ c y (n y)) '' Y = Z :=
      eq_of_subset_of_ncard_le (by rintro _ ⟨y, hy, rfl⟩; exact (hF.2.2.2 y hy).2)
        (by rw [hinj.ncard_image, hk, hk']) hZf
    intro z hz
    rw [← himg] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, hy, rfl⟩
  set S := {y ∈ Y | 1 ≤ n y} with hSdef
  -- (3): each path of `S` sends an edge from its first vertex to a later vertex of a path of `S`.
  have hnext : ∀ y ∈ S, ∃ j ∈ S, ∃ q, 1 ≤ q ∧ q ≤ n j ∧ ∃ e, e ∈ K.edgeSet ∧
      K.ends e = {c y 0, c j q} ∧ e ∉ famEdges Y n f := by
    rintro y ⟨hy, hny⟩
    have hyZ : y ∉ Z := fun hyZ ↦ by
      obtain ⟨j, hj, hjz⟩ := hZsurj y hyZ
      have := (hFp.eq_of_eq hj hy le_rfl (Nat.zero_le _) (hjz.trans (hc0 y hy).symm))
      rw [this.1] at this
      omega
    have hf0 : f y 0 ∈ incidentEdges K y := ⟨hFp.edge_mem y hy 0 hny,
      (hFp.inc_iff hy hny).2 (Or.inl (hc0 y hy).symm)⟩
    have hfin : (incidentEdges K y).Finite := K.edgeSet_finite.subset fun e he ↦ he.1
    have h1 : 1 < (incidentEdges K y).ncard := by
      have := hno2 y hy hyZ
      have := (ncard_pos hfin).2 ⟨_, hf0⟩
      omega
    obtain ⟨e, he, hef⟩ := exists_ne_of_one_lt_ncard h1 (f y 0)
    obtain ⟨u, huK, huY⟩ := not_subset.1 (hno e he.1)
    have hyu : y ≠ u := fun h ↦ huY (h ▸ hy)
    have hends : K.ends e = {y, u} := by
      have hsub : ({y, u} : Set α) ⊆ K.ends e := by rintro x (rfl | rfl); exacts [he.2, huK]
      refine (eq_of_subset_of_ncard_le hsub ?_
        (K.vertexSet_finite.subset fun x hx ↦ K.vertex_mem_of_inc hx)).symm
      rw [ncard_pair hyu, ← hKG.ends_eq e he.1]
      exact (hG e (hKG.edgeSet_subset he.1)).2
    have huV : u ∈ famVerts Y c n := hFV ▸ K.vertex_mem_of_inc huK
    obtain ⟨j, hj, q, hq, rfl⟩ := mem_famVerts.1 huV
    have hq1 : 1 ≤ q := by
      by_contra h0
      have : q = 0 := by omega
      subst this
      exact huY (by rw [hc0 j hj]; exact hj)
    refine ⟨j, ⟨hj, by omega⟩, q, hq1, hq, e, he.1, by rw [hends, hc0 y hy], fun heF ↦ ?_⟩
    obtain ⟨j', hj', b, hb, rfl⟩ := mem_famEdges.1 heF
    have hy' : c y 0 ∈ K.ends (f j' b) := by rw [hc0 y hy]; exact he.2
    rcases (hFp.inc_iff hj' hb).1 hy' with h | h
    · obtain ⟨rfl, rfl⟩ := hFp.eq_of_eq hy hj' (Nat.zero_le _) hb.le h
      exact hef rfl
    · have := (hFp.eq_of_eq hy hj' (Nat.zero_le _) hb h).2
      omega
  -- (4): there is no cycle, so `S` is empty.
  have hSe : S = ∅ := by
    by_contra hSne
    obtain ⟨y₀, hy₀⟩ := nonempty_iff_ne_empty.2 hSne
    choose! nxt hnS q hq1 hqn e he hee heF using hnext
    have hit : ∀ a, nxt^[a] y₀ ∈ S := by
      intro a
      induction a with
      | zero => exact hy₀
      | succ a ih => rw [Function.iterate_succ_apply']; exact hnS _ ih
    obtain ⟨a, b, hab, hfab⟩ := (hYf.subset fun y hy ↦ hy.1 : S.Finite).exists_lt_map_eq_of_forall_mem
      (f := fun a ↦ nxt^[a] y₀) hit
    set L := b - a with hL
    set x := nxt^[a] y₀ with hx
    have hLx : nxt^[L] x = x := by
      rw [hx, ← Function.iterate_add_apply, show L + a = b by omega]
      exact hfab.symm
    set C := {y ∈ S | nxt^[L] y = y} with hC
    have hxC : x ∈ C := ⟨hit a, hLx⟩
    have hCS : C ⊆ S := fun y hy ↦ hy.1
    have hCY : C ⊆ Y := fun y hy ↦ hy.1.1
    have hnC : ∀ y ∈ C, nxt y ∈ C := fun y hy ↦
      ⟨hnS y hy.1, by rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hy.2]⟩
    have hinjC : InjOn nxt C := by
      intro y hy y' hy' h
      have hL1 : L = (L - 1) + 1 := by omega
      rw [← hy.2, ← hy'.2, hL1, Function.iterate_succ_apply, Function.iterate_succ_apply, h]
    have hR := hFp.reroute hCY hnC hinjC (p := q) (fun y hy ↦ ⟨hq1 y hy.1, hqn y hy.1⟩)
      (e := e) (fun y hy ↦ ⟨he y hy.1, hee y hy.1⟩)
    have hgood : IsGoodFam K Y Z Y (rrC C nxt q c) (rrN C nxt q n) (rrF C nxt q e f) := by
      refine ⟨hR, hYf, rfl, fun y hy ↦ ?_⟩
      by_cases hyC : y ∈ C
      · have h1 := hq1 y hyC.1
        have h2 := hqn y hyC.1
        have hpos : n (nxt y) - q y + 1 ≠ 0 := by omega
        simp only [rrC, rrN, hyC, ite_true, hpos, ite_false]
        refine ⟨by rw [hc0 y hy]; exact hy, ?_⟩
        rw [show q y + (n (nxt y) - q y + 1) - 1 = n (nxt y) by omega]
        exact (hF.2.2.2 _ (hnS y hyC.1).1).2
      · simp only [rrC, rrN, hyC, ite_false]
        exact hF.2.2.2 y hy
    have hMR := hMu _ (hk ▸ isPathSystem_famGraph hgood)
    have hER : famEdges Y (rrN C nxt q n) (rrF C nxt q e f) = famEdges Y n f := by
      rw [← famGraph_edgeSet hR, hMR, hFE]
    have hexC : e x ∈ famEdges Y (rrN C nxt q n) (rrF C nxt q e f) := by
      refine mem_famEdges.2 ⟨x, hCY hxC, 0, ?_, ?_⟩
      · simp only [rrN, hxC, ite_true]; omega
      · simp only [rrF, hxC, ite_true]
    exact heF x hxC.1 (hER ▸ hexC)
  -- So every path is a single vertex, and `V(B ∩ A') ⊆ V(A ∩ B)`.
  have hKY : K.vertexSet ⊆ Y := by
    rw [← hFV]
    intro x hx
    obtain ⟨y, hy, a, ha, rfl⟩ := mem_famVerts.1 hx
    have hny : n y = 0 := by
      by_contra h
      have : y ∈ S := ⟨hy, by omega⟩
      rw [hSe] at this
      exact this
    obtain rfl : a = 0 := by omega
    rw [hc0 y hy]
    exact hy
  exact hno g₀ hg₀ fun x hx ↦ hKY (K.vertex_mem_of_inc hx)

end StepFour

section Main

variable {G : Hypergraph α β} {k : ℕ}

/-- The end of the induction: if `B ∩ A'` has no edges, then `(A, B) = (A', B')`. -/
theorem eq_of_edgeSet_eq_empty {A B A' B' : Hypergraph α β} (hs : G.IsSeparation A B)
    (hs' : G.IsSeparation A' B') (hAA' : A ≤ A') (hBB' : B' ≤ B)
    (hk : (A ∩ B).vertexSet.ncard = k) (hk' : (A' ∩ B').vertexSet.ncard = k)
    (hU : UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k)
    (hE : (B ∩ A').edgeSet = ∅) : A = A' ∧ B = B' := by
  obtain ⟨M, hM, -, hMV⟩ := hU
  have hME : M.edgeSet = ∅ := eq_empty_of_subset_empty (hE ▸ hM.1.1.edgeSet_subset)
  obtain ⟨hMY, hMZ⟩ := vertexSet_eq_of_edgeSet_empty hM.1 hME hM.2.1 hM.2.2 hk
    (A ∩ B).vertexSet_finite
  have hKY : (B ∩ A').vertexSet = (A ∩ B).vertexSet := hMV ▸ hMY
  have hYZ : (A ∩ B).vertexSet = (A' ∩ B').vertexSet :=
    eq_of_subset_of_ncard_le (hMY ▸ hMZ) (by rw [hk, hk']) (A' ∩ B').vertexSet_finite
  have hA := hs.left_le
  have hB := hs.right_le
  have hA' := hs'.left_le
  have hB' := hs'.right_le
  constructor
  · refine le_antisymm hAA' ((GM10.le_iff_of_le hA' hA).2 ⟨fun x hx ↦ ?_, fun e he ↦ ?_⟩)
    · have hxG := hA'.vertexSet_subset hx
      rw [← hs.vertexSet_union] at hxG
      rcases hxG with h | h
      · exact h
      · have hxK : x ∈ (B ∩ A').vertexSet := ⟨h, hx⟩
        rw [hKY] at hxK
        exact hxK.1
    · have heG := hA'.edgeSet_subset he
      rw [← hs.edgeSet_union] at heG
      rcases heG with h | h
      · exact h
      · have heK : e ∈ (B ∩ A').edgeSet := ⟨h, he⟩
        rw [hE] at heK
        exact absurd heK (notMem_empty e)
  · refine le_antisymm ((GM10.le_iff_of_le hB hB').2 ⟨fun x hx ↦ ?_, fun e he ↦ ?_⟩) hBB'
    · have hxG := hB.vertexSet_subset hx
      rw [← hs'.vertexSet_union] at hxG
      rcases hxG with h | h
      · have hxK : x ∈ (B ∩ A').vertexSet := ⟨hx, h⟩
        rw [hKY, hYZ] at hxK
        exact hxK.2
      · exact h
    · have heG := hB.edgeSet_subset he
      rw [← hs'.edgeSet_union] at heG
      rcases heG with h | h
      · have heK : e ∈ (B ∩ A').edgeSet := ⟨he, h⟩
        rw [hE] at heK
        exact absurd heK (notMem_empty e)
      · exact h

/-- **The induction of (12.1)**, on `|E(B ∩ A')|`: there is a chain of separations from `(A, B)` to
`(A', B')`. -/
theorem exists_sepChain (hG : G.IsGraph) : ∀ (N : ℕ) (A B A' B' : Hypergraph α β),
    (B ∩ A').edgeSet.ncard = N → G.IsSeparation A B → G.IsSeparation A' B' →
    (A ∩ B).vertexSet.ncard = k → (A' ∩ B').vertexSet.ncard = k → A ≤ A' → B' ≤ B →
    UniqSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k →
    ∃ (m : ℕ) (a b : ℕ → Hypergraph α β), IsSepChain G k a b m ∧ a 0 = A ∧ b 0 = B ∧
      a m = A' ∧ b m = B' := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A B A' B' hN hs hs' hk hk' hAA' hBB' hU
  by_cases hE : (B ∩ A').edgeSet = ∅
  · obtain ⟨rfl, rfl⟩ := eq_of_edgeSet_eq_empty hs hs' hAA' hBB' hk hk' hU hE
    exact ⟨0, fun _ ↦ A, fun _ ↦ B, isSepChain_single hs hk, rfl, rfl, rfl, rfl⟩
  have hstep : ∃ A₁ B₁ : Hypergraph α β, G.IsSeparation A₁ B₁ ∧ (A₁ ∩ B₁).vertexSet.ncard = k ∧
      A ≤ A₁ ∧ B₁ ≤ B ∧ A₁ ≤ A' ∧ B' ≤ B₁ ∧
      (B₁ ∩ A').edgeSet.ncard < (B ∩ A').edgeSet.ncard ∧
      UniqSystem (B₁ ∩ A') (A₁ ∩ B₁).vertexSet (A' ∩ B').vertexSet k ∧
      IsChainStep k A B A₁ B₁ := by
    by_cases h1 : ∃ g ∈ (B ∩ A').edgeSet, (B ∩ A').ends g ⊆ (A ∩ B).vertexSet
    · obtain ⟨g, hg, hgY⟩ := h1
      exact step_one hG hs hs' hAA' hBB' hk hU hg hgY
    · push Not at h1
      by_cases h2 : ∃ v ∈ (A ∩ B).vertexSet, v ∉ (A' ∩ B').vertexSet ∧
          (incidentEdges (B ∩ A') v).ncard = 1
      · obtain ⟨v, hvY, hvZ, hv1⟩ := h2
        exact step_two hG hs hs' hAA' hBB' hk hU h1 hvY hvZ hv1
      · push Not at h2
        exact absurd (edgeSet_eq_empty_of_no_step hG hs hs' hk hk' hU h1 h2) hE
  obtain ⟨A₁, B₁, hs₁, hk₁, hAA₁, hB₁B, hA₁A', hB'B₁, hlt, hU₁, hst⟩ := hstep
  obtain ⟨m, a, b, hch, ha0, hb0, ham, hbm⟩ :=
    ih _ (hN ▸ hlt) A₁ B₁ A' B' rfl hs₁ hs' hk₁ hk' hA₁A' hB'B₁ hU₁
  subst ha0 hb0
  exact ⟨m + 1, consSeq A a, consSeq B b, hch.cons hs hk hAA₁ hB₁B hst, rfl, rfl, ham, hbm⟩

section Bags

variable {m : ℕ} {a b : ℕ → Hypergraph α β} (h : IsSepChain G k a b m)
include h

theorem IsSepChain.bagUnion_ne_zero :
    bagUnion (fun t : Fin (m + 2) ↦ chainBag a b m t) (· ≠ 0) = b 0 := by
  have hV : ∀ j, (a j).vertexSet ∪ (b j).vertexSet = G.vertexSet :=
    fun j ↦ (h.sep j).vertexSet_union
  have hE : ∀ j, (a j).edgeSet ∪ (b j).edgeSet = G.edgeSet := fun j ↦ (h.sep j).edgeSet_union
  have hle : ∀ t : Fin (m + 2), t ≠ 0 → chainBag a b m t ≤ b 0 := fun t ht ↦ by
    obtain ⟨j, hj⟩ : ∃ j, t.1 = j + 1 := ⟨t.1 - 1, by
      have : t.1 ≠ 0 := fun h0 ↦ ht (Fin.ext h0)
      omega⟩
    rw [hj]
    exact (h.bag_succ_le_b (by omega)).trans (h.b_anti (Nat.zero_le _))
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.biUnion_le_of_le fun t _ ↦ h.bag_le t) (h.b_le 0) ?_ ?_
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_bagUnion_vertexSet.1 hx
      exact (hle t ht).vertexSet_subset hxt
    · intro x hx
      obtain ⟨j, hj0, hjm, hxj⟩ := h.cover_b (fun H ↦ H.vertexSet) (fun _ _ ↦ rfl) hV 0
        (Nat.zero_le _) hx
      exact mem_bagUnion_vertexSet.2 ⟨⟨j, by omega⟩, fun h0 ↦ by
        have := congrArg Fin.val h0; simp at this; omega, hxj⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_bagUnion_edgeSet.1 hx
      exact (hle t ht).edgeSet_subset hxt
    · intro x hx
      obtain ⟨j, hj0, hjm, hxj⟩ := h.cover_b (fun H ↦ H.edgeSet) (fun _ _ ↦ rfl) hE 0
        (Nat.zero_le _) hx
      exact mem_bagUnion_edgeSet.2 ⟨⟨j, by omega⟩, fun h0 ↦ by
        have := congrArg Fin.val h0; simp at this; omega, hxj⟩

theorem IsSepChain.bagUnion_ne_last :
    bagUnion (fun t : Fin (m + 2) ↦ chainBag a b m t) (· ≠ Fin.last (m + 1)) = a m := by
  have hV : ∀ j, (a j).vertexSet ∪ (b j).vertexSet = G.vertexSet :=
    fun j ↦ (h.sep j).vertexSet_union
  have hE : ∀ j, (a j).edgeSet ∪ (b j).edgeSet = G.edgeSet := fun j ↦ (h.sep j).edgeSet_union
  have hle : ∀ t : Fin (m + 2), t ≠ Fin.last (m + 1) → chainBag a b m t ≤ a m := fun t ht ↦ by
    have : t.1 ≤ m := by
      have h1 : t.1 ≠ m + 1 := fun h1 ↦ ht (Fin.ext h1)
      omega
    exact (h.bag_le_a this).trans (h.a_mono this)
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.biUnion_le_of_le fun t _ ↦ h.bag_le t) (h.a_le m) ?_ ?_
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_bagUnion_vertexSet.1 hx
      exact (hle t ht).vertexSet_subset hxt
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := h.cover_a (fun H ↦ H.vertexSet) (fun _ _ ↦ rfl) hV m le_rfl hx
      exact mem_bagUnion_vertexSet.2 ⟨⟨j, by omega⟩, fun h0 ↦ by
        have := congrArg Fin.val h0; simp at this; omega, hxj⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_bagUnion_edgeSet.1 hx
      exact (hle t ht).edgeSet_subset hxt
    · intro x hx
      obtain ⟨j, hj, hxj⟩ := h.cover_a (fun H ↦ H.edgeSet) (fun _ _ ↦ rfl) hE m le_rfl hx
      exact mem_bagUnion_edgeSet.2 ⟨⟨j, by omega⟩, fun h0 ↦ by
        have := congrArg Fin.val h0; simp at this; omega, hxj⟩

end Bags

/-- **Graph Minors XXI, (12.1).** -/
theorem theorem_12_1_proof (hG : G.IsGraph) {A B A' B' : Hypergraph α β}
    (hs : G.IsSeparation A B) (hs' : G.IsSeparation A' B') (hk : separationOrder A B = k)
    (hk' : separationOrder A' B' = k) (hAA' : A ≤ A') (hBB' : B' ≤ B)
    (hU : ∃ M, IsPathSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k M ∧
      (∀ M', IsPathSystem (B ∩ A') (A ∩ B).vertexSet (A' ∩ B').vertexSet k M' → M' = M) ∧
      M.vertexSet = (B ∩ A').vertexSet) :
    ∃ (m : ℕ) (W : Fin (m + 2) → Hypergraph α β),
      IsTreeDecomp21 G (pathGraph (m + 2)) W ∧
      (W 0 = A ∧ bagUnion W (· ≠ 0) = B ∧ bagUnion W (· ≠ Fin.last (m + 1)) = A' ∧
        W (Fin.last (m + 1)) = B') ∧
      (∀ t u, (pathGraph (m + 2)).Adj t u → (treeEdgeSet (pathGraph (m + 2)) W t u).ncard = k) ∧
      ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W t).edgeSet = {g} ∧
        ∀ u u', (pathGraph (m + 2)).Adj t u → (pathGraph (m + 2)).Adj t u' → u ≠ u' →
          (treeEdgeSet (pathGraph (m + 2)) W t u = (W t).vertexSet ∧
            treeEdgeSet (pathGraph (m + 2)) W t u' = (W t).vertexSet) ∨
          ∃ X : Set α, ∃ v v' : α,
            treeEdgeSet (pathGraph (m + 2)) W t u ∩ treeEdgeSet (pathGraph (m + 2)) W t u' = X ∧
            X.ncard = k - 1 ∧ (W t).ends g = {v, v'} ∧
            treeEdgeSet (pathGraph (m + 2)) W t u = insert v X ∧
            treeEdgeSet (pathGraph (m + 2)) W t u' = insert v' X := by
  obtain ⟨m, a, b, h, rfl, rfl, rfl, rfl⟩ :=
    exists_sepChain hG _ A B A' B' rfl hs hs' hk hk' hAA' hBB' hU
  refine ⟨m, fun t ↦ chainBag a b m t, h.isTreeDecomp21, ⟨rfl, h.bagUnion_ne_zero,
    h.bagUnion_ne_last, chainBag_last⟩, fun t u hadj ↦ by rw [h.treeEdgeSet_eq hadj]; exact h.ord _,
    fun t ht0 htl ↦ ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, t.1 = j + 1 := ⟨t.1 - 1, by
    have : t.1 ≠ 0 := fun h0 ↦ ht0 (Fin.ext h0)
    omega⟩
  have hjm : j < m := by
    have h1 : t.1 ≠ m + 1 := fun h1 ↦ htl (Fin.ext h1)
    have := t.2
    omega
  obtain ⟨g, hg, hcase⟩ := h.step j hjm
  have hWt : chainBag a b m t = b j ∩ a (j + 1) := by rw [hj, chainBag_succ_of_lt hjm]
  refine ⟨g, by simp only; rw [hWt, hg], fun u u' hu hu' huu' ↦ ?_⟩
  simp only
  rw [h.treeEdgeSet_eq hu, h.treeEdgeSet_eq hu', hWt]
  -- The two neighbours of `t` are `j` and `j + 2`.
  have hnb : ∀ w : Fin (m + 2), (pathGraph (m + 2)).Adj t w → w.1 = j ∨ w.1 = j + 2 := by
    intro w hw
    rcases pathGraph_adj.1 hw with h' | h' <;> omega
  rcases hnb u hu with hu1 | hu1 <;> rcases hnb u' hu' with hu2 | hu2
  · exact absurd (Fin.ext (hu1.trans hu2.symm)) huu'
  · rw [show min t.1 u.1 = j by omega, show min t.1 u'.1 = j + 1 by omega]
    rcases hcase with ⟨h1, h2⟩ | ⟨X, v, v', hX, hXc, he, h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨X, v, v', hX, hXc, he, h1, h2⟩
  · rw [show min t.1 u.1 = j + 1 by omega, show min t.1 u'.1 = j by omega]
    rcases hcase with ⟨h1, h2⟩ | ⟨X, v, v', hX, hXc, he, h1, h2⟩
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨X, v', v, by rw [Set.inter_comm]; exact hX, hXc, by rw [he, pair_comm],
        h2, h1⟩
  · exact absurd (Fin.ext (hu1.trans hu2.symm)) huu'

end Main

end GM21
end GraphMinor
