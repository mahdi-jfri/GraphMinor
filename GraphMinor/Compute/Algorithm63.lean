module

public import GraphMinor.Compute.Restrict

/-!
# Graph Minors XIII, Algorithm (6.3) on the Word RAM

This file formalizes Algorithm (6.3) from Robertson and Seymour, *Graph Minors XIII. The Disjoint
Paths Problem* (pages 85–86):

> (6.3) Algorithm.
> *Input:* An integer $k > 0$ and a non-null simple graph $G$ with $|E(G)| \ge k |V(G)|$.
> *Output:* A subset $X \subseteq V(G)$ such that
> (i) the restriction of $G$ to $X$ is non-null and connected,
> (ii) $N(X)$ is non-null, and
> (iii) every vertex of $N(X)$ has $\ge k$ neighbours in $N(X)$.
> *Running time:* $O(v\varepsilon)$.

We follow the paper's steps (1)–(4) and prove the step (2) recursion invariant:
at step $i$, $|X_i| = i$, $X_i$ meets at most $|N(X_i)| + k(i - 1)$ edges, and the restriction to
$X_i$ is connected.

The core CSR subroutine `alg63CsrProg` is proved in a general form over any simple graph
`H' : SimpleGraph (Fin n)` possessing a non-empty adjacency-closed vertex set `U` with
`|edgesInSet H' U| ≥ k |U|`, so that Algorithm (6.4) can invoke `alg63CsrProg` directly on the
restricted graph `restrictGraph H Y_i` in Step (3) of (6.4).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Pure Combinatorial Lemmas for Steps (1)–(4) of (6.3) -/

/-- If `U` is closed under `H'`-adjacency and `v ∈ U`, then `reachSet H' v ⊆ U`. -/
theorem reachSet_subset_of_adj_closed {n : ℕ} {H' : SimpleGraph (Fin n)} {U : Finset (Fin n)}
    (hclosed : ∀ x ∈ U, ∀ y, H'.Adj x y → y ∈ U) {v : Fin n} (hv : v ∈ U) :
    reachSet H' v ⊆ U := by
  intro w hw
  rw [mem_reachSet] at hw
  obtain ⟨p⟩ := hw
  induction p with
  | nil => exact hv
  | @cons a b c hadj _ ih =>
    exact ih (hclosed a hv b hadj)

/-- For any vertex `v`, `reachSet H' v` is closed under `H'`-adjacency. -/
theorem reachSet_adj_closed {n : ℕ} (H' : SimpleGraph (Fin n)) (v : Fin n) :
    ∀ x ∈ reachSet H' v, ∀ y, H'.Adj x y → y ∈ reachSet H' v := by
  intro x hx y hadj
  rw [mem_reachSet] at hx ⊢
  exact hx.trans hadj.reachable

/-- If both `U` and `C` are closed under `H'`-adjacency, then `U \ C` is also closed under
`H'`-adjacency. -/
theorem sdiff_adj_closed {n : ℕ} {H' : SimpleGraph (Fin n)} {U C : Finset (Fin n)}
    (hU : ∀ x ∈ U, ∀ y, H'.Adj x y → y ∈ U)
    (hC : ∀ x ∈ C, ∀ y, H'.Adj x y → y ∈ C) :
    ∀ x ∈ U \ C, ∀ y, H'.Adj x y → y ∈ U \ C := by
  intro x hx y hadj
  rw [Finset.mem_sdiff] at hx ⊢
  refine ⟨hU x hx.1 y hadj, fun hyC => hx.2 (hC y hyC x hadj.symm)⟩

/-- If `C ⊆ U` and `C` is closed under `H'`-adjacency, no edge of `H'` crosses between `C` and
`U \ C`, so `edgesInSet H' U` partitions into `edgesInSet H' C` and `edgesInSet H' (U \ C)`. -/
theorem card_edgesInSet_split_of_adj_closed {n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    {U C : Finset (Fin n)} (hCU : C ⊆ U)
    (hC : ∀ x ∈ C, ∀ y, H'.Adj x y → y ∈ C) :
    (edgesInSet H' U).card = (edgesInSet H' C).card + (edgesInSet H' (U \ C)).card := by
  have hunion : edgesInSet H' U = edgesInSet H' C ∪ edgesInSet H' (U \ C) := by
    ext e
    induction e using Sym2.ind with
    | _ x y =>
      rw [ Finset.mem_union, mem_edgesInSet, mem_edgesInSet, mem_edgesInSet, mem_edgeFinset]
      simp only [mem_edgeSet, Sym2.mem_iff, forall_eq_or_imp, forall_eq, Finset.mem_sdiff]
      constructor
      · rintro ⟨hadj, hxU, hyU⟩
        by_cases hxC : x ∈ C
        · exact Or.inl ⟨hadj, hxC, hC x hxC y hadj⟩
        · have hyC : y ∉ C := fun hy => hxC (hC y hy x hadj.symm)
          exact Or.inr ⟨hadj, ⟨hxU, hxC⟩, ⟨hyU, hyC⟩⟩
      · rintro (⟨hadj, hxC, hyC⟩ | ⟨hadj, ⟨hxU, _⟩, ⟨hyU, _⟩⟩)
        · exact ⟨hadj, hCU hxC, hCU hyC⟩
        · exact ⟨hadj, hxU, hyU⟩
  have hdisj : Disjoint (edgesInSet H' C) (edgesInSet H' (U \ C)) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgesInSet] at he₁ he₂
      have hxC : x ∈ C := he₁.2 x (Sym2.mem_mk_left x y)
      have hx_not : x ∈ U \ C := he₂.2 x (Sym2.mem_mk_left x y)
      exact (Finset.mem_sdiff.mp hx_not).2 hxC
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- Step (1) of Algorithm (6.3): in any simple graph `H'` and non-empty adjacency-closed vertex set
`U` with `|edgesInSet H' U| ≥ k |U|` (`k > 0`), there exists a vertex `v₁ ∈ U` whose connected
component `C = reachSet H' v₁` satisfies `C ⊆ U` and `|edgesInSet H' C| ≥ k |C|`. -/
theorem exists_heavy_reachSet {n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    {k : ℕ} (_hk : 0 < k) {U : Finset (Fin n)} :
    U.Nonempty →
    (∀ x ∈ U, ∀ y, H'.Adj x y → y ∈ U) →
    k * U.card ≤ (edgesInSet H' U).card →
    ∃ v₁ ∈ U, k * (reachSet H' v₁).card ≤ (edgesInSet H' (reachSet H' v₁)).card := by
  induction U using Finset.strongInduction with
  | H U ih =>
    intro hne hU hedges
    rcases hne with ⟨u, huU⟩
    let C := reachSet H' u
    have hCU : C ⊆ U := reachSet_subset_of_adj_closed hU huU
    have hC_closed : ∀ x ∈ C, ∀ y, H'.Adj x y → y ∈ C := reachSet_adj_closed H' u
    by_cases hheavy : k * C.card ≤ (edgesInSet H' C).card
    · exact ⟨u, huU, hheavy⟩
    · have hcard_split : (U \ C).card + C.card = U.card :=
        Finset.card_sdiff_add_card_eq_card hCU
      have hedges_split := card_edgesInSet_split_of_adj_closed H' hCU hC_closed
      have hmul_split : k * U.card = k * C.card + k * (U \ C).card := by
        rw [← hcard_split, Nat.mul_add, Nat.add_comm]
      have hrem_edges : k * (U \ C).card < (edgesInSet H' (U \ C)).card := by omega
      have hrem_pos : 0 < (edgesInSet H' (U \ C)).card := by omega
      have hrem_nonempty : (U \ C).Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        have h0 : edgesInSet H' (∅ : Finset (Fin n)) = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          induction e using Sym2.ind with
          | _ x y =>
            rw [mem_edgesInSet] at he
            exact Finset.notMem_empty x (he.2 x (Sym2.mem_mk_left x y))
        rw [hempty, h0, Finset.card_empty] at hrem_pos
        omega
      have huC : u ∈ C := (mem_reachSet H' u u).mpr Reachable.rfl
      have hssub : U \ C ⊂ U := by
        rw [Finset.ssubset_iff_of_subset Finset.sdiff_subset]
        exact ⟨u, huU, fun hu_sdiff => (Finset.mem_sdiff.mp hu_sdiff).2 huC⟩
      rcases ih (U \ C) hssub hrem_nonempty (sdiff_adj_closed hU hC_closed) (by omega) with
        ⟨v₁, hv₁_sdiff, hv₁_heavy⟩
      exact ⟨v₁, (Finset.mem_sdiff.mp hv₁_sdiff).1, hv₁_heavy⟩

/-- If `X ⊆ reachSet H' v₁`, then `extNeighborhood H' X ⊆ reachSet H' v₁`. -/
theorem extNeighborhood_subset_reachSet {n : ℕ} {H' : SimpleGraph (Fin n)} {v₁ : Fin n}
    {X : Finset (Fin n)} (hX : X ⊆ reachSet H' v₁) :
    extNeighborhood H' X ⊆ reachSet H' v₁ := by
  intro w hw
  rcases (mem_extNeighborhood H' X w).mp hw with ⟨_, u, huX, hadj⟩
  exact reachSet_adj_closed H' v₁ u (hX huX) w hadj

/-- Step (2) recursion invariant of Algorithm (6.3):
at step `i`, `v₁ ∈ X`, `X ⊆ reachSet H' v₁`, `|X| = i`, `X` meets at most `|N(X)| + k(i - 1)`
edges of `H'`, and the induced subgraph `H'.induce X` is connected. -/
def Alg63Step2Inv {n : ℕ} (H' : SimpleGraph (Fin n)) (v₁ : Fin n) (k i : ℕ)
    (X : Finset (Fin n)) : Prop :=
  v₁ ∈ X ∧
  X ⊆ reachSet H' v₁ ∧
  X.card = i ∧
  (edgesMetBy H' X).card ≤ (extNeighborhood H' X).card + k * (i - 1) ∧
  (H'.induce (X : Set (Fin n))).Connected

/-- Base case `i = 1` of the Step (2) invariant for `X₁ = {v₁}`. -/
theorem alg63Step2Inv_singleton {n : ℕ} (H' : SimpleGraph (Fin n)) (v₁ : Fin n) (k : ℕ) :
    Alg63Step2Inv H' v₁ k 1 {v₁} := by
  refine ⟨Finset.mem_singleton_self v₁, ?_, Finset.card_singleton v₁, ?_,
    connected_induce_singleton H' v₁⟩
  · intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact (mem_reachSet H' u u).mpr Reachable.rfl
  · rw [card_edgesMetBy_singleton H' v₁]
    omega

/-- Inductive step (Step (3)) of the Step (2) invariant when adding `v ∈ extNeighborhood H' X`
with `degInto H' (extNeighborhood H' X) v < k`. -/
theorem alg63Step2Inv_insert {n : ℕ} {H' : SimpleGraph (Fin n)} {v₁ : Fin n} {k i : ℕ}
    {X : Finset (Fin n)} {v : Fin n}
    (hinv : Alg63Step2Inv H' v₁ k i X)
    (hv : v ∈ extNeighborhood H' X)
    (hdeg : degInto H' (extNeighborhood H' X) v < k) :
    Alg63Step2Inv H' v₁ k (i + 1) (insert v X) := by
  rcases hinv with ⟨hv₁X, hsub, hcard, hmet, hconn⟩
  have hv_not_X : v ∉ X := (mem_extNeighborhood H' X v).mp hv |>.1
  have hi_pos : 1 ≤ i := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨v₁, hv₁X⟩
  have hv_reach : v ∈ reachSet H' v₁ := extNeighborhood_subset_reachSet hsub hv
  refine ⟨Finset.mem_insert_of_mem hv₁X,
    Finset.insert_subset_iff.mpr ⟨hv_reach, hsub⟩,
    by rw [Finset.card_insert_of_notMem hv_not_X, hcard],
    by simpa using card_edgesMetBy_insert_le H' X hi_pos hmet hv hdeg,
    connected_induce_insert_of_mem_extNeighborhood hconn hv⟩

/-- In Step (4) of Algorithm (6.3), if `extNeighborhood H' X = ∅` while `v₁ ∈ X` and
`X ⊆ reachSet H' v₁`, then `X = reachSet H' v₁`. -/
theorem eq_reachSet_of_extNeighborhood_empty {n : ℕ} (H' : SimpleGraph (Fin n))
    {v₁ : Fin n} {X : Finset (Fin n)}
    (hv₁X : v₁ ∈ X) (hsub : X ⊆ reachSet H' v₁)
    (hempty : extNeighborhood H' X = ∅) :
    X = reachSet H' v₁ := by
  apply Finset.Subset.antisymm hsub
  have hwalk : ∀ {u w : Fin n}, H'.Walk u w → u ∈ X → w ∈ X := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons a b c hadj _ ih =>
      intro haX
      have hbX : b ∈ X := by
        by_contra hb_not_X
        have hbN : b ∈ extNeighborhood H' X :=
          (mem_extNeighborhood H' X b).mpr ⟨hb_not_X, a, haX, hadj⟩
        rw [hempty] at hbN
        exact Finset.notMem_empty b hbN
      exact ih hbX
  intro w hw
  rw [mem_reachSet] at hw
  obtain ⟨p⟩ := hw
  exact hwalk p hv₁X

theorem edgesInSet_subset_edgesMetBy {n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (X : Finset (Fin n)) :
    edgesInSet H' X ⊆ edgesMetBy H' X := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgesInSet] at he
    rw [mem_edgesMetBy]
    exact ⟨he.1, u, he.2 u (Sym2.mem_mk_left u v), Sym2.mem_mk_left u v⟩

/-- Step (4) of Algorithm (6.3): under the Step (2) invariant on a heavy component
`reachSet H' v₁` with `|edgesInSet H' (reachSet H' v₁)| ≥ k |reachSet H' v₁|` (`k > 0`),
`extNeighborhood H' X` is guaranteed to be non-empty. -/
theorem alg63_step4_extNeighborhood_nonempty {n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    {v₁ : Fin n} {k i : ℕ} {X : Finset (Fin n)}
    (hk : 0 < k)
    (hheavy : k * (reachSet H' v₁).card ≤ (edgesInSet H' (reachSet H' v₁)).card)
    (hinv : Alg63Step2Inv H' v₁ k i X) :
    (extNeighborhood H' X).Nonempty := by
  rcases hinv with ⟨hv₁X, hsub, hcard, hmet, _⟩
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hX_eq : X = reachSet H' v₁ := eq_reachSet_of_extNeighborhood_empty H' hv₁X hsub hempty
  have hi_pos : 1 ≤ i := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨v₁, hv₁X⟩
  have hedges_le : (edgesInSet H' (reachSet H' v₁)).card ≤ (edgesMetBy H' X).card := by
    rw [← hX_eq]
    exact Finset.card_le_card (edgesInSet_subset_edgesMetBy H' X)
  have hN_zero : (extNeighborhood H' X).card = 0 := by rw [hempty, Finset.card_empty]
  have hreach_card : (reachSet H' v₁).card = i := by rw [← hX_eq, hcard]
  have hk_reach : k * (reachSet H' v₁).card = k * i := by rw [hreach_card]
  have hmul : k * i = k * (i - 1) + k := by
    have : i = (i - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ### Section 2: Word RAM Implementation of Steps (1)–(4) (`alg63CsrProg`) -/

/-- Step (1) per-vertex body:
1. Runs `bfsRegProg` from `r_3 = u` on `(6, 7, 8)` into visited array `12` using queue `13`.
2. Counts `r_5 := |reachSet H' u|` via `cardBitSetProg`.
3. Runs `restrictGraphProg` on `(6, 7, 8)` and bitset `12` into scratch CSR `(14, 15, 16)`,
   setting `r_6 := 2 * |edgesInSet H' (reachSet H' u)|`.
4. Computes `r_7 := 2 * (r_2 * r_5)` and if `¬ (r_6 < r_7)` sets `r_4 := r_3`. -/
def alg63Step1Body : Cmd :=
  .seq (bfsRegProg 0 3 6 7 8 12 13 14 15 16 9 10 11 12)
    (.seq (cardBitSetProg 12 (.reg 0) 5 8)
      (.seq (restrictGraphProg 6 7 8 12 14 15 16 0 1 8 12 6 9 10 11 13)
        (.seq (.assign 7 (.op .mul (.const 2) (.op .mul (.reg 2) (.reg 5))))
          (.ite (.op .lt (.reg 6) (.reg 7))
            .skip
            (.assign 4 (.reg 3))))))

/-- Step (1) of Algorithm (6.3): initializes `r_4 := r_0` (`n`), `r_3 := 0`, and loops `r_3` up to
`r_0` to find `v₁` in `r_4` with `|edgesInSet H' (reachSet H' v₁)| ≥ k |reachSet H' v₁|`. -/
def alg63Step1Prog : Cmd :=
  .seq (.assign 4 (.reg 0))
    (.seq (.assign 3 (.const 0))
      (forUp 3 (.reg 0) alg63Step1Body))

/-- Steps (3)–(4) per-iteration body:
1. Computes `degInto H' (extNeighborhood H' X)` for all vertices into array `11`.
2. Scans for a vertex `r_4 ∈ extNeighborhood H' X` with `degInto < r_2`.
3. If `r_4 < r_0`, expands `(a_X = 9, a_N = 10)` by `r_4`. -/
def alg63Step3Body : Cmd :=
  .seq (computeDegIntoProg 6 7 8 10 11 0 8 9 10 11 12 6)
    (.seq (findLowDegVertexProg 10 11 0 2 8 12 13 4)
      (.ite (.op .lt (.reg 4) (.reg 0))
        (expandNeighborhoodProg 6 7 8 9 10 4 9 10 11 12)
        .skip))

/-- Full CSR subroutine for Algorithm (6.3) following Steps (1)–(4):
- Input CSR graph `H'` in arrays `(6, 7, 8)`.
- Input registers: `r_0 = n`, `r_1 = cap`, `r_2 = k`.
- Output bit-arrays: `a_X = 9` (the connected set `X`) and `a_N = 10` (`extNeighborhood H' X`). -/
def alg63CsrProg : Cmd :=
  .seq alg63Step1Prog
    (.seq (initSingletonNeighborhoodProg 6 7 8 9 10 0 4 9 10 11 12)
      (.seq (.assign 3 (.const 0))
        (forUp 3 (.reg 0) alg63Step3Body)))

theorem isBitSet_reachSet_of_bfs {n : ℕ} (H' : SimpleGraph (Fin n)) (u : Fin n)
    {a_vis : Arr} {s : State}
    (hvis : s.arrs a_vis =
      (open Classical in List.ofFn (fun v : Fin n => if H'.Reachable u v then 1 else 0))) :
    IsBitSet (reachSet H' u) a_vis s := by
  have hbit : s.arrs a_vis = bitSetList (reachSet H' u) := by
    rw [hvis]
    unfold bitSetList
    congr 1
    ext v
    by_cases h : H'.Reachable u v
    · have hm : v ∈ reachSet H' u := (mem_reachSet H' u v).mpr h
      simp [h, hm]
    · have hm : v ∉ reachSet H' u := fun hm => h ((mem_reachSet H' u v).mp hm)
      simp [h, hm]
  exact IsBitSet.of_bitSetList (reachSet H' u) a_vis s hbit

theorem alg63Step1Body_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (u : Fin n) (cap k : ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (h2kn_w : 2 * (k * n) < 2 ^ w)
    (hcap_bound : 2 * H'.edgeFinset.card ≤ cap)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr1 : s.regs 1 = cap)
    (hr2 : s.regs 2 = k)
    (hr3 : s.regs 3 = u.1) :
    ∃ s' t,
      Exec w alg63Step1Body s s' t ∧
      t ≤ 70 + 68 * n + cap + 51 * totalAdjEntries lists ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 1 = cap ∧
      s'.regs 2 = k ∧
      s'.regs 3 = u.1 ∧
      (s'.regs 4 = if k * (reachSet H' u).card ≤ (edgesInSet H' (reachSet H' u)).card
        then u.1 else s.regs 4) ∧
      (∀ a : ℕ, a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 4 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by
    have hu_lt : u.1 < n := u.2
    have : 1 ≤ n := by omega
    have : k * 1 ≤ k * n := Nat.mul_le_mul_left k this
    omega
  -- 1. Run bfsRegProg 0 3 6 7 8 12 13 14 15 16 9 10 11 12
  rcases Triple.bfsRegProg_spec (w := w) H' lists u 0 3 6 7 8 12 13 14 15 16 9 10 11 12
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w s ⟨hr0, hr3, hadj, hent_w⟩ with
    ⟨s₁, t₁, hex₁, ht₁, hvis₁⟩
  dsimp only at ht₁
  have harr₁ : ∀ a : ℕ, a ≠ 12 → a ≠ 13 → s₁.arrs a = s.arrs a := by
    intro a ha12 ha13
    apply Exec.arrs_eq_of_not_mem_writtenArrs hex₁
    simp [bfsRegProg, bfsStepProg, queueInit, queuePush, queuePop, bfsLoopProg, forList, forUp,
      Cmd.writtenArrs, ha12, ha13]
  have hreg₁ : ∀ r : ℕ, r ≠ 14 → r ≠ 15 → r ≠ 16 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 12 →
      s₁.regs r = s.regs r := by
    intro r h14 h15 h16 h9 h10 h11 h12
    apply Exec.regs_eq_of_not_mem_writtenRegs hex₁
    simp [bfsRegProg, bfsStepProg, queueInit, queuePush, queuePop, bfsLoopProg, forList, forUp,
      Cmd.writtenRegs, h14, h15, h16, h9, h10, h11, h12]
  have hbit₁ : IsBitSet (reachSet H' u) 12 s₁ := isBitSet_reachSet_of_bfs H' u hvis₁
  have hr0_1 : s₁.regs 0 = n := by rw [hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
  -- 2. Run cardBitSetProg 12 (.reg 0) 5 8
  rcases cardBitSetProg_exec (reachSet H' u) 12 0 5 8
      (by decide) (by decide) (by decide)
      hw hn_w hbit₁ hr0_1 with
    ⟨s₂, t₂, hex₂, ht₂, hcard₂, harr₂, hreg₂⟩
  have hbit₂ : IsBitSet (reachSet H' u) 12 s₂ := hbit₁.of_arr_eq (harr₂ 12)
  have hadj₂ : IsAdjList H' 6 7 8 lists s₂ :=
    hadj.of_arrs_eq
      (by rw [harr₂ 6, harr₁ 6 (by decide) (by decide)])
      (by rw [harr₂ 7, harr₁ 7 (by decide) (by decide)])
      (by rw [harr₂ 8, harr₁ 8 (by decide) (by decide)])
  have hent₂ : (s₂.arrs 8).length < 2 ^ w := by
    rw [harr₂ 8, harr₁ 8 (by decide) (by decide)]; exact hent_w
  have hr0_2 : s₂.regs 0 = n := by rw [hreg₂ 0 (by decide) (by decide), hr0_1]
  have hr1_2 : s₂.regs 1 = cap := by
    rw [hreg₂ 1 (by decide) (by decide),
      hreg₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1]
  have hcap_sub : 2 * (edgesInSet H' (reachSet H' u)).card ≤ cap := by
    have := card_edgesInSet_le_card_edgeFinset H' (reachSet H' u)
    omega
  -- 3. Run restrictGraphProg 6 7 8 12 14 15 16 0 1 8 12 6 9 10 11 13
  rcases restrictGraphProg_exec H' lists (reachSet H' u) cap
      6 7 8 12 14 15 16 0 1 8 12 6 9 10 11 13
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w hcap_w hcap_sub
      hadj₂ hent₂ hbit₂ hr0_2 hr1_2 with
    ⟨s₃, t₃, hex₃, ht₃, _, _, hrcnt₃, harr₃, hreg₃⟩
  -- 4. r_7 := 2 * (r_2 * r_5) (cost 6)
  have hr2_3 : s₃.regs 2 = k := by
    rw [hreg₃ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₂ 2 (by decide) (by decide),
      hreg₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr2]
  have hr3_3 : s₃.regs 3 = u.1 := by
    rw [hreg₃ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₂ 3 (by decide) (by decide),
      hreg₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr3]
  have hr4_3 : s₃.regs 4 = s.regs 4 := by
    rw [hreg₃ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₂ 4 (by decide) (by decide),
      hreg₁ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have hr5_3 : s₃.regs 5 = (reachSet H' u).card := by
    rw [hreg₃ 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hcard₂]
  have hcard_le_n : (reachSet H' u).card ≤ n := by
    have := Finset.card_le_univ (reachSet H' u)
    simpa using this
  have hcard_w : (reachSet H' u).card < 2 ^ w := by omega
  have hkc_le : k * (reachSet H' u).card ≤ k * n := Nat.mul_le_mul_left k hcard_le_n
  have hkc_w : k * (reachSet H' u).card < 2 ^ w := by omega
  have h2kc_w : 2 * (k * (reachSet H' u).card) < 2 ^ w := by omega
  have hrcnt_w : 2 * (edgesInSet H' (reachSet H' u)).card < 2 ^ w := by omega
  let s₄ := s₃.setReg 7 (2 * (k * (reachSet H' u).card))
  have hex₄ : Exec w (.assign 7 (.op .mul (.const 2) (.op .mul (.reg 2) (.reg 5)))) s₃ s₄ 6 :=
    .assign (by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hr2_3, hr5_3,
        hk_w, hcard_w, hkc_w, h2kc_w])
  -- 5. ite (r_6 < r_7) .skip (r_4 := r_3)
  by_cases hheavy : k * (reachSet H' u).card ≤ (edgesInSet H' (reachSet H' u)).card
  · have hnot_lt : ¬ (2 * (edgesInSet H' (reachSet H' u)).card < 2 * (k * (reachSet H' u).card)) := by omega
    have hcond0 : (Expr.op .lt (.reg 6) (.reg 7)).eval w s₄ = some 0 := by
      simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcnt₃, hrcnt_w, h2kc_w, hnot_lt, h0_w]
    have hu_w : u.1 < 2 ^ w := by omega
    let s₅ := s₄.setReg 4 u.1
    have hex_set : Exec w (.assign 4 (.reg 3)) s₄ s₅ 2 :=
      .assign (by simp [s₄, Expr.eval, checkWord, hr3_3, hu_w])
    have hex₅ : Exec w (.ite (.op .lt (.reg 6) (.reg 7)) .skip (.assign 4 (.reg 3))) s₄ s₅ (3 + 2) :=
      .ite_false hcond0 hex_set
    have harr₅ : ∀ a : ℕ, a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s₅.arrs a = s.arrs a := by
      intro a h12 h13 h14 h15 h16
      simp only [s₅, s₄, State.setReg_arrs]
      rw [harr₃ a h14 h15 h16, harr₂ a, harr₁ a h12 h13]
    refine ⟨s₅, t₁ + (t₂ + (t₃ + (6 + (3 + 2)))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega,
      hadj.of_arrs_eq
        (harr₅ 6 (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₅ 7 (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₅ 8 (by decide) (by decide) (by decide) (by decide) (by decide)),
      by rw [harr₅ 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hent_w,
      by simp [s₅, s₄, State.setReg, hreg₃ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0_2],
      by simp [s₅, s₄, State.setReg, hreg₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1_2],
      by simp [s₅, s₄, State.setReg, hr2_3],
      by simp [s₅, s₄, State.setReg, hr3_3],
      by simp [s₅, hheavy],
      harr₅,
      fun r hr => by
        simp only [s₅, s₄, State.setReg,
          Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 4),
          Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 7)]
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by omega) (by omega),
          hreg₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)],
      fun r hr => by
        simp only [s₅, s₄, State.setReg,
          Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 4),
          Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 7)]
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by omega) (by omega),
          hreg₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]⟩
  · have hlt : 2 * (edgesInSet H' (reachSet H' u)).card < 2 * (k * (reachSet H' u).card) := by omega
    have hcond1 : (Expr.op .lt (.reg 6) (.reg 7)).eval w s₄ = some 1 := by
      simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcnt₃, hrcnt_w, h2kc_w, hlt, hw]
    have hex₅ : Exec w (.ite (.op .lt (.reg 6) (.reg 7)) .skip (.assign 4 (.reg 3))) s₄ s₄ (3 + 1) :=
      .ite_true hcond1 one_ne_zero (.skip s₄)
    have harr₄ : ∀ a : ℕ, a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s₄.arrs a = s.arrs a := by
      intro a h12 h13 h14 h15 h16
      simp only [s₄, State.setReg_arrs]
      rw [harr₃ a h14 h15 h16, harr₂ a, harr₁ a h12 h13]
    refine ⟨s₄, t₁ + (t₂ + (t₃ + (6 + (3 + 1)))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), by omega,
      hadj.of_arrs_eq
        (harr₄ 6 (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₄ 7 (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₄ 8 (by decide) (by decide) (by decide) (by decide) (by decide)),
      by rw [harr₄ 8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hent_w,
      by simp [s₄, State.setReg, hreg₃ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0_2],
      by simp [s₄, State.setReg, hreg₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1_2],
      by simp [s₄, State.setReg, hr2_3],
      by simp [s₄, State.setReg, hr3_3],
      by simp [s₄, State.setReg, hr4_3, hheavy],
      harr₄,
      fun r hr => by
        simp only [s₄, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 7)]
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by omega) (by omega),
          hreg₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)],
      fun r hr => by
        simp only [s₄, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 7)]
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by omega) (by omega),
          hreg₁ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]⟩

theorem alg63Step1Loop_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (cap k : ℕ)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (h2kn_w : 2 * (k * n) < 2 ^ w)
    (hcap_bound : 2 * H'.edgeFinset.card ≤ cap)
    (rem idx : ℕ) (hrem : idx + rem = n) {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr1 : s.regs 1 = cap)
    (hr2 : s.regs 2 = k)
    (hr3 : s.regs 3 = idx)
    (hf_le : s.regs 4 ≤ n)
    (hf_sound : ∀ h : s.regs 4 < n,
      k * (reachSet H' ⟨s.regs 4, h⟩).card ≤ (edgesInSet H' (reachSet H' ⟨s.regs 4, h⟩)).card)
    (hf_comp : s.regs 4 = n → ∀ v : Fin n, v.1 < idx →
      (edgesInSet H' (reachSet H' v)).card < k * (reachSet H' v).card) :
    ∃ s' t,
      Exec w (forUp 3 (.reg 0) alg63Step1Body) s s' t ∧
      t ≤ 3 + rem * (77 + 68 * n + cap + 51 * totalAdjEntries lists) ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 1 = cap ∧
      s'.regs 2 = k ∧
      s'.regs 4 ≤ n ∧
      (∀ h : s'.regs 4 < n,
        k * (reachSet H' ⟨s'.regs 4, h⟩).card ≤ (edgesInSet H' (reachSet H' ⟨s'.regs 4, h⟩)).card) ∧
      (s'.regs 4 = n → ∀ v : Fin n,
        (edgesInSet H' (reachSet H' v)).card < k * (reachSet H' v).card) ∧
      (∀ a : ℕ, a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing idx s with
  | zero =>
    have hidx_eq : idx = n := by omega
    rw [hidx_eq] at hr3 hf_comp
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hadj, hent_w, hr0, hr1, hr2,
      hf_le, hf_sound, fun h v => hf_comp h v v.2,
      fun _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hidx_lt : idx < n := by omega
    have hidx_w : idx < 2 ^ w := by omega
    let uFin : Fin n := ⟨idx, hidx_lt⟩
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hidx_w, hn_w, hidx_lt, hw]
    rcases alg63Step1Body_exec H' lists uFin cap k hw2 hn_w hcap_w h2kn_w hcap_bound
        hadj hent_w hr0 hr1 hr2 hr3 with
      ⟨s₁, t₁, hex₁, ht₁, hadj₁, hent₁, hr0_1, hr1_1, hr2_1, hr3_1, hr4_1, harr₁, hreg_lt₁, hreg_ge₁⟩
    let s₂ := s₁.setReg 3 (idx + 1)
    have hex_inc : Exec w (.assign 3 (.op .add (.reg 3) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, uFin, hidx_w, hw,
          show idx + 1 < 2 ^ w by omega])
    have hr4_2 : s₂.regs 4 = s₁.regs 4 := by simp [s₂, State.setReg]
    have hf_le₂ : s₂.regs 4 ≤ n := by
      rw [hr4_2, hr4_1]
      split_ifs <;> [exact le_of_lt hidx_lt; exact hf_le]
    have hf_sound₂ : ∀ h : s₂.regs 4 < n,
        k * (reachSet H' ⟨s₂.regs 4, h⟩).card ≤ (edgesInSet H' (reachSet H' ⟨s₂.regs 4, h⟩)).card := by
      intro h
      by_cases hheavy : k * (reachSet H' uFin).card ≤ (edgesInSet H' (reachSet H' uFin)).card
      · have hval : s₂.regs 4 = idx := by simp [hr4_2, hr4_1, hheavy, uFin]
        have hfin : (⟨s₂.regs 4, h⟩ : Fin n) = uFin := Fin.ext hval
        simpa [hfin] using hheavy
      · have hval : s₂.regs 4 = s.regs 4 := by simp [hr4_2, hr4_1, hheavy]
        have h' : s.regs 4 < n := hval ▸ h
        have hfin : (⟨s₂.regs 4, h⟩ : Fin n) = ⟨s.regs 4, h'⟩ := Fin.ext hval
        simpa [hfin] using hf_sound h'
    have hf_comp₂ : s₂.regs 4 = n → ∀ v : Fin n, v.1 < idx + 1 →
        (edgesInSet H' (reachSet H' v)).card < k * (reachSet H' v).card := by
      intro h v hv_lt
      by_cases hheavy : k * (reachSet H' uFin).card ≤ (edgesInSet H' (reachSet H' uFin)).card
      · simp [hr4_2, hr4_1, hheavy, uFin] at h
        omega
      · simp [hr4_2, hr4_1, hheavy] at h
        by_cases hveq : v.1 = idx
        · have hv_eq : v = uFin := Fin.ext hveq
          subst hv_eq
          omega
        · exact hf_comp h v (by omega)
    rcases ih (idx + 1) (by omega) (s := s₂)
        (hadj₁.of_arrs_eq rfl rfl rfl) hent₁
        (by simp [s₂, State.setReg, hr0_1])
        (by simp [s₂, State.setReg, hr1_1])
        (by simp [s₂, State.setReg, hr2_1])
        (by simp [s₂])
        hf_le₂ hf_sound₂ hf_comp₂ with
      ⟨s₃, t₃, hex₃, ht₃, hadj₃, hent₃, hr0_3, hr1_3, hr2_3, hf_le₃, hf_sound₃, hf_comp₃,
        harr₃, hreg_lt₃, hreg_ge₃⟩
    have hmul : (rem + 1) * (77 + 68 * n + cap + 51 * totalAdjEntries lists) =
        (77 + 68 * n + cap + 51 * totalAdjEntries lists) +
          rem * (77 + 68 * n + cap + 51 * totalAdjEntries lists) := by
      rw [Nat.add_comm rem 1, Nat.add_mul, Nat.one_mul]
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hadj₃, hent₃, hr0_3, hr1_3, hr2_3, hf_le₃, hf_sound₃, hf_comp₃,
      fun a h12 h13 h14 h15 h16 => by rw [harr₃ a h12 h13 h14 h15 h16]; exact harr₁ a h12 h13 h14 h15 h16,
      fun r hr => by
        rw [hreg_lt₃ r hr]
        simp only [s₂, State.setReg, Function.update_of_ne (by omega : r ≠ 3)]
        exact hreg_lt₁ r (by omega),
      fun r hr => by
        rw [hreg_ge₃ r hr]
        simp only [s₂, State.setReg, Function.update_of_ne (by omega : r ≠ 3)]
        exact hreg_ge₁ r hr⟩

/-- Step (1) specification: given `U.Nonempty` closed under `H'`-adjacency with
`|edgesInSet H' U| ≥ k |U|` (`k > 0`), `alg63Step1Prog` finds a vertex `v₁ : Fin n` in `r_4` such
that `|edgesInSet H' (reachSet H' v₁)| ≥ k |reachSet H' v₁|` and `reachSet H' v₁ ⊆ U`. -/
theorem alg63Step1Prog_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (U : Finset (Fin n)) (cap k : ℕ)
    (hk : 0 < k)
    (hU_ne : U.Nonempty)
    (hU_closed : ∀ x ∈ U, ∀ y, H'.Adj x y → y ∈ U)
    (hU_edges : k * U.card ≤ (edgesInSet H' U).card)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (h2kn_w : 2 * (k * n) < 2 ^ w)
    (hcap_bound : 2 * H'.edgeFinset.card ≤ cap)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr1 : s.regs 1 = cap)
    (hr2 : s.regs 2 = k) :
    ∃ (s' : State) (t : ℕ) (v₁ : Fin n),
      Exec w alg63Step1Prog s s' t ∧
      t ≤ 7 + n * (77 + 68 * n + cap + 51 * totalAdjEntries lists) ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 1 = cap ∧
      s'.regs 2 = k ∧
      s'.regs 4 = v₁.1 ∧
      k * (reachSet H' v₁).card ≤ (edgesInSet H' (reachSet H' v₁)).card ∧
      (∀ a : ℕ, a ≠ 12 → a ≠ 13 → a ≠ 14 → a ≠ 15 → a ≠ 16 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 4 n
  have hex₁ : Exec w (.assign 4 (.reg 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr0, hn_w])
  let s₂ := s₁.setReg 3 0
  have hex₂ : Exec w (.assign 3 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg63Step1Loop_exec H' lists cap k hw2 hn_w hcap_w h2kn_w hcap_bound
      n 0 (by omega) (s := s₂)
      (hadj.of_arrs_eq rfl rfl rfl) hent_w
      (by simp [s₂, s₁, State.setReg, hr0])
      (by simp [s₂, s₁, State.setReg, hr1])
      (by simp [s₂, s₁, State.setReg, hr2])
      (by simp [s₂])
      (by simp [s₂, s₁, State.setReg])
      (fun h => by simp [s₂, s₁, State.setReg] at h)
      (fun _ _ hv => by omega) with
    ⟨s₃, t₃, hex₃, ht₃, hadj₃, hent₃, hr0_3, hr1_3, hr2_3, hf_le₃, hf_sound₃, hf_comp₃,
      harr₃, hreg_lt₃, hreg_ge₃⟩
  have hr4_lt : s₃.regs 4 < n := by
    by_contra hge
    have heq : s₃.regs 4 = n := by omega
    rcases exists_heavy_reachSet H' hk hU_ne hU_closed hU_edges with ⟨v₀, _, hv₀_heavy⟩
    have hlt := hf_comp₃ heq v₀
    omega
  let v₁ : Fin n := ⟨s₃.regs 4, hr4_lt⟩
  refine ⟨s₃, 2 + (2 + t₃), v₁, .seq hex₁ (.seq hex₂ hex₃), by omega,
    hadj₃, hent₃, hr0_3, hr1_3, hr2_3, rfl, hf_sound₃ hr4_lt,
    harr₃,
    fun r hr => by
      rw [hreg_lt₃ r hr]
      simp [s₂, s₁, State.setReg, Function.update_of_ne (by omega : r ≠ 3),
        Function.update_of_ne (by omega : r ≠ 4)],
    fun r hr => by
      rw [hreg_ge₃ r hr]
      simp [s₂, s₁, State.setReg, Function.update_of_ne (by omega : r ≠ 3),
        Function.update_of_ne (by omega : r ≠ 4)]⟩

theorem alg63Step3Body_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (v₁ : Fin n) (k i step : ℕ) (X : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hk_w : k < 2 ^ w)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = k)
    (hr3 : s.regs 3 = step)
    (hX : IsBitSet X 9 s)
    (hN : IsBitSet (extNeighborhood H' X) 10 s)
    (hinv : Alg63Step2Inv H' v₁ k i X)
    (hprog : step < i ∨ ∀ u ∈ extNeighborhood H' X, k ≤ degInto H' (extNeighborhood H' X) u) :
    ∃ (s' : State) (t i' : ℕ) (X' : Finset (Fin n)),
      Exec w alg63Step3Body s s' t ∧
      t ≤ 35 + 61 * n + 19 * totalAdjEntries lists ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 2 = k ∧
      s'.regs 3 = step ∧
      IsBitSet X' 9 s' ∧
      IsBitSet (extNeighborhood H' X') 10 s' ∧
      Alg63Step2Inv H' v₁ k i' X' ∧
      (step + 1 < i' ∨ ∀ u ∈ extNeighborhood H' X', k ≤ degInto H' (extNeighborhood H' X') u) ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. computeDegIntoProg 6 7 8 10 11 0 8 9 10 11 12 6
  rcases computeDegIntoProg_exec H' lists (extNeighborhood H' X)
      6 7 8 10 11 0 8 9 10 11 12 6
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hadj hent_w hN hr0 with
    ⟨s₁, t₁, hex₁, ht₁, hdeg₁, harr₁, hreg₁⟩
  have hN₁ : IsBitSet (extNeighborhood H' X) 10 s₁ := hN.of_arr_eq (harr₁ 10 (by decide))
  have hr0_1 : s₁.regs 0 = n := by
    rw [hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr0]
  have hr2_1 : s₁.regs 2 = k := by
    rw [hreg₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr2]
  -- 2. findLowDegVertexProg 10 11 0 2 8 12 13 4
  rcases findLowDegVertexProg_exec H' (extNeighborhood H' X)
      10 11 0 2 8 12 13 4
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hk_w hN₁ hdeg₁ hr0_1 hr2_1 with
    ⟨s₂, t₂, hex₂, ht₂, hf_le₂, hf_sound₂, hf_comp₂, harr₂, hreg₂⟩
  have hr0_2 : s₂.regs 0 = n := by
    rw [hreg₂ 0 (by decide) (by decide) (by decide) (by decide), hr0_1]
  have hr2_2 : s₂.regs 2 = k := by
    rw [hreg₂ 2 (by decide) (by decide) (by decide) (by decide), hr2_1]
  have hr3_2 : s₂.regs 3 = step := by
    rw [hreg₂ 3 (by decide) (by decide) (by decide) (by decide),
      hreg₁ 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr3]
  have hadj₂ : IsAdjList H' 6 7 8 lists s₂ :=
    hadj.of_arrs_eq
      (by rw [harr₂ 6, harr₁ 6 (by decide)])
      (by rw [harr₂ 7, harr₁ 7 (by decide)])
      (by rw [harr₂ 8, harr₁ 8 (by decide)])
  have hent₂ : (s₂.arrs 8).length < 2 ^ w := by
    rw [harr₂ 8, harr₁ 8 (by decide)]; exact hent_w
  have hX₂ : IsBitSet X 9 s₂ :=
    hX.of_arr_eq (by rw [harr₂ 9, harr₁ 9 (by decide)])
  have hN₂ : IsBitSet (extNeighborhood H' X) 10 s₂ :=
    hN₁.of_arr_eq (harr₂ 10)
  -- 3. Branch on r_4 < r_0
  by_cases hfound : s₂.regs 4 < n
  · have hf_w : s₂.regs 4 < 2 ^ w := by omega
    have hcond1 : (Expr.op .lt (.reg 4) (.reg 0)).eval w s₂ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_2, hf_w, hn_w, hfound, hw]
    let v : Fin n := ⟨s₂.regs 4, hfound⟩
    obtain ⟨hv_in_N, hv_deg_lt⟩ := hf_sound₂ v rfl
    have hstep_lt_i : step < i := by
      rcases hprog with hlt | hall
      · exact hlt
      · have := hall v hv_in_N
        omega
    rcases expandNeighborhoodProg_exec H' lists X v
        6 7 8 9 10 4 9 10 11 12
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        hw hn_w hv_in_N hadj₂ hent₂ hX₂ hN₂ rfl with
      ⟨s₃, t₃, hex₃, ht₃, hX₃, hN₃, harr₃, hreg₃⟩
    have hex_ite : Exec w
        (.ite (.op .lt (.reg 4) (.reg 0))
          (expandNeighborhoodProg 6 7 8 9 10 4 9 10 11 12)
          .skip)
        s₂ s₃ (3 + t₃) :=
      .ite_true hcond1 one_ne_zero hex₃
    have hlen_le : (lists v).length ≤ n := (hadj.2 v).2.2.1
    have ht₃_le : t₃ ≤ 15 + 18 * n := by
      have : 18 * (lists v).length ≤ 18 * n := Nat.mul_le_mul_left 18 hlen_le
      omega
    have harr_all : ∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s₃.arrs a = s.arrs a := by
      intro a h9 h10 h11
      rw [harr₃ a h9 h10, harr₂ a, harr₁ a h11]
    refine ⟨s₃, t₁ + (t₂ + (3 + t₃)), i + 1, insert v X,
      .seq hex₁ (.seq hex₂ hex_ite), by omega,
      hadj.of_arrs_eq
        (harr_all 6 (by decide) (by decide) (by decide))
        (harr_all 7 (by decide) (by decide) (by decide))
        (harr_all 8 (by decide) (by decide) (by decide)),
      by rw [harr_all 8 (by decide) (by decide) (by decide)]; exact hent_w,
      by rw [hreg₃ 0 (by decide) (by decide) (by decide) (by decide), hr0_2],
      by rw [hreg₃ 2 (by decide) (by decide) (by decide) (by decide), hr2_2],
      by rw [hreg₃ 3 (by decide) (by decide) (by decide) (by decide), hr3_2],
      hX₃, hN₃,
      alg63Step2Inv_insert hinv hv_in_N hv_deg_lt,
      Or.inl (by omega),
      harr_all,
      fun r hr => by
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)],
      fun r hr => by
        rw [hreg₃ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]⟩
  · have hf_eq_n : s₂.regs 4 = n := by omega
    have hcond0 : (Expr.op .lt (.reg 4) (.reg 0)).eval w s₂ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr0_2, hf_eq_n, hn_w, h0_w]
    have hex_ite : Exec w
        (.ite (.op .lt (.reg 4) (.reg 0))
          (expandNeighborhoodProg 6 7 8 9 10 4 9 10 11 12)
          .skip)
        s₂ s₂ (3 + 1) :=
      .ite_false hcond0 (.skip s₂)
    have harr_all : ∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s₂.arrs a = s.arrs a := by
      intro a _ _ h11
      rw [harr₂ a, harr₁ a h11]
    refine ⟨s₂, t₁ + (t₂ + (3 + 1)), i, X,
      .seq hex₁ (.seq hex₂ hex_ite), by omega,
      hadj₂, hent₂, hr0_2, hr2_2, hr3_2, hX₂, hN₂, hinv,
      Or.inr (hf_comp₂ hf_eq_n),
      harr_all,
      fun r hr => by
        rw [hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)],
      fun r hr => by
        rw [hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
          hreg₁ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)
            (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega)]⟩

theorem alg63Step3Loop_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (v₁ : Fin n) (k : ℕ)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hk_w : k < 2 ^ w)
    (rem step i : ℕ) (hrem : step + rem = n) (X : Finset (Fin n)) {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr2 : s.regs 2 = k)
    (hr3 : s.regs 3 = step)
    (hX : IsBitSet X 9 s)
    (hN : IsBitSet (extNeighborhood H' X) 10 s)
    (hinv : Alg63Step2Inv H' v₁ k i X)
    (hprog : step < i ∨ ∀ u ∈ extNeighborhood H' X, k ≤ degInto H' (extNeighborhood H' X) u) :
    ∃ (s' : State) (t i' : ℕ) (X' : Finset (Fin n)),
      Exec w (forUp 3 (.reg 0) alg63Step3Body) s s' t ∧
      t ≤ 3 + rem * (42 + 61 * n + 19 * totalAdjEntries lists) ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 2 = k ∧
      IsBitSet X' 9 s' ∧
      IsBitSet (extNeighborhood H' X') 10 s' ∧
      Alg63Step2Inv H' v₁ k i' X' ∧
      (∀ u ∈ extNeighborhood H' X', k ≤ degInto H' (extNeighborhood H' X') u) ∧
      (∀ a : ℕ, a ≠ 9 → a ≠ 10 → a ≠ 11 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing step i X s with
  | zero =>
    have hstep_eq : step = n := by omega
    rw [hstep_eq] at hr3 hprog
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hn_w, h0_w]
    have hall : ∀ u ∈ extNeighborhood H' X, k ≤ degInto H' (extNeighborhood H' X) u := by
      rcases hprog with hlt | hall
      · exfalso
        have hcard_le : X.card ≤ n := by
          have := Finset.card_le_univ X
          simpa using this
        have hcard_eq : X.card = i := hinv.2.2.1
        omega
      · exact hall
    refine ⟨s, 3, i, X, .while_false hcond, by omega, hadj, hent_w, hr0, hr2, hX, hN, hinv, hall,
      fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ rem ih =>
    have hstep_lt : step < n := by omega
    have hstep_w : step < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 3) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr0, hstep_w, hn_w, hstep_lt, hw]
    rcases alg63Step3Body_exec H' lists v₁ k i step X hw hn_w hk_w
        hadj hent_w hr0 hr2 hr3 hX hN hinv hprog with
      ⟨s₁, t₁, i₁, X₁, hex₁, ht₁, hadj₁, hent₁, hr0_1, hr2_1, hr3_1, hX₁, hN₁,
        hinv₁, hprog₁, harr₁, hreg_lt₁, hreg_ge₁⟩
    let s₂ := s₁.setReg 3 (step + 1)
    have hex_inc : Exec w (.assign 3 (.op .add (.reg 3) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hstep_w, hw,
          show step + 1 < 2 ^ w by omega])
    rcases ih (step + 1) i₁ (by omega) X₁ (s := s₂)
        (hadj₁.of_arrs_eq rfl rfl rfl) hent₁
        (by simp [s₂, State.setReg, hr0_1])
        (by simp [s₂, State.setReg, hr2_1])
        (by simp [s₂])
        (hX₁.of_arr_eq rfl) (hN₁.of_arr_eq rfl) hinv₁ hprog₁ with
      ⟨s₃, t₃, i₃, X₃, hex₃, ht₃, hadj₃, hent₃, hr0_3, hr2_3, hX₃, hN₃, hinv₃, hall₃,
        harr₃, hreg_lt₃, hreg_ge₃⟩
    have hmul : (rem + 1) * (42 + 61 * n + 19 * totalAdjEntries lists) =
        (42 + 61 * n + 19 * totalAdjEntries lists) +
          rem * (42 + 61 * n + 19 * totalAdjEntries lists) := by
      rw [Nat.add_comm rem 1, Nat.add_mul, Nat.one_mul]
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, i₃, X₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃, by omega,
      hadj₃, hent₃, hr0_3, hr2_3, hX₃, hN₃, hinv₃, hall₃,
      fun a h9 h10 h11 => by
        rw [harr₃ a h9 h10 h11]
        simp only [s₂, State.setReg_arrs]
        exact harr₁ a h9 h10 h11,
      fun r hr => by
        rw [hreg_lt₃ r hr]
        simp only [s₂, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 3)]
        exact hreg_lt₁ r hr,
      fun r hr => by
        rw [hreg_ge₃ r hr]
        simp only [s₂, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 3)]
        exact hreg_ge₁ r hr⟩

/-- Main CSR specification for Algorithm (6.3):
Given `H' : SimpleGraph (Fin n)` stored in CSR arrays `(6, 7, 8)` with `s.regs 0 = n`,
`s.regs 1 = cap` (`2 * H'.edgeFinset.card ≤ cap`), `s.regs 2 = k` (`0 < k`), and a non-empty
adjacency-closed subset `U ⊆ Finset.univ` satisfying `k * U.card ≤ (edgesInSet H' U).card`,
`alg63CsrProg` runs in `O(n(n + cap + totalAdjEntries lists))` steps and computes a subset
`X : Finset (Fin n)` (stored in `a_X = 9`) and `extNeighborhood H' X` (stored in `a_N = 10`)
satisfying conditions (i), (ii), (iii) of GM XIII (6.3). -/
theorem alg63CsrProg_exec {w n : ℕ} (H' : SimpleGraph (Fin n)) [DecidableRel H'.Adj]
    (lists : Fin n → List ℕ) (U : Finset (Fin n)) (cap k : ℕ)
    (hk : 0 < k)
    (hU_ne : U.Nonempty)
    (hU_closed : ∀ x ∈ U, ∀ y, H'.Adj x y → y ∈ U)
    (hU_edges : k * U.card ≤ (edgesInSet H' U).card)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (h2kn_w : 2 * (k * n) < 2 ^ w)
    (hcap_bound : 2 * H'.edgeFinset.card ≤ cap)
    {s : State}
    (hadj : IsAdjList H' 6 7 8 lists s)
    (hent_w : (s.arrs 8).length < 2 ^ w)
    (hr0 : s.regs 0 = n)
    (hr1 : s.regs 1 = cap)
    (hr2 : s.regs 2 = k) :
    ∃ (s' : State) (t : ℕ) (v₁ : Fin n) (i : ℕ) (X : Finset (Fin n)),
      Exec w alg63CsrProg s s' t ∧
      t ≤ 29 + 20 * n + n * (119 + 129 * n + cap + 70 * totalAdjEntries lists) ∧
      IsAdjList H' 6 7 8 lists s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      s'.regs 0 = n ∧
      s'.regs 1 = cap ∧
      s'.regs 2 = k ∧
      IsBitSet X 9 s' ∧
      IsBitSet (extNeighborhood H' X) 10 s' ∧
      k * (reachSet H' v₁).card ≤ (edgesInSet H' (reachSet H' v₁)).card ∧
      Alg63Step2Inv H' v₁ k i X ∧
      X.Nonempty ∧
      (H'.induce (X : Set (Fin n))).Connected ∧
      (extNeighborhood H' X).Nonempty ∧
      (∀ u ∈ extNeighborhood H' X, k ≤ degInto H' (extNeighborhood H' X) u) ∧
      (∀ a : ℕ, (a < 9 ∨ 17 ≤ a) → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 3 → s'.regs r = s.regs r) ∧
      (∀ r : ℕ, 17 ≤ r → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  rcases hU_ne with ⟨u₀, hu₀⟩
  have hu₀_lt : u₀.1 < n := u₀.2
  have hn_pos : 1 ≤ n := by omega
  have hk_w : k < 2 ^ w := by
    have : k * 1 ≤ k * n := Nat.mul_le_mul_left k hn_pos
    omega
  -- Step (1): alg63Step1Prog
  rcases alg63Step1Prog_exec H' lists U cap k hk ⟨u₀, hu₀⟩ hU_closed hU_edges
      hw2 hn_w hcap_w h2kn_w hcap_bound hadj hent_w hr0 hr1 hr2 with
    ⟨s₁, t₁, v₁, hex₁, ht₁, hadj₁, hent₁, hr0_1, hr1_1, hr2_1, hr4_1, hheavy₁,
      harr₁, hreg_lt₁, hreg_ge₁⟩
  -- Step (2): initSingletonNeighborhoodProg 6 7 8 9 10 0 4 9 10 11 12
  rcases initSingletonNeighborhoodProg_exec H' lists v₁
      6 7 8 9 10 0 4 9 10 11 12
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w hadj₁ hent₁ hr0_1 hr4_1 with
    ⟨s₂, t₂, hex₂, ht₂, hX₂, hN₂, harr₂, hreg₂⟩
  have hlen_v₁ : (lists v₁).length ≤ n := (hadj.2 v₁).2.2.1
  have ht₂_le : t₂ ≤ 17 + 20 * n := by
    have : 18 * (lists v₁).length ≤ 18 * n := Nat.mul_le_mul_left 18 hlen_v₁
    omega
  -- Step (3)–(4): r_3 := 0; forUp 3 (.reg 0) alg63Step3Body
  let s₃ := s₂.setReg 3 0
  have hex₃ : Exec w (.assign 3 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hadj₃ : IsAdjList H' 6 7 8 lists s₃ :=
    hadj₁.of_arrs_eq
      (by simp [s₃, harr₂ 6 (by decide) (by decide)])
      (by simp [s₃, harr₂ 7 (by decide) (by decide)])
      (by simp [s₃, harr₂ 8 (by decide) (by decide)])
  have hent₃ : (s₃.arrs 8).length < 2 ^ w := by
    simp [s₃, harr₂ 8 (by decide) (by decide), hent₁]
  have hr0_3 : s₃.regs 0 = n := by
    simp [s₃, State.setReg, hreg₂ 0 (by decide) (by decide) (by decide) (by decide), hr0_1]
  have hr2_3 : s₃.regs 2 = k := by
    simp [s₃, State.setReg, hreg₂ 2 (by decide) (by decide) (by decide) (by decide), hr2_1]
  rcases alg63Step3Loop_exec H' lists v₁ k hw hn_w hk_w
      n 0 1 (by omega) {v₁} (s := s₃)
      hadj₃ hent₃ hr0_3 hr2_3 (by simp [s₃])
      (hX₂.of_arr_eq rfl) (hN₂.of_arr_eq rfl)
      (alg63Step2Inv_singleton H' v₁ k) (Or.inl (by omega)) with
    ⟨s₄, t₄, i₄, X₄, hex₄, ht₄, hadj₄, hent₄, hr0_4, hr2_4, hX₄, hN₄, hinv₄, hall₄,
      harr₄, hreg_lt₄, hreg_ge₄⟩
  have hmul_combine :
      n * (77 + 68 * n + cap + 51 * totalAdjEntries lists) +
        n * (42 + 61 * n + 19 * totalAdjEntries lists) =
        n * (119 + 129 * n + cap + 70 * totalAdjEntries lists) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have hN_nonempty : (extNeighborhood H' X₄).Nonempty :=
    alg63_step4_extNeighborhood_nonempty H' hk hheavy₁ hinv₄
  refine ⟨s₄, t₁ + (t₂ + (2 + t₄)), v₁, i₄, X₄,
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    hadj₄, hent₄, hr0_4,
    by
      rw [hreg_lt₄ 1 (by decide)]
      simp [s₃, State.setReg, hreg₂ 1 (by decide) (by decide) (by decide) (by decide), hr1_1],
    hr2_4, hX₄, hN₄, hheavy₁, hinv₄,
    ⟨v₁, hinv₄.1⟩, hinv₄.2.2.2.2, hN_nonempty, hall₄,
    fun a ha => by
      rw [harr₄ a (by omega) (by omega) (by omega)]
      simp only [s₃, State.setReg_arrs]
      rw [harr₂ a (by dsimp [Arr]; omega) (by dsimp [Arr]; omega),
        harr₁ a (by omega) (by omega) (by omega) (by omega) (by omega)],
    fun r hr => by
      rw [hreg_lt₄ r hr]
      simp only [s₃, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 3)]
      rw [hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
        hreg_lt₁ r hr],
    fun r hr => by
      rw [hreg_ge₄ r hr]
      simp only [s₃, State.setReg, Function.update_of_ne (by dsimp [Reg]; omega : (r : Reg) ≠ 3)]
      rw [hreg₂ r (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega) (by dsimp [Reg]; omega),
        hreg_ge₁ r hr]⟩

/-! ### Section 3: End-to-End `gm13_algorithm_6_3` (`ComputesArrRelInTime`) -/

/-- Valid problem input for GM XIII (6.3): a non-null simple graph `G : SimpleGraph (Fin n)` with
`k > 0` and `|E(G)| ≥ k |V(G)|`. -/
structure Alg63Input where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- Degree threshold parameter `k`. -/
  k : ℕ
  /-- `k > 0`. -/
  hk : 0 < k
  /-- `G` is non-null (`n > 0`). -/
  hn : 0 < n
  /-- Edge-density hypothesis `|E(G)| ≥ k |V(G)|`. -/
  hedges : k * n ≤ G.edgeFinset.card

attribute [instance] Alg63Input.decAdj

/-- Problem size for GM XIII (6.3): `v * ε = x.n * x.G.edgeFinset.card`.
Since `x.n ≥ 1`, `x.k ≥ 1`, and `x.G.edgeFinset.card ≥ x.k * x.n ≥ x.n ≥ 1`, both `x.n` and
`x.G.edgeFinset.card` are bounded by `alg63Size x`, and `O(vε)` time is linear in `alg63Size x`. -/
def alg63Size (x : Alg63Input) : ℕ :=
  x.n * x.G.edgeFinset.card

/-- Flat input encoding of an `Alg63Input` instance `(G, k)` in `inArr`:
`[n, m, u_0, v_0, ..., u_{m-1}, v_{m-1}, k]`. -/
def encAlg63In (x : Alg63Input) : List ℕ :=
  encGraph x.G ++ [x.k]

/-- Decoder from the 0/1 indicator list in `outArr` to a vertex subset `Finset (Fin n)`. -/
def decAlg63Out (n : ℕ) (out : List ℕ) : Finset (Fin n) :=
  finsetOfBitList n out

/-- Output specification for GM XIII (6.3), matching conditions (i), (ii), (iii) on page 85:
(i) the restriction of `G` to `X` is non-null (`X.Nonempty`) and connected,
(ii) `N(X)` is non-null (`(extNeighborhood G X).Nonempty`), and
(iii) every vertex of `N(X)` has `≥ k` neighbors in `N(X)`. -/
def IsAlg63Output (x : Alg63Input) (X : Finset (Fin x.n)) : Prop :=
  X.Nonempty ∧
  (x.G.induce (X : Set (Fin x.n))).Connected ∧
  (extNeighborhood x.G X).Nonempty ∧
  ∀ u ∈ extNeighborhood x.G X, x.k ≤ degInto x.G (extNeighborhood x.G X) u

/-- Fixed end-to-end Word RAM program for GM XIII (6.3):
1. Parses `G` from `inArr = 0` into CSR arrays `(6, 7, 8)` using degree array `2` and registers `0..6`
   (`r_0 := n`, `r_1 := m`).
2. Reads `k` from `inArr[2 + 2 * r_1]` into `r_2`.
3. Sets `r_1 := 2 * r_1` (`cap = 2 * m`).
4. Runs `alg63CsrProg`, placing the output bitset `X` in array `9`.
5. Copies array `9[0..n)` to `outArr = 1` via `readSliceProg`. -/
def alg63EndToEndProg : Cmd :=
  .seq (parseGraphProg 2 6 7 8 0)
    (.seq (.assign 2 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))))
      (.seq (.assign 1 (.op .mul (.const 2) (.reg 1)))
        (.seq alg63CsrProg
          (readSliceProg 9 (.const 0) outArr (.reg 0) 3))))

/-- End-to-end `O(vε)` complexity theorem for GM XIII Algorithm (6.3) (`alg63EndToEndProg`):
from any initial state whose `inArr` holds `encAlg63In x`, `alg63EndToEndProg` terminates in at
most `C * (alg63Size x + 1)` steps (where `alg63Size x = x.n * x.G.edgeFinset.card = vε`) and
leaves a bit array in `outArr` decoding via `decAlg63Out x.n` to a subset `X ⊆ V(G)` satisfying
`IsAlg63Output x X`. -/
theorem gm13_algorithm_6_3 :
    ComputesArrRelInTime alg63Size encAlg63In
      (fun x out => IsAlg63Output x (decAlg63Out x.n out)) alg63EndToEndProg (fun s => s + 1) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  refine ⟨600, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let edges := edgeListOf x.G
  have hedges_list : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
  have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
  have htot_eq : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length :=
    totalAdjEntries_edgeNeighbors edges hedges_list.1
  let w := wordSize 2 (alg63Size x)
  have hw_bound : 2 * (alg63Size x + 2) < 2 ^ w :=
    two_mul_lt_two_pow_wordSize (c := 2) (n := alg63Size x) (by omega)
  have hn_pos : 1 ≤ x.n := x.hn
  have hk_pos : 1 ≤ x.k := x.hk
  have hm_ge_kn : x.k * x.n ≤ edges.length := by rw [hm_eq]; exact x.hedges
  have hm_ge_n : x.n ≤ edges.length := by
    have : 1 * x.n ≤ x.k * x.n := Nat.mul_le_mul_right x.n hk_pos
    omega
  have hm_pos : 1 ≤ edges.length := by omega
  have hsize_eq : alg63Size x = x.n * edges.length := by simp [alg63Size, hm_eq]
  have hn_le_size : x.n ≤ alg63Size x := by
    rw [hsize_eq]
    have : x.n * 1 ≤ x.n * edges.length := Nat.mul_le_mul_left x.n hm_pos
    omega
  have hm_le_size : edges.length ≤ alg63Size x := by
    rw [hsize_eq]
    have : 1 * edges.length ≤ x.n * edges.length := Nat.mul_le_mul_right edges.length hn_pos
    omega
  have hnn_le_size : x.n * x.n ≤ alg63Size x := by
    rw [hsize_eq]
    exact Nat.mul_le_mul_left x.n hm_ge_n
  have hkn_le_size : x.k * x.n ≤ alg63Size x := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have h2kn_w : 2 * (x.k * x.n) < 2 ^ w := by omega
  have hk_w : x.k < 2 ^ w := by
    have : x.k * 1 ≤ x.k * x.n := Nat.mul_le_mul_left x.k hn_pos
    omega
  have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges ++ [x.k] := by
    simpa [encAlg63In, encGraph, edges] using hs₀
  -- 1. parseGraphProg 2 6 7 8 0
  rcases Triple.parseGraphProg_spec (w := w) x.G edges [x.k] 2 6 7 8 0 hedges_list
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s₀ hin₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0_1, hr1_1, hadj₁, hent₁, _⟩
  dsimp only at ht₁
  -- 2. r_2 := inArr[2 + 2 * r_1]
  obtain ⟨hlen_k, hget_k⟩ := inArr_getElem_after_edges edges x.k hin₁
  have heval_k :
      (Expr.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))).eval w s₁ =
        some x.k := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_1, hw2, hm_w, h2m_w, hm2_w,
      hlen_k, hget_k, hk_w]
  let s₂ := s₁.setReg 2 x.k
  have hex₂ :
      Exec w (.assign 2 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))))
        s₁ s₂ 7 := .assign heval_k
  -- 3. r_1 := 2 * r_1
  let s₃ := s₂.setReg 1 (2 * edges.length)
  have hex₃ : Exec w (.assign 1 (.op .mul (.const 2) (.reg 1))) s₂ s₃ 4 :=
    .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_1, hw2, hm_w, h2m_w])
  -- 4. alg63CsrProg
  have hadj₃ : IsAdjList x.G 6 7 8 (edgeNeighbors edges) s₃ :=
    hadj₁.of_arrs_eq rfl rfl rfl
  have hent₃_w : (s₃.arrs 8).length < 2 ^ w := by
    simp [s₃, s₂, hent₁, h2m_w]
  have hU_ne : (Finset.univ : Finset (Fin x.n)).Nonempty := ⟨⟨0, x.hn⟩, Finset.mem_univ _⟩
  have hU_edges : x.k * (Finset.univ : Finset (Fin x.n)).card ≤
      (edgesInSet x.G Finset.univ).card := by
    rw [Finset.card_univ, Fintype.card_fin, edgesInSet_univ]
    exact x.hedges
  rcases alg63CsrProg_exec (w := w) x.G (edgeNeighbors edges) Finset.univ (2 * edges.length) x.k
      x.hk hU_ne (fun _ _ _ _ => Finset.mem_univ _) hU_edges
      hw2 hn_w h2m_w h2kn_w (by omega)
      (s := s₃) hadj₃ hent₃_w
      (by simp [s₃, s₂, State.setReg, hr0_1])
      (by simp [s₃])
      (by simp [s₃, s₂, State.setReg]) with
    ⟨s₄, t₄, _, _, X, hex₄, ht₄, _, _, hr0_4, _, _, hX₄, _, _, _,
      hX_ne, hX_conn, hN_ne, hN_deg, _, _, _⟩
  -- 5. readSliceProg 9 (.const 0) outArr (.reg 0) 3
  have harr9_eq : s₄.arrs 9 = bitSetList X := hX₄.arr_eq_bitSetList
  have hmid_w : ∀ b ∈ bitSetList X, b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one X idx hidx
    omega
  rcases readSliceProg_exec 9 outArr (.const 0) 0 3
      (by decide) (by decide)
      [] (bitSetList X) []
      rfl (length_bitSetList X) hmid_w
      hw (by simpa using hn_w)
      (s := s₄)
      (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
      (by simp [harr9_eq])
      hr0_4 with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, _, _⟩
  dsimp [Expr.cost] at ht₅
  have hdec_eq : decAlg63Out x.n (s₅.arrs outArr) = X := by
    rw [hout₅]
    unfold decAlg63Out
    exact finsetOfBitList_bitSetList X
  rw [htot_eq] at ht₄
  have hmul_bound :
      x.n * (119 + 129 * x.n + 2 * edges.length + 70 * (2 * edges.length)) =
        119 * x.n + 129 * (x.n * x.n) + 142 * alg63Size x := by
    rw [hsize_eq]
    have h1 : 119 + 129 * x.n + 2 * edges.length + 70 * (2 * edges.length) =
        119 + 129 * x.n + 142 * edges.length := by omega
    rw [h1, Nat.mul_add, Nat.mul_add]
    have h2 : x.n * 119 = 119 * x.n := Nat.mul_comm _ _
    have h3 : x.n * (129 * x.n) = 129 * (x.n * x.n) := Nat.mul_left_comm _ _ _
    have h4 : x.n * (142 * edges.length) = 142 * (x.n * edges.length) := Nat.mul_left_comm _ _ _
    omega
  refine ⟨s₅, t₁ + (7 + (4 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by dsimp only; omega, ?_⟩
  dsimp only
  rw [hdec_eq]
  exact ⟨hX_ne, hX_conn, hN_ne, hN_deg⟩

end GraphMinor.Compute
