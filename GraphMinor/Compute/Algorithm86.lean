module

public import GraphMinor.Compute.Algorithm86Aux5

/-!
# GM XIII Algorithm (8.6): Finding a Cross or a Rural Division in a Society

This file proves the correctness of `alg86DivisionsProg` and `alg86Prog` for GM XIII
Algorithm (8.6) (pages 96–97), with a pure-reader output decoder `decAlg86Out` that only reads
`outArr`.

  "(8.6) Algorithm.
  *Input:* A society $(G, \Omega)$.
  *Output:* Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$.
  *Running time:* $O(\nu\varepsilon)$.
  *Description:* First we use (8.1) to find a cross if there is one. If not, we use (8.3) to find
  a 4-linked core $C$. Let $\mathcal{A}'$ be the set of all subgraphs $A$ of $G$ such that either
  (i) $A$ consists of an edge of $G$ with both ends in $V(C)$, and its ends, or
  (ii) $A$ consists of a component of $G \setminus V(C)$, together with all edges of $G$ between
  this component and $V(C)$, and their ends, or
  (iii) $A$ consists of a vertex $v \in \tilde{\Omega}$ incident with no edges of $G$.
  We compute $\mathcal{A}'$. Finally, say $A_1, A_2 \in \mathcal{A}'$ are *equivalent* if
  $\partial A_1 = \partial A_2$, let $\mathcal{A}_1, \dots, \mathcal{A}_k$ be the equivalence
  classes into which $\mathcal{A}'$ is partitioned by this relation, and let
  $$\mathcal{A} = \left\{ \bigcup(A : A \in \mathcal{A}_i) : 1 \le i \le k \right\}.$$
  Output $\mathcal{A}$, and stop."
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 3: Equivalence of `alg86DivPairList` with `alg86Division` -/

open Classical in
open scoped Graph in
theorem Alg83Trace.omega_subset {x : Alg81Input} {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C) :
    x.omega.toFinset ⊆ Z := by
  intro v hv
  have hv_bar : v ∈ x.toSociety.Ω.bar := by
    simpa [Alg81Input.toSociety_bar] using hv
  have hv_VC : v ∈ V(toCoreGraph Z C) := htrace.isCoreOf.isTrisecting.bar_subset hv_bar
  simpa [toCoreGraph] using hv_VC

open Classical in
open scoped Graph in
theorem alg86Boundary_eq_inter_Z_of_fourLinkedCore (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {A : Alg86Subgraph x.G}
    (hA : A ∈ alg86RawDivision x Z) :
    alg86Boundary x A = A.verts ∩ Z ∧ (A.verts ∩ Z).card ≤ 3 := by
  have hC_GM : GM13.IsFourLinkedCore x.toSociety (toCoreGraph Z C) :=
    isFourLinkedCore_toCoreGraph htrace h4
  have hA_GM : A.toGMGraph ∈ GM13.coreRawDivision x.toSociety (toCoreGraph Z C) :=
    (mem_alg86RawDivision_iff_toGMGraph_mem_coreRawDivision x Z C A).mp hA
  have hbd_GM : V(A.toGMGraph) ∩ V(toCoreGraph Z C) = GM13.divBoundary x.toSociety A.toGMGraph :=
    GM13.lemma_8_6_claim_2 hC_GM hA_GM
  have hcard_GM : (V(A.toGMGraph) ∩ V(toCoreGraph Z C)).ncard ≤ 3 :=
    (GM13.lemma_8_6_claim_1 hC_GM hA_GM).1
  have hset_eq : V(A.toGMGraph) ∩ V(toCoreGraph Z C) = ((A.verts ∩ Z : Finset (Fin x.n)) : Set (Fin x.n)) := by
    ext v
    simp [Alg86Subgraph.toGMGraph, toCoreGraph]
  constructor
  · apply Finset.coe_injective
    rw [← divBoundary_toGMGraph x A, ← hbd_GM, hset_eq]
  · rw [hset_eq, Set.ncard_coe_finset] at hcard_GM
    exact hcard_GM

theorem alg86BoundaryEquiv_iff_inter_Z_eq (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {A₁ A₂ : Alg86Subgraph x.G}
    (hA₁ : A₁ ∈ alg86RawDivision x Z) (hA₂ : A₂ ∈ alg86RawDivision x Z) :
    Alg86BoundaryEquiv x A₁ A₂ ↔ A₁.verts ∩ Z = A₂.verts ∩ Z := by
  rw [Alg86BoundaryEquiv, (alg86Boundary_eq_inter_Z_of_fourLinkedCore x htrace h4 hA₁).1,
    (alg86Boundary_eq_inter_Z_of_fourLinkedCore x htrace h4 hA₂).1]

theorem verts_inter_Z_mkAlg86TypeII (x : Alg81Input) (Z : Finset (Fin x.n))
    {r : Fin x.n} (hr : r ∉ Z) :
    (mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hr)).verts ∩ Z =
      alg86X x.G Z r := by
  classical
  have hX_eq := alg86X_eq_filter_Z x.G Z hr
  ext z
  simp only [mkAlg86TypeII, Finset.mem_inter, Finset.mem_union, Finset.mem_filter, hX_eq]
  constructor
  · rintro ⟨hzK | ⟨hzZ, u, huK, hadj⟩, hzZ'⟩
    · exfalso
      exact (Finset.mem_sdiff.mp (alg86K_subset_sdiff_of_not_mem x.G Z hr hzK)).2 hzZ'
    · exact ⟨hzZ, u, huK, hadj⟩
  · rintro ⟨hzZ, u, huK, hadj⟩
    exact ⟨Or.inr ⟨hzZ, u, huK, hadj⟩, hzZ⟩

theorem card_alg86X_le_three (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {r : Fin x.n} (hr : r ∉ Z) :
    (alg86X x.G Z r).card ≤ 3 := by
  let A_r := mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hr)
  have hA_r : A_r ∈ alg86RawDivision x Z :=
    Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
  have hcard := (alg86Boundary_eq_inter_Z_of_fourLinkedCore x htrace h4 hA_r).2
  rwa [verts_inter_Z_mkAlg86TypeII x Z hr] at hcard

theorem mem_alg86L_iff {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    (r z : Fin n) :
    z ∈ alg86L G Z r ↔ z ∈ alg86X G Z r := by
  simp [alg86L]

theorem length_alg86L_eq_card_alg86X {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (r : Fin n) :
    (alg86L G Z r).length = (alg86X G Z r).card := by
  have hnodup : (alg86L G Z r).Nodup := (List.nodup_finRange n).filter _
  have htoFinset : (alg86L G Z r).toFinset = alg86X G Z r := by
    ext z
    simp [mem_alg86L_iff]
  rw [← htoFinset, List.toFinset_card_of_nodup hnodup]

theorem alg86Tuple_eq_iff_alg86X_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {u r : Fin n}
    (hu_card : (alg86X G Z u).card ≤ 3) :
    alg86Tuple G Z u = alg86Tuple G Z r ↔ alg86X G Z u = alg86X G Z r := by
  constructor
  · intro htup
    have hLu_len : (alg86L G Z u).length ≤ 3 := by
      rw [length_alg86L_eq_card_alg86X]; exact hu_card
    dsimp [alg86Tuple] at htup
    rcases Prod.mk.injEq _ _ _ _ ▸ htup with ⟨hlen, htup1⟩
    rcases Prod.mk.injEq _ _ _ _ ▸ htup1 with ⟨he0, htup2⟩
    rcases Prod.mk.injEq _ _ _ _ ▸ htup2 with ⟨he1, he2⟩
    have hL_eq : alg86L G Z u = alg86L G Z r := by
      refine List.ext_getElem hlen (fun i hi_u hi_r => Fin.ext ?_)
      have hi3 : i < 3 := Nat.lt_of_lt_of_le hi_u hLu_len
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · simpa [hi_u, hi_r] using he0
      · simpa [hi_u, hi_r] using he1
      · simpa [hi_u, hi_r] using he2
    ext z
    rw [← mem_alg86L_iff, hL_eq, mem_alg86L_iff]
  · intro hX_eq
    have hL_eq : alg86L G Z u = alg86L G Z r := by
      dsimp [alg86L]; rw [hX_eq]
    dsimp [alg86Tuple]; rw [hL_eq]

theorem mem_alg86U_iff_of_fourLinkedCore (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {r : Fin x.n} (_hr : r ∉ Z) (u : Fin x.n) :
    u ∈ alg86U x.G Z r ↔ u ∉ Z ∧ alg86X x.G Z u = alg86X x.G Z r := by
  simp only [alg86U, Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun huZ => ?_
  exact alg86Tuple_eq_iff_alg86X_eq x.G Z (card_alg86X_le_three x htrace h4 huZ)

theorem self_mem_alg86U {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    {r : Fin n} (hr : r ∉ Z) :
    r ∈ alg86U G Z r := by
  simp [alg86U, hr]

theorem alg86U_eq_of_mem_of_fourLinkedCore (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {r u : Fin x.n} (hr : r ∉ Z)
    (huU : u ∈ alg86U x.G Z r) :
    alg86U x.G Z u = alg86U x.G Z r := by
  obtain ⟨huZ, hX_ur⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr u).mp huU
  ext w
  rw [mem_alg86U_iff_of_fourLinkedCore x htrace h4 huZ w,
      mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr w, hX_ur]

theorem alg86K_subset_alg86U_of_fourLinkedCore (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {r u : Fin x.n} (hr : r ∉ Z)
    (huU : u ∈ alg86U x.G Z r) :
    alg86K x.G Z u ⊆ alg86U x.G Z r := by
  obtain ⟨huZ, hX_ur⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr u).mp huU
  have hK_u := isComponentOutsideCore_alg86K x.G Z huZ
  intro w hwK
  have hwZ : w ∉ Z := hK_u.not_mem_Z hwK
  have hK_wu : alg86K x.G Z w = alg86K x.G Z u :=
    alg86K_eq_of_isComponentOutsideCore x.G Z (alg86K x.G Z u) hK_u hwK
  have hX_wu : alg86X x.G Z w = alg86X x.G Z u := by
    simp only [alg86X, hK_wu]
  exact (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr w).mpr ⟨hwZ, hX_wu.trans hX_ur⟩

theorem mem_alg86CaseCPairs_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) (k : ℕ) (hk_le : k ≤ n)
    (p : Finset (Fin n) × List (Fin n × Fin n)) :
    p ∈ alg86CaseCPairs G Z edges₀ k ↔
      ∃ r : Fin n,
        r.1 < k ∧ r ∉ Z ∧ (∀ u ∈ alg86U G Z r, r.1 ≤ u.1) ∧
        p = (alg86U G Z r ∪ alg86X G Z r,
          edges₀.filter (alg86KeepEdge (alg86U G Z r) (alg86X G Z r)
            (decide ((alg86L G Z r).length = 2)))) := by
  induction k with
  | zero => simp [alg86CaseCPairs]
  | succ k ih =>
    have hk_lt : k < n := by omega
    simp only [alg86CaseCPairs, hk_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro (⟨r, hr_lt, hrZ, hmin, hp⟩ | rfl)
        · exact ⟨r, by omega, hrZ, hmin, hp⟩
        · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hcond.1, hcond.2, rfl⟩
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
        · exact Or.inl ⟨r, hlt', hrZ, hmin, hp⟩
        · have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hr_eq
          exact Or.inr hp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        exact ⟨r, by omega, hrZ, hmin, hp⟩
      · rintro ⟨r, hr_lt, hrZ, hmin, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
        · exact ⟨r, hlt', hrZ, hmin, hp⟩
        · exfalso
          have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hr_eq
          exact hcond ⟨hrZ, hmin⟩

theorem mem_alg86CaseCMarked_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n))
    (M₀ : Finset (Fin edges₀.length)) (k : ℕ) (hk_le : k ≤ n)
    (j : Fin edges₀.length) :
    j ∈ alg86CaseCMarked G Z edges₀ M₀ k ↔
      j ∈ M₀ ∨
      ∃ r : Fin n,
        r.1 < k ∧ r ∉ Z ∧ (∀ u ∈ alg86U G Z r, r.1 ≤ u.1) ∧
        (alg86L G Z r).length = 2 ∧
        j ∈ alg86XEdgeIndices edges₀ (alg86X G Z r) := by
  induction k with
  | zero => simp [alg86CaseCMarked]
  | succ k ih =>
    have hk_lt : k < n := by omega
    simp only [alg86CaseCMarked, hk_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [Finset.mem_union, ih (by omega)]
      constructor
      · rintro ((hjM | ⟨r, hr_lt, hrZ, hmin, hlen, hjX⟩) | hjX)
        · exact Or.inl hjM
        · exact Or.inr ⟨r, by omega, hrZ, hmin, hlen, hjX⟩
        · exact Or.inr ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hcond.1.1, hcond.1.2, hcond.2, hjX⟩
      · rintro (hjM | ⟨r, hr_lt, hrZ, hmin, hlen, hjX⟩)
        · exact Or.inl (Or.inl hjM)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
          · exact Or.inl (Or.inr ⟨r, hlt', hrZ, hmin, hlen, hjX⟩)
          · have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
            subst hr_eq
            exact Or.inr hjX
    · rw [ih (by omega)]
      constructor
      · rintro (hjM | ⟨r, hr_lt, hrZ, hmin, hlen, hjX⟩)
        · exact Or.inl hjM
        · exact Or.inr ⟨r, by omega, hrZ, hmin, hlen, hjX⟩
      · rintro (hjM | ⟨r, hr_lt, hrZ, hmin, hlen, hjX⟩)
        · exact Or.inl hjM
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hlt' | heq
          · exact Or.inr ⟨r, hlt', hrZ, hmin, hlen, hjX⟩
          · exfalso
            have hr_eq : r = ⟨k, hk_lt⟩ := Fin.ext heq
            subst hr_eq
            exact hcond ⟨⟨hrZ, hmin⟩, hlen⟩

theorem pair_eq_of_mem_of_card_eq_two {α : Type*} [DecidableEq α]
    {X : Finset α} {u v : α} (hne : u ≠ v) (hu : u ∈ X) (hv : v ∈ X) (hcard : X.card = 2) :
    ({u, v} : Finset α) = X := by
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hzv
    · exact hu
    · rw [Finset.mem_singleton.mp hzv]; exact hv
  · rw [hcard, Finset.card_pair hne]

theorem mem_alg86CaseCMarked_iff_exists_alg86X_eq
    (x : Alg81Input) {Z : Finset (Fin x.n)} {C : SimpleGraph (Fin x.n)}
    (htrace : Alg83Trace x Z C) (h4 : IsFourLinkedCore x.omega Z C)
    (j : Fin (edgeListOf x.G).length) :
    j ∈ alg86CaseCMarked x.G Z (edgeListOf x.G) ∅ x.n ↔
      ∃ r : Fin x.n, r ∉ Z ∧
        alg86X x.G Z r = {((edgeListOf x.G)[j.1]'j.2).1, ((edgeListOf x.G)[j.1]'j.2).2} := by
  let edges₀ := edgeListOf x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  let e := edges₀[j.1]'j.2
  have hadj : x.G.Adj e.1 e.2 := (hedges₀.2.2 e.1 e.2).mpr ⟨j.1, j.2, Or.inl ⟨rfl, rfl⟩⟩
  have hne : e.1 ≠ e.2 := x.G.ne_of_adj hadj
  rw [mem_alg86CaseCMarked_iff x.G Z edges₀ ∅ x.n le_rfl j]
  simp only [Finset.notMem_empty, false_or, mem_alg86XEdgeIndices_iff]
  constructor
  · rintro ⟨r, _, hrZ, _, hlen, he1, he2⟩
    rw [length_alg86L_eq_card_alg86X] at hlen
    exact ⟨r, hrZ, (pair_eq_of_mem_of_card_eq_two hne he1 he2 hlen).symm⟩
  · rintro ⟨r₀, hr₀Z, hX₀⟩
    classical
    let U := alg86U x.G Z r₀
    have hU_ne : U.Nonempty := ⟨r₀, self_mem_alg86U x.G Z hr₀Z⟩
    let r := U.min' hU_ne
    have hrU : r ∈ U := Finset.min'_mem U hU_ne
    obtain ⟨hrZ, hX_r⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr₀Z r).mp hrU
    have hU_eq : alg86U x.G Z r = U := alg86U_eq_of_mem_of_fourLinkedCore x htrace h4 hr₀Z hrU
    have hX_pair : alg86X x.G Z r = {e.1, e.2} := hX_r.trans hX₀
    refine ⟨r, r.2, hrZ, ?_, ?_, ?_⟩
    · intro u hu
      rw [hU_eq] at hu
      exact Fin.le_iff_val_le_val.mp (Finset.min'_le U u hu)
    · rw [length_alg86L_eq_card_alg86X, hX_pair, Finset.card_pair hne]
    · rw [hX_pair]
      exact ⟨Finset.mem_insert_self e.1 {e.2},
        Finset.mem_insert_of_mem (Finset.mem_singleton_self e.2)⟩

theorem verts_inter_Z_of_isAlg86TypeI (x : Alg81Input) (Z : Finset (Fin x.n))
    {A : Alg86Subgraph x.G} {u v : Fin x.n} (huZ : u ∈ Z) (hvZ : v ∈ Z)
    (hverts : A.verts = {u, v}) :
    A.verts ∩ Z = {u, v} := by
  rw [hverts, Finset.inter_eq_left]
  intro z hz
  rcases Finset.mem_insert.mp hz with rfl | hzv
  · exact huZ
  · rw [Finset.mem_singleton.mp hzv]; exact hvZ

theorem verts_inter_Z_of_isAlg86TypeII (x : Alg81Input) (Z : Finset (Fin x.n))
    {A : Alg86Subgraph x.G} {K : Finset (Fin x.n)} (hK : IsComponentOutsideCore x.G Z K)
    (hverts : A.verts = K ∪ (open Classical in Z.filter (fun z => ∃ u ∈ K, x.G.Adj u z)))
    {r : Fin x.n} (hrK : r ∈ K) :
    A.verts ∩ Z = alg86X x.G Z r := by
  have hrZ : r ∉ Z := hK.not_mem_Z hrK
  have hK_eq : alg86K x.G Z r = K := alg86K_eq_of_isComponentOutsideCore x.G Z K hK hrK
  ext z
  simp only [hverts, Finset.mem_inter, Finset.mem_union, Finset.mem_filter,
    alg86X, mem_extNeighborhood, hK_eq]
  constructor
  · rintro ⟨hzK | ⟨hzZ, u, huK, hadj⟩, hzZ'⟩
    · exact (hK.not_mem_Z hzK hzZ').elim
    · exact ⟨⟨fun hzK => hK.not_mem_Z hzK hzZ, u, huK, hadj⟩, hzZ⟩
  · rintro ⟨⟨_, u, huK, hadj⟩, hzZ⟩
    exact ⟨Or.inr ⟨hzZ, u, huK, hadj⟩, hzZ⟩

theorem self_mem_alg86K {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    r ∈ alg86K G Z r :=
  (mem_reachSet (restrictGraph G (Finset.univ \ Z)) r r).mpr (Reachable.refl r)

theorem alg86SubgraphOfPair_caseC (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) {r : Fin x.n} (hr : r ∉ Z) :
    let U := alg86U x.G Z r
    let X := alg86X x.G Z r
    let incX := decide ((alg86L x.G Z r).length = 2)
    let A_r := mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hr)
    alg86SubgraphOfPair x.G (U ∪ X, (edgeListOf x.G).filter (alg86KeepEdge U X incX)) =
      alg86SubgraphUnion (alg86EquivClass x Z A_r) := by
  intro U X incX A_r
  let edges₀ := edgeListOf x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  have hA_r_raw : A_r ∈ alg86RawDivision x Z :=
    Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
  have hA_r_Z : A_r.verts ∩ Z = X := verts_inter_Z_mkAlg86TypeII x Z hr
  have hA_r_cls : A_r ∈ alg86EquivClass x Z A_r := ⟨hA_r_raw, rfl⟩
  have hcls_iff : ∀ A : Alg86Subgraph x.G,
      A ∈ alg86EquivClass x Z A_r ↔ A ∈ alg86RawDivision x Z ∧ A.verts ∩ Z = X := by
    intro A
    simp only [alg86EquivClass, Set.mem_ofPred_eq]
    refine and_congr_right fun hA => ?_
    rw [alg86BoundaryEquiv_iff_inter_Z_eq x htrace h4 hA hA_r_raw, hA_r_Z]
  have hverts_sub : ∀ A ∈ alg86EquivClass x Z A_r, A.verts ⊆ U ∪ X := by
    intro A hA a ha
    obtain ⟨hA_raw, hAZ⟩ := (hcls_iff A).mp hA
    by_cases haZ : a ∈ Z
    · have haX : a ∈ X := by rw [← hAZ]; exact Finset.mem_inter.mpr ⟨ha, haZ⟩
      exact Finset.mem_union_right U haX
    · apply Finset.mem_union_left X
      rcases hA_raw with ⟨u, v, huZ, hvZ, _, hverts, _⟩ | ⟨K, hK, hverts, _⟩ | ⟨v, hv_om, _, hverts, _⟩
      · rw [hverts] at ha
        rcases Finset.mem_insert.mp ha with rfl | hav
        · exact (haZ huZ).elim
        · rw [Finset.mem_singleton.mp hav] at haZ; exact (haZ hvZ).elim
      · rw [hverts] at ha
        rcases Finset.mem_union.mp ha with haK | ha_filt
        · have ha_X : alg86X x.G Z a = X := by
            rw [← verts_inter_Z_of_isAlg86TypeII x Z hK hverts haK, hAZ]
          exact (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr a).mpr ⟨haZ, ha_X⟩
        · exact (haZ (Finset.mem_filter.mp ha_filt).1).elim
      · rw [hverts, Finset.mem_singleton] at ha
        subst ha
        exact (haZ (htrace.omega_subset hv_om)).elim
  ext a b
  · rw [verts_alg86SubgraphOfPair, mem_verts_alg86SubgraphUnion]
    constructor
    · intro ha
      rcases Finset.mem_union.mp ha with haU | haX
      · obtain ⟨haZ, haX_eq⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr a).mp haU
        let A_a := mkAlg86TypeII x Z (alg86K x.G Z a) (isComponentOutsideCore_alg86K x.G Z haZ)
        have hA_a_raw : A_a ∈ alg86RawDivision x Z :=
          Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
        have hA_a_Z : A_a.verts ∩ Z = X :=
          (verts_inter_Z_mkAlg86TypeII x Z haZ).trans haX_eq
        refine ⟨A_a, (hcls_iff A_a).mpr ⟨hA_a_raw, hA_a_Z⟩, ?_⟩
        apply Finset.mem_union_left
        exact self_mem_alg86K x.G Z a
      · refine ⟨A_r, hA_r_cls, ?_⟩
        have hX_sub : X ⊆ A_r.verts := by
          rw [← hA_r_Z]; exact Finset.inter_subset_left
        exact hX_sub haX
    · rintro ⟨A, hA, ha⟩
      exact hverts_sub A hA ha
  · rw [adj_alg86SubgraphOfPair, adj_alg86SubgraphUnion]
    constructor
    · rintro ⟨hadj, _, _, hmem | hmem⟩
      · have hkeep := (List.mem_filter.mp hmem).2
        simp only [alg86KeepEdge, decide_eq_true_eq] at hkeep
        rcases hkeep with (haU | hbU) | ⟨hinc, haX, hbX⟩
        · obtain ⟨haZ, haX_eq⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr a).mp haU
          let A_a := mkAlg86TypeII x Z (alg86K x.G Z a) (isComponentOutsideCore_alg86K x.G Z haZ)
          have hA_a_raw : A_a ∈ alg86RawDivision x Z :=
            Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
          have hA_a_Z : A_a.verts ∩ Z = X :=
            (verts_inter_Z_mkAlg86TypeII x Z haZ).trans haX_eq
          refine ⟨A_a, (hcls_iff A_a).mpr ⟨hA_a_raw, hA_a_Z⟩, ?_⟩
          change x.G.Adj a b ∧ _
          rw [(isComponentOutsideCore_alg86K x.G Z haZ).adj_iff_mem_or_mem]
          exact ⟨hadj, Or.inl (self_mem_alg86K x.G Z a)⟩
        · obtain ⟨hbZ, hbX_eq⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr b).mp hbU
          let A_b := mkAlg86TypeII x Z (alg86K x.G Z b) (isComponentOutsideCore_alg86K x.G Z hbZ)
          have hA_b_raw : A_b ∈ alg86RawDivision x Z :=
            Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
          have hA_b_Z : A_b.verts ∩ Z = X :=
            (verts_inter_Z_mkAlg86TypeII x Z hbZ).trans hbX_eq
          refine ⟨A_b, (hcls_iff A_b).mpr ⟨hA_b_raw, hA_b_Z⟩, ?_⟩
          change x.G.Adj a b ∧ _
          rw [(isComponentOutsideCore_alg86K x.G Z hbZ).adj_iff_mem_or_mem]
          exact ⟨hadj, Or.inr (self_mem_alg86K x.G Z b)⟩
        · have hX_card : X.card = 2 := by
            have hlen2 : (alg86L x.G Z r).length = 2 := of_decide_eq_true hinc
            rwa [length_alg86L_eq_card_alg86X] at hlen2
          have haZ : a ∈ Z := (Finset.mem_inter.mp haX).2
          have hbZ : b ∈ Z := (Finset.mem_inter.mp hbX).2
          have hpair_X : ({a, b} : Finset (Fin x.n)) = X :=
            pair_eq_of_mem_of_card_eq_two (x.G.ne_of_adj hadj) haX hbX hX_card
          let A_ab := mkAlg86TypeI x hadj
          have hA_ab_raw : A_ab ∈ alg86RawDivision x Z :=
            Or.inl (isAlg86TypeI_mkAlg86TypeI x Z haZ hbZ hadj)
          have hA_ab_Z : A_ab.verts ∩ Z = X :=
            (verts_inter_Z_of_isAlg86TypeI x Z haZ hbZ rfl).trans hpair_X
          refine ⟨A_ab, (hcls_iff A_ab).mpr ⟨hA_ab_raw, hA_ab_Z⟩, ?_⟩
          exact Or.inl ⟨rfl, rfl⟩
      · have hkeep := (List.mem_filter.mp hmem).2
        simp only [alg86KeepEdge, decide_eq_true_eq] at hkeep
        rcases hkeep with (hbU | haU) | ⟨hinc, hbX, haX⟩
        · obtain ⟨hbZ, hbX_eq⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr b).mp hbU
          let A_b := mkAlg86TypeII x Z (alg86K x.G Z b) (isComponentOutsideCore_alg86K x.G Z hbZ)
          have hA_b_raw : A_b ∈ alg86RawDivision x Z :=
            Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
          have hA_b_Z : A_b.verts ∩ Z = X :=
            (verts_inter_Z_mkAlg86TypeII x Z hbZ).trans hbX_eq
          refine ⟨A_b, (hcls_iff A_b).mpr ⟨hA_b_raw, hA_b_Z⟩, ?_⟩
          change x.G.Adj a b ∧ _
          rw [(isComponentOutsideCore_alg86K x.G Z hbZ).adj_iff_mem_or_mem]
          exact ⟨hadj, Or.inr (self_mem_alg86K x.G Z b)⟩
        · obtain ⟨haZ, haX_eq⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr a).mp haU
          let A_a := mkAlg86TypeII x Z (alg86K x.G Z a) (isComponentOutsideCore_alg86K x.G Z haZ)
          have hA_a_raw : A_a ∈ alg86RawDivision x Z :=
            Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
          have hA_a_Z : A_a.verts ∩ Z = X :=
            (verts_inter_Z_mkAlg86TypeII x Z haZ).trans haX_eq
          refine ⟨A_a, (hcls_iff A_a).mpr ⟨hA_a_raw, hA_a_Z⟩, ?_⟩
          change x.G.Adj a b ∧ _
          rw [(isComponentOutsideCore_alg86K x.G Z haZ).adj_iff_mem_or_mem]
          exact ⟨hadj, Or.inl (self_mem_alg86K x.G Z a)⟩
        · have hX_card : X.card = 2 := by
            have hlen2 : (alg86L x.G Z r).length = 2 := of_decide_eq_true hinc
            rwa [length_alg86L_eq_card_alg86X] at hlen2
          have haZ : a ∈ Z := (Finset.mem_inter.mp haX).2
          have hbZ : b ∈ Z := (Finset.mem_inter.mp hbX).2
          have hpair_X : ({a, b} : Finset (Fin x.n)) = X :=
            pair_eq_of_mem_of_card_eq_two (x.G.ne_of_adj hadj) haX hbX hX_card
          let A_ab := mkAlg86TypeI x hadj
          have hA_ab_raw : A_ab ∈ alg86RawDivision x Z :=
            Or.inl (isAlg86TypeI_mkAlg86TypeI x Z haZ hbZ hadj)
          have hA_ab_Z : A_ab.verts ∩ Z = X :=
            (verts_inter_Z_of_isAlg86TypeI x Z haZ hbZ rfl).trans hpair_X
          refine ⟨A_ab, (hcls_iff A_ab).mpr ⟨hA_ab_raw, hA_ab_Z⟩, ?_⟩
          exact Or.inl ⟨rfl, rfl⟩
    · rintro ⟨A, hA, hadj_A⟩
      have hadj : x.G.Adj a b := A.sub hadj_A
      have hverts_ab := A.adj_verts a b hadj_A
      have ha_UX : a ∈ U ∪ X := hverts_sub A hA hverts_ab.1
      have hb_UX : b ∈ U ∪ X := hverts_sub A hA hverts_ab.2
      obtain ⟨hA_raw, hAZ⟩ := (hcls_iff A).mp hA
      have hkeep_cond : (a ∈ U ∨ b ∈ U) ∨ (incX = true ∧ a ∈ X ∧ b ∈ X) := by
        rcases hA_raw with ⟨u, v, huZ, hvZ, hadj_uv, hverts, hgraph⟩ | ⟨K, hK, hverts, hgraph⟩ | ⟨v, _, _, _, hgraph⟩
        · right
          have hpair_X : ({u, v} : Finset (Fin x.n)) = X := by
            rw [← verts_inter_Z_of_isAlg86TypeI x Z huZ hvZ hverts, hAZ]
          have hX_card : X.card = 2 := by
            rw [← hpair_X, Finset.card_pair (x.G.ne_of_adj hadj_uv)]
          have hinc_true : incX = true := by
            simp only [incX, decide_eq_true_eq, length_alg86L_eq_card_alg86X]
            exact hX_card
          rw [hgraph a b] at hadj_A
          rcases hadj_A with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [← hpair_X]
            exact ⟨hinc_true, Finset.mem_insert_self a {b},
              Finset.mem_insert_of_mem (Finset.mem_singleton_self b)⟩
          · rw [← hpair_X]
            exact ⟨hinc_true,
              Finset.mem_insert_of_mem (Finset.mem_singleton_self a),
              Finset.mem_insert_self b {a}⟩
        · left
          rw [hgraph a b, hK.adj_iff_mem_or_mem] at hadj_A
          rcases hadj_A.2 with haK | hbK
          · left
            have haZ : a ∉ Z := hK.not_mem_Z haK
            have ha_X : alg86X x.G Z a = X := by
              rw [← verts_inter_Z_of_isAlg86TypeII x Z hK hverts haK, hAZ]
            exact (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr a).mpr ⟨haZ, ha_X⟩
          · right
            have hbZ : b ∉ Z := hK.not_mem_Z hbK
            have hb_X : alg86X x.G Z b = X := by
              rw [← verts_inter_Z_of_isAlg86TypeII x Z hK hverts hbK, hAZ]
            exact (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr b).mpr ⟨hbZ, hb_X⟩
        · rw [hgraph] at hadj_A
          exact hadj_A.elim
      rcases (hedges₀.2.2 a b).mp hadj with ⟨j, hj, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · refine ⟨hadj, ha_UX, hb_UX, Or.inl ?_⟩
        have he_eq : edges₀[j]'hj = (a, b) := Prod.ext h1 h2
        rw [← he_eq, List.mem_filter]
        refine ⟨List.getElem_mem hj, ?_⟩
        simp only [alg86KeepEdge, h1, h2, decide_eq_true_eq]
        exact hkeep_cond
      · refine ⟨hadj, ha_UX, hb_UX, Or.inr ?_⟩
        have he_eq : edges₀[j]'hj = (b, a) := Prod.ext h1 h2
        rw [← he_eq, List.mem_filter]
        refine ⟨List.getElem_mem hj, ?_⟩
        simp only [alg86KeepEdge, h1, h2, decide_eq_true_eq]
        rcases hkeep_cond with hU | ⟨hinc, haX, hbX⟩
        · exact Or.inl hU.symm
        · exact Or.inr ⟨hinc, hbX, haX⟩

theorem alg86EquivClass_typeI_eq_singleton (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C)
    (j : Fin (edgeListOf x.G).length)
    (huZ : ((edgeListOf x.G)[j.1]'j.2).1 ∈ Z)
    (hvZ : ((edgeListOf x.G)[j.1]'j.2).2 ∈ Z)
    (hnotM : j ∉ alg86CaseCMarked x.G Z (edgeListOf x.G) ∅ x.n)
    (hadj : x.G.Adj ((edgeListOf x.G)[j.1]'j.2).1 ((edgeListOf x.G)[j.1]'j.2).2) :
    alg86EquivClass x Z (mkAlg86TypeI x hadj) = {mkAlg86TypeI x hadj} := by
  let e := (edgeListOf x.G)[j.1]'j.2
  let A_e := mkAlg86TypeI x hadj
  have hne : e.1 ≠ e.2 := x.G.ne_of_adj hadj
  have hA_e_raw : A_e ∈ alg86RawDivision x Z :=
    Or.inl (isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj)
  have hA_e_Z : A_e.verts ∩ Z = {e.1, e.2} :=
    verts_inter_Z_of_isAlg86TypeI x Z huZ hvZ rfl
  ext A
  simp only [alg86EquivClass, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hA_raw, hequiv⟩
    have hAZ : A.verts ∩ Z = {e.1, e.2} := by
      rw [alg86BoundaryEquiv_iff_inter_Z_eq x htrace h4 hA_raw hA_e_raw, hA_e_Z] at hequiv
      exact hequiv
    rcases hA_raw with ⟨u, v, hu'Z, hv'Z, hadj_uv, hverts, hgraph⟩ | ⟨K, hK, hverts, _⟩ | ⟨v, _, _, hverts, _⟩
    · have hpair_eq : ({u, v} : Finset (Fin x.n)) = {e.1, e.2} := by
        rw [← verts_inter_Z_of_isAlg86TypeI x Z hu'Z hv'Z hverts, hAZ]
      ext a b
      · rw [hverts, hpair_eq]; rfl
      · rw [hgraph a b]
        change (a = u ∧ b = v ∨ a = v ∧ b = u) ↔ (a = e.1 ∧ b = e.2 ∨ a = e.2 ∧ b = e.1)
        have hu_mem : u ∈ ({e.1, e.2} : Finset (Fin x.n)) := by
          rw [← hpair_eq]; exact Finset.mem_insert_self u {v}
        have hv_mem : v ∈ ({e.1, e.2} : Finset (Fin x.n)) := by
          rw [← hpair_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
        have huv_ne : u ≠ v := x.G.ne_of_adj hadj_uv
        rcases Finset.mem_insert.mp hu_mem with rfl | hu2 <;>
          rcases Finset.mem_insert.mp hv_mem with rfl | hv2
        · exact (huv_ne rfl).elim
        · rw [Finset.mem_singleton.mp hv2]
        · rw [Finset.mem_singleton.mp hu2]; exact or_comm
        · exfalso
          exact huv_ne ((Finset.mem_singleton.mp hu2).trans (Finset.mem_singleton.mp hv2).symm)
    · exfalso
      obtain ⟨r, hrK⟩ := hK.nonempty
      have hrZ : r ∉ Z := hK.not_mem_Z hrK
      have hX_eq : alg86X x.G Z r = {e.1, e.2} := by
        rw [← verts_inter_Z_of_isAlg86TypeII x Z hK hverts hrK, hAZ]
      exact hnotM ((mem_alg86CaseCMarked_iff_exists_alg86X_eq x htrace h4 j).mpr ⟨r, hrZ, hX_eq⟩)
    · exfalso
      have hcard2 : (A.verts ∩ Z).card = 2 := by
        rw [hAZ, Finset.card_pair hne]
      have hcard1 : (A.verts ∩ Z).card ≤ 1 := by
        rw [hverts]
        exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
      omega
  · rintro rfl
    exact ⟨hA_e_raw, rfl⟩

theorem alg86EquivClass_typeIII_eq_singleton (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C)
    {v : Fin x.n} (hv_om : v ∈ x.omega.toFinset) (hiso : ∀ w : Fin x.n, ¬ x.G.Adj v w) :
    alg86EquivClass x Z (mkAlg86TypeIII x v) = {mkAlg86TypeIII x v} := by
  let A_v := mkAlg86TypeIII x v
  have hvZ : v ∈ Z := htrace.omega_subset hv_om
  have hA_v_raw : A_v ∈ alg86RawDivision x Z :=
    Or.inr (Or.inr (isAlg86TypeIII_mkAlg86TypeIII x hv_om hiso))
  have hA_v_Z : A_v.verts ∩ Z = {v} := by
    change ({v} : Finset (Fin x.n)) ∩ Z = {v}
    exact Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hvZ)
  ext A
  simp only [alg86EquivClass, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hA_raw, hequiv⟩
    have hAZ : A.verts ∩ Z = {v} := by
      rw [alg86BoundaryEquiv_iff_inter_Z_eq x htrace h4 hA_raw hA_v_raw, hA_v_Z] at hequiv
      exact hequiv
    rcases hA_raw with ⟨u, w, huZ, hwZ, hadj_uw, hverts, _⟩ | ⟨K, hK, hverts, _⟩ | ⟨v', hv'_om, _, hverts, hgraph⟩
    · exfalso
      have hpair_eq : ({u, w} : Finset (Fin x.n)) = {v} := by
        rw [← verts_inter_Z_of_isAlg86TypeI x Z huZ hwZ hverts, hAZ]
      have hcard2 : ({u, w} : Finset (Fin x.n)).card = 2 :=
        Finset.card_pair (x.G.ne_of_adj hadj_uw)
      rw [hpair_eq, Finset.card_singleton] at hcard2
      omega
    · exfalso
      obtain ⟨r, hrK⟩ := hK.nonempty
      have hX_eq : alg86X x.G Z r = {v} := by
        rw [← verts_inter_Z_of_isAlg86TypeII x Z hK hverts hrK, hAZ]
      have hv_X : v ∈ alg86X x.G Z r := by rw [hX_eq]; exact Finset.mem_singleton_self v
      simp only [alg86X, Finset.mem_inter, mem_extNeighborhood] at hv_X
      rcases hv_X.1.2 with ⟨u, _, hadj⟩
      exact hiso u hadj.symm
    · have hv'_Z : v' ∈ Z := htrace.omega_subset hv'_om
      have hv'_eq : ({v'} : Finset (Fin x.n)) = {v} := by
        have : A.verts ∩ Z = {v'} := by
          rw [hverts]
          exact Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hv'_Z)
        exact this.symm.trans hAZ
      ext a b
      · rw [hverts, hv'_eq]; rfl
      · rw [hgraph]; rfl
  · rintro rfl
    exact ⟨hA_v_raw, rfl⟩

@[simp]
theorem alg86SubgraphUnion_singleton {n : ℕ} {G : SimpleGraph (Fin n)} (A : Alg86Subgraph G) :
    alg86SubgraphUnion ({A} : Set (Alg86Subgraph G)) = A := by
  ext a b
  · rw [mem_verts_alg86SubgraphUnion]
    simp
  · rw [adj_alg86SubgraphUnion]
    simp

/-- The division pair list `alg86DivPairList` emitted by `alg86DivisionsProg` decodes under
`alg86SubgraphOfPair x.G` to the quotient division `alg86Division x Z` ($\mathcal{A}$). -/
theorem setOf_mem_map_alg86DivPairList (x : Alg81Input) {Z : Finset (Fin x.n)}
    {C : SimpleGraph (Fin x.n)} (htrace : Alg83Trace x Z C)
    (h4 : IsFourLinkedCore x.omega Z C) :
    { B | B ∈ (alg86DivPairList x.G Z x.omega.toFinset (edgeListOf x.G)).map
        (alg86SubgraphOfPair x.G) } =
      alg86Division x Z := by
  let edges₀ := edgeListOf x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  let M' := alg86CaseCMarked x.G Z edges₀ ∅ x.n
  ext B
  simp only [Set.mem_ofPred_eq, alg86DivPairList, List.map_append, List.mem_append,
    List.mem_map, alg86Division]
  constructor
  · rintro ((⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩)
    · rw [mem_alg86CaseCPairs_iff x.G Z edges₀ x.n le_rfl] at hp
      rcases hp with ⟨r, _, hrZ, _, rfl⟩
      rw [alg86SubgraphOfPair_caseC x htrace h4 hrZ]
      exact ⟨mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hrZ),
        Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _)), rfl⟩
    · rw [mem_alg86TypeIPairs_iff Z edges₀ M' edges₀.length le_rfl] at hp
      rcases hp with ⟨j, _, huZ, hvZ, hnotM, rfl⟩
      have hadj : x.G.Adj (edges₀[j.1]'j.2).1 (edges₀[j.1]'j.2).2 :=
        (hedges₀.2.2 _ _).mpr ⟨j.1, j.2, Or.inl ⟨rfl, rfl⟩⟩
      rw [alg86SubgraphOfPair_typeI x hadj]
      refine ⟨mkAlg86TypeI x hadj, Or.inl (isAlg86TypeI_mkAlg86TypeI x Z huZ hvZ hadj), ?_⟩
      rw [alg86EquivClass_typeI_eq_singleton x htrace h4 j huZ hvZ hnotM hadj,
        alg86SubgraphUnion_singleton]
    · rw [mem_alg86TypeIIIPairs_iff x.omega.toFinset edges₀ x.n le_rfl] at hp
      rcases hp with ⟨v, _, hv_om, hdeg0, rfl⟩
      have hiso : ∀ w : Fin x.n, ¬ x.G.Adj v w := by
        intro w hadj
        have hmem_nb : w.1 ∈ edgeNeighbors edges₀ v :=
          ((isAdjListFamily_edgeNeighbors hedges₀ v).2.2.2 w).mpr hadj
        have hlen_pos : 0 < (edgeNeighbors edges₀ v).length :=
          List.length_pos_of_mem hmem_nb
        omega
      rw [alg86SubgraphOfPair_typeIII x v]
      refine ⟨mkAlg86TypeIII x v,
        Or.inr (Or.inr (isAlg86TypeIII_mkAlg86TypeIII x hv_om hiso)), ?_⟩
      rw [alg86EquivClass_typeIII_eq_singleton x htrace h4 hv_om hiso,
        alg86SubgraphUnion_singleton]
  · rintro ⟨A₀, hA₀_raw, rfl⟩
    by_cases hex_II : ∃ r₀ : Fin x.n, r₀ ∉ Z ∧ alg86X x.G Z r₀ = A₀.verts ∩ Z
    · rcases hex_II with ⟨r₀, hr₀Z, hX₀⟩
      classical
      let U := alg86U x.G Z r₀
      have hU_ne : U.Nonempty := ⟨r₀, self_mem_alg86U x.G Z hr₀Z⟩
      let r := U.min' hU_ne
      have hrU : r ∈ U := Finset.min'_mem U hU_ne
      obtain ⟨hrZ, hX_r⟩ := (mem_alg86U_iff_of_fourLinkedCore x htrace h4 hr₀Z r).mp hrU
      have hU_eq : alg86U x.G Z r = U := alg86U_eq_of_mem_of_fourLinkedCore x htrace h4 hr₀Z hrU
      have hmin : ∀ u ∈ alg86U x.G Z r, r.1 ≤ u.1 := by
        intro u hu
        rw [hU_eq] at hu
        exact Fin.le_iff_val_le_val.mp (Finset.min'_le U u hu)
      let A_r := mkAlg86TypeII x Z (alg86K x.G Z r) (isComponentOutsideCore_alg86K x.G Z hrZ)
      have hA_r_raw : A_r ∈ alg86RawDivision x Z :=
        Or.inr (Or.inl (isAlg86TypeII_mkAlg86TypeII x Z _ _))
      have hcls_eq : alg86EquivClass x Z A₀ = alg86EquivClass x Z A_r := by
        ext A
        simp only [alg86EquivClass, Set.mem_ofPred_eq]
        refine and_congr_right fun hA => ?_
        rw [alg86BoundaryEquiv_iff_inter_Z_eq x htrace h4 hA hA₀_raw,
            alg86BoundaryEquiv_iff_inter_Z_eq x htrace h4 hA hA_r_raw,
            verts_inter_Z_mkAlg86TypeII x Z hrZ, hX_r, hX₀]
      left; left
      refine ⟨(alg86U x.G Z r ∪ alg86X x.G Z r,
        edges₀.filter (alg86KeepEdge (alg86U x.G Z r) (alg86X x.G Z r)
          (decide ((alg86L x.G Z r).length = 2)))), ?_, ?_⟩
      · rw [mem_alg86CaseCPairs_iff x.G Z edges₀ x.n le_rfl]
        exact ⟨r, r.2, hrZ, hmin, rfl⟩
      · rw [alg86SubgraphOfPair_caseC x htrace h4 hrZ, hcls_eq]
    · rcases hA₀_raw with ⟨u, v, huZ, hvZ, hadj, hverts, hgraph⟩ | ⟨K, hK, hverts, _⟩ | ⟨v, hv_om, hiso, hverts, hgraph⟩
      · rcases (hedges₀.2.2 u v).mp hadj with ⟨j, hj, hpair⟩
        let jFin : Fin edges₀.length := ⟨j, hj⟩
        have he1_Z : (edges₀[j]'hj).1 ∈ Z := by
          rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> assumption
        have he2_Z : (edges₀[j]'hj).2 ∈ Z := by
          rcases hpair with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> assumption
        have hadj_e : x.G.Adj (edges₀[j]'hj).1 (edges₀[j]'hj).2 :=
          (hedges₀.2.2 _ _).mpr ⟨j, hj, Or.inl ⟨rfl, rfl⟩⟩
        have hpair_eq : ({(edges₀[j]'hj).1, (edges₀[j]'hj).2} : Finset (Fin x.n)) = {u, v} := by
          rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]
          · rw [h1, h2, Finset.pair_comm]
        have hA₀_Z : A₀.verts ∩ Z = {(edges₀[j]'hj).1, (edges₀[j]'hj).2} :=
          (verts_inter_Z_of_isAlg86TypeI x Z huZ hvZ hverts).trans hpair_eq.symm
        have hnotM : jFin ∉ M' := by
          intro hjM
          rcases (mem_alg86CaseCMarked_iff_exists_alg86X_eq x htrace h4 jFin).mp hjM with
            ⟨r, hrZ, hX_r⟩
          exact hex_II ⟨r, hrZ, hX_r.trans hA₀_Z.symm⟩
        have hA₀_eq : A₀ = mkAlg86TypeI x hadj_e := by
          ext a b
          · rw [hverts, ← hpair_eq]; rfl
          · rw [hgraph a b]
            change (a = u ∧ b = v ∨ a = v ∧ b = u) ↔
              (a = (edges₀[j]'hj).1 ∧ b = (edges₀[j]'hj).2 ∨
               a = (edges₀[j]'hj).2 ∧ b = (edges₀[j]'hj).1)
            rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [h1, h2]
            · rw [h1, h2]; exact or_comm
        left; right
        refine ⟨({(edges₀[j]'hj).1, (edges₀[j]'hj).2}, [edges₀[j]'hj]), ?_, ?_⟩
        · rw [mem_alg86TypeIPairs_iff Z edges₀ M' edges₀.length le_rfl]
          exact ⟨jFin, hj, he1_Z, he2_Z, hnotM, rfl⟩
        · rw [alg86SubgraphOfPair_typeI x hadj_e, hA₀_eq,
              alg86EquivClass_typeI_eq_singleton x htrace h4 jFin he1_Z he2_Z hnotM hadj_e,
              alg86SubgraphUnion_singleton]
      · exfalso
        obtain ⟨r₀, hr₀K⟩ := hK.nonempty
        exact hex_II ⟨r₀, hK.not_mem_Z hr₀K,
          (verts_inter_Z_of_isAlg86TypeII x Z hK hverts hr₀K).symm⟩
      · have hA₀_eq : A₀ = mkAlg86TypeIII x v := by
          ext a b
          · rw [hverts]; rfl
          · rw [hgraph]; rfl
        right
        refine ⟨({v}, []), ?_, ?_⟩
        · rw [mem_alg86TypeIIIPairs_iff x.omega.toFinset edges₀ x.n le_rfl]
          refine ⟨v, v.2, hv_om, ?_, rfl⟩
          by_contra hne
          have hpos : 0 < (edgeNeighbors edges₀ v).length := Nat.pos_of_ne_zero hne
          let w_val := (edgeNeighbors edges₀ v)[0]'hpos
          have hmem : w_val ∈ edgeNeighbors edges₀ v := List.getElem_mem hpos
          have h_lt := (isAdjListFamily_edgeNeighbors hedges₀ v).1 w_val hmem
          let w : Fin x.n := ⟨w_val, h_lt⟩
          have hadj := ((isAdjListFamily_edgeNeighbors hedges₀ v).2.2.2 w).mp hmem
          exact hiso w hadj
        · rw [alg86SubgraphOfPair_typeIII x v, hA₀_eq,
              alg86EquivClass_typeIII_eq_singleton x htrace h4 hv_om hiso,
              alg86SubgraphUnion_singleton]

/-! ### Section 4: Output Bundle, Pure-Reader Decoder `decAlg86Out`, `alg86Prog`, and `gm13_algorithm_8_6` -/

/-- Second-case output bundle of GM XIII Algorithm (8.6) on input society `x : Alg81Input`:
- `core`: the 4-linked core `(Z, C)` computed by Algorithm (8.3),
- `rawDiv`: the raw family $\mathcal{A}'$ of subgraphs of `x.G` built from `core.Z`,
- `div`: the family $\mathcal{A}$ of unions of equivalence classes of `rawDiv` under
  $\partial A_1 = \partial A_2$. -/
structure Alg86DivisionOutput (x : Alg81Input) where
  /-- The 4-linked core `(Z, C)` produced by Algorithm (8.3). -/
  core : Alg83Output x
  /-- The raw family $\mathcal{A}'$ of subgraphs satisfying (i), (ii), or (iii). -/
  rawDiv : Set (Alg86Subgraph x.G)
  /-- The quotient family $\mathcal{A}$ of unions of equivalence classes of `rawDiv` under
  $\partial A_1 = \partial A_2$. -/
  div : Set (Alg86Subgraph x.G)

/-- View the raw family `d.rawDiv` as a set of subgraphs of `x.toSociety.G` in
`Graph (Fin x.n) (Sym2 (Fin x.n))`. -/
def Alg86DivisionOutput.toGMRawDivision {x : Alg81Input} (d : Alg86DivisionOutput x) :
    Set (Graph (Fin x.n) (Sym2 (Fin x.n))) :=
  Alg86Subgraph.toGMGraph '' d.rawDiv

/-- View the division `d.div` ($\mathcal{A}$) as a set of subgraphs of `x.toSociety.G` in
`Graph (Fin x.n) (Sym2 (Fin x.n))`. -/
def Alg86DivisionOutput.toGMDivision {x : Alg81Input} (d : Alg86DivisionOutput x) :
    Set (Graph (Fin x.n) (Sym2 (Fin x.n))) :=
  Alg86Subgraph.toGMGraph '' d.div

/-- Output conditions for the second case of GM XIII Algorithm (8.6) (pages 96–97):
1. `(x.G, x.omega)` has no cross (`¬ HasCrossInSociety x.G x.omega` and
   `¬ GM13.HasCross x.toSociety`).
2. `d.core` is a valid 4-linked core of `(x.G, x.omega)` (`IsValidAlg83Output x d.core`, which
   includes `GM13.IsCoreOf x.toSociety d.core.toCoreGraph` and
   `GM13.IsFourLinkedCore x.toSociety d.core.toCoreGraph`).
3. `d.rawDiv` ($\mathcal{A}'$) is the set of all subgraphs $A$ of `x.G` satisfying condition (i)
   (`IsAlg86TypeI x d.core.Z A`), condition (ii) (`IsAlg86TypeII x d.core.Z A`), or condition (iii)
   (`IsAlg86TypeIII x A`).
4. `d.div` ($\mathcal{A}$) is the set of unions $\bigcup(A : A \in \mathcal{A}_i)$ of the
   equivalence classes $\mathcal{A}_i = \{A \in d.\text{rawDiv} \mid \partial A = \partial A_0\}$
   for $A_0 \in d.\text{rawDiv}$.
5. Every $A \in d.\text{rawDiv}$ satisfies $\partial A \subseteq V(A) \cap V(C)$.
6. `d.toGMRawDivision = GM13.coreRawDivision x.toSociety d.core.toCoreGraph`,
   `d.toGMDivision = GM13.coreDivision x.toSociety d.core.toCoreGraph`, and
   `GM13.IsRuralDivision x.toSociety d.toGMDivision` (by `GM13.isRuralDivision_coreDivision`). -/
def IsValidAlg86DivisionOutput (x : Alg81Input) (d : Alg86DivisionOutput x) : Prop :=
  ¬ HasCrossInSociety x.G x.omega ∧
  ¬ GM13.HasCross x.toSociety ∧
  IsValidAlg83Output x d.core ∧
  (∀ A : Alg86Subgraph x.G,
    A ∈ d.rawDiv ↔
      IsAlg86TypeI x d.core.Z A ∨
      IsAlg86TypeII x d.core.Z A ∨
      IsAlg86TypeIII x A) ∧
  (∀ B : Alg86Subgraph x.G,
    B ∈ d.div ↔
      ∃ A₀ ∈ d.rawDiv,
        B = alg86SubgraphUnion { A ∈ d.rawDiv | Alg86BoundaryEquiv x A A₀ }) ∧
  (∀ A ∈ d.rawDiv, alg86Boundary x A ⊆ A.verts ∩ d.core.Z) ∧
  d.toGMRawDivision = GM13.coreRawDivision x.toSociety d.core.toCoreGraph ∧
  d.toGMDivision = GM13.coreDivision x.toSociety d.core.toCoreGraph ∧
  GM13.IsRuralDivision x.toSociety d.toGMDivision

/-- Decoded output type of GM XIII Algorithm (8.6):
either a cross in `(x.G, x.omega)` (`Sum.inl w`), or the division bundle `Alg86DivisionOutput x`
built from a 4-linked core (`Sum.inr d`). -/
abbrev Alg86Output (x : Alg81Input) : Type :=
  Sum (CrossWitness x.G x.omega) (Alg86DivisionOutput x)

/-- Output validity predicate for GM XIII Algorithm (8.6) (pages 96–97):
either `res = Sum.inl w` is a cross in `x.toSociety` (`w.IsValid`,
`x.toSociety.IsCross w.toGraphP w.toGraphQ`, and `GM13.HasCross x.toSociety`), or
`res = Sum.inr d` is a rural division of `x.toSociety` (`IsValidAlg86DivisionOutput x d`, which
includes `GM13.IsRuralDivision x.toSociety d.toGMDivision`). -/
def IsValidAlg86Output (x : Alg81Input) (res : Alg86Output x) : Prop :=
  match res with
  | Sum.inl w =>
    w.IsValid ∧
    x.toSociety.IsCross w.toGraphP w.toGraphQ ∧
    GM13.HasCross x.toSociety
  | Sum.inr d => IsValidAlg86DivisionOutput x d

/-- Pure reader from `outArr : List ℕ` into `Alg86Output x`:
- If `out.head? = some 1` and `decAlg81Out x out = some w`, returns `Sum.inl w`.
- Otherwise reads the core `(Z, C)` via `decAlg86SubgraphWords x.n out.tail`, the raw division list
  `rawList` via `decAlg86PairListWords x.n rest₁`, and the quotient division list `divList` via
  `decAlg86PairListWords x.n rest₂`, without computing any reachability, components, or equivalence
  classes in the decoder. -/
noncomputable def decAlg86Out (x : Alg81Input) (out : List ℕ) : Alg86Output x :=
  if out.head? = some 1 then
    match decAlg81Out x out with
    | some w => Sum.inl w
    | none =>
      let ((Z, C), rest₁) := decAlg86SubgraphWords x.n out.tail
      let (rawList, rest₂) := decAlg86PairListWords x.n rest₁
      let (divList, _) := decAlg86PairListWords x.n rest₂
      Sum.inr
        { core := { Z := Z, C := C }
          rawDiv := { A | A ∈ rawList.map (alg86SubgraphOfDecoded x.G) }
          div := { B | B ∈ divList.map (alg86SubgraphOfDecoded x.G) } }
  else
    let ((Z, C), rest₁) := decAlg86SubgraphWords x.n out.tail
    let (rawList, rest₂) := decAlg86PairListWords x.n rest₁
    let (divList, _) := decAlg86PairListWords x.n rest₂
    Sum.inr
      { core := { Z := Z, C := C }
        rawDiv := { A | A ∈ rawList.map (alg86SubgraphOfDecoded x.G) }
        div := { B | B ∈ divList.map (alg86SubgraphOfDecoded x.G) } }

/-- Complete Word RAM program for GM XIII Algorithm (8.6), parameterized by Shiloach's program
`shiloachProg : Cmd`:
1. Runs `alg81Prog shiloachProg` to test for a cross in `(G, Ω)`.
2. Reads `r_0 := outArr[0]`. If `r_0 ≠ 0`, a cross was written to `outArr`, so stops (`skip`).
3. If `r_0 = 0`, runs `alg86DivisionsProg` on `inArr = 0` (which `alg81Prog` preserved) to compute
   a 4-linked core `(Z, C)` via `alg83Prog` and construct and serialize both $\mathcal{A}'$ and
   $\mathcal{A}$ to `outArr`. -/
def alg86Prog (shiloachProg : Cmd) : Cmd :=
  .seq (alg81Prog shiloachProg)
    (.seq (.assign 0 (.read outArr (.const 0)))
      (.ite (.reg 0)
        .skip
        alg86DivisionsProg))

/-- **Graph Minors XIII, (8.6) Algorithm** (pages 96–97):
Given a society `(G, Ω)`, `alg86Prog` runs in time `O(vε)` (`alg81Size x`) and outputs either a
cross in `(G, Ω)` (`Sum.inl w` with `x.toSociety.IsCross w.toGraphP w.toGraphQ` and
`GM13.HasCross x.toSociety`), or a rural division `𝒜` of `(G, Ω)` (`Sum.inr d` with
`GM13.IsRuralDivision x.toSociety d.toGMDivision`, built from a 4-linked core `d.core` and the raw
family `𝒜'`), assuming `Shiloach80Statement`. -/
theorem gm13_algorithm_8_6 (hShiloach : Shiloach80Statement) :
    ∃ shiloachProg : Cmd,
      ComputesArrRelInTime alg81Size encAlg81In
        (fun x out => IsValidAlg86Output x (decAlg86Out x out))
        (alg86Prog shiloachProg) (fun s => s) := by
  rcases hShiloach with ⟨shiloachProg, C_sh, c_sh, hC_sh, hc_sh, hSh_spec⟩
  refine ⟨shiloachProg, 6300 + 10 * C_sh, 5 * c_sh + 4, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let w := wordSize (5 * c_sh + 4) (alg81Size x)
  have hm_eq : (edgeListOf x.G).length = x.G.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.G
  have hS_def : alg81Size x = (x.n + 1) * ((edgeListOf x.G).length + x.n + 1) := by
    dsimp [alg81Size, societySize]; rw [hm_eq]
  have hS_pos : 1 ≤ alg81Size x := by
    rw [hS_def]; exact Nat.mul_pos (by omega) (by omega)
  have hpow4 : (alg81Size x + 2) ^ 4 < 2 ^ w := by
    have hpow_c := pow_lt_two_pow_wordSize (c := 5 * c_sh + 4) (by omega) (alg81Size x)
    have hle : (alg81Size x + 2) ^ 4 ≤ (alg81Size x + 2) ^ (5 * c_sh + 4) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.lt_of_le_of_lt hle hpow_c
  have h16_le : 16 * (alg81Size x + 2) ≤ (alg81Size x + 2) ^ 4 := by
    have h3 : 3 ≤ alg81Size x + 2 := by omega
    have h16 : 16 ≤ (alg81Size x + 2) ^ 3 := by
      calc 16 ≤ 3 ^ 3 := by decide
        _ ≤ (alg81Size x + 2) ^ 3 := Nat.pow_le_pow_left h3 3
    have hmul := Nat.mul_le_mul_right (alg81Size x + 2) h16
    simpa [Nat.pow_succ] using hmul
  have hsize_w : 16 * (alg81Size x + 2) < 2 ^ w :=
    Nat.lt_of_le_of_lt h16_le hpow4
  have hw4 : 4 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  -- 1. Run alg81Prog shiloachProg
  rcases alg81Prog_exec hC_sh hc_sh hSh_spec x le_rfl hs₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hres₁⟩
  rcases hres₁ with ⟨cw, hcw_valid, hout₁⟩ | ⟨hout0, hno_cross⟩
  · -- Case 1: A cross was found by (8.1)
    have hlen_pos : 0 < (s₁.arrs outArr).length := by simp [hout₁]
    have hget0_1 : (s₁.arrs outArr)[0]'hlen_pos = 1 := by simp [hout₁]
    let s₂ := s₁.setReg 0 1
    have hex₂ : Exec w (.assign 0 (.read outArr (.const 0))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, hlen_pos, hget0_1, hw1])
    have hcond : (Expr.reg 0).eval w s₂ = some 1 := by
      simp [s₂, Expr.eval, checkWord, hw1]
    have hex_ite : Exec w (.ite (.reg 0) .skip alg86DivisionsProg) s₂ s₂ (1 + 1) :=
      .ite_true hcond (by omega) (.skip s₂)
    have htime : t₁ + (3 + (1 + 1)) ≤ (6300 + 10 * C_sh) * alg81Size x := by
      have : (6300 + 10 * C_sh) * alg81Size x =
          5100 * alg81Size x + (1200 + 10 * C_sh) * alg81Size x := by ring
      omega
    refine ⟨s₂, t₁ + (3 + (1 + 1)), .seq hex₁ (.seq hex₂ hex_ite), htime, ?_⟩
    have hout₂ : s₂.arrs outArr = s₁.arrs outArr := rfl
    have hhead₁ : (s₁.arrs outArr).head? = some 1 := by simp [hout₁]
    have hdec₁ : decAlg81Out x (s₁.arrs outArr) = some cw := by
      rw [hout₁]; exact decAlg81Out_encode x cw
    dsimp only
    rw [hout₂]
    unfold decAlg86Out
    simp only [hhead₁, ↓reduceIte, hdec₁, IsValidAlg86Output]
    have hcr := CrossWitness.isCross_of_isValid x hcw_valid
    exact ⟨hcw_valid, hcr, ⟨_, _, hcr⟩⟩
  · -- Case 2: No cross in (x.G, x.omega); run alg86DivisionsProg
    let s₂ := s₁.setReg 0 0
    have hex₂ : Exec w (.assign 0 (.read outArr (.const 0))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, h0_w, hout0])
    have hcond : (Expr.reg 0).eval w s₂ = some 0 := by
      simp [s₂, Expr.eval, checkWord, h0_w]
    have hin₂ : s₂.arrs 0 = encAlg81In x := hin₁
    rcases alg86DivisionsProg_exec x hw4 hsize_w hin₂ with
      ⟨s₃, t₃, Z, C, edges_C, hex₃, ht₃, htrace, hom_sub, hadj_Z, hcore4,
        hedges_C, _, hout₃⟩
    have hex_ite : Exec w (.ite (.reg 0) .skip alg86DivisionsProg) s₂ s₃ (1 + t₃) :=
      .ite_false hcond hex₃
    have htime : t₁ + (3 + (1 + t₃)) ≤ (6300 + 10 * C_sh) * alg81Size x := by
      have hsplit : (6300 + 10 * C_sh) * alg81Size x =
          (1200 + 10 * C_sh) * alg81Size x + 5000 * alg81Size x + 100 * alg81Size x := by ring
      linarith [ht₁, ht₃, hS_pos, hsplit]
    refine ⟨s₃, t₁ + (3 + (1 + t₃)), .seq hex₁ (.seq hex₂ hex_ite), htime, ?_⟩
    let edges₀ := edgeListOf x.G
    let cap := 12 * alg81Size x
    let rawPairs := alg86RawPairList x.G Z x.omega.toFinset edges₀
    let divPairs := alg86DivPairList x.G Z x.omega.toFinset edges₀
    let fullPref :=
      ([0] ++ encAlg86Subgraph Z edges_C ++ encAlg86PairList rawPairs ++ encAlg86PairList divPairs)
    let pad := List.replicate (cap - fullPref.length) 0
    have hout₃' : s₃.arrs outArr =
        0 :: (encAlg86Subgraph Z edges_C ++
          (encAlg86PairList rawPairs ++ (encAlg86PairList divPairs ++ pad))) := by
      simpa [fullPref, pad, encAlg86Subgraph, List.append_assoc] using hout₃
    dsimp only
    rw [hout₃']
    have hhead :
        (0 :: (encAlg86Subgraph Z edges_C ++
          (encAlg86PairList rawPairs ++ (encAlg86PairList divPairs ++ pad)))).head? ≠ some 1 := by
      simp
    have hraw_map :
        (rawPairs.map (fun p =>
          (p.1, graphOfFlatEdges x.n ([x.n, p.2.length] ++ flatEdges p.2)))).map
            (alg86SubgraphOfDecoded x.G) =
          rawPairs.map (alg86SubgraphOfPair x.G) := by
      rw [List.map_map]
      rfl
    have hdiv_map :
        (divPairs.map (fun p =>
          (p.1, graphOfFlatEdges x.n ([x.n, p.2.length] ++ flatEdges p.2)))).map
            (alg86SubgraphOfDecoded x.G) =
          divPairs.map (alg86SubgraphOfPair x.G) := by
      rw [List.map_map]
      rfl
    have hraw_set :
        { A | A ∈ rawPairs.map (alg86SubgraphOfPair x.G) } = alg86RawDivision x Z :=
      setOf_mem_map_alg86RawPairList x Z
    have hdiv_set :
        { B | B ∈ divPairs.map (alg86SubgraphOfPair x.G) } = alg86Division x Z :=
      setOf_mem_map_alg86DivPairList x htrace hcore4
    unfold decAlg86Out
    simp only [hhead, ↓reduceIte, List.tail_cons,
      decAlg86SubgraphWords_append, graphOfFlatEdges_eq C edges_C hedges_C,
      decAlg86PairListWords_append, hraw_map, hdiv_map, hraw_set, hdiv_set,
      IsValidAlg86Output, IsValidAlg86DivisionOutput,
      Alg86DivisionOutput.toGMRawDivision, Alg86DivisionOutput.toGMDivision,
      Alg83Output.toCoreGraph]
    refine ⟨hno_cross, fun h => hno_cross ((hasCrossInSociety_iff_hasCross x).mpr h),
      ?_, fun _ => Iff.rfl, fun _ => Iff.rfl, fun A hA => ?_,
      image_toGMGraph_alg86RawDivision x Z C,
      image_toGMGraph_alg86Division x Z C,
      isRuralDivision_image_alg86Division x htrace hcore4 hno_cross⟩
    · refine ⟨htrace.isCoreOf, isFourLinkedCore_toCoreGraph htrace hcore4,
        htrace, hom_sub, hadj_Z, hcore4, fun v hvZ => ?_⟩
      exact fourLinkedPaths_of_isFourLinkedAt x.omega Z C v hom_sub hadj_Z hvZ (hcore4.2.2 v hvZ)
    · exact alg86Boundary_subset_inter_Z x Z hom_sub hA

end GraphMinor.Compute
