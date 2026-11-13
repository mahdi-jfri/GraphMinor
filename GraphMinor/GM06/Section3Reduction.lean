module

public import GraphMinor.GM06.Section3InduceSingleton
public import GraphMinor.GM06.Section3Main
public import GraphMinor.GM06.DualExists

/-!
# Graph Minors VI, Section 3: Reduction Sequences and Termination for (3.3)–(3.4)

This file formalizes the mathematical reduction sequences and termination measure for the disc
division feasibility reductions of Robertson and Seymour,
*Graph Minors. VI. Disjoint Paths Across a Disc*, J. Combin. Theory Ser. B **41** (1986), 115–138
(Section 3, pages 120–121).

## Main definitions and theorems

* `DiscDivInstance`: a proper drawing `G` on a closed disc space `S` together with a division `Δ`
  satisfying `divisionUnion Δ = G.V ∩ bd S` (conditions (i) and (ii) of GM VI Section 3, page 120),
  with measure `I.measure = I.G.V.ncard + I.G.R.ncard`.
* `Alg34Tree`: an inductive derivation tree recording the reduction steps of (3.3) and (3.4):
  cross-free check (`isCrossFree_of_isFeasible`), empty division check (`isFeasible_empty`),
  singleton reduction (3.3)(i) (`theorem_3_3_i`), internal component deletion (3.3)(ii)
  (`theorem_3_3_ii`), split division detection (3.3)(iii) (`theorem_3_3_iii`), component
  decomposition (3.3)(iv) (`theorem_3_3_iv`), and passage to the dual `(G*, Δ*)` via (3.2) and
  (2.3) followed by singleton reduction (3.3)(i) (`theorem_3_2`, `theorem_2_3`, `theorem_3_3_i`).
* `Alg34Tree.sound`: every derivation tree `T : Alg34Tree I b` is sound
  (`b = true ↔ I.IsFeasibleInst`).
* `exists_alg34Tree`: every instance `I : DiscDivInstance.{u}` admits a derivation tree of depth at
  most `I.measure = |V(G)| + |R(G)|`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM11

universe u

/-! ### Section 1: Problem Instances and Reduction Steps of (3.3)–(3.4) -/

/-- An instance of the disc division feasibility problem of Graph Minors VI, Section 3 (page 120):
a closed disc space `S`, a proper drawing `G : Drawing S`, and a division `Δ : Set (Set S)` with
`divisionUnion Δ = G.V ∩ bd S`. -/
structure DiscDivInstance : Type (u + 1) where
  /-- The underlying topological space `S` (a closed disc). -/
  S : Type u
  /-- Topology on `S`. -/
  [topS : TopologicalSpace S]
  /-- `S` is homeomorphic to the closed unit disc. -/
  hDisc : IsClosedDiscSpace S
  /-- The drawing `G` on `S`. -/
  G : Drawing S
  /-- Condition (i) of Section 3 (page 120): `G` is properly drawn on `S`. -/
  hProper : G.IsProper
  /-- The division `Δ` of boundary vertices. -/
  Δ : Set (Set S)
  /-- `Δ` is a division (finite set of pairwise disjoint non-empty subsets). -/
  hΔ : IsDivision Δ
  /-- Condition (ii) of Section 3 (page 120): `⋃ Δ = V(G) ∩ bd(S)`. -/
  hΔ_eq : divisionUnion Δ = G.V ∩ bd S

attribute [instance] DiscDivInstance.topS

namespace DiscDivInstance

/-- The termination measure `|V(G)| + |R(G)|` of the Section 3 reductions (page 121:
"Each reduction decreases the number of vertices plus the number of regions of $G$"). -/
noncomputable def measure (I : DiscDivInstance.{u}) : ℕ :=
  I.G.V.ncard + I.G.R.ncard

/-- Feasibility of the division `I.Δ` in `I.G.toGraph`. -/
def IsFeasibleInst (I : DiscDivInstance.{u}) : Prop :=
  IsFeasible I.G.toGraph I.Δ

/-- Cross-freeness of `I.Δ` on `bd I.S`. -/
def IsCrossFreeInst (I : DiscDivInstance.{u}) : Prop :=
  IsCrossFree (bd I.S) I.Δ

/-- **Reduction (3.3)(i)** on a `DiscDivInstance`: deleting a singleton `{v} ∈ I.Δ` from `I.Δ` and
`v` from `I.G` yields a smaller `DiscDivInstance` with equivalent feasibility. -/
noncomputable def reduceSingleton (I : DiscDivInstance.{u}) (v : I.S) (hv : {v} ∈ I.Δ) :
    DiscDivInstance.{u} :=
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  { S := I.S
    hDisc := I.hDisc
    G := induceDrawing I.G (I.G.V \ {v})
    hProper := induceDrawing_isProper I.G I.hProper sdiff_subset
    Δ := I.Δ \ {{v}}
    hΔ := ⟨I.hΔ.1.subset sdiff_subset, fun δ hδ => I.hΔ.2.1 δ hδ.1, I.hΔ.2.2.subset sdiff_subset⟩
    hΔ_eq := by
      rw [induceDrawing_V I.G sdiff_subset]
      ext x
      simp only [divisionUnion, mem_sUnion, mem_inter_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨δ, ⟨hδ, hne⟩, hxδ⟩
        have hx_bd : x ∈ I.G.V ∩ bd I.S := I.hΔ_eq ▸ ⟨δ, hδ, hxδ⟩
        refine ⟨⟨hx_bd.1, ?_⟩, hx_bd.2⟩
        rintro rfl
        exact (I.hΔ.2.2 hδ hv hne).ne_of_mem hxδ rfl rfl
      · rintro ⟨⟨hxV, hxv⟩, hx_bd⟩
        have hx_union : x ∈ divisionUnion I.Δ := I.hΔ_eq.symm ▸ ⟨hxV, hx_bd⟩
        obtain ⟨δ, hδ, hxδ⟩ := hx_union
        refine ⟨δ, ⟨hδ, ?_⟩, hxδ⟩
        rintro rfl
        exact hxv hxδ }

theorem reduceSingleton_measure_lt (I : DiscDivInstance.{u}) (v : I.S) (hv : {v} ∈ I.Δ) :
    (I.reduceSingleton v hv).measure < I.measure := by
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  change (induceDrawing I.G (I.G.V \ {v})).V.ncard +
      (induceDrawing I.G (I.G.V \ {v})).R.ncard < I.G.V.ncard + I.G.R.ncard
  have hv_bd : v ∈ I.G.V ∩ bd I.S := I.hΔ_eq ▸ ⟨{v}, hv, rfl⟩
  have hSub : (induceDrawing I.G (I.G.V \ {v})).IsSubdrawing I.G :=
    induceDrawing_isSubdrawing I.G sdiff_subset
  have hV_lt : (induceDrawing I.G (I.G.V \ {v})).V.ncard < I.G.V.ncard := by
    rw [induceDrawing_V I.G sdiff_subset]
    exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h hv_bd.1).2 rfl⟩ I.G.finite_V
  have hR_le : (induceDrawing I.G (I.G.V \ {v})).R.ncard ≤ I.G.R.ncard :=
    disc_region_ncard_le_of_isSubdrawing I.hDisc I.hProper hSub
  omega

theorem reduceSingleton_isFeasible_iff (I : DiscDivInstance.{u}) (v : I.S) (hv : {v} ∈ I.Δ) :
    I.IsFeasibleInst ↔ (I.reduceSingleton v hv).IsFeasibleInst := by
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  change IsFeasible I.G.toGraph I.Δ ↔
    IsFeasible (induceDrawing I.G (I.G.V \ {v})).toGraph (I.Δ \ {{v}})
  rw [induceDrawing_toGraph_deleteVerts I.G {v}]
  exact theorem_3_3_i I.G.toGraph I.Δ v I.hΔ (I.hΔ_eq.subset.trans inter_subset_left) hv

/-- **Reduction (3.3)(ii)** on a `DiscDivInstance`: deleting a component `C₀` of `I.G.toGraph`
with `V(C₀) ∩ bd I.S = ∅` yields a smaller `DiscDivInstance` with equivalent feasibility. -/
noncomputable def reduceInternalComp (I : DiscDivInstance.{u}) (C₀ : Graph I.S (Set I.S))
    (_hC₀ : IsGraphComponent C₀ I.G.toGraph) (hC₀_disj : V(C₀) ∩ bd I.S = ∅) :
    DiscDivInstance.{u} :=
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  { S := I.S
    hDisc := I.hDisc
    G := induceDrawing I.G (I.G.V \ V(C₀))
    hProper := induceDrawing_isProper I.G I.hProper sdiff_subset
    Δ := I.Δ
    hΔ := I.hΔ
    hΔ_eq := by
      rw [induceDrawing_V I.G sdiff_subset, I.hΔ_eq]
      ext x
      simp only [mem_inter_iff, mem_sdiff]
      refine ⟨fun ⟨hxV, hx_bd⟩ => ⟨⟨hxV, fun hxC₀ => ?_⟩, hx_bd⟩,
        fun ⟨⟨hxV, _⟩, hx_bd⟩ => ⟨hxV, hx_bd⟩⟩
      have hx_empty : x ∈ (∅ : Set I.S) := hC₀_disj ▸ ⟨hxC₀, hx_bd⟩
      exact hx_empty }

theorem reduceInternalComp_measure_lt (I : DiscDivInstance.{u}) (C₀ : Graph I.S (Set I.S))
    (hC₀ : IsGraphComponent C₀ I.G.toGraph) (hC₀_disj : V(C₀) ∩ bd I.S = ∅) :
    (I.reduceInternalComp C₀ hC₀ hC₀_disj).measure < I.measure := by
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  change (induceDrawing I.G (I.G.V \ V(C₀))).V.ncard +
      (induceDrawing I.G (I.G.V \ V(C₀))).R.ncard < I.G.V.ncard + I.G.R.ncard
  obtain ⟨v₀, hv₀⟩ := hC₀.2.1.1
  have hv₀G : v₀ ∈ I.G.V := hC₀.1.vertexSet_mono hv₀
  have hSub : (induceDrawing I.G (I.G.V \ V(C₀))).IsSubdrawing I.G :=
    induceDrawing_isSubdrawing I.G sdiff_subset
  have hV_lt : (induceDrawing I.G (I.G.V \ V(C₀))).V.ncard < I.G.V.ncard := by
    rw [induceDrawing_V I.G sdiff_subset]
    exact ncard_lt_ncard ⟨sdiff_subset, fun h => (h hv₀G).2 hv₀⟩ I.G.finite_V
  have hR_le : (induceDrawing I.G (I.G.V \ V(C₀))).R.ncard ≤ I.G.R.ncard :=
    disc_region_ncard_le_of_isSubdrawing I.hDisc I.hProper hSub
  omega

theorem reduceInternalComp_isFeasible_iff (I : DiscDivInstance.{u}) (C₀ : Graph I.S (Set I.S))
    (hC₀ : IsGraphComponent C₀ I.G.toGraph) (hC₀_disj : V(C₀) ∩ bd I.S = ∅) :
    I.IsFeasibleInst ↔ (I.reduceInternalComp C₀ hC₀ hC₀_disj).IsFeasibleInst := by
  have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
  change IsFeasible I.G.toGraph I.Δ ↔
    IsFeasible (induceDrawing I.G (I.G.V \ V(C₀))).toGraph I.Δ
  rw [induceDrawing_toGraph_deleteVerts I.G V(C₀)]
  exact theorem_3_3_ii I.G C₀ I.Δ I.hΔ I.hΔ_eq.subset hC₀
    (disjoint_iff_inter_eq_empty.mpr hC₀_disj)

end DiscDivInstance

lemma two_le_ncard_graphComponents_of_not_connected' {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (hV_ne : G.V.Nonempty) (hNotConn : ¬ IsGraphConnected G.toGraph) :
    2 ≤ (graphComponents G.toGraph).ncard := by
  obtain ⟨v₀, hv₀⟩ := hV_ne
  have h_ex : ∃ v₁ ∈ G.V, compOf G.toGraph v₀ ≠ compOf G.toGraph v₁ := by
    by_contra h_all
    push Not at h_all
    apply hNotConn
    refine ⟨⟨v₀, hv₀⟩, fun u hu v hv => ?_⟩
    have hu_in : u ∈ reachSet G.toGraph v₀ := by
      have : u ∈ V(compOf G.toGraph u) := self_mem_reachSet hu
      rwa [← h_all u hu] at this
    have hv_in : v ∈ reachSet G.toGraph v₀ := by
      have : v ∈ V(compOf G.toGraph v) := self_mem_reachSet hv
      rwa [← h_all v hv] at this
    obtain ⟨_, ⟨Wu⟩⟩ := hu_in
    obtain ⟨_, ⟨Wv⟩⟩ := hv_in
    exact ⟨Wu.reverse.append Wv⟩
  obtain ⟨v₁, hv₁, hne⟩ := h_ex
  have h_pair_sub : ({compOf G.toGraph v₀, compOf G.toGraph v₁} : Set (Graph S (Set S))) ⊆
      graphComponents G.toGraph := by
    rintro C (rfl | rfl)
    · exact isGraphComponent_compOf hv₀
    · exact isGraphComponent_compOf hv₁
  have h_card_pair :
      ({compOf G.toGraph v₀, compOf G.toGraph v₁} : Set (Graph S (Set S))).ncard = 2 :=
    ncard_pair hne
  rw [← h_card_pair]
  exact ncard_le_ncard h_pair_sub (finite_graphComponents G)

/-! ### Section 2: Inductive Reduction Tree (`Alg34Tree`) and Completeness -/

/-- Inductive derivation tree for the Section 3 reductions on `I : DiscDivInstance.{u}`, producing
a boolean decision `b : Bool`:
- `notCrossFree`: `Δ` is not cross-free on `bd S`, so `Δ` is not feasible (`b = false`).
- `emptyDiv`: `Δ = ∅`, so `Δ` is feasible (`b = true`).
- `step33i`: `{v} ∈ Δ` for some `v`, reducing to `I.reduceSingleton v hv`.
- `step33ii`: `G` has a component `C₀` disjoint from `bd S`, reducing to
  `I.reduceInternalComp C₀ hC₀ hC₀_disj`.
- `step33iii`: some `δ ∈ Δ` intersects two distinct components of `G`, so `Δ` is not feasible
  (`b = false`).
- `step33iv`: `G` has `k ≥ 2` components `G_comp` and `Δ` partitions into `Δ_part`, reducing to the
  `k` subproblems `(G_i, Δ_part i)`.
- `stepDual`: `G` is connected, `Δ` is cross-free, and `(G*, Δ*)` is a dual drawing and dual
  division (which by (2.3) contains a singleton `{u} ∈ Δ*`), reducing via (3.2) and (3.3)(i) to a
  smaller instance `I'`. -/
inductive Alg34Tree : DiscDivInstance.{u} → Bool → Type (u + 1)
  | notCrossFree (I : DiscDivInstance.{u}) (hnot : ¬ I.IsCrossFreeInst) :
      Alg34Tree I false
  | emptyDiv (I : DiscDivInstance.{u}) (hemp : I.Δ = ∅) :
      Alg34Tree I true
  | step33i (I : DiscDivInstance.{u}) (v : I.S) (hv : {v} ∈ I.Δ) {b : Bool}
      (sub : Alg34Tree (I.reduceSingleton v hv) b) :
      Alg34Tree I b
  | step33ii (I : DiscDivInstance.{u}) (C₀ : Graph I.S (Set I.S))
      (hC₀ : IsGraphComponent C₀ I.G.toGraph) (hC₀_disj : V(C₀) ∩ bd I.S = ∅) {b : Bool}
      (sub : Alg34Tree (I.reduceInternalComp C₀ hC₀ hC₀_disj) b) :
      Alg34Tree I b
  | step33iii (I : DiscDivInstance.{u}) (δ : Set I.S) (hδ : δ ∈ I.Δ)
      (C₁ C₂ : Graph I.S (Set I.S)) (hC₁ : IsGraphComponent C₁ I.G.toGraph)
      (hC₂ : IsGraphComponent C₂ I.G.toGraph) (hne : C₁ ≠ C₂)
      (h₁ : (δ ∩ V(C₁)).Nonempty) (h₂ : (δ ∩ V(C₂)).Nonempty) :
      Alg34Tree I false
  | step33iv (I : DiscDivInstance.{u}) (k : ℕ) (hk : 2 ≤ k)
      (I_sub : Fin k → DiscDivInstance.{u})
      (h_lt : ∀ i : Fin k, (I_sub i).measure < I.measure)
      (h_iff : I.IsFeasibleInst ↔ ∀ i : Fin k, (I_sub i).IsFeasibleInst)
      (b_sub : Fin k → Bool)
      (subs : ∀ i : Fin k, Alg34Tree (I_sub i) (b_sub i)) :
      Alg34Tree I (List.all (List.ofFn b_sub) id)
  | stepDual (I : DiscDivInstance.{u}) (I_dual : DiscDivInstance.{u})
      (h_eq : I_dual.measure = I.measure)
      (h_iff : I.IsFeasibleInst ↔ I_dual.IsFeasibleInst)
      (u : I_dual.S) (hu : {u} ∈ I_dual.Δ) {b : Bool}
      (sub : Alg34Tree (I_dual.reduceSingleton u hu) b) :
      Alg34Tree I b

/-- Soundness of `Alg34Tree`: the boolean output `b` of any `Alg34Tree I b` equals `true` if and
only if `I.Δ` is feasible in `I.G.toGraph`. -/
theorem Alg34Tree.sound {I : DiscDivInstance.{u}} {b : Bool} (T : Alg34Tree I b) :
    (b = true ↔ I.IsFeasibleInst) := by
  induction T with
  | notCrossFree I hnot =>
    simp only [Bool.false_eq_true, false_iff]
    intro hFeas
    exact hnot (isCrossFree_of_isFeasible I.hDisc hFeas)
  | emptyDiv I hemp =>
    simp only [true_iff, DiscDivInstance.IsFeasibleInst]
    rw [hemp]
    exact isFeasible_empty I.G.toGraph
  | step33i I v hv _ ih =>
    exact ih.trans (I.reduceSingleton_isFeasible_iff v hv).symm
  | step33ii I C₀ hC₀ hC₀_disj _ ih =>
    exact ih.trans (I.reduceInternalComp_isFeasible_iff C₀ hC₀ hC₀_disj).symm
  | step33iii I δ hδ C₁ C₂ hC₁ hC₂ hne h₁ h₂ =>
    simp only [Bool.false_eq_true, false_iff]
    exact theorem_3_3_iii I.G.toGraph I.Δ δ C₁ C₂ hδ hC₁ hC₂ hne h₁ h₂
  | step33iv I k hk I_sub _ h_iff b_sub _ ih =>
    rw [List.all_eq_true, h_iff]
    constructor
    · intro hall i
      refine (ih i).mp ?_
      exact hall (b_sub i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
    · intro hall x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (ih i).mpr (hall i)
  | stepDual I I_dual _ h_iff u hu _ ih =>
    exact ih.trans ((I_dual.reduceSingleton_isFeasible_iff u hu).symm.trans h_iff.symm)

/-- Completeness and termination of the Section 3 reductions: every `DiscDivInstance` admits a
valid derivation tree `Alg34Tree I b`. -/
noncomputable def exists_alg34Tree (I : DiscDivInstance.{u}) :
    Σ b : Bool, Alg34Tree I b := by
  classical
  suffices ∀ n : ℕ, ∀ I : DiscDivInstance.{u}, I.measure = n → Σ b : Bool, Alg34Tree I b from
    this I.measure I rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro I hn
    have : T2Space I.S := t2Space_of_isClosedDiscSpace I.hDisc
    -- Step 0: Check if Δ is cross-free
    by_cases hCF : I.IsCrossFreeInst
    · -- Step 1: Check if Δ = ∅
      by_cases hΔ_emp : I.Δ = ∅
      · exact ⟨true, .emptyDiv I hΔ_emp⟩
      · have hΔ_ne : I.Δ.Nonempty := nonempty_iff_ne_empty.mpr hΔ_emp
        have hv₀_ex : ∃ v₀ : I.S, v₀ ∈ I.G.V ∩ bd I.S := by
          obtain ⟨δ₀, hδ₀⟩ := hΔ_ne
          obtain ⟨v₀, hv₀⟩ := I.hΔ.2.1 δ₀ hδ₀
          exact ⟨v₀, I.hΔ_eq ▸ ⟨δ₀, hδ₀, hv₀⟩⟩
        -- Step 2: Check if (3.3)(i) applies (∃ v, {v} ∈ Δ)
        by_cases h_sing : ∃ v : I.S, {v} ∈ I.Δ
        · let v := Classical.choose h_sing
          have hv : {v} ∈ I.Δ := Classical.choose_spec h_sing
          have hlt : (I.reduceSingleton v hv).measure < n :=
            hn ▸ I.reduceSingleton_measure_lt v hv
          let sub := ih (I.reduceSingleton v hv).measure hlt (I.reduceSingleton v hv) rfl
          exact ⟨sub.1, .step33i I v hv sub.2⟩
        · -- Step 3: Check if (3.3)(ii) applies (some component disjoint from bd S)
          by_cases h_int : ∃ C₀ ∈ graphComponents I.G.toGraph, V(C₀) ∩ bd I.S = ∅
          · let C₀ := Classical.choose h_int
            have hC₀_spec := Classical.choose_spec h_int
            have hC₀ : IsGraphComponent C₀ I.G.toGraph := hC₀_spec.1
            have hC₀_disj : V(C₀) ∩ bd I.S = ∅ := hC₀_spec.2
            have hlt : (I.reduceInternalComp C₀ hC₀ hC₀_disj).measure < n :=
              hn ▸ I.reduceInternalComp_measure_lt C₀ hC₀ hC₀_disj
            let sub := ih (I.reduceInternalComp C₀ hC₀ hC₀_disj).measure hlt
              (I.reduceInternalComp C₀ hC₀ hC₀_disj) rfl
            exact ⟨sub.1, .step33ii I C₀ hC₀ hC₀_disj sub.2⟩
          · -- Step 4: Check if (3.3)(iii) applies
            by_cases h_split : ∃ δ ∈ I.Δ, ∃ C₁ ∈ graphComponents I.G.toGraph,
                ∃ C₂ ∈ graphComponents I.G.toGraph,
                  C₁ ≠ C₂ ∧ (δ ∩ V(C₁)).Nonempty ∧ (δ ∩ V(C₂)).Nonempty
            · let δ := Classical.choose h_split
              have hδ_spec := Classical.choose_spec h_split
              let C₁ := Classical.choose hδ_spec.2
              have hC₁_spec := Classical.choose_spec hδ_spec.2
              let C₂ := Classical.choose hC₁_spec.2
              have hC₂_spec := Classical.choose_spec hC₁_spec.2
              exact ⟨false, .step33iii I δ hδ_spec.1 C₁ C₂ hC₁_spec.1 hC₂_spec.1
                hC₂_spec.2.1 hC₂_spec.2.2.1 hC₂_spec.2.2.2⟩
            · -- Step 5: Check if G is connected or has k ≥ 2 components ((3.3)(iv))
              by_cases hConn : IsGraphConnected I.G.toGraph
              · -- Step 6: G is connected; pass to (G*, Δ*) by (3.2) and apply (2.3) + (3.3)(i)
                have hDual_ex := exists_isDiscDualDrawing I.hDisc I.hProper hConn
                let G_dual := Classical.choose hDual_ex
                have hDual : IsDiscDualDrawing I.G G_dual := Classical.choose_spec hDual_ex
                let U_dual := G_dual.V ∩ bd I.S
                let Δ_dual := dualDivision (bd I.S) U_dual I.Δ
                have hC : IsOArc (bd I.S) := I.hDisc.isOArc_bd
                have hV_fin : (divisionUnion I.Δ).Finite :=
                  I.hΔ_eq ▸ I.G.finite_V.inter_of_left _
                have hV_sub : divisionUnion I.Δ ⊆ bd I.S := I.hΔ_eq ▸ inter_subset_right
                have hU_dual : IsDualPointSet (bd I.S) (divisionUnion I.Δ) U_dual :=
                  I.hΔ_eq ▸ hDual.2.2.2.2.1
                have hΔ_dual_div : IsDivision Δ_dual :=
                  isDivision_dualDivision hC hV_fin hV_sub hU_dual
                have hΔ_dual_eq : divisionUnion Δ_dual = G_dual.V ∩ bd I.S :=
                  divisionUnion_dualDivision (bd I.S) U_dual I.Δ
                let I_dual : DiscDivInstance.{u} := {
                  S := I.S
                  hDisc := I.hDisc
                  G := G_dual
                  hProper := hDual.2.1
                  Δ := Δ_dual
                  hΔ := hΔ_dual_div
                  hΔ_eq := hΔ_dual_eq
                }
                have h_meas_eq : I_dual.measure = I.measure :=
                  hDual.ncard_V_add_ncard_R_eq I.hDisc hConn
                have h_feas_iff : I.IsFeasibleInst ↔ I_dual.IsFeasibleInst :=
                  theorem_3_2_proof I.G G_dual I.Δ I.hDisc hConn I.hΔ I.hΔ_eq hCF hDual
                have hW_ne : (divisionUnion I.Δ ∪ U_dual).Nonempty := by
                  obtain ⟨v₀, hv₀_bd⟩ := hv₀_ex
                  exact ⟨v₀, Or.inl (I.hΔ_eq.symm ▸ hv₀_bd)⟩
                have h23 := theorem_2_3_proof (bd I.S) U_dual I.Δ hC I.hΔ hV_fin hV_sub hU_dual hW_ne
                have hu_ex : ∃ u : I.S, {u} ∈ Δ_dual := by
                  obtain ⟨γ, hγ_mem, hγ_card⟩ := h23
                  obtain ⟨u, rfl⟩ := ncard_eq_one.mp hγ_card
                  exact ⟨u, hγ_mem.resolve_left fun huΔ => h_sing ⟨u, huΔ⟩⟩
                let u := Classical.choose hu_ex
                have hu : {u} ∈ I_dual.Δ := Classical.choose_spec hu_ex
                have hlt : (I_dual.reduceSingleton u hu).measure < n := by
                  have hlt1 := I_dual.reduceSingleton_measure_lt u hu
                  omega
                let sub := ih (I_dual.reduceSingleton u hu).measure hlt
                  (I_dual.reduceSingleton u hu) rfl
                exact ⟨sub.1, .stepDual I I_dual h_meas_eq h_feas_iff u hu sub.2⟩
              · -- Step 5b: G is not connected, so (3.3)(iv) applies
                have h2_le : 2 ≤ (graphComponents I.G.toGraph).ncard := by
                  obtain ⟨v₀, hv₀_bd⟩ := hv₀_ex
                  exact two_le_ncard_graphComponents_of_not_connected' I.G ⟨v₀, hv₀_bd.1⟩ hConn
                have h_comps_fin : (graphComponents I.G.toGraph).Finite :=
                  finite_graphComponents I.G
                let k := (graphComponents I.G.toGraph).ncard
                have hk : 2 ≤ k := h2_le
                have h_card_coe : Nat.card (graphComponents I.G.toGraph) = k :=
                  Nat.card_coe_set_eq (graphComponents I.G.toGraph)
                have : Finite (graphComponents I.G.toGraph) := h_comps_fin.to_subtype
                let enum : Fin k ≃ graphComponents I.G.toGraph :=
                  (Finite.equivFinOfCardEq h_card_coe).symm
                let G_comp : Fin k → Graph I.S (Set I.S) := fun i => (enum i).1
                let Δ_part : Fin k → Set (Set I.S) := fun i => {δ ∈ I.Δ | δ ⊆ V(G_comp i)}
                have hinj_G : InjOn G_comp univ := by
                  intro i _ j _ heq
                  exact enum.injective (Subtype.ext heq)
                have hG_comps : graphComponents I.G.toGraph = range G_comp := by
                  ext C
                  simp only [mem_range, G_comp]
                  exact ⟨fun hC =>
                      ⟨enum.symm ⟨C, hC⟩, congrArg Subtype.val (enum.apply_symm_apply ⟨C, hC⟩)⟩,
                    by rintro ⟨i, rfl⟩; exact (enum i).2⟩
                have hΔ_cov : ∀ δ ∈ I.Δ, ∃ i : Fin k, δ ⊆ V(G_comp i) := by
                  intro δ hδ
                  obtain ⟨a, haδ⟩ := I.hΔ.2.1 δ hδ
                  have ha_bd : a ∈ I.G.V ∩ bd I.S := I.hΔ_eq ▸ ⟨δ, hδ, haδ⟩
                  let C_a := compOf I.G.toGraph a
                  have hCa_mem : C_a ∈ graphComponents I.G.toGraph :=
                    isGraphComponent_compOf ha_bd.1
                  let i := enum.symm ⟨C_a, hCa_mem⟩
                  have hGi_eq : G_comp i = C_a :=
                    congrArg Subtype.val (enum.apply_symm_apply ⟨C_a, hCa_mem⟩)
                  refine ⟨i, fun b hbδ => ?_⟩
                  by_contra hb_not
                  have hb_bd : b ∈ I.G.V ∩ bd I.S := I.hΔ_eq ▸ ⟨δ, hδ, hbδ⟩
                  let C_b := compOf I.G.toGraph b
                  have hCb_mem : C_b ∈ graphComponents I.G.toGraph :=
                    isGraphComponent_compOf hb_bd.1
                  have hCa_ne_Cb : C_a ≠ C_b := by
                    intro heq
                    apply hb_not
                    rw [hGi_eq, heq]
                    exact self_mem_reachSet hb_bd.1
                  exact h_split ⟨δ, hδ, C_a, hCa_mem, C_b, hCb_mem, hCa_ne_Cb,
                    ⟨a, haδ, self_mem_reachSet ha_bd.1⟩, ⟨b, hbδ, self_mem_reachSet hb_bd.1⟩⟩
                let I_sub : Fin k → DiscDivInstance.{u} := fun i =>
                  have hCi_mem : G_comp i ∈ graphComponents I.G.toGraph := (enum i).2
                  have hΔi_sub : Δ_part i ⊆ I.Δ := fun _ h => h.1
                  { S := I.S
                    hDisc := I.hDisc
                    G := induceDrawing I.G V(G_comp i)
                    hProper := induceDrawing_isProper I.G I.hProper hCi_mem.1.vertexSet_mono
                    Δ := Δ_part i
                    hΔ := ⟨I.hΔ.1.subset hΔi_sub, fun δ hδ => I.hΔ.2.1 δ hδ.1,
                      I.hΔ.2.2.subset hΔi_sub⟩
                    hΔ_eq := by
                      rw [induceDrawing_V I.G hCi_mem.1.vertexSet_mono]
                      ext x
                      simp only [divisionUnion, Δ_part, mem_sUnion, mem_ofPred_eq, mem_inter_iff]
                      constructor
                      · rintro ⟨δ, ⟨hδ, hδ_sub⟩, hxδ⟩
                        have hx_bd : x ∈ I.G.V ∩ bd I.S := I.hΔ_eq ▸ ⟨δ, hδ, hxδ⟩
                        exact ⟨hδ_sub hxδ, hx_bd.2⟩
                      · rintro ⟨hx_Ci, hx_bd⟩
                        have hx_union : x ∈ divisionUnion I.Δ :=
                          I.hΔ_eq.symm ▸ ⟨hCi_mem.1.vertexSet_mono hx_Ci, hx_bd⟩
                        obtain ⟨δ, hδ, hxδ⟩ := hx_union
                        obtain ⟨j, hj⟩ := hΔ_cov δ hδ
                        have heq_ij : G_comp i = G_comp j :=
                          hCi_mem.eq_of_mem_mem (enum j).2 hx_Ci (hj hxδ)
                        exact ⟨δ, ⟨hδ, heq_ij ▸ hj⟩, hxδ⟩ }
                have h_lt : ∀ i : Fin k, (I_sub i).measure < I.measure := by
                  intro i
                  have hCi_mem : G_comp i ∈ graphComponents I.G.toGraph := (enum i).2
                  have hSub_i : (induceDrawing I.G V(G_comp i)).IsSubdrawing I.G :=
                    induceDrawing_isSubdrawing I.G hCi_mem.1.vertexSet_mono
                  have hGi_V : (induceDrawing I.G V(G_comp i)).V = V(G_comp i) :=
                    induceDrawing_V I.G hCi_mem.1.vertexSet_mono
                  let j : Fin k := ⟨(i.1 + 1) % k, Nat.mod_lt _ (by omega)⟩
                  have hij : i ≠ j := by
                    intro heq
                    have hval : i.1 = (i.1 + 1) % k := congrArg Fin.val heq
                    have hi_lt : i.1 < k := i.2
                    by_cases h_last : i.1 + 1 = k
                    · rw [h_last, Nat.mod_self] at hval; omega
                    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
                  have hCj_mem : G_comp j ∈ graphComponents I.G.toGraph := (enum j).2
                  obtain ⟨w_j, hw_j⟩ := hCj_mem.2.1.1
                  have hw_j_G : w_j ∈ I.G.V := hCj_mem.1.vertexSet_mono hw_j
                  have hw_j_not : w_j ∉ (induceDrawing I.G V(G_comp i)).V := by
                    rw [hGi_V]
                    intro hw_i
                    have heq := hCi_mem.eq_of_mem_mem hCj_mem hw_i hw_j
                    exact hij (hinj_G trivial trivial heq)
                  have hV_lt : (induceDrawing I.G V(G_comp i)).V.ncard < I.G.V.ncard :=
                    ncard_lt_ncard ⟨hSub_i.1, fun h => hw_j_not (h hw_j_G)⟩ I.G.finite_V
                  have hR_le : (induceDrawing I.G V(G_comp i)).R.ncard ≤ I.G.R.ncard :=
                    disc_region_ncard_le_of_isSubdrawing I.hDisc I.hProper hSub_i
                  unfold DiscDivInstance.measure
                  dsimp only [I_sub]
                  omega
                have h_iff : I.IsFeasibleInst ↔ ∀ i : Fin k, (I_sub i).IsFeasibleInst := by
                  have h33iv := theorem_3_3_iv I.G I.Δ k G_comp Δ_part hk I.hΔ I.hΔ_eq
                    hinj_G hG_comps (fun _ => rfl) hΔ_cov
                  refine h33iv.trans (forall_congr' fun i => ?_)
                  have hCi_mem : G_comp i ∈ graphComponents I.G.toGraph := (enum i).2
                  unfold DiscDivInstance.IsFeasibleInst
                  dsimp only [I_sub]
                  rw [induceDrawing_toGraph_of_component I.G hCi_mem]
                let res := fun i : Fin k =>
                  ih (I_sub i).measure (hn ▸ h_lt i) (I_sub i) rfl
                exact ⟨List.all (List.ofFn (fun i => (res i).1)) id,
                  .step33iv I k hk I_sub h_lt h_iff (fun i => (res i).1) (fun i => (res i).2)⟩
    · exact ⟨false, .notCrossFree I hCF⟩

/-- Flattened reduction trace along a path of `Alg34Tree I b`:
a list of remaining measures `[m_1, ..., m_L]` at each reduction step (`L ≤ I.measure`). -/
noncomputable def Alg34Tree.traceSteps :
    {I : DiscDivInstance.{u}} → {b : Bool} → Alg34Tree I b → List ℕ
  | _, _, .notCrossFree _ _ => []
  | _, _, .emptyDiv _ _ => []
  | I, _, .step33i _ v hv sub =>
      (I.reduceSingleton v hv).measure :: sub.traceSteps
  | I, _, .step33ii _ C₀ hC₀ hC₀_disj sub =>
      (I.reduceInternalComp C₀ hC₀ hC₀_disj).measure :: sub.traceSteps
  | _, _, .step33iii _ _ _ _ _ _ _ _ _ _ => []
  | _, _, .step33iv _ k hk I_sub _ _ _ subs =>
      have hk0 : 0 < k := by omega
      (I_sub ⟨0, hk0⟩).measure :: (subs ⟨0, hk0⟩).traceSteps
  | _, _, .stepDual _ I_dual _ _ u hu sub =>
      (I_dual.reduceSingleton u hu).measure :: sub.traceSteps

theorem Alg34Tree.length_traceSteps_le :
    ∀ {I : DiscDivInstance.{u}} {b : Bool} (T : Alg34Tree I b),
      T.traceSteps.length ≤ I.measure
  | _, _, .notCrossFree _ _ => Nat.zero_le _
  | _, _, .emptyDiv _ _ => Nat.zero_le _
  | I, _, .step33i _ v hv sub => by
      simp only [traceSteps, List.length_cons]
      have hlt := I.reduceSingleton_measure_lt v hv
      have hle := sub.length_traceSteps_le
      omega
  | I, _, .step33ii _ C₀ hC₀ hC₀_disj sub => by
      simp only [traceSteps, List.length_cons]
      have hlt := I.reduceInternalComp_measure_lt C₀ hC₀ hC₀_disj
      have hle := sub.length_traceSteps_le
      omega
  | _, _, .step33iii _ _ _ _ _ _ _ _ _ _ => Nat.zero_le _
  | _, _, .step33iv _ k hk _ h_lt _ _ subs => by
      simp only [traceSteps, List.length_cons]
      have hk0 : 0 < k := by omega
      have hlt := h_lt ⟨0, hk0⟩
      have hle := (subs ⟨0, hk0⟩).length_traceSteps_le
      omega
  | _, _, .stepDual _ I_dual h_eq _ u hu sub => by
      simp only [traceSteps, List.length_cons]
      have hlt := I_dual.reduceSingleton_measure_lt u hu
      have hle := sub.length_traceSteps_le
      omega

theorem Alg34Tree.mem_traceSteps_lt :
    ∀ {I : DiscDivInstance.{u}} {b : Bool} (T : Alg34Tree I b) {m : ℕ},
      m ∈ T.traceSteps → m < I.measure
  | _, _, .notCrossFree _ _, _, hm => by simp [traceSteps] at hm
  | _, _, .emptyDiv _ _, _, hm => by simp [traceSteps] at hm
  | I, _, .step33i _ v hv sub, m, hm => by
      have hlt := I.reduceSingleton_measure_lt v hv
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hlt
      · exact lt_trans (sub.mem_traceSteps_lt hm') hlt
  | I, _, .step33ii _ C₀ hC₀ hC₀_disj sub, m, hm => by
      have hlt := I.reduceInternalComp_measure_lt C₀ hC₀ hC₀_disj
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hlt
      · exact lt_trans (sub.mem_traceSteps_lt hm') hlt
  | _, _, .step33iii _ _ _ _ _ _ _ _ _ _, _, hm => by simp [traceSteps] at hm
  | _, _, .step33iv _ k hk _ h_lt _ _ subs, m, hm => by
      have hk0 : 0 < k := by omega
      have hlt := h_lt ⟨0, hk0⟩
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hlt
      · exact lt_trans ((subs ⟨0, hk0⟩).mem_traceSteps_lt hm') hlt
  | I, _, .stepDual _ I_dual h_eq _ u hu sub, m, hm => by
      have hlt : (I_dual.reduceSingleton u hu).measure < I.measure :=
        h_eq ▸ I_dual.reduceSingleton_measure_lt u hu
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact hlt
      · exact lt_trans (sub.mem_traceSteps_lt hm') hlt

end GraphMinor.GM06
