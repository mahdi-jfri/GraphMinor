module

public import GraphMinor.GM13.Section7Six
public import GraphMinor.GM13.Section9b
public import GraphMinor.GM13.Section9
public import GraphMinor.GM07.ExplicitV
public import Mathlib.Computability.Partrec

import GraphMinor.GM12.Primrec

/-!
# Explicit, computable bounds for Graph Minors XIII, (7.7) and (9.1)–(9.6)

This file provides explicit, computable (`Computable`) bounds for **Graph Minors XIII, (7.7),
(9.1), (9.2), (9.3), and (9.6)** (N. Robertson and P. D. Seymour, *Graph Minors. XIII. The
disjoint paths problem*, J. Combin. Theory Ser. B **63** (1995), 65–110, pages 93–103):

- For each theorem `(N)` in `{7.7, 9.1, 9.2, 9.3, 9.6}`:
  - explicit bound functions parameterized by an arbitrary upper bound `V` on `GM07.vModel`
    (`theorem_7_7_boundL`, `theorem_7_7_boundMOf`, `theorem_9_1_boundK`, `theorem_9_1_boundROf`,
    `theorem_9_2_boundK`, `theorem_9_2_boundROf`, `theorem_9_3_boundK`, `theorem_9_3_boundROf`,
    `theorem_9_6_boundHOf`), together with `theorem_N_explicitOf` matching `GM13/Results.lean`
    word for word;
  - concrete bound functions instantiated at `GM07.vModelExplicit` (`theorem_7_7_boundM`,
    `theorem_9_1_boundR`, `theorem_9_2_boundR`, `theorem_9_3_boundR`, `theorem_9_6_boundH`), each
    proved `Computable` via primitive recursion (`Primrec`);
  - `theorem_N_explicit_of (hW : GM07.WExplicitStatement)`: the exact statement of `theorem_N` in
    `GM13/Results.lean` with the concrete bound functions in place of the existential witnesses.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical Graph SimpleGraph GraphMinor GraphMinor.Surface GraphMinor.GM09
  GraphMinor.GM16

universe u v

/-! ## 1. Concrete bound definitions at `GM07.vModelExplicit` -/

/-- Concrete star-separation bound `m` for **Graph Minors XIII, (7.7)** (page 93), instantiated at
`GM07.vModelExplicit`. -/
def theorem_7_7_boundM (p : ℕ) : ℕ :=
  theorem_7_7_boundMOf GM07.vModelExplicit p

/-- Concrete subwall distance bound `r` for **Graph Minors XIII, (9.1)** (page 98), instantiated
at `GM07.vModelExplicit`. -/
def theorem_9_1_boundR (p : ℕ) : ℕ :=
  theorem_9_1_boundROf GM07.vModelExplicit p

/-- Concrete subwall distance bound `r` for **Graph Minors XIII, (9.2)** (page 99), instantiated
at `GM07.vModelExplicit`. -/
def theorem_9_2_boundR (l m p : ℕ) : ℕ :=
  theorem_9_2_boundROf GM07.vModelExplicit l m p

/-- Concrete subwall distance bound `r` for **Graph Minors XIII, (9.3)** (page 101), instantiated
at `GM07.vModelExplicit`. -/
def theorem_9_3_boundR (p : ℕ) : ℕ :=
  theorem_9_3_boundROf GM07.vModelExplicit p

/-- Concrete wall height `h'` for **Graph Minors XIII, (9.6)** (page 103), instantiated at
`GM07.vModelExplicit`. -/
def theorem_9_6_boundH (p s h : ℕ) : ℕ :=
  theorem_9_6_boundHOf GM07.vModelExplicit p s h

/-! ## 2. Explicit theorems parameterized by `V ≥ GM07.vModel` -/

/-- **Graph Minors XIII, (7.7)** (page 93) with explicit bounds `theorem_7_7_boundL p` and
`theorem_7_7_boundMOf V p`, parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_7_7_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p : ℕ) (h1 : 2 ≤ p) :
    3 ≤ theorem_7_7_boundL p ∧ ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β),
    H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
    (∀ a, IsLMStarOver G H (theorem_7_7_boundL p) (theorem_7_7_boundMOf V p) (S a) (v a)) →
    Function.Injective v →
    HasGraphModel (GM16.completeGraph p) G :=
  ⟨three_le_theorem_7_7_boundL p, theorem_7_7_explicitBound.{u, v} V hV p h1⟩

/-- **Graph Minors XIII, (9.1)** (page 98) with explicit bounds `theorem_9_1_boundK p` and
`theorem_9_1_boundROf V p`, parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_9_1_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p : ℕ) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin (theorem_9_1_boundK p) → Wall α β)
      (P Q : Fin (theorem_9_1_boundK p) → Graph α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin (theorem_9_1_boundK p), (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin (theorem_9_1_boundK p), i ≠ j →
        theorem_9_1_boundROf V p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∀ i : Fin (theorem_9_1_boundK p), IsCrossOverWall G (H_sub i) (P i) (Q i)) →
      (∀ i : Fin (theorem_9_1_boundK p), (V(P i) ∪ V(Q i)) ∩ V(H.graph) ⊆ V((H_sub i).graph)) →
      Pairwise (fun i j : Fin (theorem_9_1_boundK p) =>
        Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))) →
      HasGraphModel (GM16.completeGraph p) G :=
  theorem_9_1_explicitBound.{u, v} V hV p

/-- **Graph Minors XIII, (9.2)** (page 99) with explicit bounds `theorem_9_2_boundK l m p` and
`theorem_9_2_boundROf V l m p`, parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_9_2_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (l m p : ℕ) (hl : 3 ≤ l) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin (theorem_9_2_boundK l m p) → Wall α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin (theorem_9_2_boundK l m p), IsNonDividingSubwall G H.toWall (H_sub i)) →
      (∀ i j : Fin (theorem_9_2_boundK l m p), i ≠ j →
        theorem_9_2_boundROf V l m p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v) ∨
        HasGraphModel (GM16.completeGraph p) G :=
  theorem_9_2_explicitBound.{u, v} V hV l m p hl

/-- **Graph Minors XIII, (9.3)** (page 101) with explicit bounds `theorem_9_3_boundK p` and
`theorem_9_3_boundROf V p`, parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_9_3_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p : ℕ) :
    ∀ {α : Type u} {β : Type v} {t : ℕ} {G : Graph α β} {H : DrawnWall α β}
      (H_sub : Fin t → Wall α β),
      H.IsFigure1 →
      H.graph ≤ G →
      (∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin t, i ≠ j →
        theorem_9_3_boundROf V p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (I : Finset (Fin t)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          t - theorem_9_3_boundK p ≤ I.card ∧
          ∀ i ∈ I, IsDividingSubwall
            (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) :=
  theorem_9_3_explicitBound.{u, v} V hV p

/-- **Graph Minors XIII, (9.6)** (page 103) with explicit exact wall height
`theorem_9_6_boundHOf V p s h`, parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_9_6_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (p s h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    p ^ 2 + 2 ≤ theorem_9_6_boundHOf V p s h ∧ Even (theorem_9_6_boundHOf V p s h) ∧
    ∀ {α : Type u} {β : Type v} {G : Graph α β} {H : Wall α β},
      H.graph ≤ G →
      H.height = theorem_9_6_boundHOf V p s h →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (H_flat : Fin s → Wall α β),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
          ∀ a : Fin s,
            IsProperSubwallOf (H_flat a) H ∧
            (H_flat a).height = h ∧
            IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
            IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
            Disjoint V((H_flat a).graph) X :=
  theorem_9_6_explicitBound.{u, v} V hV p s h h2 heven

/-! ## 3. Concrete explicit theorems assuming `GM07.WExplicitStatement` -/

/-- **Graph Minors XIII, (7.7)** (page 93) with the explicit, computable bounds
`theorem_7_7_boundL p` and `theorem_7_7_boundM p`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_7_7_explicit_of (hW : GM07.WExplicitStatement) (p : ℕ) (h1 : 2 ≤ p) :
    3 ≤ theorem_7_7_boundL p ∧ ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β),
    H.IsFigure1 → IsWallIn G H.toWall →
    ∀ (S : Fin (p.choose 2) → Graph α β) (v : Fin (p.choose 2) → α),
    (∀ a, IsLMStarOver G H (theorem_7_7_boundL p) (theorem_7_7_boundM p) (S a) (v a)) →
    Function.Injective v →
    HasGraphModel (GM16.completeGraph p) G :=
  theorem_7_7_explicitOf.{u, v} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) p h1

/-- **Graph Minors XIII, (9.1)** (page 98) with the explicit, computable bounds
`theorem_9_1_boundK p` and `theorem_9_1_boundR p`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_9_1_explicit_of (hW : GM07.WExplicitStatement) (p : ℕ) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin (theorem_9_1_boundK p) → Wall α β)
      (P Q : Fin (theorem_9_1_boundK p) → Graph α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin (theorem_9_1_boundK p), (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin (theorem_9_1_boundK p), i ≠ j →
        theorem_9_1_boundR p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∀ i : Fin (theorem_9_1_boundK p), IsCrossOverWall G (H_sub i) (P i) (Q i)) →
      (∀ i : Fin (theorem_9_1_boundK p), (V(P i) ∪ V(Q i)) ∩ V(H.graph) ⊆ V((H_sub i).graph)) →
      Pairwise (fun i j : Fin (theorem_9_1_boundK p) =>
        Disjoint (V(P i) ∪ V(Q i)) (V(P j) ∪ V(Q j))) →
      HasGraphModel (GM16.completeGraph p) G :=
  theorem_9_1_explicitOf.{u, v} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) p

/-- **Graph Minors XIII, (9.2)** (page 99) with the explicit, computable bounds
`theorem_9_2_boundK l m p` and `theorem_9_2_boundR l m p`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_9_2_explicit_of (hW : GM07.WExplicitStatement) (l m p : ℕ) (hl : 3 ≤ l) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (H : DrawnWall α β)
      (H_sub : Fin (theorem_9_2_boundK l m p) → Wall α β),
      H.IsFigure1 →
      IsWallIn G H.toWall →
      (∀ i : Fin (theorem_9_2_boundK l m p), IsNonDividingSubwall G H.toWall (H_sub i)) →
      (∀ i j : Fin (theorem_9_2_boundK l m p), i ≠ j →
        theorem_9_2_boundR l m p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      (∃ (S : Graph α β) (v : α), IsLMStarOver G H l m S v) ∨
        HasGraphModel (GM16.completeGraph p) G :=
  theorem_9_2_explicitOf.{u, v} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) l m p hl

/-- **Graph Minors XIII, (9.3)** (page 101) with the explicit, computable bounds
`theorem_9_3_boundK p` and `theorem_9_3_boundR p`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_9_3_explicit_of (hW : GM07.WExplicitStatement) (p : ℕ) :
    ∀ {α : Type u} {β : Type v} {t : ℕ} {G : Graph α β} {H : DrawnWall α β}
      (H_sub : Fin t → Wall α β),
      H.IsFigure1 →
      H.graph ≤ G →
      (∀ i : Fin t, (H_sub i).IsSubwallOf H.toWall) →
      (∀ i j : Fin t, i ≠ j →
        theorem_9_3_boundR p ≤ wallSubgraphDist H (H_sub i).graph (H_sub j).graph) →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (I : Finset (Fin t)),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          t - theorem_9_3_boundK p ≤ I.card ∧
          ∀ i ∈ I, IsDividingSubwall
            (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H.toWall (H_sub i) :=
  theorem_9_3_explicitOf.{u, v} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) p

/-- **Graph Minors XIII, (9.6)** (page 103) with the explicit, computable exact wall height
`theorem_9_6_boundH p s h`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_9_6_explicit_of (hW : GM07.WExplicitStatement)
    (p s h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    p ^ 2 + 2 ≤ theorem_9_6_boundH p s h ∧ Even (theorem_9_6_boundH p s h) ∧
    ∀ {α : Type u} {β : Type v} {G : Graph α β} {H : Wall α β},
      H.graph ≤ G →
      H.height = theorem_9_6_boundH p s h →
      HasGraphModel (GM16.completeGraph p) G ∨
        ∃ (X : Set α) (H_flat : Fin s → Wall α β),
          X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
          Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
          ∀ a : Fin s,
            IsProperSubwallOf (H_flat a) H ∧
            (H_flat a).height = h ∧
            IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
            IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
            Disjoint V((H_flat a).graph) X :=
  theorem_9_6_explicitOf.{u, v} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) p s h h2
    heven

/-! ## 4. Primitive recursiveness and computability of all concrete bounds -/

section Computability

open GM12.PrimrecHelpers

private lemma primrec_theorem_7_4_bound {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_7_4_bound GM07.vModelExplicit (p x) := by
  unfold theorem_7_4_bound
  exact primrec_add
    (primrec_mul (Primrec.const 4)
      (primrec_gm12_4_4 (Primrec.const 0) (Primrec.const 0) hp))
    (Primrec.const 5)

private lemma primrec_theorem_7_5_bound {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_7_5_bound GM07.vModelExplicit (p x) := by
  unfold theorem_7_5_bound
  exact primrec_mul (Primrec.const 2) (primrec_theorem_7_4_bound hp)

private lemma primrec_theorem_7_7_boundL {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_7_7_boundL (p x) := by
  unfold theorem_7_7_boundL
  have hc : Primrec fun x => (p x).choose 2 := primrec_choose_two hp
  exact primrec_add
    (primrec_sub (primrec_mul (Primrec.const 2) (primrec_pow hc (Primrec.const 2))) hc)
    (Primrec.const 3)

private lemma primrec_theorem_7_7_boundM {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_7_7_boundM (p x) := by
  unfold theorem_7_7_boundM theorem_7_7_boundMOf
  exact primrec_add
    (primrec_max (primrec_theorem_7_5_bound hp) (Primrec.const 3))
    (primrec_mul (Primrec.const 4) (primrec_choose_two hp))

private lemma primrec_theorem_9_1_boundK {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_9_1_boundK (p x) := by
  unfold theorem_9_1_boundK
  exact primrec_add (primrec_max (primrec_gm12_4_5_k hp) (Primrec.const 1)) (Primrec.const 1)

private lemma primrec_theorem_9_1_boundR {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_9_1_boundR (p x) := by
  unfold theorem_9_1_boundR theorem_9_1_boundROf
  exact primrec_add
    (primrec_mul (Primrec.const 12)
      (primrec_add
        (primrec_mul (Primrec.const 4)
          (primrec_gm12_4_5_N (Primrec.const 0) (Primrec.const 0) hp))
        (Primrec.const 32)))
    (Primrec.const 26)

private lemma primrec_r_hole_9_2 {α : Type} [Primcodable α] {r₁ : α → ℕ} (hr : Primrec r₁) :
    Primrec fun x => r_hole_9_2 (r₁ x) := by
  unfold r_hole_9_2
  exact primrec_add (primrec_mul (Primrec.const 8) hr) (Primrec.const 200)

private lemma primrec_R_s_9_2 {α : Type} [Primcodable α] {r₁ : α → ℕ} (hr : Primrec r₁) :
    Primrec fun x => R_s_9_2 (r₁ x) := by
  unfold R_s_9_2
  exact primrec_add
    (primrec_mul (Primrec.const 8)
      (primrec_add (primrec_mul (Primrec.const 4) (primrec_r_hole_9_2 hr)) (Primrec.const 6)))
    (Primrec.const 200)

private lemma primrec_theorem_9_2_boundK {α : Type} [Primcodable α]
    {l m p : α → ℕ} (hl : Primrec l) (hp : Primrec p) :
    Primrec fun x => theorem_9_2_boundK (l x) (m x) (p x) := by
  unfold theorem_9_2_boundK
  have hc : Primrec fun x => (p x).choose 2 := primrec_choose_two hp
  have hn₁ : Primrec fun x => 3 * (p x).choose 2 := primrec_mul (Primrec.const 3) hc
  have hn₂ : Primrec fun x => theorem_9_1_boundK (p x) + 1 :=
    primrec_add (primrec_theorem_9_1_boundK hp) (Primrec.const 1)
  have hn₃ : Primrec fun x => 4 * (p x).choose 2 + 1 :=
    primrec_add (primrec_mul (Primrec.const 4) hc) (Primrec.const 1)
  exact primrec_mul
    (primrec_add hn₂ (primrec_mul hn₁ (primrec_add hn₃ (Primrec.const 1))))
    (primrec_pow (primrec_sub hl (Primrec.const 1)) (Primrec.const 2))

private lemma primrec_theorem_9_2_boundR {α : Type} [Primcodable α]
    {l m p : α → ℕ} (hm : Primrec m) (hp : Primrec p) :
    Primrec fun x => theorem_9_2_boundR (l x) (m x) (p x) := by
  unfold theorem_9_2_boundR theorem_9_2_boundROf
  have hr₀ : Primrec fun x => theorem_7_4_bound GM07.vModelExplicit (p x) :=
    primrec_theorem_7_4_bound hp
  have hr₁ : Primrec fun x => 2 * theorem_7_4_bound GM07.vModelExplicit (p x) :=
    primrec_mul (Primrec.const 2) hr₀
  have hr₉₁ : Primrec fun x => theorem_9_1_boundROf GM07.vModelExplicit (p x) :=
    primrec_theorem_9_1_boundR hp
  have h1 : Primrec fun x =>
      theorem_7_4_bound GM07.vModelExplicit (p x) +
        2 * R_s_9_2 (2 * theorem_7_4_bound GM07.vModelExplicit (p x)) +
        4 * r_hole_9_2 (2 * theorem_7_4_bound GM07.vModelExplicit (p x)) + 10 :=
    primrec_add
      (primrec_add
        (primrec_add hr₀ (primrec_mul (Primrec.const 2) (primrec_R_s_9_2 hr₁)))
        (primrec_mul (Primrec.const 4) (primrec_r_hole_9_2 hr₁)))
      (Primrec.const 10)
  have h2 : Primrec fun x =>
      theorem_9_1_boundROf GM07.vModelExplicit (p x) +
        12 * (2 * theorem_7_4_bound GM07.vModelExplicit (p x)) + 64 :=
    primrec_add (primrec_add hr₉₁ (primrec_mul (Primrec.const 12) hr₁)) (Primrec.const 64)
  exact primrec_max hm (primrec_max h1 h2)

private lemma primrec_theorem_9_3_boundK {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_9_3_boundK (p x) := by
  unfold theorem_9_3_boundK
  exact primrec_theorem_9_2_boundK (primrec_theorem_7_7_boundL hp) hp

private lemma primrec_theorem_9_3_boundR {α : Type} [Primcodable α] {p : α → ℕ} (hp : Primrec p) :
    Primrec fun x => theorem_9_3_boundR (p x) := by
  unfold theorem_9_3_boundR theorem_9_3_boundROf
  exact primrec_theorem_9_2_boundR (primrec_theorem_7_7_boundM hp) hp

private lemma primrec_theorem_9_6_boundH {α : Type} [Primcodable α]
    {p s h : α → ℕ} (hp : Primrec p) (hs : Primrec s) (hh : Primrec h) :
    Primrec fun x => theorem_9_6_boundH (p x) (s x) (h x) := by
  unfold theorem_9_6_boundH theorem_9_6_boundHOf
  have hk₁ : Primrec fun x => theorem_9_3_boundK (p x) := primrec_theorem_9_3_boundK hp
  have hr₁ : Primrec fun x => theorem_9_3_boundROf GM07.vModelExplicit (p x) :=
    primrec_theorem_9_3_boundR hp
  have hk₂ : Primrec fun x => theorem_9_1_boundK (p x) := primrec_theorem_9_1_boundK hp
  have hr₂ : Primrec fun x => theorem_9_1_boundROf GM07.vModelExplicit (p x) :=
    primrec_theorem_9_1_boundR hp
  have ht : Primrec fun x =>
      s x + theorem_9_3_boundK (p x) + theorem_9_1_boundK (p x) + (p x).choose 2 + 1 :=
    primrec_add (primrec_add (primrec_add (primrec_add hs hk₁) hk₂) (primrec_choose_two hp))
      (Primrec.const 1)
  have hr : Primrec fun x =>
      h x + max (theorem_9_3_boundROf GM07.vModelExplicit (p x))
        (max (theorem_9_1_boundROf GM07.vModelExplicit (p x)) 1) + 4 :=
    primrec_add
      (primrec_add hh (primrec_max hr₁ (primrec_max hr₂ (Primrec.const 1))))
      (Primrec.const 4)
  exact primrec_mul (Primrec.const 2)
    (primrec_add (primrec_add (primrec_mul ht hr) (primrec_pow hp (Primrec.const 2)))
      (Primrec.const 2))

/-- `theorem_7_7_boundL` is computable (in fact primitive recursive). -/
theorem theorem_7_7_boundL_computable : Computable theorem_7_7_boundL :=
  (primrec_theorem_7_7_boundL Primrec.id).to_comp

/-- `theorem_7_7_boundM` is computable (in fact primitive recursive). -/
theorem theorem_7_7_boundM_computable : Computable theorem_7_7_boundM :=
  (primrec_theorem_7_7_boundM Primrec.id).to_comp

/-- `theorem_9_1_boundK` is computable (in fact primitive recursive). -/
theorem theorem_9_1_boundK_computable : Computable theorem_9_1_boundK :=
  (primrec_theorem_9_1_boundK Primrec.id).to_comp

/-- `theorem_9_1_boundR` is computable (in fact primitive recursive). -/
theorem theorem_9_1_boundR_computable : Computable theorem_9_1_boundR :=
  (primrec_theorem_9_1_boundR Primrec.id).to_comp

/-- `theorem_9_2_boundK` is computable (in fact primitive recursive). -/
theorem theorem_9_2_boundK_computable :
    Computable fun x : ℕ × ℕ × ℕ => theorem_9_2_boundK x.1 x.2.1 x.2.2 :=
  (primrec_theorem_9_2_boundK Primrec.fst (Primrec.snd.comp Primrec.snd)).to_comp

/-- `theorem_9_2_boundR` is computable (in fact primitive recursive). -/
theorem theorem_9_2_boundR_computable :
    Computable fun x : ℕ × ℕ × ℕ => theorem_9_2_boundR x.1 x.2.1 x.2.2 :=
  (primrec_theorem_9_2_boundR (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp

/-- `theorem_9_3_boundK` is computable (in fact primitive recursive). -/
theorem theorem_9_3_boundK_computable : Computable theorem_9_3_boundK :=
  (primrec_theorem_9_3_boundK Primrec.id).to_comp

/-- `theorem_9_3_boundR` is computable (in fact primitive recursive). -/
theorem theorem_9_3_boundR_computable : Computable theorem_9_3_boundR :=
  (primrec_theorem_9_3_boundR Primrec.id).to_comp

/-- `theorem_9_6_boundH` is computable (in fact primitive recursive). -/
theorem theorem_9_6_boundH_computable :
    Computable fun x : ℕ × ℕ × ℕ => theorem_9_6_boundH x.1 x.2.1 x.2.2 :=
  (primrec_theorem_9_6_boundH Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.snd.comp Primrec.snd)).to_comp

end Computability

end GraphMinor.GM13
