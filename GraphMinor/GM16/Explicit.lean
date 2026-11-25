module

public import GraphMinor.GM16.InductionsProved
public import GraphMinor.GM16.Section1Proof
public import GraphMinor.GM16.Section2
public import GraphMinor.GM07.ExplicitV
public import Mathlib.Computability.Partrec

import GraphMinor.GM12.Primrec
import GraphMinor.GM12.Bridge

/-!
# Explicit, computable bounds for Graph Minors XVI, (3.1) and (1.3)

This file provides explicit, computable (`Computable`, via `Primrec`) bounds for
**Graph Minors XVI, (3.1)** (pages 49 and 54) and **Graph Minors XVI, (1.3)** (pages 46 and 51–52)
of N. Robertson and P. D. Seymour, *Graph Minors. XVI. Excluding a non-planar graph*,
J. Combin. Theory Ser. B **89** (2003), 43–76:

1. Computability of `theorem_3_1_bound GM07.vModelExplicit`:
   `primrec_theorem_3_1_bound` and `theorem_3_1_bound_computable`.
2. **Graph Minors XVI, (3.1)** under `GM07.WExplicitStatement`: `theorem_3_1_explicit_of`.
3. **Graph Minors XVI, (1.3)** with explicit `(r, d, w₀)`:
   `theorem_1_3_bound`, `primrec_theorem_1_3_bound`, `theorem_1_3_bound_computable`,
   `theorem_1_3_explicitOf`, and `theorem_1_3_explicit_of`.
4. Bounded-adhesion tree-decomposition form of **Graph Minors XVI, (1.3)** with explicit
   `(adh, w₀, g, d, r)`:
   `theorem_1_3_treeDecomp_boundOf`, `theorem_1_3_treeDecomp_bound`,
   `primrec_theorem_1_3_treeDecomp_bound`, `theorem_1_3_treeDecomp_bound_computable`,
   `theorem_1_3_treeDecomp_explicitOf`, and `theorem_1_3_treeDecomp_explicit_of`,
   together with `exists_cliqueFilledTorso_of_treeDecomposition` (`GM16/Section2.lean`).
-/

@[expose] public section

namespace GraphMinor.GM16

open Set Function Topology Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM15

universe u v w u' v'

/-! ## 1. Primitive recursiveness and computability of `theorem_3_1_bound` -/

section Computability31

open GM12.PrimrecHelpers

/-- `GM20.Draw.drawBound` is primitive recursive. -/
theorem primrec_drawBound {α : Type} [Primcodable α] {e : α → ℕ} (he : Primrec e) :
    Primrec fun x => GM20.Draw.drawBound (e x) := by
  unfold GM20.Draw.drawBound
  exact primrec_max (Primrec.const 2)
    (primrec_mul he (primrec_sub (primrec_mul (Primrec.const 2) he) (Primrec.const 1)))

private lemma primrec_properEyeStep {α : Type} [Primcodable α]
    {φ μ lam θ : α → ℕ} (hφ : Primrec φ) (hμ : Primrec μ) (hθ : Primrec θ) :
    Primrec fun x => properEyeStep (φ x) (μ x) (lam x) (θ x) := by
  unfold properEyeStep
  have hθ'' : Primrec fun x => 2 * (θ x + 3 * μ x + 8) :=
    primrec_mul (Primrec.const 2)
      (primrec_add (primrec_add hθ (primrec_mul (Primrec.const 3) hμ)) (Primrec.const 8))
  have hτ₁ : Primrec fun x => 4 + μ x / 2 :=
    primrec_add (Primrec.const 4) (primrec_div hμ (Primrec.const 2))
  have hτ₂ : Primrec fun x => 6 + 2 * (θ x + 3 * μ x + 8) / 2 :=
    primrec_add (Primrec.const 6) (primrec_div hθ'' (Primrec.const 2))
  have hπ : Primrec fun x =>
      (φ x - 1) * (2 * (4 + μ x / 2) + (6 + 2 * (θ x + 3 * μ x + 8) / 2) - 7) :=
    primrec_mul (primrec_sub hφ (Primrec.const 1))
      (primrec_sub (primrec_add (primrec_mul (Primrec.const 2) hτ₁) hτ₂) (Primrec.const 7))
  have hbeta : Primrec fun x =>
      2 * ((φ x - 1) * (2 * (4 + μ x / 2) + (6 + 2 * (θ x + 3 * μ x + 8) / 2) - 7)) + 8 :=
    primrec_add (primrec_mul (Primrec.const 2) hπ) (Primrec.const 8)
  exact (primrec_add (primrec_mul (Primrec.const 3) hπ) (Primrec.const 9)).pair
    ((primrec_mul (Primrec.const 20) hbeta).pair (primrec_mul (Primrec.const 100) hbeta))

private lemma primrec_properArrangementBound {α : Type} [Primcodable α]
    {κ φ μ : α → ℕ} (hκ : Primrec κ) (hφ : Primrec φ) (hμ : Primrec μ) :
    Primrec fun x => properArrangementBound (κ x) (φ x) (μ x) := by
  unfold properArrangementBound
  have hμ' : Primrec fun x => 2 * (μ x + 6) :=
    primrec_mul (Primrec.const 2) (primrec_add hμ (Primrec.const 6))
  have hφ' : Primrec fun x => max (φ x) 8 := primrec_max hφ (Primrec.const 8)
  have hθtop : Primrec fun x => max (max (φ x) 8) (4 * 4 + 2 * (μ x + 6) + 2) :=
    primrec_max hφ' (primrec_add (primrec_add (Primrec.const 16) hμ') (Primrec.const 2))
  have hstep : Primrec₂ fun (x : α) (st : ℕ × ℕ × ℕ) =>
      properEyeIndStep (max (φ x) 8) (2 * (μ x + 6)) st := by
    refine Primrec₂.mk ?_
    unfold properEyeIndStep
    have hpe : Primrec fun q : α × ℕ × ℕ × ℕ =>
        properEyeStep (max (φ q.1) 8) (2 * (μ q.1 + 6)) q.2.2.1 q.2.2.2 :=
      primrec_properEyeStep (hφ'.comp Primrec.fst) (hμ'.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hlam : Primrec fun q : α × ℕ × ℕ × ℕ =>
        max (properEyeStep (max (φ q.1) 8) (2 * (μ q.1 + 6)) q.2.2.1 q.2.2.2).2.1 4 :=
      primrec_max (Primrec.fst.comp (Primrec.snd.comp hpe)) (Primrec.const 4)
    exact (primrec_max (Primrec.fst.comp hpe) (Primrec.fst.comp Primrec.snd)).pair
      (hlam.pair (primrec_max (Primrec.snd.comp (Primrec.snd.comp hpe))
        (primrec_add (primrec_add (primrec_mul (Primrec.const 4) hlam) (hμ'.comp Primrec.fst))
          (Primrec.const 2))))
  have hres : Primrec fun x =>
      Nat.iterate (properEyeIndStep (max (φ x) 8) (2 * (μ x + 6))) (κ x + 1)
        (0, 4, max (max (φ x) 8) (4 * 4 + 2 * (μ x + 6) + 2)) :=
    Primrec.nat_iterate (primrec_add hκ (Primrec.const 1))
      ((Primrec.const 0).pair ((Primrec.const 4).pair hθtop)) hstep
  exact (primrec_max (Primrec.snd.comp (Primrec.snd.comp hres))
      (primrec_add
        (primrec_add (primrec_mul (Primrec.const 4) (Primrec.fst.comp (Primrec.snd.comp hres))) hμ')
        (Primrec.const 2))).pair
    ((Primrec.fst.comp (Primrec.snd.comp hres)).pair (Primrec.fst.comp hres))

private lemma primrec_section9Beta {α : Type} [Primcodable α]
    {δ φ ψ : α → ℕ} (hδ : Primrec δ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => section9Beta (δ x) (φ x) (ψ x) := by
  unfold section9Beta
  have hκ : Primrec fun x => δ x ^ 2 * φ x ^ 2 / 2 + 1 :=
    primrec_add
      (primrec_div
        (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ (Primrec.const 2)))
        (Primrec.const 2))
      (Primrec.const 1)
  exact primrec_mul (Primrec.const 2)
    (primrec_div (primrec_add (primrec_mul hκ (primrec_add hψ (Primrec.const 6))) (Primrec.const 1))
      (Primrec.const 2))

private lemma primrec_gm16_7_1_theta {α : Type} [Primcodable α]
    {χ δ lam θreq φ ψ : α → ℕ}
    (hχ : Primrec χ) (hδ : Primrec δ) (hlam : Primrec lam)
    (hθreq : Primrec θreq) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => theorem_7_1_theta (χ x) (δ x) (lam x) (θreq x) (φ x) (ψ x) := by
  unfold theorem_7_1_theta theorem_8_1_gamma theorem_8_1_theta theorem_8_3_bound
  have hβ := primrec_section9Beta hδ hφ hψ
  have hγ : Primrec fun x => 3 * section9Beta (δ x) (φ x) (ψ x) + 3 :=
    primrec_add (primrec_mul (Primrec.const 3) hβ) (Primrec.const 3)
  have hθ₁ : Primrec fun x =>
      12 * (δ x + 3) * (section9Beta (δ x) (φ x) (ψ x) + 1) + 4 * φ x + 8 :=
    primrec_add
      (primrec_add
        (primrec_mul (primrec_mul (Primrec.const 12) (primrec_add hδ (Primrec.const 3)))
          (primrec_add hβ (Primrec.const 1)))
        (primrec_mul (Primrec.const 4) hφ))
      (Primrec.const 8)
  have hζ : Primrec fun x => χ x + δ x ^ 2 * φ x ^ 2 / 2 :=
    primrec_add hχ
      (primrec_div
        (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ (Primrec.const 2)))
        (Primrec.const 2))
  have hlow : Primrec fun x => max (θreq x + (χ x + δ x ^ 2 * φ x ^ 2 / 2)) (4 * ψ x + 2) :=
    primrec_max (primrec_add hθreq hζ) (primrec_add (primrec_mul (Primrec.const 4) hψ) (Primrec.const 2))
  have hθ₂ : Primrec fun x =>
      max (θreq x + (χ x + δ x ^ 2 * φ x ^ 2 / 2)) (4 * ψ x + 2) +
        4 * ψ x + 10 * lam x + 3 * (χ x + δ x ^ 2 * φ x ^ 2 / 2) + 31 :=
    primrec_add
      (primrec_add
        (primrec_add (primrec_add hlow (primrec_mul (Primrec.const 4) hψ))
          (primrec_mul (Primrec.const 10) hlam))
        (primrec_mul (Primrec.const 3) hζ))
      (Primrec.const 31)
  exact primrec_add
    (primrec_add
      (primrec_add (primrec_add hχ hθ₁) (primrec_mul (Primrec.const 3) hγ))
      (primrec_mul (primrec_add (primrec_mul (Primrec.const 4) hγ) (Primrec.const 2)) hδ))
    hθ₂

private lemma primrec_gm16_7_2 {α : Type} [Primcodable α]
    {a b p φ μ : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p)
    (hφ : Primrec φ) (hμ : Primrec μ) :
    Primrec fun x => theorem_7_2_bound GM07.vModelExplicit (a x) (b x) (p x) (φ x) (μ x) := by
  unfold theorem_7_2_bound
  have hp4 : Primrec fun x => max (p x) 4 := primrec_max hp (Primrec.const 4)
  have hκ := primrec_gm12_4_5_k hp4
  have hφ₁ := primrec_gm12_4_5_N ha hb hp4
  have hφ₂ := primrec_max hφ hφ₁
  have hres := primrec_properArrangementBound hκ hφ₂ hμ
  have hlam : Primrec fun x =>
      (properArrangementBound (GM12.theorem_4_5_kBound (max (p x) 4))
        (max (φ x) (GM12.theorem_4_5_NBound GM07.vModelExplicit (a x) (b x) (max (p x) 4)))
        (μ x)).2.1 + μ x + 2 :=
    primrec_add (primrec_add (Primrec.fst.comp (Primrec.snd.comp hres)) hμ) (Primrec.const 2)
  have hθ := primrec_max (primrec_max (Primrec.fst.comp hres) hp4)
    (primrec_add (primrec_mul (Primrec.const 4) hlam) (Primrec.const 3))
  exact hκ.pair (hlam.pair ((Primrec.snd.comp (Primrec.snd.comp hres)).pair hθ))

private lemma primrec_gm16_6_1 {α : Type} [Primcodable α]
    {a b p τ χ δ φ ψ : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hτ : Primrec τ)
    (hχ : Primrec χ) (hδ : Primrec δ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x =>
      theorem_6_1_bound GM07.vModelExplicit (a x) (b x) (p x) (τ x) (χ x) (δ x) (φ x) (ψ x) := by
  unfold theorem_6_1_bound theorem_7_1_sigma
  have hφ' := primrec_max hφ (Primrec.const 3)
  have hψ' := primrec_max hψ (Primrec.const 3)
  have hres72 := primrec_gm16_7_2 ha hb hp hφ' (primrec_mul (Primrec.const 2) hψ')
  have hθ' := primrec_max (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres72))) hp
  have hθ := primrec_gm16_7_1_theta hχ hδ (Primrec.fst.comp (Primrec.snd.comp hres72)) hθ' hφ' hψ'
  have hζ := primrec_add hχ
    (primrec_div
      (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ' (Primrec.const 2)))
      (Primrec.const 2))
  have hσ := primrec_add (primrec_add hδ hτ) hζ
  exact hσ.pair ((Primrec.fst.comp hres72).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres72))).pair (hζ.pair hθ)))

private lemma primrec_gm16_5_1 {α : Type} [Primcodable α]
    {a b p τ χ φ ψ : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hτ : Primrec τ)
    (hχ : Primrec χ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x =>
      theorem_5_1_bound GM07.vModelExplicit (a x) (b x) (p x) (τ x) (χ x) (φ x) (ψ x) := by
  unfold theorem_5_1_bound theorem_6_3_delta theorem_6_3_theta
  have hδ : Primrec fun x => 2 * (p x * (p x - 1) / 2) ^ 2 * max (τ x) 2 ^ 2 :=
    primrec_mul (primrec_mul (Primrec.const 2)
      (primrec_pow (primrec_div (primrec_mul hp (primrec_sub hp (Primrec.const 1))) (Primrec.const 2))
        (Primrec.const 2)))
      (primrec_pow (primrec_max hτ (Primrec.const 2)) (Primrec.const 2))
  have hinit : Primrec fun x => (τ x + 1, 0, 0, 0,
      5 * max (ψ x) (max 3 (GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x))) + 34) :=
    (primrec_add hτ (Primrec.const 1)).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair
        (primrec_add (primrec_mul (Primrec.const 5)
          (primrec_max hψ (primrec_max (Primrec.const 3) (primrec_gm12_4_4 ha hb hp))))
          (Primrec.const 34)))))
  refine primrec_natRec hδ hinit ?_
  unfold theorem_5_1_step
  have h1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => a q.1 := ha.comp Primrec.fst
  have hres := primrec_gm16_6_1
    h1 (hb.comp Primrec.fst) (hp.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (hχ.comp Primrec.fst)
    (primrec_sub (hδ.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
    (hφ.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.fst.comp hres).pair
    ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp hres))).pair
      ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
        ((primrec_max
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))))).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))

private lemma primrec_gm16_4_1 {α : Type} [Primcodable α]
    {a b p φ : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hφ : Primrec φ) :
    Primrec fun x => theorem_4_1_bound GM07.vModelExplicit (a x) (b x) (p x) (φ x) := by
  unfold theorem_4_1_bound theorem_5_5_bound
  have hμ : Primrec fun x => p x * (p x - 1) / 2 :=
    primrec_div (primrec_mul hp (primrec_sub hp (Primrec.const 1))) (Primrec.const 2)
  have hinit : Primrec fun x => (4 * p x * (p x - 1), 0, 0, 0,
      2 * GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x)) :=
    (primrec_mul (primrec_mul (Primrec.const 4) hp) (primrec_sub hp (Primrec.const 1))).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair
        (primrec_mul (Primrec.const 2) (primrec_gm12_4_4 ha hb hp)))))
  have hrec : Primrec fun x => Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ)
      (4 * p x * (p x - 1), 0, 0, 0, 2 * GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x))
      (fun m acc => theorem_4_1_step GM07.vModelExplicit (a x) (b x) (p x) (φ x)
        (p x * (p x - 1) / 2) m acc)
      (p x * (p x - 1) / 2) := by
    refine primrec_natRec hμ hinit ?_
    unfold theorem_4_1_step
    have h1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => a q.1 := ha.comp Primrec.fst
    have hres := primrec_gm16_5_1
      h1 (hb.comp Primrec.fst) (hp.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (primrec_sub (hμ.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
      (hφ.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    exact (Primrec.fst.comp hres).pair
      ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.fst.comp (Primrec.snd.comp hres))).pair
        ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
          ((primrec_max
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))))).pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))
  exact (Primrec.fst.comp (Primrec.snd.comp hrec)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hrec))).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrec)))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrec))))))

private lemma primrec_gm16_4_2 {α : Type} [Primcodable α] {θ : α → ℕ} (hθ : Primrec θ) :
    Primrec fun x => theorem_4_2_bound (θ x) := by
  unfold theorem_4_2_bound conformalWallBound wallMinorBound
  have h2 : Primrec fun x => 2 * (θ x + 2) :=
    primrec_mul (Primrec.const 2) (primrec_add hθ (Primrec.const 2))
  have h21 : Primrec fun x => 2 * (2 * (θ x + 2)) + 1 :=
    primrec_add (primrec_mul (Primrec.const 2) h2) (Primrec.const 1)
  exact primrec_add
    (primrec_add
      (primrec_pow (Primrec.const 20)
        (primrec_mul (primrec_pow h21 (Primrec.const 4))
          (primrec_sub (primrec_mul (Primrec.const 2) h21) (Primrec.const 1))))
      h2)
    h2

/-- `theorem_3_1_bound GM07.vModelExplicit` is primitive recursive. -/
theorem primrec_theorem_3_1_bound {α : Type} [Primcodable α] {vB eB : α → ℕ}
    (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => theorem_3_1_bound GM07.vModelExplicit (vB x) (eB x) := by
  unfold theorem_3_1_bound GM12.gm16_theorem42_bound towerLen towerN
  have hp : Primrec fun x => vB x + 2 * eB x + 1 :=
    primrec_add (primrec_add hv (primrec_mul (Primrec.const 2) he)) (Primrec.const 1)
  have hN : Primrec fun x => 3 * GM20.Draw.drawBound (eB x) + 2 :=
    primrec_add (primrec_mul (Primrec.const 3) (primrec_drawBound he)) (Primrec.const 2)
  have hlen : Primrec fun x =>
      (3 * GM20.Draw.drawBound (eB x) + 2 + 1) * (3 * GM20.Draw.drawBound (eB x) + 2 + 1) :=
    primrec_mul (primrec_add hN (Primrec.const 1)) (primrec_add hN (Primrec.const 1))
  have hst : Primrec fun x => Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ) (0, 0, 0, 1)
      (fun m acc => theorem_3_1_towerStep GM07.vModelExplicit (vB x) (eB x) m acc)
      ((3 * GM20.Draw.drawBound (eB x) + 2 + 1) * (3 * GM20.Draw.drawBound (eB x) + 2 + 1)) := by
    refine primrec_natRec hlen (Primrec.const (0, 0, 0, 1)) ?_
    unfold theorem_3_1_towerStep GM12.gm16_theorem42_bound towerLen towerN towerA towerB
    have hidx : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) -
          (q.2.1 + 1) :=
      primrec_sub (hlen.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
    have hN1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ => 3 * GM20.Draw.drawBound (eB q.1) + 2 + 1 :=
      primrec_add (hN.comp Primrec.fst) (Primrec.const 1)
    have ha : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        min (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) *
              (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) %
          (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1))
          (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) *
              (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
            (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) / 2) :=
      primrec_min (primrec_mod hidx hN1) (primrec_div (primrec_div hidx hN1) (Primrec.const 2))
    have hb : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        ((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) *
            (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
          (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) -
          2 * min (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) *
                (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) %
            (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1))
            (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) *
                (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
              (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) / 2) :=
      primrec_sub (primrec_div hidx hN1) (primrec_mul (Primrec.const 2) ha)
    have hθmax : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ => q.2.2.2.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    have hφm := primrec_add hθmax (Primrec.const 1)
    have hθdraw := primrec_gm12_4_3 ha hb (hv.comp Primrec.fst) (he.comp Primrec.fst)
    have hres := primrec_gm16_4_1 ha hb (hp.comp Primrec.fst) hφm
    exact (primrec_max (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.fst.comp hres)).pair
      ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
          (Primrec.fst.comp (Primrec.snd.comp hres))).pair
        ((primrec_max
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
          (primrec_max hθmax
            (primrec_max hθdraw (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))
  exact (Primrec.fst.comp hst).pair
    ((Primrec.fst.comp (Primrec.snd.comp hst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))).pair
        (primrec_max (primrec_gm16_4_2 (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst))))
          hp)))

/-- `theorem_3_1_bound GM07.vModelExplicit` is computable (in fact primitive recursive). -/
theorem theorem_3_1_bound_computable :
    Computable fun p : ℕ × ℕ => theorem_3_1_bound GM07.vModelExplicit p.1 p.2 :=
  (primrec_theorem_3_1_bound Primrec.fst Primrec.snd).to_comp

end Computability31

/-! ## 2. Graph Minors XVI, (3.1) under `GM07.WExplicitStatement` -/

/-- **Graph Minors XVI, (3.1)** (pages 49 and 54), with explicit, computable parameters
`theorem_3_1_bound GM07.vModelExplicit vB eB`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_3_1_explicit_of (hW : GM07.WExplicitStatement)
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    {vB eB : ℕ} (hvB : V(L).ncard ≤ vB) (heB : E(L).ncard ≤ eB) :
    let res := theorem_3_1_bound GM07.vModelExplicit vB eB
    1 ≤ res.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_G : ℕ)
      (T : Set (Hypergraph α β × Hypergraph α β))
      (hT : IsGraphTangle G θ_G T),
      res.2.2.2 ≤ θ_G → ¬ ControlsMinor G L T →
      ∃ (Z : Set α) (S_seg : Set (Society α β))
        (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
        (α_disc : Society α β → Set S) (α_pt : α → S),
        Z ⊆ V(G) ∧ Z.ncard ≤ res.2.2.1 ∧ Z.ncard < θ_G ∧
        IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
        IsCentralSegregation (deleteVertices G Z)
          (deleteGraphVerticesTangle G hT.finite_V hT.finite_E Z T θ_G) S_seg ∧
        IsSegregationOfType (deleteVertices G Z) res.2.1 res.1 S_seg ∧
        IsProperArrangement S_seg α_disc α_pt :=
  theorem_3_1_explicit.{u, v, w, u', v'} GM07.vModelExplicit
    (GM07.vModel_le_vModelExplicit_of hW) L hVL hEL hvB heB

/-! ## 3. Graph Minors XVI, (1.3), with explicit, computable `r, d, w₀` -/

section Computability13

open GM12.PrimrecHelpers

/-- `theorem_1_3_bound GM07.vModelExplicit` is primitive recursive. -/
theorem primrec_theorem_1_3_bound {α : Type} [Primcodable α] {vB eB : α → ℕ}
    (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => theorem_1_3_bound GM07.vModelExplicit (vB x) (eB x) := by
  unfold theorem_1_3_bound
  have hres := primrec_theorem_3_1_bound hv he
  have hκ := Primrec.fst.comp hres
  have hρ := Primrec.fst.comp (Primrec.snd.comp hres)
  have hζ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ₀ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ := primrec_max hθ₀
    (primrec_add (primrec_add (primrec_mul (Primrec.const 2) hρ) (Primrec.const 4)) hζ)
  have hw₀ := primrec_sub (primrec_add hζ (primrec_mul (Primrec.const 4) hθ)) (Primrec.const 3)
  have hr := primrec_mul (primrec_add hw₀ (Primrec.const 1))
    (primrec_add (primrec_mul (Primrec.const 2) hρ) (Primrec.const 1))
  exact hr.pair (hκ.pair hw₀)

/-- `theorem_1_3_bound GM07.vModelExplicit` is computable (in fact primitive recursive). -/
theorem theorem_1_3_bound_computable :
    Computable fun p : ℕ × ℕ => theorem_1_3_bound GM07.vModelExplicit p.1 p.2 :=
  (primrec_theorem_1_3_bound Primrec.fst Primrec.snd).to_comp

end Computability13

/-- **Graph Minors XVI, (1.3)** (pages 46 and 51–52), with explicit, computable `r, d, w₀` given by
`theorem_1_3_bound GM07.vModelExplicit vB eB`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_1_3_explicit_of (hW : GM07.WExplicitStatement)
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    {vB eB : ℕ} (hvB : V(L).ncard ≤ vB) (heB : E(L).ncard ≤ eB)
    (hNonplanar : ∀ (S : Type w) [TopologicalSpace S] [T2Space S],
      IsSphere S → ¬ CanBeDrawnIn S L) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β), V(G).Finite → E(G).Finite →
    ¬ IsIsoMinor L G →
    HasTreeStructureOver
    {H : Graph α (β ⊕ ℕ) | ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S)
      (H₀ : Graph α (β ⊕ ℕ)), IsClosedSurface S ∧ ConnectedSpace S ∧ ¬ CanBeDrawnIn S L ∧
      IsVertexExtension (theorem_1_3_bound GM07.vModelExplicit vB eB).2.2 H H₀ ∧
      IsOutgrowthByRings S H₀
        (theorem_1_3_bound GM07.vModelExplicit vB eB).2.1
        (theorem_1_3_bound GM07.vModelExplicit vB eB).1} (liftEdgeInl G) :=
  theorem_1_3_explicitOf.{u, v, w, u', v'} GM07.vModelExplicit
    (GM07.vModel_le_vModelExplicit_of hW) L hVL hEL hvB heB hNonplanar

/-! ## 4. Bounded-adhesion tree-decomposition form of Graph Minors XVI, (1.3) -/

/-- Concrete explicit `(adh, w₀, g, d, r)` bounds for the bounded-adhesion tree-decomposition form
of **Graph Minors XVI, (1.3)**, instantiated at `GM07.vModelExplicit`. -/
def theorem_1_3_treeDecomp_bound (vB eB : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  theorem_1_3_treeDecomp_boundOf GM07.vModelExplicit vB eB

section ComputabilityTreeDecomp

open GM12.PrimrecHelpers

/-- `theorem_1_3_treeDecomp_bound` is primitive recursive. -/
theorem primrec_theorem_1_3_treeDecomp_bound {α : Type} [Primcodable α] {vB eB : α → ℕ}
    (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => theorem_1_3_treeDecomp_bound (vB x) (eB x) := by
  unfold theorem_1_3_treeDecomp_bound theorem_1_3_treeDecomp_boundOf
  have hres := primrec_theorem_3_1_bound hv he
  have hκ := Primrec.fst.comp hres
  have hρ := Primrec.fst.comp (Primrec.snd.comp hres)
  have hζ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ₀ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ := primrec_max hθ₀
    (primrec_add (primrec_add (primrec_mul (Primrec.const 2) hρ) (Primrec.const 4)) hζ)
  have hadh := primrec_sub (primrec_mul (Primrec.const 4) hθ) (Primrec.const 3)
  have hw₀ := primrec_sub (primrec_add hζ (primrec_mul (Primrec.const 4) hθ)) (Primrec.const 3)
  have hg := primrec_mul (Primrec.const 3) (primrec_drawBound he)
  have hr := primrec_mul (primrec_add hw₀ (Primrec.const 1))
    (primrec_add (primrec_mul (Primrec.const 2) hρ) (Primrec.const 1))
  exact hadh.pair (hw₀.pair (hg.pair (hκ.pair hr)))

/-- `theorem_1_3_treeDecomp_bound` is computable (in fact primitive recursive). -/
theorem theorem_1_3_treeDecomp_bound_computable :
    Computable fun p : ℕ × ℕ => theorem_1_3_treeDecomp_bound p.1 p.2 :=
  (primrec_theorem_1_3_treeDecomp_bound Primrec.fst Primrec.snd).to_comp

end ComputabilityTreeDecomp

/-- Bounded-adhesion tree-decomposition form of **Graph Minors XVI, (1.3)**, with explicit,
computable `(adh, w₀, g, d, r)` given by `theorem_1_3_treeDecomp_bound vB eB`, assuming
`GM07.WExplicitStatement`. -/
theorem theorem_1_3_treeDecomp_explicit_of (hW : GM07.WExplicitStatement)
    {α' : Type u'} {β' : Type v'} (L : Graph α' β') (hVL : V(L).Finite) (hEL : E(L).Finite)
    {vB eB : ℕ} (hvB : V(L).ncard ≤ vB) (heB : E(L).ncard ≤ eB) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β), V(G).Finite → E(G).Finite → ¬ IsIsoMinor L G →
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Graph α (β ⊕ ℕ)),
        IsGraphTreeDecomposition (liftEdgeInl G) T τ ∧
        (∀ t t', T.Adj t t' →
          (V(τ t) ∩ V(τ t')).ncard ≤ (theorem_1_3_treeDecomp_bound vB eB).1) ∧
        ∀ t₀ (H' : Graph α (β ⊕ ℕ)), E(H').Finite →
          IsTorsoOfDesign (graphVertexDesign T τ t₀) H' →
          V(H').ncard ≤ (theorem_1_3_treeDecomp_bound vB eB).1 ∨
          ∃ (S : Type w) (_ : TopologicalSpace S) (_ : T2Space S) (a b : ℕ)
            (_ : Nonempty (S ≃ₜ SurfaceModel a b 0)) (H₀ : Graph α (β ⊕ ℕ)),
            IsClosedSurface S ∧ ConnectedSpace S ∧
            2 * a + b ≤ (theorem_1_3_treeDecomp_bound vB eB).2.2.1 ∧ ¬ CanBeDrawnIn S L ∧
            IsVertexExtension (theorem_1_3_treeDecomp_bound vB eB).2.1 H' H₀ ∧
            IsOutgrowthByRings S H₀
              (theorem_1_3_treeDecomp_bound vB eB).2.2.2.1
              (theorem_1_3_treeDecomp_bound vB eB).2.2.2.2 :=
  theorem_1_3_treeDecomp_explicitOf.{u, v, w, u', v'} GM07.vModelExplicit
    (GM07.vModel_le_vModelExplicit_of hW) L hVL hEL hvB heB

end GraphMinor.GM16
