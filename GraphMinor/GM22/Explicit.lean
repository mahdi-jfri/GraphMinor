module

public import GraphMinor.GM22.Section3
public import GraphMinor.GM07.ExplicitV
public import Mathlib.Computability.Partrec

import GraphMinor.GM12.Primrec
import GraphMinor.GM12.Bridge
import GraphMinor.GM16.InductionsProved
import GraphMinor.GM17.Section13Proved
import GraphMinor.GM17.Section13d
import GraphMinor.GM17.Section13b

/-!
# Explicit, computable, monotone bound for Graph Minors XXII, (3.1)

This file provides an explicit insulation bound for **Graph Minors XXII, 3.1**
(N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563, page 534):

- `hBoundOf V p`: the explicit insulation bound for `GM22.theorem_3_1`, parameterized by an
  arbitrary upper bound `V : ℕ → ℕ → ℕ → ℕ → ℕ` on `GM07.vModel`.
- `theorem_3_1_explicitOf`: **Graph Minors XXII, 3.1** with explicit bound `hBoundOf V p` for any
  `V` dominating `GM07.vModel`.
- `hBound p`: the monotone envelope of `hBoundOf GM07.vModelExplicit` using the explicit bound
  `GM07.vModelExplicit` built from `GM07.wExplicit` (`GraphMinor/GM07/ExplicitW.lean`,
  `GraphMinor/GM07/ExplicitV.lean`).
- `hBound_computable`: `Computable hBound`, proved via primitive recursion (`Primrec`).
- `hBound_mono`: `Monotone hBound`.
- `theorem_3_1_explicit_of`: **Graph Minors XXII, 3.1** with explicit bound `hBound p` under
  `GM07.WExplicitStatement`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

/-! ## 1. Parameterized explicit bound `hBoundOf` -/

/-- Explicit insulation bound for **Graph Minors XXII, 3.1** (page 534), parameterized by an upper
bound `V` on `GM07.vModel`. -/
def hBoundOf (V : ℕ → ℕ → ℕ → ℕ → ℕ) (p : ℕ) : ℕ :=
  theorem_3_1_bound V p

/-- **Graph Minors XXII, 3.1** (page 534) with the explicit insulation bound `hBoundOf V p`,
parameterized by an arbitrary upper bound `V` on `GM07.vModel`. -/
theorem theorem_3_1_explicitOf
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k) (p : ℕ) :
    1 ≤ hBoundOf V p ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
        Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
        ∀ (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
        ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) (hBoundOf V p) v₀ →
        ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
        ∃ L' ≤ G.deleteVerts {ιV v₀},
          HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L :=
  ⟨one_le_theorem_3_1_bound V p, theorem_3_1_explicitBound.{u, v, w} V hV p⟩

/-! ## 2. Monotonicity of insulation and the concrete monotone bound `hBound` -/

/-- If a point `x` is `h'`-insulated from `Y` by `D` and `1 ≤ h ≤ h'`, then `x` is `h`-insulated
from `Y` by `D` (taking the innermost `h` discs of the nested family). -/
theorem IsInsulated.of_le {S : Type w} [TopologicalSpace S] {D : Drawing S} {Y : Set S}
    {h h' : ℕ} {x : S} (hh : 1 ≤ h) (hle : h ≤ h') (hIns : IsInsulated D Y h' x) :
    IsInsulated D Y h x := by
  rcases hIns with ⟨Δ, hΔ_disc, hΔ_nest, hΔ_end⟩
  have hsub_zero : ∀ k : ℕ, (hk : k < h') → Δ ⟨k, hk⟩ ⊆ Δ ⟨0, by omega⟩ := by
    intro k
    induction k with
    | zero => intro _; exact Subset.rfl
    | succ k ih =>
      intro hk
      exact (hΔ_nest ⟨k, by omega⟩ hk).trans (diff_subset.trans (ih (by omega)))
  let Δ' : Fin h → Set S := fun i => Δ ⟨i.1 + (h' - h), by have := i.2; omega⟩
  refine ⟨Δ', fun i => hΔ_disc ⟨i.1 + (h' - h), by have := i.2; omega⟩, fun i hi => ?_, fun hpos => ?_⟩
  · have hidx : (⟨i.1 + 1 + (h' - h), by omega⟩ : Fin h') =
        ⟨(i.1 + (h' - h)) + 1, by have := i.2; omega⟩ := Fin.ext (by dsimp; omega)
    simpa only [Δ', hidx] using hΔ_nest ⟨i.1 + (h' - h), by have := i.2; omega⟩ (by dsimp; omega)
  · have hlast : (⟨h - 1 + (h' - h), by omega⟩ : Fin h') = ⟨h' - 1, by omega⟩ :=
      Fin.ext (by dsimp; omega)
    refine ⟨?_, ?_⟩
    · simpa only [Δ', hlast] using (hΔ_end (by omega)).1
    · have h0 : (⟨0 + (h' - h), by omega⟩ : Fin h') = ⟨h' - h, by omega⟩ := Fin.ext (by dsimp; omega)
      simpa only [Δ', h0] using (hΔ_end (by omega)).2.mono_right (hsub_zero (h' - h) (by omega))

/-- Concrete explicit, computable, and monotone insulation bound for **Graph Minors XXII, 3.1**
(page 534), obtained by instantiating `hBoundOf` with `GM07.vModelExplicit` and taking the running
maximum over `0, …, p`. -/
def hBound (p : ℕ) : ℕ :=
  GM17.maxRange (p + 1) (hBoundOf GM07.vModelExplicit)

/-- `hBound` is monotone. -/
theorem hBound_mono : Monotone hBound := by
  intro p₁ p₂ hp
  have hstep : ∀ a b : ℕ, a ≤ b →
      GM17.maxRange a (hBoundOf GM07.vModelExplicit) ≤
        GM17.maxRange b (hBoundOf GM07.vModelExplicit) := by
    intro a b hab
    induction hab with
    | refl => exact le_rfl
    | @step m _ ih => exact ih.trans (le_max_left _ _)
  exact hstep (p₁ + 1) (p₂ + 1) (Nat.add_le_add_right hp 1)

/-- **Graph Minors XXII, 3.1** (page 534) with the explicit, computable, monotone insulation bound
`hBound p`, assuming `GM07.WExplicitStatement`. -/
theorem theorem_3_1_explicit_of (hW : GM07.WExplicitStatement) (p : ℕ) :
    1 ≤ hBound p ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
        Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
        ∀ (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
        ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) (hBound p) v₀ →
        ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
        ∃ L' ≤ G.deleteVerts {ιV v₀},
          HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L := by
  obtain ⟨h1, h31⟩ :=
    theorem_3_1_explicitOf.{u, v, w} GM07.vModelExplicit (GM07.vModel_le_vModelExplicit_of hW) p
  have hle : hBoundOf GM07.vModelExplicit p ≤ hBound p :=
    GM17.le_maxRange (f := hBoundOf GM07.vModelExplicit) (Nat.lt_succ_self p)
  refine ⟨h1.trans hle, ?_⟩
  intro S _ _ hS α β G Γ K L hVG hEG_fin hΓG hKG hUG hEG D ιV ιE hΓD v₀ hv₀ hIns Z hZK hZp hLG
  exact h31 hS G Γ K L hVG hEG_fin hΓG hKG hUG hEG D ιV ιE hΓD v₀ hv₀
    (hIns.of_le h1 hle) Z hZK hZp hLG

/-! ## 3. Primitive recursiveness and computability of `hBound` -/

section Computability

open GM12.PrimrecHelpers

private lemma primrec_maxRange {α : Type} [Primcodable α] {n : α → ℕ} {f : α → ℕ → ℕ}
    (hn : Primrec n) (hf : Primrec fun p : α × ℕ => f p.1 p.2) :
    Primrec fun a => GM17.maxRange (n a) (f a) := by
  unfold GM17.maxRange
  refine primrec_natRec hn (Primrec.const 0) ?_
  exact primrec_max (Primrec.snd.comp Primrec.snd)
    (hf.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))

/-! ### GM20.Draw explicit bound -/

private lemma primrec_drawBound {α : Type} [Primcodable α] {e : α → ℕ} (he : Primrec e) :
    Primrec fun x => GM20.Draw.drawBound (e x) := by
  unfold GM20.Draw.drawBound
  exact primrec_max (Primrec.const 2)
    (primrec_mul he (primrec_sub (primrec_mul (Primrec.const 2) he) (Primrec.const 1)))

/-! ### GM16 explicit bounds -/

private lemma primrec_properEyeStep {α : Type} [Primcodable α]
    {φ μ lam θ : α → ℕ} (hφ : Primrec φ) (hμ : Primrec μ) (hθ : Primrec θ) :
    Primrec fun x => GM16.properEyeStep (φ x) (μ x) (lam x) (θ x) := by
  unfold GM16.properEyeStep
  have hθ'' : Primrec fun x => 2 * (θ x + 3 * μ x + 8) :=
    primrec_mul (Primrec.const 2) (primrec_add (primrec_add hθ (primrec_mul (Primrec.const 3) hμ)) (Primrec.const 8))
  have hτ₁ : Primrec fun x => 4 + μ x / 2 :=
    primrec_add (Primrec.const 4) (primrec_div hμ (Primrec.const 2))
  have hτ₂ : Primrec fun x => 6 + 2 * (θ x + 3 * μ x + 8) / 2 :=
    primrec_add (Primrec.const 6) (primrec_div hθ'' (Primrec.const 2))
  have hπ : Primrec fun x => (φ x - 1) * (2 * (4 + μ x / 2) + (6 + 2 * (θ x + 3 * μ x + 8) / 2) - 7) :=
    primrec_mul (primrec_sub hφ (Primrec.const 1))
      (primrec_sub (primrec_add (primrec_mul (Primrec.const 2) hτ₁) hτ₂) (Primrec.const 7))
  have hbeta : Primrec fun x => 2 * ((φ x - 1) * (2 * (4 + μ x / 2) + (6 + 2 * (θ x + 3 * μ x + 8) / 2) - 7)) + 8 :=
    primrec_add (primrec_mul (Primrec.const 2) hπ) (Primrec.const 8)
  exact (primrec_add (primrec_mul (Primrec.const 3) hπ) (Primrec.const 9)).pair
    ((primrec_mul (Primrec.const 20) hbeta).pair (primrec_mul (Primrec.const 100) hbeta))

private lemma primrec_properArrangementBound {α : Type} [Primcodable α]
    {κ φ μ : α → ℕ} (hκ : Primrec κ) (hφ : Primrec φ) (hμ : Primrec μ) :
    Primrec fun x => GM16.properArrangementBound (κ x) (φ x) (μ x) := by
  unfold GM16.properArrangementBound
  have hμ' : Primrec fun x => 2 * (μ x + 6) :=
    primrec_mul (Primrec.const 2) (primrec_add hμ (Primrec.const 6))
  have hφ' : Primrec fun x => max (φ x) 8 := primrec_max hφ (Primrec.const 8)
  have hθtop : Primrec fun x => max (max (φ x) 8) (4 * 4 + 2 * (μ x + 6) + 2) :=
    primrec_max hφ' (primrec_add (primrec_add (Primrec.const 16) hμ') (Primrec.const 2))
  have hstep : Primrec₂ fun (x : α) (st : ℕ × ℕ × ℕ) =>
      GM16.properEyeIndStep (max (φ x) 8) (2 * (μ x + 6)) st := by
    refine Primrec₂.mk ?_
    unfold GM16.properEyeIndStep
    have hpe : Primrec fun q : α × ℕ × ℕ × ℕ =>
        GM16.properEyeStep (max (φ q.1) 8) (2 * (μ q.1 + 6)) q.2.2.1 q.2.2.2 :=
      primrec_properEyeStep (hφ'.comp Primrec.fst) (hμ'.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    have hlam : Primrec fun q : α × ℕ × ℕ × ℕ => max (GM16.properEyeStep (max (φ q.1) 8) (2 * (μ q.1 + 6)) q.2.2.1 q.2.2.2).2.1 4 :=
      primrec_max (Primrec.fst.comp (Primrec.snd.comp hpe)) (Primrec.const 4)
    exact (primrec_max (Primrec.fst.comp hpe) (Primrec.fst.comp Primrec.snd)).pair
      (hlam.pair (primrec_max (Primrec.snd.comp (Primrec.snd.comp hpe))
        (primrec_add (primrec_add (primrec_mul (Primrec.const 4) hlam) (hμ'.comp Primrec.fst)) (Primrec.const 2))))
  have hres : Primrec fun x =>
      Nat.iterate (GM16.properEyeIndStep (max (φ x) 8) (2 * (μ x + 6))) (κ x + 1)
        (0, 4, max (max (φ x) 8) (4 * 4 + 2 * (μ x + 6) + 2)) :=
    Primrec.nat_iterate (primrec_add hκ (Primrec.const 1))
      ((Primrec.const 0).pair ((Primrec.const 4).pair hθtop)) hstep
  exact (primrec_max (Primrec.snd.comp (Primrec.snd.comp hres))
      (primrec_add (primrec_add (primrec_mul (Primrec.const 4) (Primrec.fst.comp (Primrec.snd.comp hres))) hμ')
        (Primrec.const 2))).pair
    ((Primrec.fst.comp (Primrec.snd.comp hres)).pair (Primrec.fst.comp hres))

private lemma primrec_section9Beta {α : Type} [Primcodable α]
    {δ φ ψ : α → ℕ} (hδ : Primrec δ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => GM16.section9Beta (δ x) (φ x) (ψ x) := by
  unfold GM16.section9Beta
  have hκ : Primrec fun x => δ x ^ 2 * φ x ^ 2 / 2 + 1 :=
    primrec_add (primrec_div (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ (Primrec.const 2))) (Primrec.const 2))
      (Primrec.const 1)
  exact primrec_mul (Primrec.const 2)
    (primrec_div (primrec_add (primrec_mul hκ (primrec_add hψ (Primrec.const 6))) (Primrec.const 1)) (Primrec.const 2))

private lemma primrec_gm16_7_1_theta {α : Type} [Primcodable α]
    {χ δ lam θreq φ ψ : α → ℕ}
    (hχ : Primrec χ) (hδ : Primrec δ) (hlam : Primrec lam)
    (hθreq : Primrec θreq) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => GM16.theorem_7_1_theta (χ x) (δ x) (lam x) (θreq x) (φ x) (ψ x) := by
  unfold GM16.theorem_7_1_theta GM16.theorem_8_1_gamma GM16.theorem_8_1_theta GM16.theorem_8_3_bound
  have hβ := primrec_section9Beta hδ hφ hψ
  have hγ : Primrec fun x => 3 * GM16.section9Beta (δ x) (φ x) (ψ x) + 3 :=
    primrec_add (primrec_mul (Primrec.const 3) hβ) (Primrec.const 3)
  have hθ₁ : Primrec fun x => 12 * (δ x + 3) * (GM16.section9Beta (δ x) (φ x) (ψ x) + 1) + 4 * φ x + 8 :=
    primrec_add (primrec_add (primrec_mul (primrec_mul (Primrec.const 12) (primrec_add hδ (Primrec.const 3)))
      (primrec_add hβ (Primrec.const 1))) (primrec_mul (Primrec.const 4) hφ)) (Primrec.const 8)
  have hζ : Primrec fun x => χ x + δ x ^ 2 * φ x ^ 2 / 2 :=
    primrec_add hχ (primrec_div (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ (Primrec.const 2))) (Primrec.const 2))
  have hlow : Primrec fun x => max (θreq x + (χ x + δ x ^ 2 * φ x ^ 2 / 2)) (4 * ψ x + 2) :=
    primrec_max (primrec_add hθreq hζ) (primrec_add (primrec_mul (Primrec.const 4) hψ) (Primrec.const 2))
  have hθ₂ : Primrec fun x => max (θreq x + (χ x + δ x ^ 2 * φ x ^ 2 / 2)) (4 * ψ x + 2) +
      4 * ψ x + 10 * lam x + 3 * (χ x + δ x ^ 2 * φ x ^ 2 / 2) + 31 :=
    primrec_add (primrec_add (primrec_add (primrec_add hlow (primrec_mul (Primrec.const 4) hψ))
      (primrec_mul (Primrec.const 10) hlam)) (primrec_mul (Primrec.const 3) hζ)) (Primrec.const 31)
  exact primrec_add (primrec_add (primrec_add (primrec_add hχ hθ₁) (primrec_mul (Primrec.const 3) hγ))
    (primrec_mul (primrec_add (primrec_mul (Primrec.const 4) hγ) (Primrec.const 2)) hδ)) hθ₂

private lemma primrec_gm16_7_2 {α : Type} [Primcodable α]
    {a b p φ μ : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p)
    (hφ : Primrec φ) (hμ : Primrec μ) :
    Primrec fun x => GM16.theorem_7_2_bound GM07.vModelExplicit (a x) (b x) (p x) (φ x) (μ x) := by
  unfold GM16.theorem_7_2_bound
  have hp4 : Primrec fun x => max (p x) 4 := primrec_max hp (Primrec.const 4)
  have hκ := primrec_gm12_4_5_k hp4
  have hφ₁ := primrec_gm12_4_5_N ha hb hp4
  have hφ₂ := primrec_max hφ hφ₁
  have hres := primrec_properArrangementBound hκ hφ₂ hμ
  have hlam : Primrec fun x => (GM16.properArrangementBound (GM12.theorem_4_5_kBound (max (p x) 4))
      (max (φ x) (GM12.theorem_4_5_NBound GM07.vModelExplicit (a x) (b x) (max (p x) 4))) (μ x)).2.1 + μ x + 2 :=
    primrec_add (primrec_add (Primrec.fst.comp (Primrec.snd.comp hres)) hμ) (Primrec.const 2)
  have hθ := primrec_max (primrec_max (Primrec.fst.comp hres) hp4)
    (primrec_add (primrec_mul (Primrec.const 4) hlam) (Primrec.const 3))
  exact hκ.pair (hlam.pair ((Primrec.snd.comp (Primrec.snd.comp hres)).pair hθ))

private lemma primrec_gm16_6_1 {α : Type} [Primcodable α]
    {a b p τ χ δ φ ψ : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hτ : Primrec τ)
    (hχ : Primrec χ) (hδ : Primrec δ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => GM16.theorem_6_1_bound GM07.vModelExplicit (a x) (b x) (p x) (τ x) (χ x) (δ x) (φ x) (ψ x) := by
  unfold GM16.theorem_6_1_bound GM16.theorem_7_1_sigma
  have hφ' := primrec_max hφ (Primrec.const 3)
  have hψ' := primrec_max hψ (Primrec.const 3)
  have hres72 := primrec_gm16_7_2 ha hb hp hφ' (primrec_mul (Primrec.const 2) hψ')
  have hθ' := primrec_max (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres72))) hp
  have hθ := primrec_gm16_7_1_theta hχ hδ (Primrec.fst.comp (Primrec.snd.comp hres72)) hθ' hφ' hψ'
  have hζ := primrec_add hχ (primrec_div (primrec_mul (primrec_pow hδ (Primrec.const 2)) (primrec_pow hφ' (Primrec.const 2))) (Primrec.const 2))
  have hσ := primrec_add (primrec_add hδ hτ) hζ
  exact hσ.pair ((Primrec.fst.comp hres72).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres72))).pair (hζ.pair hθ)))

private lemma primrec_gm16_5_1 {α : Type} [Primcodable α]
    {a b p τ χ φ ψ : α → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hτ : Primrec τ)
    (hχ : Primrec χ) (hφ : Primrec φ) (hψ : Primrec ψ) :
    Primrec fun x => GM16.theorem_5_1_bound GM07.vModelExplicit (a x) (b x) (p x) (τ x) (χ x) (φ x) (ψ x) := by
  unfold GM16.theorem_5_1_bound GM16.theorem_6_3_delta GM16.theorem_6_3_theta
  have hδ : Primrec fun x => 2 * (p x * (p x - 1) / 2) ^ 2 * max (τ x) 2 ^ 2 :=
    primrec_mul (primrec_mul (Primrec.const 2)
      (primrec_pow (primrec_div (primrec_mul hp (primrec_sub hp (Primrec.const 1))) (Primrec.const 2)) (Primrec.const 2)))
      (primrec_pow (primrec_max hτ (Primrec.const 2)) (Primrec.const 2))
  have hinit : Primrec fun x => (τ x + 1, 0, 0, 0,
      5 * max (ψ x) (max 3 (GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x))) + 34) :=
    (primrec_add hτ (Primrec.const 1)).pair ((Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair
      (primrec_add (primrec_mul (Primrec.const 5)
        (primrec_max hψ (primrec_max (Primrec.const 3) (primrec_gm12_4_4 ha hb hp)))) (Primrec.const 34)))))
  refine primrec_natRec hδ hinit ?_
  unfold GM16.theorem_5_1_step
  have h1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => a q.1 := ha.comp Primrec.fst
  have hres := primrec_gm16_6_1
    h1 (hb.comp Primrec.fst) (hp.comp Primrec.fst)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (hχ.comp Primrec.fst)
    (primrec_sub (hδ.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
    (hφ.comp Primrec.fst)
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact (Primrec.fst.comp hres).pair
    ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.fst.comp (Primrec.snd.comp hres))).pair
      ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
        ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))))).pair
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))

private lemma primrec_gm16_4_1 {α : Type} [Primcodable α]
    {a b p φ : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hp : Primrec p) (hφ : Primrec φ) :
    Primrec fun x => GM16.theorem_4_1_bound GM07.vModelExplicit (a x) (b x) (p x) (φ x) := by
  unfold GM16.theorem_4_1_bound GM16.theorem_5_5_bound
  have hμ : Primrec fun x => p x * (p x - 1) / 2 :=
    primrec_div (primrec_mul hp (primrec_sub hp (Primrec.const 1))) (Primrec.const 2)
  have hinit : Primrec fun x => (4 * p x * (p x - 1), 0, 0, 0,
      2 * GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x)) :=
    (primrec_mul (primrec_mul (Primrec.const 4) hp) (primrec_sub hp (Primrec.const 1))).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair ((Primrec.const 0).pair
        (primrec_mul (Primrec.const 2) (primrec_gm12_4_4 ha hb hp)))))
  have hrec : Primrec fun x => Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ)
      (4 * p x * (p x - 1), 0, 0, 0, 2 * GM12.theorem_4_4_bound GM07.vModelExplicit (a x) (b x) (p x))
      (fun m acc => GM16.theorem_4_1_step GM07.vModelExplicit (a x) (b x) (p x) (φ x) (p x * (p x - 1) / 2) m acc)
      (p x * (p x - 1) / 2) := by
    refine primrec_natRec hμ hinit ?_
    unfold GM16.theorem_4_1_step
    have h1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ => a q.1 := ha.comp Primrec.fst
    have hres := primrec_gm16_5_1
      h1 (hb.comp Primrec.fst) (hp.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (primrec_sub (hμ.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
      (hφ.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
    exact (Primrec.fst.comp hres).pair
      ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.fst.comp (Primrec.snd.comp hres))).pair
        ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
          ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))))).pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))
  exact (Primrec.fst.comp (Primrec.snd.comp hrec)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hrec))).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrec)))).pair
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrec))))))

private lemma primrec_gm16_4_2 {α : Type} [Primcodable α] {θ : α → ℕ} (hθ : Primrec θ) :
    Primrec fun x => GM16.theorem_4_2_bound (θ x) := by
  unfold GM16.theorem_4_2_bound GM16.conformalWallBound GM16.wallMinorBound
  have h2 : Primrec fun x => 2 * (θ x + 2) := primrec_mul (Primrec.const 2) (primrec_add hθ (Primrec.const 2))
  have h21 : Primrec fun x => 2 * (2 * (θ x + 2)) + 1 := primrec_add (primrec_mul (Primrec.const 2) h2) (Primrec.const 1)
  exact primrec_add
    (primrec_add
      (primrec_pow (Primrec.const 20)
        (primrec_mul (primrec_pow h21 (Primrec.const 4))
          (primrec_sub (primrec_mul (Primrec.const 2) h21) (Primrec.const 1))))
      h2)
    h2

private lemma primrec_gm16_3_1 {α : Type} [Primcodable α]
    {vB eB : α → ℕ} (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => GM16.theorem_3_1_bound GM07.vModelExplicit (vB x) (eB x) := by
  unfold GM16.theorem_3_1_bound GM12.gm16_theorem42_bound GM16.towerLen GM16.towerN
  have hp : Primrec fun x => vB x + 2 * eB x + 1 :=
    primrec_add (primrec_add hv (primrec_mul (Primrec.const 2) he)) (Primrec.const 1)
  have hN : Primrec fun x => 3 * GM20.Draw.drawBound (eB x) + 2 :=
    primrec_add (primrec_mul (Primrec.const 3) (primrec_drawBound he)) (Primrec.const 2)
  have hlen : Primrec fun x => (3 * GM20.Draw.drawBound (eB x) + 2 + 1) * (3 * GM20.Draw.drawBound (eB x) + 2 + 1) :=
    primrec_mul (primrec_add hN (Primrec.const 1)) (primrec_add hN (Primrec.const 1))
  have hst : Primrec fun x => Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ) (0, 0, 0, 1)
      (fun m acc => GM16.theorem_3_1_towerStep GM07.vModelExplicit (vB x) (eB x) m acc)
      ((3 * GM20.Draw.drawBound (eB x) + 2 + 1) * (3 * GM20.Draw.drawBound (eB x) + 2 + 1)) := by
    refine primrec_natRec hlen (Primrec.const (0, 0, 0, 1)) ?_
    unfold GM16.theorem_3_1_towerStep GM12.gm16_theorem42_bound GM16.towerLen GM16.towerN
      GM16.towerA GM16.towerB
    have hidx : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1) :=
      primrec_sub (hlen.comp Primrec.fst) (primrec_add (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
    have hN1 : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ => 3 * GM20.Draw.drawBound (eB q.1) + 2 + 1 :=
      primrec_add (hN.comp Primrec.fst) (Primrec.const 1)
    have ha : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        min (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) %
          (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1))
          (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
            (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) / 2) :=
      primrec_min (primrec_mod hidx hN1) (primrec_div (primrec_div hidx hN1) (Primrec.const 2))
    have hb : Primrec fun q : α × ℕ × ℕ × ℕ × ℕ × ℕ =>
        ((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
          (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) -
          2 * min (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) %
            (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1))
            (((3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) * (3 * GM20.Draw.drawBound (eB q.1) + 2 + 1) - (q.2.1 + 1)) /
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
        ((primrec_max (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres)))).pair
          (primrec_max hθmax (primrec_max hθdraw (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres)))))))
  exact (Primrec.fst.comp hst).pair
    ((Primrec.fst.comp (Primrec.snd.comp hst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hst))).pair
        (primrec_max (primrec_gm16_4_2 (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hst)))) hp)))

/-! ### GM17 explicit bounds -/

private lemma primrec_gm17_13_1 {α : Type} [Primcodable α]
    {vB eB : α → ℕ} (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => GM17.theorem_13_1_bound GM07.vModelExplicit (vB x) (eB x) := by
  unfold GM17.theorem_13_1_bound
  have hres := primrec_gm16_3_1
    (primrec_add hv (primrec_mul (Primrec.const 2) he))
    (primrec_mul (Primrec.const 3) he)
  have hρ1 := primrec_add (Primrec.fst.comp (Primrec.snd.comp hres)) (Primrec.const 1)
  have hζ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ₀ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  exact hρ1.pair ((Primrec.fst.comp hres).pair (hζ.pair
    (primrec_max hθ₀
      (primrec_add (primrec_add hζ
        (primrec_max (Primrec.const 3) (primrec_add (primrec_mul (Primrec.const 2) hρ1) (Primrec.const 2))))
        (Primrec.const 1)))))

private lemma primrec_sigmaBound_2p3 {α : Type} [Primcodable α]
    {p h z : α → ℕ} (hp : Primrec p) (hh : Primrec h) (hz : Primrec z) :
    Primrec fun x => GM17.sigmaBoundExplicit (fun _ _ _ p' _ => 2 * p' + 3) (p x) (h x) (z x) := by
  unfold GM17.sigmaBoundExplicit
  refine primrec_maxRange (primrec_add hh (Primrec.const 1)) ?_
  refine primrec_maxRange (primrec_add (hh.comp Primrec.fst) (Primrec.const 1)) ?_
  refine primrec_maxRange (primrec_add (hh.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)) ?_
  refine primrec_maxRange (primrec_add (hz.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 1)) ?_
  exact primrec_add
    (primrec_mul (Primrec.const 2) (hp.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
    (Primrec.const 3)

private lemma primrec_gm17_13_3 {α : Type} [Primcodable α]
    {p h z₀ : α → ℕ} (hp : Primrec p) (hh : Primrec h) (hz₀ : Primrec z₀) :
    Primrec fun x => GM17.theorem_13_3_bound (fun _ _ _ p' _ => 2 * p' + 3) (p x) (h x) (z₀ x) := by
  unfold GM17.theorem_13_3_bound GM17.theorem_13_3_iter
  have hstep : Primrec₂ fun (x : α) (acc : ℕ × ℕ) =>
      GM17.theorem_13_3_step (fun _ _ _ p' _ => 2 * p' + 3) (p x) (h x) acc := by
    refine Primrec₂.mk ?_
    unfold GM17.theorem_13_3_step
    have hacc2 : Primrec fun q : α × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
    have hM := primrec_sigmaBound_2p3 (hp.comp Primrec.fst) (hh.comp Primrec.fst) hacc2
    exact (primrec_max (Primrec.fst.comp Primrec.snd)
      (primrec_add (primrec_add (primrec_add hacc2 hM)
        (primrec_max (Primrec.const 3) (primrec_add (primrec_mul (Primrec.const 2) (hp.comp Primrec.fst)) (Primrec.const 2))))
        (Primrec.const 1))).pair (primrec_add hacc2 hM)
  have hres := Primrec.nat_iterate hh ((Primrec.const 0).pair hz₀) hstep
  have hM := primrec_sigmaBound_2p3 hp hh (Primrec.snd.comp hres)
  exact (primrec_max (Primrec.fst.comp hres)
    (primrec_add (primrec_add (primrec_add (Primrec.snd.comp hres) hM)
      (primrec_max (Primrec.const 3) (primrec_add (primrec_mul (Primrec.const 2) hp) (Primrec.const 2))))
      (Primrec.const 1))).pair (Primrec.snd.comp hres)

private lemma primrec_gm17_13_4 {α : Type} [Primcodable α]
    {vB eB : α → ℕ} (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => GM17.theorem_13_4_bound GM07.vModelExplicit (fun _ _ _ p' _ => 2 * p' + 3) (vB x) (eB x) := by
  unfold GM17.theorem_13_4_bound
  have hres1 := primrec_gm17_13_1 hv he
  have hp₀ := Primrec.fst.comp hres1
  have hq₀ := Primrec.fst.comp (Primrec.snd.comp hres1)
  have hz₀ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres1))
  have hθ₀ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres1))
  have hp := primrec_max hp₀ (Primrec.const 1)
  have hq := primrec_add (primrec_mul (Primrec.const 6) (primrec_drawBound he)) hq₀
  have hh := primrec_add (primrec_mul (primrec_pow hq (Primrec.const 2)) hp) (primrec_mul hq₀ hp)
  have hres3 := primrec_gm17_13_3 hp hh hz₀
  exact hp.pair (hq.pair ((Primrec.snd.comp hres3).pair
    (primrec_max hθ₀ (Primrec.fst.comp hres3))))

/-! ### GM21 explicit bounds -/

private def tangleRegionAB : ℕ → ℕ × ℕ :=
  Nat.rec (1, 7) fun _ st => (1 + st.1 * st.1, 6 + st.1 * st.2 + st.2)

private lemma tangleRegionBound_eq_linear (k θ : ℕ) :
    GM21.tangleRegionBound k θ = (tangleRegionAB k).1 * θ + (tangleRegionAB k).2 := by
  induction k generalizing θ with
  | zero =>
    change (θ + 6) + 1 = 1 * θ + 7
    omega
  | succ k ih =>
    change (θ + 6) + GM21.tangleRegionBound k (GM21.tangleRegionBound k θ) =
      (1 + (tangleRegionAB k).1 * (tangleRegionAB k).1) * θ +
        (6 + (tangleRegionAB k).1 * (tangleRegionAB k).2 + (tangleRegionAB k).2)
    rw [ih, ih]
    ring

private lemma primrec_tangleRegionBound {α : Type} [Primcodable α]
    {k θ : α → ℕ} (hk : Primrec k) (hθ : Primrec θ) :
    Primrec fun x => GM21.tangleRegionBound (k x) (θ x) := by
  have hAB : Primrec tangleRegionAB := by
    unfold tangleRegionAB
    refine Primrec.nat_rec₁ (1, 7) (Primrec₂.mk ?_)
    have h1 : Primrec fun q : ℕ × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
    have h2 : Primrec fun q : ℕ × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
    exact (primrec_add (Primrec.const 1) (primrec_mul h1 h1)).pair
      (primrec_add (primrec_add (Primrec.const 6) (primrec_mul h1 h2)) h2)
  exact (primrec_add (primrec_mul (Primrec.fst.comp (hAB.comp hk)) hθ)
    (Primrec.snd.comp (hAB.comp hk))).of_eq fun x => (tangleRegionBound_eq_linear (k x) (θ x)).symm

private lemma primrec_gm21_4_6 {α : Type} [Primcodable α]
    {k ρ θ' : α → ℕ} (hk : Primrec k) (hρ : Primrec ρ) (hθ' : Primrec θ') :
    Primrec fun x => GM21.theorem_4_6_bound (k x) (ρ x) (θ' x) := by
  unfold GM21.theorem_4_6_bound
  exact Primrec.nat_iterate hρ hθ'
    (Primrec₂.mk (primrec_tangleRegionBound (hk.comp Primrec.fst) Primrec.snd))

private lemma primrec_gm21_2_6 {α : Type} [Primcodable α]
    {p k : α → ℕ} (hp : Primrec p) (hk : Primrec k) :
    Primrec fun x => GM21.theorem_2_6_bound (p x) (k x) := by
  unfold GM21.theorem_2_6_bound GM21.monotoneIntervalLen
  refine primrec_natRec (s := fun x j acc => acc * ((2 * p x + 1) * (p x + (0 + j) + 1) ^ (2 * (p x + (0 + j))) + 1))
    (primrec_add hk (Primrec.const 1)) (Primrec.const 1) ?_
  have hp' : Primrec fun q : α × ℕ × ℕ => p q.1 := hp.comp Primrec.fst
  have hj : Primrec fun q : α × ℕ × ℕ => 0 + q.2.1 := primrec_add (Primrec.const 0) (Primrec.fst.comp Primrec.snd)
  have hacc : Primrec fun q : α × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
  have hf := primrec_mul
    (primrec_add (primrec_mul (Primrec.const 2) hp') (Primrec.const 1))
    (primrec_pow (primrec_add (primrec_add hp' hj) (Primrec.const 1))
      (primrec_mul (Primrec.const 2) (primrec_add hp' hj)))
  exact primrec_mul hacc (primrec_add hf (Primrec.const 1))

private lemma primrec_gm21_6_4 {α : Type} [Primcodable α]
    {p q : α → ℕ} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_6_4_bound (p x) (q x) := by
  unfold GM21.theorem_6_4_bound
  have hn := primrec_gm21_2_6 hp (primrec_mul (Primrec.const 2) hq)
  exact primrec_pow hn hn

private lemma primrec_gm21_6_5 {α : Type} [Primcodable α]
    {p q : α → ℕ} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_6_5_bound (p x) (q x) := by
  unfold GM21.theorem_6_5_bound
  exact primrec_mul (primrec_gm21_2_6 hp (primrec_mul (Primrec.const 2) hq))
    (primrec_add (primrec_mul (Primrec.const 2) (primrec_gm21_6_4 (primrec_add hp (primrec_mul (Primrec.const 2) hq)) hq))
      (Primrec.const 1))

private lemma primrec_gm21_6_6 {α : Type} [Primcodable α]
    {p q : α → ℕ} (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_6_6_bound (p x) (q x) := by
  unfold GM21.theorem_6_6_bound
  exact primrec_mul (Primrec.const 3) (primrec_gm21_6_5 (primrec_add hp (primrec_mul (Primrec.const 2) hq)) hq)

private lemma primrec_gm21_6_7 {α : Type} [Primcodable α]
    {p r q : α → ℕ} (hp : Primrec p) (hr : Primrec r) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_6_7_bound (p x) (r x) (q x) := by
  unfold GM21.theorem_6_7_bound GM21.discBaseBound
  have hr3 := primrec_sub hr (Primrec.const 3)
  have hp' := primrec_add hp (primrec_mul (primrec_mul (Primrec.const 2) hq) hr3)
  exact primrec_mul (primrec_pow (Primrec.const 2) hr3)
    (primrec_max (primrec_gm21_6_4 hp' hq) (primrec_max (primrec_gm21_6_5 hp' hq) (primrec_gm21_6_6 hp' hq)))

private lemma primrec_gm21_6_3 {α : Type} [Primcodable α]
    {n c p r q : α → ℕ} (hn : Primrec n) (hc : Primrec c) (hp : Primrec p)
    (hr : Primrec r) (hq : Primrec q) :
    Primrec fun x => GM21.Induction.theorem_6_3_bound (n x) (c x) (p x) (r x) (q x) := by
  unfold GM21.Induction.theorem_6_3_bound
  have hstep : Primrec₂ fun (x : α) (st : ℕ × ℕ × ℕ) => GM21.Induction.step63 (q x) st := by
    refine Primrec₂.mk ?_
    unfold GM21.Induction.step63
    have hq' : Primrec fun r : α × ℕ × ℕ × ℕ => q r.1 := hq.comp Primrec.fst
    have hc' : Primrec fun r : α × ℕ × ℕ × ℕ => r.2.1 := Primrec.fst.comp Primrec.snd
    have hp' : Primrec fun r : α × ℕ × ℕ × ℕ => r.2.2.1 := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hr' : Primrec fun r : α × ℕ × ℕ × ℕ => r.2.2.2 := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have hcNext := primrec_add (primrec_add hr' (primrec_mul (Primrec.const 2) hc')) (Primrec.const 2)
    have hpNext := primrec_add hp' (primrec_mul (primrec_mul (Primrec.const 4) hq') (primrec_add hc' (Primrec.const 1)))
    exact hcNext.pair (hpNext.pair hcNext)
  have hst := Primrec.nat_iterate hn (hc.pair (hp.pair hr)) hstep
  exact primrec_mul (primrec_pow (Primrec.const 2) hn)
    (primrec_gm21_6_7
      (primrec_add (Primrec.fst.comp (Primrec.snd.comp hst))
        (primrec_mul (primrec_mul (Primrec.const 4) hq) (Primrec.fst.comp hst)))
      (primrec_add (Primrec.snd.comp (Primrec.snd.comp hst))
        (primrec_mul (Primrec.const 2) (Primrec.fst.comp hst)))
      hq)

private lemma primrec_gm21_3_2_cuff {α : Type} [Primcodable α]
    {a b t z : α → ℕ} (ha : Primrec a) (hb : Primrec b) (ht : Primrec t) (hz : Primrec z) :
    Primrec fun x => GM21.theorem_3_2_of_cuff_ins_bound GM07.vModelExplicit (a x) (b x) (t x) (z x) := by
  unfold GM21.theorem_3_2_of_cuff_ins_bound
  have hsep := primrec_add (primrec_mul (Primrec.const 2) (primrec_max (primrec_gm12_3_1 ha hb ht hz) hz)) (Primrec.const 1)
  have hN := primrec_mul (primrec_mul (Primrec.const 42) (primrec_add hz (Primrec.const 4)))
    (primrec_vModelExplicit ha hb (Primrec.const 4) (primrec_add hz (Primrec.const 4)))
  have htwo := primrec_add (primrec_mul (Primrec.const 2)
    (primrec_add (primrec_mul (Primrec.const 2) (primrec_max hN hz)) (Primrec.const 1))) (Primrec.const 1)
  exact primrec_max hsep (primrec_max (primrec_max (Primrec.const 1) hz) htwo)

private lemma primrec_gm21_5_1_raw {α : Type} [Primcodable α]
    {k c p : α → ℕ} (hk : Primrec k) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => GM21.theorem_5_1_bound_raw GM07.vModelExplicit (k x) (c x) (p x) := by
  unfold GM21.theorem_5_1_bound_raw
  have hη : Primrec fun x => GM17.maxRange (k x + 1) fun a =>
      GM17.maxRange (k x + 1) fun b => GM21.theorem_3_2_of_cuff_ins_bound GM07.vModelExplicit a b (c x) (p x) := by
    refine primrec_maxRange (primrec_add hk (Primrec.const 1)) ?_
    refine primrec_maxRange (primrec_add (hk.comp Primrec.fst) (Primrec.const 1)) ?_
    exact primrec_gm21_3_2_cuff (Primrec.snd.comp Primrec.fst) Primrec.snd
      (hc.comp (Primrec.fst.comp Primrec.fst)) (hp.comp (Primrec.fst.comp Primrec.fst))
  exact primrec_add (primrec_mul (Primrec.const 2) (primrec_max hη (primrec_add hp (Primrec.const 11)))) (Primrec.const 1)

private lemma primrec_gm21_5_1 {α : Type} [Primcodable α]
    {k c p : α → ℕ} (hk : Primrec k) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => GM21.theorem_5_1_bound GM07.vModelExplicit (k x) (c x) (p x) := by
  unfold GM21.theorem_5_1_bound
  refine primrec_maxRange (primrec_add hc (Primrec.const 1)) ?_
  refine primrec_maxRange (primrec_add (hp.comp Primrec.fst) (Primrec.const 1)) ?_
  exact primrec_gm21_5_1_raw (hk.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst) Primrec.snd

private lemma primrec_shift52 {α : Type} [Primcodable α]
    {k c p : α → ℕ} (hk : Primrec k) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => GM21.shift52 GM07.vModelExplicit (k x) (c x) (p x) := by
  unfold GM21.shift52
  exact primrec_add hp (primrec_mul (Primrec.const 3) (primrec_gm21_5_1 hk hc hp))

private lemma primrec_pTop52 {α : Type} [Primcodable α]
    {k c p : α → ℕ} (hk : Primrec k) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => GM21.pTop52 GM07.vModelExplicit (k x) (c x) (p x) := by
  unfold GM21.pTop52
  exact Primrec.nat_iterate hc hp
    (Primrec₂.mk (primrec_shift52 (hk.comp Primrec.fst) (hc.comp Primrec.fst) Primrec.snd))

private lemma primrec_addStar52 {α : Type} [Primcodable α]
    {k c p : α → ℕ} (hk : Primrec k) (hc : Primrec c) (hp : Primrec p) :
    Primrec fun x => GM21.addStar52 GM07.vModelExplicit (k x) (c x) (p x) := by
  unfold GM21.addStar52
  have hP := primrec_pTop52 hk hc hp
  exact primrec_mul
    (primrec_mul (primrec_mul (Primrec.const 2) (primrec_add hc (Primrec.const 1))) (primrec_add hP (Primrec.const 1)))
    (primrec_gm21_5_1 hk hc hP)

private lemma primrec_gm21_5_2 {α : Type} [Primcodable α]
    {k p : α → ℕ} (hk : Primrec k) (hp : Primrec p) :
    Primrec fun x => GM21.theorem_5_2_bound GM07.vModelExplicit (k x) (p x) := by
  unfold GM21.theorem_5_2_bound GM21.theorem_5_2_iter
  have hstep : Primrec₂ fun (x : α) (st : ℕ × ℕ) => GM21.closedStep52 GM07.vModelExplicit (k x) st := by
    refine Primrec₂.mk ?_
    unfold GM21.closedStep52
    have hk' : Primrec fun q : α × ℕ × ℕ => k q.1 := hk.comp Primrec.fst
    have hp' : Primrec fun q : α × ℕ × ℕ => q.2.1 := Primrec.fst.comp Primrec.snd
    have hacc : Primrec fun q : α × ℕ × ℕ => q.2.2 := Primrec.snd.comp Primrec.snd
    exact (primrec_shift52 hk' hp' (primrec_pTop52 hk' hp' hp')).pair
      (primrec_add hacc (primrec_addStar52 hk' hp' hp'))
  exact Primrec.snd.comp (Primrec.nat_iterate (primrec_add hk (Primrec.const 1)) (hp.pair (Primrec.const 1)) hstep)

private lemma primrec_gm21_7_3 {α : Type} [Primcodable α]
    {a b c p r q : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hp : Primrec p) (hr : Primrec r) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_7_3_bound GM07.vModelExplicit (a x) (b x) (c x) (p x) (r x) (q x) := by
  unfold GM21.theorem_7_3_bound
  have hlam := primrec_gm21_6_3 (primrec_add (primrec_mul (Primrec.const 2) ha) hb) hc hp hr hq
  have hk := primrec_add (primrec_mul (Primrec.const 4) ha) (primrec_mul (Primrec.const 2) hb)
  have hθ₁ := primrec_gm21_5_2 hk (primrec_mul (Primrec.const 2) (primrec_add hp hlam))
  exact primrec_mul hq (primrec_gm21_4_6 hk hc hθ₁)

private lemma primrec_gm21_8_4 {α : Type} [Primcodable α]
    {a b c p r q : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hp : Primrec p) (hr : Primrec r) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_8_4_bound GM07.vModelExplicit (a x) (b x) (c x) (p x) (r x) (q x) := by
  unfold GM21.theorem_8_4_bound
  exact primrec_add
    (primrec_max
      (primrec_gm21_7_3 ha hb hc (primrec_add hp (primrec_mul (primrec_mul (Primrec.const 2) hq) hr)) hr hq)
      (primrec_add (primrec_mul (Primrec.const 2) hq) (Primrec.const 3)))
    (primrec_mul hq hr)

private lemma primrec_gm21_9_2 {α : Type} [Primcodable α]
    {a b c p q : α → ℕ} (ha : Primrec a) (hb : Primrec b) (hc : Primrec c)
    (hp : Primrec p) (hq : Primrec q) :
    Primrec fun x => GM21.theorem_9_2_bound GM07.vModelExplicit (a x) (b x) (c x) (p x) (q x) := by
  unfold GM21.theorem_9_2_bound
  have hr := primrec_add (primrec_mul (Primrec.const 3) hp) hc
  have hn := primrec_add (primrec_mul (Primrec.const 3) hp) (primrec_mul (primrec_mul (Primrec.const 2) hq) hr)
  exact primrec_add
    (primrec_max (primrec_gm21_8_4 ha hb hc (primrec_add hp hn) hr hq)
      (primrec_add (primrec_mul (Primrec.const 2) hq) (Primrec.const 4)))
    hn

private lemma primrec_gm21_10_1 {α : Type} [Primcodable α] {n : α → ℕ} (hn : Primrec n) :
    Primrec fun x => GM21.theorem_10_1_bound GM07.vModelExplicit (n x) := by
  unfold GM21.theorem_10_1_bound
  have hres := primrec_gm17_13_4 hn (primrec_mul hn hn)
  have hp := Primrec.fst.comp hres
  have hρ := Primrec.fst.comp (Primrec.snd.comp hres)
  have hξ := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ₀ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  exact hρ.pair (hξ.pair ((primrec_add hp (Primrec.const 1)).pair
    (primrec_max hθ₀ (primrec_add (primrec_add hξ (primrec_mul (Primrec.const 4) hp)) (Primrec.const 6)))))

private lemma primrec_gm21_10_2 {α : Type} [Primcodable α]
    {n p : α → ℕ} (hn : Primrec n) (hp : Primrec p) :
    Primrec fun x => GM21.theorem_10_2_bound GM07.vModelExplicit (n x) (p x) := by
  unfold GM21.theorem_10_2_bound
  have hres := primrec_gm21_10_1 hn
  have hρ := Primrec.fst.comp hres
  have hξ := Primrec.fst.comp (Primrec.snd.comp hres)
  have hq := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hθ₁ := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hres))
  have hL := primrec_drawBound (primrec_mul hn hn)
  have hsup : Primrec fun x => GM17.maxRange (GM20.Draw.drawBound (n x * n x)) fun a =>
      GM17.maxRange (GM20.Draw.drawBound (n x * n x)) fun b =>
        GM17.maxRange ((GM21.theorem_10_1_bound GM07.vModelExplicit (n x)).1 + 1) fun c =>
          GM21.theorem_9_2_bound GM07.vModelExplicit a b c
            (p x + 2 * (GM21.theorem_10_1_bound GM07.vModelExplicit (n x)).2.1)
            (GM21.theorem_10_1_bound GM07.vModelExplicit (n x)).2.2.1 := by
    refine primrec_maxRange hL ?_
    refine primrec_maxRange (hL.comp Primrec.fst) ?_
    refine primrec_maxRange (primrec_add (hρ.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)) ?_
    exact primrec_gm21_9_2
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
      Primrec.snd
      (primrec_add (hp.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
        (primrec_mul (Primrec.const 2) (hξ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))))
      (hq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  exact primrec_max hθ₁ (primrec_add hξ (primrec_max (Primrec.const 1) hsup))

private lemma primrec_hBoundOf : Primrec (hBoundOf GM07.vModelExplicit) := by
  unfold hBoundOf theorem_3_1_bound theorem_2_1_bound GM21.theorem_1_1_bound GM21.theorem_10_4_bound
  have h7p : Primrec fun p : ℕ => 7 * p := primrec_mul (Primrec.const 7) Primrec.id
  have hn : Primrec fun p : ℕ => 5 * (7 * p) / 2 + 1 :=
    primrec_add (primrec_div (primrec_mul (Primrec.const 5) h7p) (Primrec.const 2)) (Primrec.const 1)
  have h102 := primrec_gm21_10_2 hn h7p
  exact primrec_add (primrec_mul (Primrec.const 2)
    (primrec_div (primrec_mul (Primrec.const 3) h102) (Primrec.const 2))) (Primrec.const 3)

private lemma primrec_hBound : Primrec hBound := by
  unfold hBound
  exact primrec_maxRange (primrec_add Primrec.id (Primrec.const 1))
    (primrec_hBoundOf.comp Primrec.snd)

end Computability

/-- `hBound` is computable (in fact primitive recursive). -/
theorem hBound_computable : Computable hBound :=
  primrec_hBound.to_comp

end GraphMinor.GM22
