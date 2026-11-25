module

public import GraphMinor.GM22.Section3
public import GraphMinor.GM07.ExplicitV
public import Mathlib.Computability.Partrec

import GraphMinor.GM12.Primrec
import GraphMinor.GM12.Bridge
import GraphMinor.GM16.Explicit
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

/-! ### GM17 explicit bounds -/

private lemma primrec_gm17_13_1 {α : Type} [Primcodable α]
    {vB eB : α → ℕ} (hv : Primrec vB) (he : Primrec eB) :
    Primrec fun x => GM17.theorem_13_1_bound GM07.vModelExplicit (vB x) (eB x) := by
  unfold GM17.theorem_13_1_bound
  have hres := GM16.primrec_theorem_3_1_bound
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
  have hq := primrec_add (primrec_mul (Primrec.const 6) (GM16.primrec_drawBound he)) hq₀
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
  have hL := GM16.primrec_drawBound (primrec_mul hn hn)
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
