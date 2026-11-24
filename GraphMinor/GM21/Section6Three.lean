module

public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.Section6Base
import GraphMinor.GM21.Section6ClaimThreeProof
import GraphMinor.GM21.Section6LastStep

/-!
# Graph Minors XXI, (6.3)

"**6.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\lambda \ge 0$ such that, if $G$ is a graph with a presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$, and there is an exhaustive vital $p$-linkage in $G$, then there are at most
$\lambda$ $\Sigma$-jumps.*" (page 24 of the preprint.)

The proof is by induction on the type `(n, c)` of `Σ` (`Induction.HasType`), in lexicographic
order. Let `λ₂ = λ(p + 4q, q, r + 2)` and `λ₁ = λ(p + 4q, q, r + 1)` be the bounds for the smaller
types (`exists_uniform_bound`). The step (`boundForType_step`) has four cases.
* `c = 0`: there are no jumps (`boundForType_zero`).
* `(n, c) = (0, 1)`: `Σ` is a disc, and (6.7) gives the bound (`boundForType_disc`).
* `c = 1` and `n ≥ 1`: the last step gives `max(λ₂, 2λ₁)` (`LastStep.last_step`).
* `c ≥ 2`: claim (3) gives `λ₂` (`ClaimThree.claim_3`).

`theorem_6_3_parallel_proof` is (6.3).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

universe u v

namespace Induction

open Set Topology GraphMinor.Surface

/-- One Euler-genus reduction step for the explicit bound of Graph Minors XXI, (6.3). -/
def step63 (q : ℕ) (st : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (st.2.2 + 2 * st.1 + 2, st.2.1 + 4 * q * (st.1 + 1), st.2.2 + 2 * st.1 + 2)

/-- Explicit jump bound for Graph Minors XXI, (6.3), indexed by surface type `(n, c)` and `(p, r, q)`. -/
def theorem_6_3_bound (n c p r q : ℕ) : ℕ :=
  let st := Nat.iterate (step63 q) n (c, p, r)
  2 ^ n * theorem_6_7_bound (st.2.1 + 4 * q * st.1) (st.2.2 + 2 * st.1) q

private lemma step63_mono (q : ℕ) {c₁ c₂ p₁ p₂ r₁ r₂ : ℕ}
    (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) :
    let s₁ := step63 q (c₁, p₁, r₁)
    let s₂ := step63 q (c₂, p₂, r₂)
    s₁.1 ≤ s₂.1 ∧ s₁.2.1 ≤ s₂.2.1 ∧ s₁.2.2 ≤ s₂.2.2 := by
  dsimp only [step63]
  refine ⟨by omega, ?_, by omega⟩
  have := Nat.mul_le_mul_left (4 * q) (by omega : c₁ + 1 ≤ c₂ + 1)
  omega

private lemma iterate_step63_mono (q : ℕ) : ∀ (n : ℕ) {c₁ c₂ p₁ p₂ r₁ r₂ : ℕ},
    c₁ ≤ c₂ → p₁ ≤ p₂ → r₁ ≤ r₂ →
    let s₁ := Nat.iterate (step63 q) n (c₁, p₁, r₁)
    let s₂ := Nat.iterate (step63 q) n (c₂, p₂, r₂)
    s₁.1 ≤ s₂.1 ∧ s₁.2.1 ≤ s₂.2.1 ∧ s₁.2.2 ≤ s₂.2.2 := by
  intro n
  induction n with
  | zero =>
    intro _ _ _ _ _ _ hc hp hr
    exact ⟨hc, hp, hr⟩
  | succ n ih =>
    intro c₁ c₂ p₁ p₂ r₁ r₂ hc hp hr
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨h1, h2, h3⟩ := ih hc hp hr
    exact step63_mono q h1 h2 h3

private lemma theorem_6_3_bound_succ (n c p r q : ℕ) :
    theorem_6_3_bound (n + 1) c p r q =
      2 * theorem_6_3_bound n (r + 2 * c + 2) (p + 4 * q * (c + 1)) (r + 2 * c + 2) q := by
  dsimp only [theorem_6_3_bound]
  rw [Function.iterate_succ_apply]
  dsimp only [step63]
  rw [Nat.pow_succ]
  ring

private lemma theorem_6_3_bound_mono_cpr {n c₁ c₂ p₁ p₂ r₁ r₂ q : ℕ}
    (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) :
    theorem_6_3_bound n c₁ p₁ r₁ q ≤ theorem_6_3_bound n c₂ p₂ r₂ q := by
  dsimp only [theorem_6_3_bound]
  obtain ⟨h1, h2, h3⟩ := iterate_step63_mono q n hc hp hr
  refine Nat.mul_le_mul_left _ (theorem_6_7_bound_mono ?_ (by omega) le_rfl)
  have := Nat.mul_le_mul_left (4 * q) h1
  omega

private lemma theorem_6_3_bound_le_succ (n c p r q : ℕ) :
    theorem_6_3_bound n c p r q ≤ theorem_6_3_bound (n + 1) c p r q := by
  rw [theorem_6_3_bound_succ]
  have hle : theorem_6_3_bound n c p r q ≤
      theorem_6_3_bound n (r + 2 * c + 2) (p + 4 * q * (c + 1)) (r + 2 * c + 2) q :=
    theorem_6_3_bound_mono_cpr (by omega) (by omega) (by omega)
  omega

theorem theorem_6_3_bound_mono {n₁ n₂ c₁ c₂ p₁ p₂ r₁ r₂ q : ℕ}
    (hn : n₁ ≤ n₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) (hr : r₁ ≤ r₂) :
    theorem_6_3_bound n₁ c₁ p₁ r₁ q ≤ theorem_6_3_bound n₂ c₂ p₂ r₂ q := by
  have h1 : theorem_6_3_bound n₁ c₁ p₁ r₁ q ≤ theorem_6_3_bound n₁ c₂ p₂ r₂ q :=
    theorem_6_3_bound_mono_cpr hc hp hr
  have h2 : ∀ k, n₁ ≤ k → theorem_6_3_bound n₁ c₂ p₂ r₂ q ≤ theorem_6_3_bound k c₂ p₂ r₂ q := by
    intro k hk
    induction hk with
    | refl => exact le_rfl
    | @step m _ ih => exact ih.trans (theorem_6_3_bound_le_succ m c₂ p₂ r₂ q)
  exact h1.trans (h2 n₂ hn)

/-- Explicit version of `boundForType_all`: every surface of type `(n, c)` satisfies the jump
bound `theorem_6_3_bound n c p r q`. -/
theorem boundForType_explicit (n c : ℕ) :
    ∀ (p r q : ℕ), 1 ≤ q →
      ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S], IsSurface S → HasType S n c →
        ∀ {α : Type u} {β : Type v}
          (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
          (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
          (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
          G.IsGraph →
          r' ≤ r →
          PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
          IsExhaustiveLinkage G Γ_sub r' H L →
          IsPLinkage G L p →
          (sigmaJumps Γ Γ_sub ιV).encard ≤ theorem_6_3_bound n c p r q := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ihn =>
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
      intro p r q hq
      have hbelow : ∀ (p' r' lam : ℕ),
          (∀ n' c', TypeLt n' c' n c → 1 ≤ c' → c' ≤ r' → theorem_6_3_bound n' c' p' r' q ≤ lam) →
          BoundBelow.{u, v} n c p' q r' lam := by
        intro p' r' lam hle S _ _ hS n' c' hT hlt α β G Γ Γ_sub ιV ιE r'' F_star H μ L
          hG hr'' hd hL hLp
        rcases Nat.eq_zero_or_pos c' with rfl | hc'pos
        · have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
          have hc : cuffs S = ∅ := (ncard_eq_zero hfin).mp hT.ncard_cuffs
          rw [sigmaJumps_eq_empty_of_bd (bd_eq_empty_of_cuffs hc)]
          simp
        · have hc' : c' ≤ r' := by
            obtain ⟨qf, hP, -, -⟩ := hd
            rw [← hT.ncard_cuffs]
            exact (ncard_cuffs_le hP).trans hr''
          have hstep : (sigmaJumps Γ Γ_sub ιV).encard ≤ theorem_6_3_bound n' c' p' r' q := by
            rcases hlt with h | ⟨rfl, h⟩
            · exact ihn n' h c' p' r' q hq S hS hT G Γ Γ_sub ιV ιE r'' F_star H μ L hG hr'' hd hL hLp
            · exact ihc c' h p' r' q hq S hS hT G Γ Γ_sub ιV ιE r'' F_star H μ L hG hr'' hd hL hLp
          exact hstep.trans (Nat.cast_le.mpr (hle n' c' hlt hc'pos hc'))
      rcases c with _ | _ | c₀
      · intro S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L _ _ _ _ _
        have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
        have hc : cuffs S = ∅ := (ncard_eq_zero hfin).mp hT.ncard_cuffs
        rw [sigmaJumps_eq_empty_of_bd (bd_eq_empty_of_cuffs hc)]
        simp
      · rcases n with _ | m
        · intro S _ _ _ hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp
          have hdisc := theorem_6_7_explicit.{u, v, 0} p r q hq G Γ Γ_sub ιV ιE F_star H μ L
            hr (isClosedDiscSpace_of_hasType hT) hG hd hL hLp
          have hle : theorem_6_7_bound p r q ≤ theorem_6_3_bound 0 1 p r q := by
            dsimp only [theorem_6_3_bound]
            simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
            exact theorem_6_7_bound_mono (by omega) (by omega) le_rfl
          exact hdisc.trans (Nat.cast_le.mpr hle)
        · let lam₂ := theorem_6_3_bound m (r + 2) (p + 4 * q) (r + 2) q
          let lam₁ := theorem_6_3_bound m (r + 1) (p + 4 * q) (r + 1) q
          have hlam₂ : BoundBelow.{u, v} (m + 1) 1 (p + 4 * q) q (r + 2) lam₂ := by
            refine hbelow _ _ _ fun n' c' hlt hc'pos hc' => ?_
            rcases hlt with hn' | ⟨_, hc'0⟩
            · exact theorem_6_3_bound_mono (by omega) hc' le_rfl le_rfl
            · omega
          have hlam₁ : BoundBelow.{u, v} (m + 1) 1 (p + 4 * q) q (r + 1) lam₁ := by
            refine hbelow _ _ _ fun n' c' hlt hc'pos hc' => ?_
            rcases hlt with hn' | ⟨_, hc'0⟩
            · exact theorem_6_3_bound_mono (by omega) hc' le_rfl le_rfl
            · omega
          have hle_max : max lam₂ (lam₁ + lam₁) ≤ theorem_6_3_bound (m + 1) 1 p r q := by
            rw [theorem_6_3_bound_succ]
            have h1 : lam₁ ≤ theorem_6_3_bound m (r + 2 * 1 + 2) (p + 4 * q * (1 + 1)) (r + 2 * 1 + 2) q :=
              theorem_6_3_bound_mono_cpr (by omega) (by omega) (by omega)
            have h2 : lam₂ ≤ theorem_6_3_bound m (r + 2 * 1 + 2) (p + 4 * q * (1 + 1)) (r + 2 * 1 + 2) q :=
              theorem_6_3_bound_mono_cpr (by omega) (by omega) (by omega)
            omega
          intro S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp
          exact (LastStep.last_step hS hT (Nat.succ_pos m) hlam₂ hlam₁ hG hr hd hL hLp).trans
            (Nat.cast_le.mpr hle_max)
      · have hlam₂ : BoundBelow.{u, v} n (c₀ + 2) (p + 4 * q) q (r + 2)
            (theorem_6_3_bound n (c₀ + 2) p r q) := by
          refine hbelow _ _ _ fun n' c' hlt _ hc' => ?_
          rcases hlt with hn' | ⟨rfl, hc'lt⟩
          · rcases n with _ | m
            · omega
            · rw [theorem_6_3_bound_succ]
              have hle : theorem_6_3_bound n' c' (p + 4 * q) (r + 2) q ≤
                  theorem_6_3_bound m (r + 2 * (c₀ + 2) + 2) (p + 4 * q * (c₀ + 2 + 1))
                    (r + 2 * (c₀ + 2) + 2) q := by
                refine theorem_6_3_bound_mono (by omega) (by omega) ?_ (by omega)
                have : 4 * q * 1 ≤ 4 * q * (c₀ + 2 + 1) := Nat.mul_le_mul_left _ (by omega)
                omega
              omega
          · rcases n' with _ | m
            · dsimp only [theorem_6_3_bound]
              simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
              refine theorem_6_7_bound_mono ?_ (by omega) le_rfl
              have h1 : 4 * q + 4 * q * c' = 4 * q * (c' + 1) := by ring
              have h2 : 4 * q * (c' + 1) ≤ 4 * q * (c₀ + 2) := Nat.mul_le_mul_left _ (by omega)
              omega
            · rw [theorem_6_3_bound_succ, theorem_6_3_bound_succ]
              refine Nat.mul_le_mul_left 2 (theorem_6_3_bound_mono_cpr (by omega) ?_ (by omega))
              have h1 : 4 * q + 4 * q * (c' + 1) = 4 * q * (c' + 2) := by ring
              have h2 : 4 * q * (c' + 2) ≤ 4 * q * (c₀ + 2 + 1) := Nat.mul_le_mul_left _ (by omega)
              omega
        intro S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp
        exact ClaimThree.claim_3 hS hT hlam₂ hG hr hd hL hLp (by rw [hT.ncard_cuffs]; omega)

/-- The bound holds for every type, by induction in the order `TypeLt`. -/
theorem boundForType_all (n c : ℕ) : BoundForType.{u, v} n c :=
  fun p r q hq => ⟨theorem_6_3_bound n c p r q, boundForType_explicit.{u, v} n c p r q hq⟩

end Induction

open Induction

/-- Explicit version of **Graph Minors XXI, (6.3)** with bound `theorem_6_3_bound n c p r q`. -/
theorem theorem_6_3_explicit {n c : ℕ} (S : Type) [TopologicalSpace S] [ConnectedSpace S]
    (hS : Surface.IsSurface S) (hT : HasType S n c) (p r q : ℕ) (hq : 1 ≤ q) :
    ∀ {α : Type u} {β : Type v}
      (G : Hypergraph α β) (Γ : Surface.Drawing S) (Γ_sub : Hypergraph α β)
      (ιV : S → α) (ιE : Set S → β)
      (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
      (μ : BoundaryUnit S → Hypergraph α β) (L : Hypergraph α β),
      G.IsGraph →
      r' ≤ r →
      PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
      IsExhaustiveLinkage G Γ_sub r' H L →
      IsPLinkage G L p →
      (sigmaJumps Γ Γ_sub ιV).encard ≤ theorem_6_3_bound n c p r q :=
  boundForType_explicit.{u, v} n c p r q hq S hS hT

/-- **Graph Minors XXI, (6.3)** (page 24 of the preprint). -/
theorem theorem_6_3_parallel_proof : GM21Theorem63Statement.{u, v, 0} := by
  intro S _ _ hS p r q hq
  obtain ⟨n, c, hT⟩ := exists_hasType hS
  exact ⟨theorem_6_3_bound n c p r q, theorem_6_3_explicit.{u, v} S hS hT p r q hq⟩

end GM21
end GraphMinor
