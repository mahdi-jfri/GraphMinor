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

/-- **The induction step of (6.3)** (Graph Minors XXI, pages 28–29 of the preprint), with
`λ = max(λ(p + 4q, q, r + 2), 2λ(p + 4q, q, r + 1))`. -/
theorem boundForType_step {n c : ℕ} (ih : ∀ n' c', TypeLt n' c' n c → BoundForType.{u, v} n' c') :
    BoundForType.{u, v} n c := by
  intro p r q hq
  obtain ⟨lam₂, hlam₂⟩ := exists_uniform_bound ih (p + 4 * q) (r + 2) q hq
  obtain ⟨lam₁, hlam₁⟩ := exists_uniform_bound ih (p + 4 * q) (r + 1) q hq
  rcases c with _ | _ | c
  · exact boundForType_zero n p r q hq
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact boundForType_disc p r q hq
    · exact ⟨max lam₂ (lam₁ + lam₁), fun S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd
        hL hLp => LastStep.last_step hS hT hn hlam₂ hlam₁ hG hr hd hL hLp⟩
  · exact ⟨lam₂, fun S _ _ hS hT α β G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp =>
      ClaimThree.claim_3 hS hT hlam₂ hG hr hd hL hLp (by rw [hT.ncard_cuffs]; omega)⟩

/-- The bound holds for every type, by induction in the order `TypeLt`. -/
theorem boundForType_all (n c : ℕ) : BoundForType.{u, v} n c := by
  induction n using Nat.strong_induction_on generalizing c with
  | _ n ihn =>
    induction c using Nat.strong_induction_on with
    | _ c ihc =>
      refine boundForType_step fun n' c' hlt => ?_
      rcases hlt with h | ⟨rfl, h⟩
      · exact ihn n' h c'
      · exact ihc c' h

end Induction

open Induction

/-- **Graph Minors XXI, (6.3)** (page 24 of the preprint):
"**6.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\lambda \ge 0$ such that, if $G$ is a graph with a presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$, and there is an exhaustive vital $p$-linkage in $G$, then there are at most
$\lambda$ $\Sigma$-jumps.*"

Every connected surface has a type (`exists_hasType`), and `boundForType_all` gives the bound for
it. -/
theorem theorem_6_3_parallel_proof : GM21Theorem63Statement.{u, v, 0} := by
  intro S _ _ hS p r q hq
  obtain ⟨n, c, hT⟩ := exists_hasType hS
  obtain ⟨lam, hlam⟩ := boundForType_all.{u, v} n c p r q hq
  exact ⟨lam, fun G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp =>
    hlam S hS hT G Γ Γ_sub ιV ιE r' F_star H μ L hG hr hd hL hLp⟩

end GM21
end GraphMinor
