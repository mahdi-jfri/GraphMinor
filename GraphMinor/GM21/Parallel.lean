module

public import GraphMinor.GM21.Defs

/-!
# Graph Minors XXI: statements of (5.2), (6.3) and (7.3)

Statements of three results of N. Robertson and P. D. Seymour, *Graph Minors. XXI. Graphs with
unique linkages*, J. Combin. Theory Ser. B 99 (2009), 583–616:

- `GM21Theorem52Statement`, the statement of (5.2), which `theorem_7_3` uses;
- `GM21Theorem63Statement`, the statement of (6.3), which `theorem_7_3` uses;
- `GM21Theorem73Statement`, the statement of (7.3), which `theorem_7_3` proves.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v w

/-- **Graph Minors XXI, (5.2)** (Section 5, page 17 of the preprint):
"**5.2** *For every surface* $\Sigma$ *with* $bd(\Sigma) = \emptyset$ *and every integer*
$p \ge 0$ *there exists* $\theta \ge 1$ *such that every drawing in* $\Sigma$ *with a tangle of
order* $\ge \theta$ *has no vital* $p$*-linkage.*"

A surface is connected (page 10 of the preprint: "A *surface* is a connected compact 2-manifold,
possibly with boundary"). A drawing `Γ` is a graph through `Γ.toHypergraph`. -/
def GM21Theorem52Statement : Prop :=
  ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S],
    IsSurface S → bd S = ∅ →
    ∀ p : ℕ, ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Drawing S) (θ_G : ℕ) (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
        θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p

/-- **Graph Minors XXI, (6.3)** (Section 6, page 24 of the preprint):
"**6.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\lambda \ge 0$ such that, if $G$ is a graph with a presentation in $\Sigma$ of depth $\le q$ and
defect $\le r$, and there is an exhaustive vital $p$-linkage in $G$, then there are at most
$\lambda$ $\Sigma$-jumps.*"

The `Σ`-jumps are those of the drawing `Γ` of the presentation (`sigmaJumps`). -/
def GM21Theorem63Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S],
    IsSurface S →
    ∀ (p r q : ℕ), 1 ≤ q →
      ∃ lam : ℕ,
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
          (sigmaJumps Γ Γ_sub ιV).encard ≤ lam

/-- **Graph Minors XXI, (7.3)** (Section 7, page 31 of the preprint):
"**7.3** *For every surface $\Sigma$ and all integers $p, r \ge 0$ and $q \ge 1$, there exists
$\theta \ge 1$ such that, if a graph $G$ has a presentation in $\Sigma$ of depth $\le q$, and
defect $\le r$ which surrounds a tangle of order $\ge \theta$, then $G$ has no vital
$p$-linkage.*" -/
def GM21Theorem73Statement : Prop :=
  ∀ (S : Type w) [TopologicalSpace S] [ConnectedSpace S],
    IsSurface S →
    ∀ (p r q : ℕ), 1 ≤ q →
      ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ {α : Type u} {β : Type v}
          (G : Hypergraph α β) (Γ : Drawing S) (Γ_sub : Hypergraph α β)
          (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S) (H : Fin r' → Hypergraph α β)
          (μ : BoundaryUnit S → Hypergraph α β)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
          G.IsGraph →
          r' ≤ r →
          PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star H μ q →
          θ ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PresentationSurroundsTangle Γ r' F_star μ 𝒯 →
          ¬ HasVitalPLinkage G p

end GM21
end GraphMinor
