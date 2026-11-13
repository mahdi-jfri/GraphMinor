module

public import GraphMinor.GM22.Section7b
public import GraphMinor.GM22.Cited
import GraphMinor.GM22.Section7d5

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 8 Parallel Interface: Statement of (7.4)

This file states **7.4** (`GM22Theorem74Statement`, pages 552–553) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563, in the same form as `theorem_7_3` in
`GraphMinor/GM22/Section7c5.lean`, so that Section 8 (`theorem_8_2` and `theorem_8_3`) can take it
as a hypothesis. `theorem_7_4_proof` (`GraphMinor/GM22/Section7d5.lean`) proves it.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM14

universe w u v u₁ v₁

/-- **Graph Minors XXII, (7.4)** (Section 7, pages 552–553):
"For all integers $q, \delta, \tau \ge 0$ there exists $\theta \ge 4$ with the following property.
Let (J1)–(J7) hold, and let $\mathcal{B} \subseteq \mathcal{A}$ be sufficient for $\phi$. Let
$A_1, \ldots, A_t \in \mathcal{B}$ where $t \le \tau$, and let
$d(D(A), \Sigma \setminus \Delta) \ge \theta$ for every
$A \in \mathcal{B} \setminus \{A_1, \ldots, A_t\}$. Let $A'_1, \ldots, A'_t \in \mathcal{A}$, and
suppose that ...
(i) for $1 \le i \le t$, $(A'_i, \pi(A'_i) + \omega)$ has the same $\delta$-folio as
$(A_i, \pi(A_i) + \omega)$,
(ii) for $1 \le i \le t$, $D(A_i) \cap \Delta = \emptyset$,
(iii) for $1 \le i \le t$, $d(v^*, D(A'_i)) \ge \theta$ and $D(A'_i) \cap \Delta = \emptyset$,
(iv) for $1 \le i < j \le t$, $d(D(A'_i), D(A'_j)) \ge \theta$.
Then there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
def GM22Theorem74Statement : Prop :=
  ∀ (q δ τ : ℕ), ∃ θ : ℕ, 4 ≤ θ ∧
    ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
      {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
      (ιV : S ↪ α) (ιE : Set S ↪ β)
      (R_G : RootedDigraph α β q) (W : Set α)
      (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
      (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
      (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (ins : Set S → Set S) (d : Set S → Set S → ℕ)
      (D : Graph α β → Set S)
      (N K : Graph α β) (Δ : Set S) (v_star : S)
      (R_H : RootedDigraph αH βH q)
      (φV : αH → Graph α β) (φE : βH → β)
      (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
      ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T →
      IsSufficientFor W 𝒜 ℬ K R_H φV φE →
      ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
      t ≤ τ →
      (∀ i : Fin t, A_fam i ∈ ℬ) →
      (∀ i : Fin t, A_fam' i ∈ 𝒜) →
      (∀ A ∈ ℬ \ Set.range A_fam,
        θ ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) →
      ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
      (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
        (hπi : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (ιV ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
        (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
          seqConcat (fun k : Fin (πLen (A_fam i)) =>
            ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G (A_fam' i) hA'i
            (seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
          (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
      (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
      (∀ i : Fin t, θ ≤ subsetTangleDist Γ ord d {v_star} (D (A_fam' i))) →
      (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
      (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ ord d (D (A_fam' i)) (D (A_fam' j))) →
      HasRootedDigraphModel
        (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots hJ.roots_mem_deleteVerts_v_star)
        R_H

/-- Discharge `GM22Theorem74Statement` from `theorem_7_4_proof` (`GraphMinor/GM22/Section7d5.lean`). -/
theorem theorem_7_4_parallel  :
    GM22Theorem74Statement.{w, u, v, u₁, v₁} :=
  theorem_7_4_proof

end GraphMinor.GM22
