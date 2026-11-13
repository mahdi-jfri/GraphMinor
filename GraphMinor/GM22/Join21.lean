module

public import GraphMinor.GM22.GM21Proved
public import GraphMinor.GM22.ParallelProofs
public import GraphMinor.GM22.Section2Forest
public import GraphMinor.GM22.Section3
public import GraphMinor.GM22.Section4
public import GraphMinor.GM22.Section4Sleeve
public import GraphMinor.GM22.Section5
public import GraphMinor.GM22.Section7b
public import GraphMinor.GM22.Section7c5
public import GraphMinor.GM22.Section7d5

/-!
# Join of Graph Minors XXI (1.1) and Graph Minors XXII

This file connects `GM21.theorem_1_1_proof` (`GraphMinor/GM21/Final.lean`) to Graph Minors XXII's
cited hypothesis `GM22.GM21Theorem11Statement` (`GraphMinor/GM22/Cited.lean`), and deduces the top
results of `GraphMinor/GM22/ParallelProofs.lean` and the numbered theorems of Graph Minors XXII
with no hypotheses.

## Main results

- `GM22.gm21Theorem11`: proves `GM22.GM21Theorem11Statement.{u, v}` from `GM21.theorem_1_1_proof`.
- `GM22.theorem_3_1_parallel_proved`: proves `GM22Theorem31Statement.{w, u, v}` with no hypotheses.
- `GM22.theorem_5_3_parallel_proved`: proves `GM22Theorem53Statement.{w, u, v}` with no hypotheses.
- `GM22.theorem_2_1_proved`, `GM22.theorem_3_1_proved`, `GM22.theorem_4_1_proved`,
  `GM22.theorem_4_2_proved`, `GM22.theorem_5_3_proved`, `GM22.theorem_7_2_proved`,
  `GM22.theorem_7_3_proved`, `GM22.theorem_7_4_proved`: the numbered theorems of Graph Minors XXII
  with `h11 : GM21Theorem11Statement.{u, v}` discharged by `GM22.gm21Theorem11`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁ u₂ v₂

/-! ## Section 1: Bridge between `GM21.GM21Theorem11Statement` and `GM22.GM21Theorem11Statement` -/

/-! ## Section 2: Top Results of `GraphMinor/GM22/ParallelProofs.lean` with No Hypotheses -/

/-- Proof of `GM22Theorem31Statement` (`Parallel.lean`) from `gm21Theorem11`. -/
theorem theorem_3_1_parallel_proved :
    GM22Theorem31Statement.{w, u, v} :=
  theorem_3_1_parallel.{w, u, v}

/-- Proof of `GM22Theorem53Statement` (`Parallel.lean`) from `gm21Theorem11`. -/
theorem theorem_5_3_parallel_proved :
    GM22Theorem53Statement.{w, u, v} :=
  theorem_5_3_parallel.{w, u, v}

/-! ## Section 3: Numbered Theorems of Graph Minors XXII with No Hypotheses -/

/-- **Graph Minors XXII, 2.1** (page 531), with `GM21Theorem11Statement` proved:
For every integer `p ≥ 0` there exists `w ≥ 0` such that for every graph `G`, if there is a vital
subgraph for some subset `Z ⊆ V(G)` with `|Z| ≤ p`, then `G` has tree-width at most `w`. -/
theorem theorem_2_1_proved (p : ℕ) :
    ∃ w : ℕ, ∀ {α : Type u} {β : Type v} (G L : Graph α β) (Z : Set α),
      V(G).Finite → E(G).Finite → Z ⊆ V(G) → Z.ncard ≤ p →
      IsVitalFor G L Z → TreeWidthLE G w :=
  theorem_2_1_proof.{u, v} p

/-- **Graph Minors XXII, 3.1** (page 534), with `GM21Theorem11Statement` proved. -/
theorem theorem_3_1_proved (p : ℕ) :
    ∃ h ≥ 1, ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
        Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
        ∀ (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
        ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
        ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
        ∃ L' ≤ G.deleteVerts {ιV v₀},
          HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L :=
  theorem_3_1_proof.{u, v, w} p

/-- **Graph Minors XXII, 4.1** (page 537), with `GM21Theorem11Statement` proved. -/
theorem theorem_4_1_proved (p : ℕ) :
    ∃ h ≥ 1, ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  theorem_4_1_proof.{u, v, w} p

/-- **Graph Minors XXII, 4.2** (page 538), with `GM21Theorem11Statement` proved. -/
theorem theorem_4_2_proved (p : ℕ) :
    ∃ h ≥ 1, ∀ (S Shat : Type w) [TopologicalSpace S] [T2Space S]
      [TopologicalSpace Shat] [T2Space Shat],
      (hS : IsSurface S) → (cap : GM19.IsCappedSurface S Shat) →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Surface.Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      D.U ∩ bd S ⊆ D.V → D'.V ∩ bd S = D.V ∩ bd S →
      ∀ (S_sleeve : Set S → Set Shat),
      (∀ C ∈ cuffs S, IsSleeve cap D C (S_sleeve C)) →
      (∀ C₁ ∈ cuffs S, ∀ C₂ ∈ cuffs S, C₁ ≠ C₂ → Disjoint (S_sleeve C₁) (S_sleeve C₂)) →
      (∀ C ∈ cuffs S, ∃ P : ↑(D.V ∩ C) → Graph S (Set S),
        (∀ x : ↑(D.V ∩ C), ∃ y ∈ D.V ∩ cap.emb ⁻¹' subBd (S_sleeve C),
          IsGraphPathWithEnds D.toGraph (P x) x.1 y) ∧
        Pairwise (fun x₁ x₂ => Disjoint V(P x₁) V(P x₂))) →
      (∀ C ∈ cuffs S,
        subBd (S_sleeve C) ⊆
          cap.emb '' (cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) ∧
        Disjoint (S_sleeve C) (cap.emb '' (ιV ⁻¹' (V(Γ) ∩ V(K))))) →
      IsVariant D D'
        ((⋃ C ∈ cuffs S, cap.emb ⁻¹' S_sleeve C) ∪
          cap.emb ⁻¹' insulatedSet (drawingMapEmb D (isClosedEmbedding_w hS cap))
            (cap.emb '' ((ιV ⁻¹' (V(Γ) ∩ V(K))) ∪ (D.V ∩ bd S))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) ∪ ιV '' (D.V ∩ bd S) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' :=
  theorem_4_2_proof.{u, v, w} p

/-- **Graph Minors XXII, 5.3** (page 540), with `GM21Theorem11Statement` proved. -/
theorem theorem_5_3_proved (p : ℕ) :
    ∃ θ : ℕ, p < θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
        {α : Type u} {β : Type v}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (Γ Γ' : Surface.Drawing S) (K L' : Graph α β)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (Z : Set α) (t : ℕ) (F : Fin t → Set S),
        IsClosedSurface S →
        V(K).Finite → E(K).Finite →
        (Γ.toEmbeddedGraph ιV ιE).Compatible K →
        Γ.IsTwoCell →
        θ ≤ ord →
        HasTangleMetric Γ ord T d →
        (∀ F₀ : Set S, IsOArc F₀ → Γ.IsNormal F₀ → (F₀ ∩ Γ.V).ncard < ord →
          IsTangleIns Γ T F₀ (ins F₀)) →
        Z ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K) →
        Z.ncard ≤ p →
        (∀ i : Fin t, IsOArc (F i) ∧ Γ.IsNormal (F i)) →
        ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ⊆ Z →
        Z ⊆ ιV '' ((⋃ i : Fin t, F i) ∩ Γ.V) ∪ V(K) →
        Pairwise (fun i j : Fin t => Disjoint (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ¬ ∃ F₀ : Set S, IsOArc F₀ ∧ Γ.IsNormal F₀ ∧
          (F₀ ∩ Γ.V).ncard < (F i ∩ Γ.V).ncard ∧ ins (F i) ⊆ ins F₀) →
        (∀ i j : Fin t, i ≠ j → θ ≤ subsetTangleDist Γ ord d (ins (F i)) (ins (F j))) →
        (∀ i : Fin t, ∀ v ∈ Γ.V, ιV v ∈ V(K) →
          θ ≤ subsetTangleDist Γ ord d (ins (F i)) {v}) →
        let R := ⋃ z ∈ {z ∈ Γ.A | ∀ v ∈ Γ.V, ιV v ∈ V(K) → θ ≤ d z {v}}, z
        let S' := Set.univ \ ⋃ i : Fin t, (ins (F i) \ F i)
        IsVariant Γ Γ' (R ∩ S') →
        (Γ'.toEmbeddedGraph ιV ιE).Compatible K →
        (Γ'.toEmbeddedGraph ιV ιE) ⊓ K = (Γ.toEmbeddedGraph ιV ιE) ⊓ K →
        (∀ i : Fin t, Γ.interSet (ins (F i)) = Γ'.interSet (ins (F i))) →
        L' ≤ graphUnion ((Γ'.interSet S').toEmbeddedGraph ιV ιE) K →
        ∃ L ≤ graphUnion ((Γ.interSet S').toEmbeddedGraph ιV ιE) K,
          effectOn L Z = effectOn L' Z ∧ L ⊓ K ≤ L' :=
  theorem_5_3_proof.{u, v, w} p

/-- **Graph Minors XXII, 7.2** (page 547), with `GM21Theorem11Statement` proved. -/
theorem theorem_7_2_proved
    (q δ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 𝒜' : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV φV' : αH → Graph α β) (φE φE' : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        IsRootedDigraphModel R_G R_H φV' φE' →
        IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE' →
        (∀ A ∈ 𝒜', θ ≤ subsetTangleDist Γ ord d {v_star} (D A)) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_2_proof.{w, u, v, u₁, v₁} q δ

/-- **Graph Minors XXII, 7.3** (pages 547–548), with `GM21Theorem11Statement` proved. -/
theorem theorem_7_3_proved
    (q δ τ : ℕ) :
    ∃ θ : ℕ, 5 ≤ θ ∧
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
        IsAdequateFor ιV ιE W 𝒜 ℬ Γ K R_H φV φE →
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
        (∀ i : Fin t, ¬ ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧
          (F ∩ Γ.V).ncard < (Set.range (πS (A_fam' i))).ncard ∧ D (A_fam' i) ⊆ ins F) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_3_proof q δ τ

/-- **Graph Minors XXII, 7.4** (page 552), with `GM21Theorem11Statement` proved. -/
theorem theorem_7_4_proved
    (q δ τ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV₀ : S ↪ α) (ιE₀ : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 ℬ : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ₀ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord₀ : ℕ) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins₀ : Set S → Set S) (d₀ : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV₀ : αH → Graph α β) (φE₀ : βH → β)
        (hJ₀ : SystemJ1ToJ6 ιV₀ ιE₀ R_G W 𝒜 πLen πS Γ₀ orient θ ord₀ T₀ ins₀ d₀ D N K Δ v_star δ R_H φV₀ φE₀),
        ConditionJ7 ιV₀ ιE₀ R_G.G.toGraph W 𝒜 πLen πS Γ₀ T₀ →
        IsSufficientFor W 𝒜 ℬ K R_H φV₀ φE₀ →
        ∀ (t : ℕ) (A_fam A_fam' : Fin t → Graph α β),
        t ≤ τ →
        (∀ i : Fin t, A_fam i ∈ ℬ) →
        (∀ i : Fin t, A_fam' i ∈ 𝒜) →
        (∀ A ∈ ℬ \ Set.range A_fam,
          θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D A) (Set.univ \ Δ)) →
        ∀ (hlen : ∀ i : Fin t, πLen (A_fam' i) = πLen (A_fam i)),
        (∀ (i : Fin t) (hAi : A_fam i ≤ R_G.G.toGraph) (hA'i : A_fam' i ≤ R_G.G.toGraph)
          (hπi : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots k ∈ V(A_fam i))
          (hπ'i : ∀ k : Fin (πLen (A_fam i) + q),
            seqConcat (fun k : Fin (πLen (A_fam i)) =>
              ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots k ∈ V(A_fam' i)),
          HasSameDeltaFolio
            (subRootedDigraph R_G.G (A_fam' i) hA'i
              (seqConcat (fun k : Fin (πLen (A_fam i)) =>
                ιV₀ (πS (A_fam' i) (Fin.cast (hlen i).symm k))) R_G.roots) hπ'i)
            (subRootedDigraph R_G.G (A_fam i) hAi (seqConcat (ιV₀ ∘ πS (A_fam i)) R_G.roots) hπi) δ) →
        (∀ i : Fin t, Disjoint (D (A_fam i)) Δ) →
        (∀ i : Fin t, θ ≤ subsetTangleDist Γ₀ ord₀ d₀ {v_star} (D (A_fam' i))) →
        (∀ i : Fin t, Disjoint (D (A_fam' i)) Δ) →
        (∀ i j : Fin t, i < j → θ ≤ subsetTangleDist Γ₀ ord₀ d₀ (D (A_fam' i)) (D (A_fam' j))) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV₀ v_star}) Graph.deleteVerts_le
            R_G.roots hJ₀.roots_mem_deleteVerts_v_star)
          R_H :=
  theorem_7_4_proof q δ τ

end GraphMinor.GM22
