module

public import GraphMinor.Compute.Algorithm62
public import GraphMinor.Compute.Algorithm65
public import GraphMinor.Compute.FolioTable
public import GraphMinor.Compute.Restrict
public import GraphMinor.Compute.BFS
public import GraphMinor.Compute.BranchDecomp

/-!
# Ambient Subgraph and Folio Helpers for GM XIII Section 9

This file provides ambient subgraph, size-measure, clique-model monotonicity, and `δ`-folio helpers
used by the GM XIII Section 9 algorithms.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Ambient Subgraphs on `Fin n` and Size Measure `ε(G)` -/

/-- A simple graph `G_sub : SimpleGraph (Fin n)` lives on active vertex set `V_sub ⊆ Fin n` if
every edge of `G_sub` has both endpoints in `V_sub`. -/
def IsSubgraphOn {n : ℕ} (V_sub : Finset (Fin n)) (G_sub : SimpleGraph (Fin n)) : Prop :=
  ∀ ⦃u v : Fin n⦄, G_sub.Adj u v → u ∈ V_sub ∧ v ∈ V_sub

theorem isSubgraphOn_univ {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsSubgraphOn Finset.univ G :=
  fun _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩

theorem isSubgraphOn_restrictGraph {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Finset (Fin n)) :
    IsSubgraphOn Y (restrictGraph G Y) := by
  intro u v hadj
  rw [restrictGraph_adj] at hadj
  exact ⟨hadj.1, hadj.2.1⟩

/-- The size measure $\varepsilon(G) = |E(G)| + |V(G)| + 1$ of a subgraph `(V_sub, G_sub)` on
`Fin n` (GM XIII Section 3, page 71: "We write $\varepsilon(G) = |E(G)| + |V(G)| + 1$"). -/
def graphEps {n : ℕ} (V_sub : Finset (Fin n)) (G_sub : SimpleGraph (Fin n))
    [DecidableRel G_sub.Adj] : ℕ :=
  G_sub.edgeFinset.card + V_sub.card + 1

@[simp]
theorem graphEps_univ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    graphEps Finset.univ G = G.edgeFinset.card + n + 1 := by
  simp [graphEps]

theorem graphEps_pos {n : ℕ} (V_sub : Finset (Fin n)) (G_sub : SimpleGraph (Fin n))
    [DecidableRel G_sub.Adj] :
    1 ≤ graphEps V_sub G_sub := by
  unfold graphEps
  omega

theorem graphEps_mono {n : ℕ} {V₁ V₂ : Finset (Fin n)}
    {G₁ G₂ : SimpleGraph (Fin n)} [DecidableRel G₁.Adj] [DecidableRel G₂.Adj]
    (hV : V₁ ⊆ V₂) (hG : G₁ ≤ G₂) :
    graphEps V₁ G₁ ≤ graphEps V₂ G₂ := by
  unfold graphEps
  have hcardV : V₁.card ≤ V₂.card := Finset.card_le_card hV
  have hcardE : G₁.edgeFinset.card ≤ G₂.edgeFinset.card := by
    apply Finset.card_le_card
    intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono hG he
  omega

/-- Every restricted graph `restrictGraph G Y` is a subgraph of `G`. -/
theorem restrictGraph_le {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Finset (Fin n)) :
    restrictGraph G Y ≤ G :=
  fun _ _ h => ((restrictGraph_adj G Y _ _).mp h).2.2

/-- Monotonicity of `IsCliqueModel`: if `H ≤ G`, any $K_p$ model in `H` is also a $K_p$ model in `G`. -/
theorem IsCliqueModel.mono {n p : ℕ} {H G : SimpleGraph (Fin n)} (hle : H ≤ G)
    {sets : Fin p → Finset (Fin n)} (hM : IsCliqueModel H p sets) :
    IsCliqueModel G p sets := by
  rcases hM with ⟨hconn, hdisj, hadj⟩
  refine ⟨fun i => ⟨(hconn i).1, induce_connected_of_le (fun u v h => hle h) (hconn i).2⟩,
    hdisj, fun i j hij => ?_⟩
  rcases hadj i j hij with ⟨u, hu, v, hv, huv⟩
  exact ⟨u, hu, v, hv, hle huv⟩

/-! ### Section 2: Rooted Digraphs, `δ`-Folios, and Irrelevant Vertices (GM XIII Sections 2, 6, 10) -/

theorem sortedFinsetList_nodup {n : ℕ} (Z : Finset (Fin n)) :
    (sortedFinsetList Z).Nodup :=
  nodup_sortedFinsetList Z

theorem rootsZ_injective {n : ℕ} (Z : Finset (Fin n)) :
    Function.Injective (rootsZ Z) :=
  injective_rootsZ Z

/-- Cast the root count of a `ComputeRootedDigraph q₁` along an equality `h : q₁ = q₂`. -/
def ComputeRootedDigraph.castRoots {q₁ q₂ : ℕ} (h : q₁ = q₂)
    (H : ComputeRootedDigraph q₁) : ComputeRootedDigraph q₂ where
  digraph := H.digraph
  roots i := H.roots (i.cast h.symm)

/-- Cast the root count of a `FolioSetRep q₁ δ` along an equality `h : q₁ = q₂`. -/
def FolioSetRep.castQ {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (F : FolioSetRep q₁ δ) : FolioSetRep q₂ δ where
  codes := F.codes
  all_detail := h ▸ F.all_detail
  pairwise_nonIso := h ▸ F.pairwise_nonIso

@[simp]
theorem encFolioSetRep_castQ {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (F : FolioSetRep q₁ δ) :
    encFolioSetRep (F.castQ h) = encFolioSetRep F :=
  rfl

theorem memIso_castQ_iff {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (F : FolioSetRep q₁ δ)
    (H : ComputeRootedDigraph q₂) :
    (F.castQ h).MemIso H ↔ F.MemIso (H.castRoots h.symm) := by
  subst h
  rfl

theorem hasDetailLe_castRoots_iff {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (H : ComputeRootedDigraph q₁) :
    (H.castRoots h).HasDetailLe δ ↔ H.HasDetailLe δ := by
  subst h
  rfl

/-- Two rooted multi-digraphs `(G₁, Z₁)` and `(G₂, Z₂)` have the same `δ`-folio
(GM XIII Section 2, page 69): `|Z₁| = |Z₂|` and every rooted digraph `H` of detail `≤ δ` is a
minor of `(G₁, Z₁)` if and only if it is a minor of `(G₂, Z₂)`. -/
def SameDeltaFolio {n₁ n₂ : ℕ} (δ : ℕ)
    (G₁ : MultiDigraph n₁) (Z₁ : Finset (Fin n₁))
    (G₂ : MultiDigraph n₂) (Z₂ : Finset (Fin n₂)) : Prop :=
  Z₁.card = Z₂.card ∧
  ∀ (q : ℕ) (hq₁ : q = Z₁.card) (hq₂ : q = Z₂.card) (H : ComputeRootedDigraph q),
    H.HasDetailLe δ →
    (HasRootedDigraphModel (H.castRoots hq₁) (rootedDigraphOfZ G₁ Z₁) ↔
      HasRootedDigraphModel (H.castRoots hq₂) (rootedDigraphOfZ G₂ Z₂))

theorem SameDeltaFolio.refl {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n)) :
    SameDeltaFolio δ G Z G Z := by
  refine ⟨rfl, fun q hq₁ hq₂ H _ => ?_⟩
  subst hq₁
  rfl

theorem SameDeltaFolio.symm {n₁ n₂ : ℕ} {δ : ℕ}
    {G₁ : MultiDigraph n₁} {Z₁ : Finset (Fin n₁)}
    {G₂ : MultiDigraph n₂} {Z₂ : Finset (Fin n₂)}
    (h : SameDeltaFolio δ G₁ Z₁ G₂ Z₂) :
    SameDeltaFolio δ G₂ Z₂ G₁ Z₁ :=
  ⟨h.1.symm, fun q hq₂ hq₁ H hdet => (h.2 q hq₁ hq₂ H hdet).symm⟩

theorem SameDeltaFolio.trans {n₁ n₂ n₃ : ℕ} {δ : ℕ}
    {G₁ : MultiDigraph n₁} {Z₁ : Finset (Fin n₁)}
    {G₂ : MultiDigraph n₂} {Z₂ : Finset (Fin n₂)}
    {G₃ : MultiDigraph n₃} {Z₃ : Finset (Fin n₃)}
    (h₁₂ : SameDeltaFolio δ G₁ Z₁ G₂ Z₂)
    (h₂₃ : SameDeltaFolio δ G₂ Z₂ G₃ Z₃) :
    SameDeltaFolio δ G₁ Z₁ G₃ Z₃ := by
  refine ⟨h₁₂.1.trans h₂₃.1, fun q hq₁ hq₃ H hdet => ?_⟩
  have hq₂ : q = Z₂.card := hq₁.trans h₁₂.1
  exact (h₁₂.2 q hq₁ hq₂ H hdet).trans (h₂₃.2 q hq₂ hq₃ H hdet)

theorem SameDeltaFolio.isDeltaFolioRep_castQ {n₁ n₂ : ℕ} {δ : ℕ}
    {G₁ : MultiDigraph n₁} {Z₁ : Finset (Fin n₁)}
    {G₂ : MultiDigraph n₂} {Z₂ : Finset (Fin n₂)}
    (hsame : SameDeltaFolio δ G₁ Z₁ G₂ Z₂)
    {F : FolioSetRep Z₂.card δ} (hF : IsDeltaFolioRep δ G₂ Z₂ F) :
    IsDeltaFolioRep δ G₁ Z₁ (F.castQ hsame.1.symm) := by
  intro H hdet
  have hdet' : (H.castRoots hsame.1).HasDetailLe δ :=
    (hasDetailLe_castRoots_iff hsame.1 H).mpr hdet
  rw [memIso_castQ_iff, hF (H.castRoots hsame.1) hdet']
  exact (hsame.2 Z₁.card rfl hsame.1 H hdet).symm

/-- A vertex `v₀ ∈ V(G) \ X` is **irrelevant to the `δ`-folio of `G` relative to `X`** if deleting
`v₀` preserves the `δ`-folio relative to `X`
(GM XIII Section 2, page 69: "A vertex $v \in V(G) \setminus Z$ is *irrelevant* (to the $\delta$-folio
of $G$ relative to $Z$) if $G \setminus v$ has the same $\delta$-folio relative to $Z$ as $G$."). -/
def IsIrrelevantToDeltaFolio {n' : ℕ} (δ : ℕ) (G : MultiDigraph (n' + 1))
    (X : Finset (Fin (n' + 1))) (v₀ : Fin (n' + 1)) : Prop :=
  v₀ ∉ X ∧
  SameDeltaFolio δ G X (G.deleteVertex v₀) (deleteVertexFinset X v₀)

end GraphMinor.Compute
