module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.Cited
public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.PortraitDefs
public import GraphMinor.GM21.LinkagePaths
public import GraphMinor.GM21.Section3
public import GraphMinor.GM21.Section9
public import GraphMinor.GM17.Defs
public import GraphMinor.GM17.Section13d
public import GraphMinor.GM10.TreeWidth
import GraphMinor.GM21.Join61
import GraphMinor.GM21.Section2
import GraphMinor.GM20.Section10j
import GraphMinor.GM20.Section10k
import GraphMinor.GM07.Bridge
import GraphMinor.GM07.CuffSlide
import GraphMinor.GM07.Section35
import GraphMinor.GM07.Defs
import GraphMinor.GM07.Open
import GraphMinor.GM07.Section7
import GraphMinor.GM09.Bridge
import GraphMinor.GM11.Cited
import GraphMinor.GM12.Bridge
import GraphMinor.GM12.Cited
import GraphMinor.GM12.Section5Final
import GraphMinor.GM12.Section6
import GraphMinor.GM12.Section710
import GraphMinor.GM12.Section75Proof
import GraphMinor.GM12.Section76
import GraphMinor.GM12.Section77
import GraphMinor.GM14.Adapted
import GraphMinor.GM14.Bridge
import GraphMinor.GM14.Cited
import GraphMinor.GM14.Section8Core
import GraphMinor.GM14.Section9a
import GraphMinor.GM14.Section9b
import GraphMinor.GM14.Whitney
import GraphMinor.GM15.Cited
import GraphMinor.GM15.Section3
import GraphMinor.GM15.Section3Crosscap
import GraphMinor.GM15.Section3Handle
import GraphMinor.GM15.Section3Parallel
import GraphMinor.GM15.Section3Given
import GraphMinor.GM15.Section4
import GraphMinor.GM16.Cited
import GraphMinor.GM16.Defs
import GraphMinor.GM16.MainProof
import GraphMinor.GM16.Section4
import GraphMinor.GM16.Section4Proof
import GraphMinor.GM16.Section5
import GraphMinor.GM16.Section5Five
import GraphMinor.GM16.Theorem35Bridge
import GraphMinor.GM16.Tower

import GraphMinor.GM16.InductionsProved

import GraphMinor.GM17.Section13Proved

/-!
# Graph Minors XXI, Section 10: The main proof

Formalization of Section 10 (pages 41–42 of the preprint) and main theorem `(1.1)`
(Section 1, page 1 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Proves:
- `theorem_10_1` (Graph Minors XXI, (10.1)): excluding a `K_n`-minor with a high-order tangle `𝒯`
  yields a surface `Σ` with `c(Σ) ≤ ρ` in which `K_n` cannot be drawn and a vertex set `Z ⊆ V(G)`
  with `|Z| ≤ ξ` such that `G \ Z` has a portrait in `Σ` of depth `≤ q` surrounding `𝒯 \ Z`
  (from Graph Minors XVII, (8.2), (8.4), (9.8), and (13.4)).
- `theorem_10_2` (Graph Minors XXI, (10.2)): for all `n, p ≥ 0` there exists `θ ≥ 1` such that no
  graph with a tangle of order `≥ θ` and no `K_n`-minor has a vital `p`-linkage (from `(10.1)`,
  `(9.2)`, `(3.2)`, and `(2.1)`).
- `theorem_10_3` (Graph Minors XXI, (10.3)): for every `p ≥ 0`, no graph with a `K_n`-minor has a
  vital `p`-linkage, where `n = ⌊5p/2⌋ + 1` (from Graph Minors XIII, (6.1)).
- `theorem_10_4` (Graph Minors XXI, (10.4)): for every `p ≥ 0` there exists `θ ≥ 1` such that no
  graph with a tangle of order `≥ θ` has a vital `p`-linkage (from `(10.2)` and `(10.3)`).
- `theorem_1_1` (Graph Minors XXI, (1.1)): for every `p ≥ 0` there exists `w ≥ 0` such that every
  graph with a vital `p`-linkage has tree-width at most `w` (from `(10.4)` and `(3.1)`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.Surface GraphMinor.GM10

universe u v

/-! ## (10.1): Structure of graphs with no `K_n`-minor and a high-order tangle -/

/-- A graph `G` has a `K_n`-minor (Graph Minors XXI, Section 10, page 41 of the preprint)
if there exist `n` mutually vertex-disjoint non-null connected subgraphs `G_1, …, G_n` of `G` such
that for `1 ≤ i < j ≤ n` there is an edge of `G` between `G_i` and `G_j`. -/
def HasCliqueMinor {α : Type u} {β : Type v} (G : Hypergraph α β) (n : ℕ) : Prop :=
  ∃ SubG : Fin n → Hypergraph α β,
    (∀ i : Fin n, SubG i ≤ G ∧ (SubG i).vertexSet.Nonempty ∧
      ∀ x ∈ (SubG i).vertexSet, ∀ y ∈ (SubG i).vertexSet, (SubG i).skeleton.Reachable x y) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (SubG i).vertexSet (SubG j).vertexSet) ∧
    (∀ i j : Fin n, i < j →
      ∃ e ∈ G.edgeSet, ∃ u ∈ (SubG i).vertexSet, ∃ v ∈ (SubG j).vertexSet,
        G.Inc e u ∧ G.Inc e v)

/-- The complete graph `K_n` as a finite hypergraph on `Fin n` with non-diagonal unordered pairs as
edges. -/
def completeHypergraph (n : ℕ) : Hypergraph (Fin n) (Sym2 (Fin n)) where
  vertexSet := univ
  edgeSet := {e | ¬ e.IsDiag}
  Inc e v := ¬ e.IsDiag ∧ v ∈ e
  vertex_mem_of_inc _ _ _ := mem_univ _
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := finite_univ
  edgeSet_finite := finite_univ.subset (subset_univ _)

/-- `completeHypergraph n` is a graph (`Hypergraph.IsGraph`). -/
theorem isGraph_completeHypergraph (n : ℕ) : (completeHypergraph n).IsGraph := by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    change ¬ s(x, y).IsDiag at he
    have hxy : x ≠ y := by rwa [Sym2.mk_isDiag_iff] at he
    have hends : (completeHypergraph n).ends s(x, y) = {x, y} := by
      ext v
      simp only [Hypergraph.ends, completeHypergraph, mem_ofPred_eq, Sym2.mem_iff, mem_insert_iff,
        mem_singleton_iff]
      exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩
    rw [hends]
    exact ⟨⟨x, Or.inl rfl⟩, (ncard_pair hxy).le⟩

/-- If a tangle `𝒯` in a graph `G` controls a `(completeHypergraph n)`-minor of `G*` in the sense
of Graph Minors XVII (`GM17.ControlsMinor`), then `G` has a `K_n`-minor (`HasCliqueMinor G n`). -/
theorem hasCliqueMinor_of_controlsMinor {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG : G.IsGraph)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} {n : ℕ}
    (hctrl : GM17.ControlsMinor G 𝒯 (completeHypergraph n)) :
    HasCliqueMinor G n := by
  rcases hctrl with ⟨_, av, ae', ae, hav, hdisj, hae_mem, _, hae_ends, _, _⟩
  let SubG (i : Fin n) : Hypergraph α β :=
    { vertexSet := av i
      edgeSet := {e ∈ G.edgeSet | G.ends e ⊆ av i}
      Inc := fun e v => e ∈ G.edgeSet ∧ G.ends e ⊆ av i ∧ G.Inc e v
      vertex_mem_of_inc := fun _ _ h => h.2.1 h.2.2
      edge_mem_of_inc := fun _ _ h => ⟨h.1, h.2.1⟩
      vertexSet_finite := G.vertexSet_finite.subset (hav i (mem_univ i)).2.1
      edgeSet_finite := G.edgeSet_finite.subset fun _ h => h.1 }
  refine ⟨SubG, fun i => ⟨?_, (hav i (mem_univ i)).1, ?_⟩,
    fun i j hij => hdisj i (mem_univ i) j (mem_univ j) hij, fun i j hij => ?_⟩
  · refine ⟨(hav i (mem_univ i)).2.1, fun _ h => h.1, fun e he => ?_⟩
    ext v; exact ⟨fun h => ⟨he.1, he.2, h⟩, fun h => h.2.2⟩
  · intro x hx y hy
    have hreach := (hav i (mem_univ i)).2.2.2.2 x hx y hy
    induction hreach with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ hadj_ae ih =>
      obtain ⟨hb_av, hc_av⟩ := (hav i (mem_univ i)).2.2.2.1 b c hadj_ae
      have hadj_G : G.skeleton.Adj b c := (hav i (mem_univ i)).2.2.1 hadj_ae
      rcases hadj_G with ⟨hbc, e, hb_inc, hc_inc⟩
      have heG : e ∈ G.edgeSet := G.edge_mem_of_inc hb_inc
      have hfin_ends : (G.ends e).Finite :=
        G.vertexSet_finite.subset fun _ hw => G.vertex_mem_of_inc hw
      have hends_eq : G.ends e = {b, c} :=
        eq_pair_of_mem_of_ncard_le_two hfin_ends (hG e heG).2 hb_inc hc_inc hbc
      have hends_sub : G.ends e ⊆ av i := by
        rw [hends_eq]
        rintro w (rfl | rfl)
        · exact hb_av
        · exact hc_av
      have hadj_sub : (SubG i).skeleton.Adj b c :=
        ⟨hbc, e, ⟨heG, hends_sub, hb_inc⟩, ⟨heG, hends_sub, hc_inc⟩⟩
      exact (ih hb_av).trans hadj_sub.reachable
  · have hne : i ≠ j := ne_of_lt hij
    have he_mem : s(i, j) ∈ (completeHypergraph n).edgeSet := by
      change ¬ s(i, j).IsDiag
      rwa [Sym2.mk_isDiag_iff]
    have hi_inc : (completeHypergraph n).Inc s(i, j) i :=
      ⟨he_mem, Sym2.mem_mk_left i j⟩
    have hj_inc : (completeHypergraph n).Inc s(i, j) j :=
      ⟨he_mem, Sym2.mem_mk_right i j⟩
    obtain ⟨u, hu, v, hv, hae_eq⟩ := hae_ends s(i, j) he_mem i j hne hi_inc hj_inc
    have hadj_uv : G.skeleton.Adj u v := by
      change s(u, v) ∈ G.skeleton.edgeSet
      rw [← hae_eq]
      exact hae_mem s(i, j) he_mem
    rcases hadj_uv with ⟨_, e, hu_inc, hv_inc⟩
    exact ⟨e, G.edge_mem_of_inc hu_inc, u, hu, v, hv, hu_inc, hv_inc⟩

/-- If `G` is a graph (`G.IsGraph`), then `G.deleteVertices Z` is a graph. -/
theorem isGraph_deleteVertices {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG : G.IsGraph) (Z : Set α) :
    (G.deleteVertices Z).IsGraph := by
  have hle : G.deleteVertices Z ≤ G := deleteVertices_le G Z
  intro e he
  have heG : e ∈ G.edgeSet := hle.2 he
  rw [← hle.3 e he]
  exact hG e heG

/-- Assembled proof of Graph Minors XVII, (13.1) (`GM17.Theorem131Statement.{u, v}`) from Graph
Minors XVI, (3.1). -/
theorem gm17_theorem_13_1_assembled : GM17.Theorem131Statement.{u, v} := by
  have hGM14_GM12Theorem710 : GM14.GM12Theorem710Statement.{0} :=
    GM12.gm14_theorem_7_10
  have hGM15_GM12Theorem77 : GM15.GM12Theorem77Statement.{0} := GM12.gm15_theorem_7_7
  have hGM15_GM12Theorem61 : GM15.GM12Theorem61Statement.{0} := GM12.theorem_6_1_proof
  have hGM15_GM15Theorem34 : GM15.GM15Theorem34Statement.{u, v, 0} :=
    GM15.theorem_3_4_proof
  have hGM15_GM15Theorem47 : GM15.GM15Theorem47Statement.{0} :=
    GM15.theorem_4_7_proof
  have hGM15_GM15Theorem41 : GM15.GM15Theorem41Statement.{0} := GM15.theorem_4_1_proof
  have hGM15_GM11Theorem91 : GM15.GM11Theorem91Statement.{0} := GM15.gm11_theorem_9_1
  have hGM15_GM12Theorem51 : GM15.GM12Theorem51Statement.{0} := GM12.theorem_5_1_proof
  have hGM15_GM12Theorem52 : GM15.GM12Theorem52Statement.{0} := GM12.theorem_5_2_proof
  have hGM15_GM15Theorem33 : GM15.GM15Theorem33Statement.{u, v, 0} :=
    GM15.theorem_3_3_proof
  have hGM15_GM15Theorem35 : GM15.GM15Theorem35Statement.{u, v, 0} :=
    GM15.theorem_3_5_proof
  have hGM16_GM15Theorem35 : GM16.GM15Theorem35Statement.{u, v, 0} :=
    GM16.gm15Theorem35
  have hGM16_GM14Theorem92 : GM16.GM14Theorem92Statement.{0} := GM14.theorem_9_2_proof
  have hGM16_GM14Theorem95 : GM16.GM14Theorem95Statement.{0} :=
    GM14.theorem_9_5_proof
  have hGM16_GM09Theorem105 : GM16.GM09Theorem105Statement.{0, 0} := GM09.gm16_theorem_10_5
  have hGM15_GM09Theorem71 : GM15.GM09Theorem71Statement.{u, v} := GM09.gm15_theorem_7_1
  have hGM15_GM09Theorem81 : GM15.GM09Theorem81Statement.{u, v} := GM09.gm15_theorem_8_1
  have hGM15_GM09Theorem1111 : GM15.GM09Theorem1111Statement.{u, v} := GM09.gm15_theorem_11_11
  have hGM15_GM14Theorem96 : GM15.GM14Theorem96Statement.{u, v, 0} :=
    GM14.gm14_theorem_9_6
  have hGM14_Theorem81 : GM14.Theorem81Statement.{u, v, 0} := GM14.theorem_8_1_proof
  have hGM07_ForestSurroundingMatching : GM07.ForestSurroundingMatchingStatement.{0} :=
    GM07.forestSurroundingMatching
  have hGM07_ForestMatchingFiniteIntersection :
      GM07.ForestMatchingFiniteIntersectionStatement.{0} :=
    GM07.forestMatchingFiniteIntersection
  have hGM15_GM14Theorem101 : GM15.GM14Theorem101Statement.{u, v, 0} :=
    GM14.gm14_theorem_10_1
  have hGM12_GM07Theorem75 : GM12.GM07Theorem75Statement.{0} :=
    GM07.gm07_theorem_7_5
  have hGM12_GM07Theorem51 : GM12.GM07Theorem51Statement.{0} := GM07.gm07_theorem_5_1
  have hGM12_GM07Theorem55 : GM12.GM07Theorem55Statement.{0} := GM07.gm07_theorem_5_5
  have hGM15_GM12Theorem45 : GM15.GM12Theorem45Statement.{u, v, 0} :=
    GM12.gm15_theorem45
  have hGM16_GM12Theorem44 : GM16.GM12Theorem44Statement.{u, v, 0} :=
    GM12.gm16_theorem44
  have hGM16_GM14Theorem93 : GM16.GM14Theorem93Statement.{0} := GM14.theorem_9_3_proof
  have hGM16_GM16Theorem51 : GM16.GM16Theorem51Statement.{u, v, 0} :=
    GM16.theorem_5_1_proof
  have hGM16_GM16Theorem55 : GM16.GM16Theorem55Statement.{u, v, 0} :=
    GM16.theorem_5_5_proof
  have hGM16_GM16Theorem41 : GM16.GM16Theorem41Statement.{u, v, 0} :=
    GM16.theorem_4_1_of_5_1_and_5_5
  have hGM16_GM16Theorem42 : GM16.GM16Theorem42Statement.{u, v, 0} := GM16.theorem_4_2_proof
  have hGM16_GM12Theorem43 : GM16.GM12Theorem43Statement.{u, v, 0, 0, 0} :=
    GM12.gm16_theorem43
  have hGM16_GM12Theorem42 : GM16.GM12Theorem42Statement.{u, v, 0, 0} := GM12.gm16_theorem42
  have hGM16_SurfaceTower : GM16.SurfaceTowerStatement.{u, v, 0, 0, 0} := GM16.surfaceTower
  have hGM16_GM16Theorem31 : GM16.GM16Theorem31Statement.{u, v, 0, 0, 0} :=
    GM16.theorem_3_1_of_statements
  intro α' β' H hH
  exact @GM17.theorem_13_1_proof.{u, v} α' β' H hH

/-- **Graph Minors XXI, (10.1)** (page 41 of the preprint):
"**10.1** *For every integer* $n \ge 0$ *there exist* $\rho, \xi \ge 0, q \ge 1$ *and* $\theta > \xi$
*such that, if a graph* $G$ *has no* $K_n$*-minor, and* $\mathcal{T}$ *is a tangle in* $G$ *of order*
$\ge \theta$, *then there exists a surface* $\Sigma$ *such that* $c(\Sigma) \le \rho$ *and* $K_n$
*cannot be drawn in* $\Sigma$, *and there exists* $Z \subseteq V(G)$ *with* $|Z| \le \xi$ *such that
there is a portrait of* $G \setminus Z$ *in* $\Sigma$ *with depth* $\le q$, *surrounding*
$\mathcal{T} \setminus Z$." -/
theorem theorem_10_1_proof (n : ℕ) :
    ∃ (ρ ξ q θ : ℕ),
      1 ≤ q ∧ ξ < θ ∧
      ∀ {α : Type u} {β : Type v} (G : Hypergraph α β) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        G.IsGraph →
        ¬ HasCliqueMinor G n →
        θ ≤ θ_G →
        IsTangle G θ_G 𝒯 →
        ∃ (S : Type) (_ : TopologicalSpace S),
          IsSurface S ∧
          ConnectedSpace S ∧
          (cuffs S).ncard ≤ ρ ∧
          ¬ GM17.CanBeDrawn S (completeHypergraph n) ∧
          ∃ (Z : Set α) (Γ : GM17.Painting S) (ιN : S → α)
            (α_cell : Set S → Hypergraph α β) (α_vert : S → Hypergraph α β),
            Z ⊆ G.vertexSet ∧
            Z.ncard ≤ ξ ∧
            PortraitHasDepthLe21 (G.deleteVertices Z) Γ ιN α_cell α_vert q ∧
            PortraitSurroundsTangle21 Γ α_cell (deleteVerticesTangle G Z 𝒯 θ_G) := by
  let σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ := fun _ _ p _ => 2 * p + 3
  have hσ : GM17.IsStandard σ := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  obtain ⟨p, ρ, ξ, θ₀, hξ_lt, h134⟩ :=
    GM17.theorem_13_4_proof
      (completeHypergraph n) (isGraph_completeHypergraph n) σ hσ
  let q := p + 1
  let θ := max θ₀ (ξ + 4 * p + 6)
  refine ⟨ρ, ξ, q, θ, by omega, by omega, ?_⟩
  intro α β G θ_G 𝒯 hG hnoKn hθ_le h𝒯
  have hθ₀_le : θ₀ ≤ θ_G := (le_max_left _ _).trans hθ_le
  have hθ_red : ξ + 4 * p + 6 ≤ θ_G := (le_max_right _ _).trans hθ_le
  rcases h134 G hG θ_G 𝒯 h𝒯 hθ₀_le with
    hctrl | ⟨Z, hZ_sub, hZ_card, π, hwarp, hcuffs, hnodraw, htrue, hred⟩
  · exact (hnoKn (hasCliqueMinor_of_controlsMinor hG hctrl)).elim
  · have hZ_lt : Z.ncard < θ_G := by omega
    have h𝒯_del : IsTangle (G.deleteVertices Z) (θ_G - Z.ncard) (deleteVerticesTangle G Z 𝒯 θ_G) :=
      theorem_3_2_proof hG h𝒯 hZ_sub hZ_lt
    have hG_del : (G.deleteVertices Z).IsGraph := isGraph_deleteVertices hG Z
    obtain ⟨ιN, α_cell, α_vert, hport_depth, hport_surr⟩ :=
      exists_portrait_of_true_portrayal hG_del h𝒯_del π htrue hred hwarp (by omega)
    have hcuffs_ncard : (cuffs π.S).ncard ≤ ρ := by
      have hcast : ((cuffs π.S).ncard : ℕ∞) = (cuffs π.S).encard :=
        π.finite_cuffs.cast_ncard_eq
      rw [← hcast] at hcuffs
      exact_mod_cast hcuffs
    exact ⟨π.S, π.top, π.isSurface, π.connected, hcuffs_ncard, hnodraw,
      Z, π.Γ, ιN, α_cell, α_vert, hZ_sub, hZ_card, hport_depth, hport_surr⟩

/-! ## (10.2): Graphs with no `K_n`-minor and a high-order tangle have no vital `p`-linkage -/

/-- Transport of `GM17.Painting` along a surface homeomorphism `ψ : S ≃ₜ T`. -/
noncomputable def mapPaintingHomeo {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : S ≃ₜ T) (Γ : GM17.Painting S) : GM17.Painting T where
  U := ψ '' Γ.U
  N := ψ '' Γ.N
  isClosed_U := ψ.isClosed_image.mpr Γ.isClosed_U
  N_subset := image_mono Γ.N_subset
  finite_N := Γ.finite_N.image _
  finite_cells := by
    rw [← image_sdiff ψ.injective, GM20.image_arcComponentsIn]
    exact Γ.finite_cells.image _
  cell_disc := by
    rw [← image_sdiff ψ.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨hdisc, hsub, hfin, hcard⟩ := Γ.cell_disc c hc
    rw [← ψ.image_closure, GM20.image_tilde, GM20.image_discBd,
      Set.ncard_image_of_injective _ ψ.injective]
    exact ⟨GM20.image_isClosedDisc ψ hdisc, image_mono hsub, hfin.image _, hcard⟩
  bd_subset := by
    rw [← image_bd_homeomorph ψ]
    exact image_mono Γ.bd_subset
  border_cell := by
    rw [← image_sdiff ψ.injective, GM20.image_arcComponentsIn]
    rintro _ ⟨c, hc, rfl⟩ hb
    rw [← image_bd_homeomorph ψ, ← image_inter ψ.injective] at hb
    obtain ⟨hcard, hfin, hline, hends⟩ := Γ.border_cell c hc hb.of_image
    rw [← ψ.image_closure, GM20.image_tilde, ← image_bd_homeomorph ψ,
      ← image_inter ψ.injective, Set.ncard_image_of_injective _ ψ.injective,
      GM20.image_lineEnds, hends]
    exact ⟨hcard, hfin.image _, GM20.image_isLine ψ hline, rfl⟩

theorem mapPaintingHomeo_C {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : S ≃ₜ T) (Γ : GM17.Painting S) :
    (mapPaintingHomeo ψ Γ).C = (fun c => ψ '' c) '' Γ.C := by
  change arcComponentsIn (ψ '' Γ.U \ ψ '' Γ.N) = _
  rw [← image_sdiff ψ.injective, GM20.image_arcComponentsIn]
  rfl

/-- `InCuffOrder` is preserved under homeomorphisms. -/
theorem inCuffOrder_map {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    (φ : S ≃ₜ T) {C X₁ : Set S} {u₁ : S} {X₂ : Set S} {u₂ : S}
    (h : InCuffOrder C X₁ u₁ X₂ u₂) :
    InCuffOrder (φ '' C) (φ '' X₁) (φ u₁) (φ '' X₂) (φ u₂) := by
  rcases h with ⟨f, a₁, b₁, t₁, a₂, b₂, t₂, ha₁b₁, hb₁t₁, ht₁a₂, ha₂b₂, hb₂t₂, ht₂a₁,
    hu₁, hu₂, hne₁, hsub₁, hne₂, hsub₂⟩
  let f' : Circle ≃ₜ φ '' C := f.trans (φ.image C)
  have hcuff : ∀ t : ℝ, GM19.cuffPoint f' t = φ (GM19.cuffPoint f t) := fun _ => rfl
  have hcuff_img : ∀ I : Set ℝ, GM19.cuffPoint f' '' I = φ '' (GM19.cuffPoint f '' I) := by
    intro I; rw [← image_comp]; rfl
  refine ⟨f', a₁, b₁, t₁, a₂, b₂, t₂, ha₁b₁, hb₁t₁, ht₁a₂, ha₂b₂, hb₂t₂, ht₂a₁,
    by rw [hcuff, hu₁], by rw [hcuff, hu₂], ?_, ?_, ?_, ?_⟩
  · rw [← φ.image_closure, ← image_inter φ.injective]
    exact hne₁.image φ
  · rw [← φ.image_closure, ← image_inter φ.injective, hcuff_img]
    exact image_mono hsub₁
  · rw [← φ.image_closure, ← image_inter φ.injective]
    exact hne₂.image φ
  · rw [← φ.image_closure, ← image_inter φ.injective, hcuff_img]
    exact image_mono hsub₂

/-- Transport of `IsPortrait21` along a surface homeomorphism `ψ : S ≃ₜ T`. -/
theorem isPortrait21_map_homeo {α : Type u} {β : Type v}
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : S ≃ₜ T) (hT_surf : IsSurface T) (hT_conn : ConnectedSpace T)
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β} {q_cuff : Set S → ℕ}
    (hport : IsPortrait21 G Γ ιN α_cell α_vert q_cuff) :
    IsPortrait21 G (mapPaintingHomeo ψ Γ) (ιN ∘ ψ.symm)
      (fun c' => α_cell (ψ.symm '' c')) (α_vert ∘ ψ.symm) (fun C' => q_cuff (ψ.symm '' C')) := by
  have hιN_img : ∀ A : Set S, (ιN ∘ ψ.symm) '' (ψ '' A) = ιN '' A := fun A => by
    rw [← image_comp]
    exact image_congr fun x _ => by simp
  have hbd_img : ∀ x : S, ψ x ∈ bd T ↔ x ∈ bd S := by
    intro x
    rw [← image_bd_homeomorph ψ]
    exact ψ.injective.mem_set_image
  refine
    { is_surface := hT_surf
      is_connected_surface := hT_conn
      r1_painting := ?_
      r1_injOn := ?_
      r1_subset := ?_
      r2_cell_le := ?_
      r2_cell_inter := ?_
      r3_union_V := ?_
      r3_union_E := ?_
      r3_edge_disjoint := ?_
      r4_vert := ?_
      r5_cuff_pos := ?_
      r5_cuff_card := ?_
      r6_border := ?_
      r7_inter := ?_
      r8_order := ?_
      r9_three := ?_
      r10_null := ?_ }
  · unfold IsPainting21
    rw [mapPaintingHomeo_C]
    rintro _ ⟨c, hc, rfl⟩
    rw [GM20.image_tilde, Set.ncard_image_of_injective _ ψ.injective]
    exact hport.r1_painting c hc
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [Function.comp_apply, Homeomorph.symm_apply_apply] at hab
    rw [hport.r1_injOn ha hb hab]
  · change (ιN ∘ ψ.symm) '' (ψ '' Γ.N) ⊆ G.vertexSet
    rw [hιN_img]
    exact hport.r1_subset
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c, hc, rfl⟩
    change α_cell (ψ.symm '' (ψ '' c)) ≤ G
    rw [GM20.symm_image_image]
    exact hport.r2_cell_le c hc
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c, hc, rfl⟩
    change (α_cell (ψ.symm '' (ψ '' c))).vertexSet ∩ ((ιN ∘ ψ.symm) '' (ψ '' Γ.N)) =
      (ιN ∘ ψ.symm) '' tilde (ψ '' c)
    rw [GM20.symm_image_image, GM20.image_tilde, hιN_img, hιN_img]
    exact hport.r2_cell_inter c hc
  · rw [hport.r3_union_V, mapPaintingHomeo_C]
    ext v
    simp only [mem_iUnion, exists_prop, mem_image]
    constructor
    · rintro ⟨c, hc, hv⟩
      exact ⟨ψ '' c, ⟨c, hc, rfl⟩, by rwa [GM20.symm_image_image]⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, hv⟩
      rw [GM20.symm_image_image] at hv
      exact ⟨c, hc, hv⟩
  · rw [hport.r3_union_E, mapPaintingHomeo_C]
    ext e
    simp only [mem_iUnion, exists_prop, mem_image]
    constructor
    · rintro ⟨c, hc, he⟩
      exact ⟨ψ '' c, ⟨c, hc, rfl⟩, by rwa [GM20.symm_image_image]⟩
    · rintro ⟨_, ⟨c, hc, rfl⟩, he⟩
      rw [GM20.symm_image_image] at he
      exact ⟨c, hc, he⟩
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne
    change Disjoint (α_cell (ψ.symm '' (ψ '' c₁))).edgeSet (α_cell (ψ.symm '' (ψ '' c₂))).edgeSet
    rw [GM20.symm_image_image, GM20.symm_image_image]
    exact hport.r3_edge_disjoint c₁ hc₁ c₂ hc₂ (fun h => hne (by rw [h]))
  · rintro _ ⟨⟨v, hvN, rfl⟩, hvbd⟩
    have hvbd' : v ∈ bd S := (hbd_img v).mp hvbd
    change α_vert (ψ.symm (ψ v)) ≤ G ∧
      (α_vert (ψ.symm (ψ v))).edgeSet = ∅ ∧
      (α_vert (ψ.symm (ψ v))).vertexSet ∩ ((ιN ∘ ψ.symm) '' (ψ '' Γ.N)) =
        {ιN (ψ.symm (ψ v))}
    rw [ψ.symm_apply_apply, hιN_img]
    exact hport.r4_vert v ⟨hvN, hvbd'⟩
  · intro C' hC'
    rw [GM20.image_cuffs ψ] at hC'
    rcases hC' with ⟨C, hC, rfl⟩
    change 1 ≤ q_cuff (ψ.symm '' (ψ '' C))
    rw [GM20.symm_image_image]
    exact hport.r5_cuff_pos C hC
  · rintro C' hC' _ ⟨⟨v, hvN, rfl⟩, hvC'⟩
    rw [GM20.image_cuffs ψ] at hC'
    rcases hC' with ⟨C, hC, rfl⟩
    have hvC : v ∈ C := ψ.injective.mem_set_image.mp hvC'
    change (α_vert (ψ.symm (ψ v))).vertexSet.ncard = q_cuff (ψ.symm '' (ψ '' C))
    rw [ψ.symm_apply_apply, GM20.symm_image_image]
    exact hport.r5_cuff_card C hC v ⟨hvN, hvC⟩
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c, hc, rfl⟩ hbd u' v' hne huv'
    rw [← image_bd_homeomorph ψ, ← image_inter ψ.injective, image_nonempty] at hbd
    let u := ψ.symm u'
    let v := ψ.symm v'
    have huv : u ≠ v := fun h => hne (by simpa [u, v] using congrArg ψ h)
    have htc : tilde c = {u, v} := by
      have h1 := congrArg (image ψ.symm) huv'
      rw [GM20.image_tilde, GM20.symm_image_image, image_pair] at h1
      exact h1
    obtain ⟨hu_le, hv_le, h6⟩ := hport.r6_border c hc hbd u v huv htc
    change α_vert u ≤ α_cell (ψ.symm '' (ψ '' c)) ∧
      α_vert v ≤ α_cell (ψ.symm '' (ψ '' c)) ∧ _
    rw [GM20.symm_image_image]
    refine ⟨hu_le, hv_le, ?_⟩
    rcases h6 with hpaths | ⟨c₀, hc₀, hcard3, hu_c₀, hv_c₀⟩
    · exact Or.inl hpaths
    · refine Or.inr ⟨ψ '' c₀, ⟨c₀, hc₀, rfl⟩, ?_, ?_, ?_⟩
      · rw [GM20.image_tilde, Set.ncard_image_of_injective _ ψ.injective]; exact hcard3
      · rw [GM20.image_tilde]; exact ⟨u, hu_c₀, ψ.apply_symm_apply u'⟩
      · rw [GM20.image_tilde]; exact ⟨v, hv_c₀, ψ.apply_symm_apply v'⟩
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ hne hnocuff
    change (α_cell (ψ.symm '' (ψ '' c₁)) ∩ α_cell (ψ.symm '' (ψ '' c₂))).vertexSet =
      (ιN ∘ ψ.symm) '' (tilde (ψ '' c₁) ∩ tilde (ψ '' c₂))
    rw [GM20.symm_image_image, GM20.symm_image_image, GM20.image_tilde, GM20.image_tilde,
      ← image_inter ψ.injective, hιN_img]
    refine hport.r7_inter c₁ hc₁ c₂ hc₂ (fun h => hne (by rw [h])) (fun C hC ⟨h1, h2⟩ => ?_)
    refine hnocuff (ψ '' C) (by rw [GM20.image_cuffs ψ]; exact ⟨C, hC, rfl⟩) ⟨?_, ?_⟩
    · rw [← image_inter ψ.injective]; exact h1.image ψ
    · rw [← image_inter ψ.injective]; exact h2.image ψ
  · rw [mapPaintingHomeo_C]
    rintro C' hC' _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ h1 h2
      _ ⟨⟨u₁, hu₁N, rfl⟩, hu₁C'⟩ _ ⟨⟨u₂, hu₂N, rfl⟩, hu₂C'⟩ hord
    rw [GM20.image_cuffs ψ] at hC'
    rcases hC' with ⟨C, hC, rfl⟩
    rw [← image_inter ψ.injective, image_nonempty] at h1 h2
    have hu₁C : u₁ ∈ C := ψ.injective.mem_set_image.mp hu₁C'
    have hu₂C : u₂ ∈ C := ψ.injective.mem_set_image.mp hu₂C'
    have hord' := inCuffOrder_map ψ.symm hord
    simp only [GM20.symm_image_image, Homeomorph.symm_apply_apply] at hord'
    change α_cell (ψ.symm '' (ψ '' c₁)) ∩ α_cell (ψ.symm '' (ψ '' c₂)) ≤
      α_vert (ψ.symm (ψ u₁)) ∪ α_vert (ψ.symm (ψ u₂))
    rw [GM20.symm_image_image, GM20.symm_image_image, ψ.symm_apply_apply, ψ.symm_apply_apply]
    exact hport.r8_order C hC c₁ hc₁ c₂ hc₂ h1 h2 u₁ ⟨hu₁N, hu₁C⟩ u₂ ⟨hu₂N, hu₂C⟩ hord'
  · rw [mapPaintingHomeo_C]
    rintro _ ⟨c, hc, rfl⟩ hcard3
    rw [GM20.image_tilde, Set.ncard_image_of_injective _ ψ.injective] at hcard3
    change ¬ CanBeDrawnInDisc21 (α_cell (ψ.symm '' (ψ '' c))) ((ιN ∘ ψ.symm) '' tilde (ψ '' c))
    rw [GM20.symm_image_image, GM20.image_tilde, hιN_img]
    exact hport.r9_three c hc hcard3
  · intro C' hC'
    rw [GM20.image_cuffs ψ] at hC'
    rcases hC' with ⟨C, hC, rfl⟩
    rw [← hport.r10_null C hC]
    ext w
    simp only [mem_iInter, mem_inter_iff, Function.comp_apply]
    constructor
    · intro h u ⟨huN, huC⟩
      have := h (ψ u) ⟨⟨u, huN, rfl⟩, mem_image_of_mem ψ huC⟩
      rwa [ψ.symm_apply_apply] at this
    · rintro h _ ⟨⟨u, huN, rfl⟩, huC'⟩
      rw [ψ.symm_apply_apply]
      exact h u ⟨huN, ψ.injective.mem_set_image.mp huC'⟩

theorem portraitHasDepthLe21_map_homeo {α : Type u} {β : Type v}
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : S ≃ₜ T) (hT_surf : IsSurface T) (hT_conn : ConnectedSpace T)
    {G : Hypergraph α β} {Γ : GM17.Painting S} {ιN : S → α}
    {α_cell : Set S → Hypergraph α β} {α_vert : S → Hypergraph α β} {q : ℕ}
    (hdepth : PortraitHasDepthLe21 G Γ ιN α_cell α_vert q) :
    PortraitHasDepthLe21 G (mapPaintingHomeo ψ Γ) (ιN ∘ ψ.symm)
      (fun c' => α_cell (ψ.symm '' c')) (α_vert ∘ ψ.symm) q := by
  rcases hdepth with ⟨q_cuff, hport, hq_le⟩
  refine ⟨fun C' => q_cuff (ψ.symm '' C'),
    isPortrait21_map_homeo ψ hT_surf hT_conn hport, ?_⟩
  intro C' hC'
  rw [GM20.image_cuffs ψ] at hC'
  rcases hC' with ⟨C, hC, rfl⟩
  change q_cuff (ψ.symm '' (ψ '' C)) ≤ q
  rw [GM20.symm_image_image]
  exact hq_le C hC

theorem portraitSurroundsTangle21_map_homeo {α : Type u} {β : Type v}
    {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : S ≃ₜ T) {Γ : GM17.Painting S} {α_cell : Set S → Hypergraph α β}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsurr : PortraitSurroundsTangle21 Γ α_cell 𝒯) :
    PortraitSurroundsTangle21 (mapPaintingHomeo ψ Γ) (fun c' => α_cell (ψ.symm '' c')) 𝒯 := by
  rw [PortraitSurroundsTangle21, mapPaintingHomeo_C]
  rintro _ ⟨c, hc, rfl⟩
  rw [GM20.symm_image_image]
  exact hsurr c hc

/-- `HasVitalPLinkage` is monotone in `p`. -/
theorem hasVitalPLinkage_mono {α : Type u} {β : Type v}
    {G : Hypergraph α β} {p₁ p₂ : ℕ} (hle : p₁ ≤ p₂)
    (h : HasVitalPLinkage G p₁) : HasVitalPLinkage G p₂ := by
  rcases h with ⟨L, hvit, hL_link, hL_card⟩
  exact ⟨L, hvit, hL_link, hL_card.trans hle⟩

set_option linter.style.haveILetI false in
/-- **Graph Minors XXI, (10.2)** (page 42 of the preprint):
"**10.2** *For all integers* $n, p \ge 0$ *there exists* $\theta \ge 1$ *such that, if a graph* $G$
*has a tangle of order* $\ge \theta$ *and has no* $K_n$*-minor then* $G$ *has no vital*
$p$*-linkage.*" -/
theorem theorem_10_2_proof
    (n p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v}
        (G : Hypergraph α β) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        G.IsGraph →
        ¬ HasCliqueMinor G n →
        θ ≤ θ_G →
        IsTangle G θ_G 𝒯 →
        ¬ HasVitalPLinkage G p := by
  classical
  obtain ⟨ρ, ξ, q, θ₁, hq_pos, hξ_lt, h101⟩ := theorem_10_1_proof.{u, v} n
  obtain ⟨L, hL⟩ :=
    GM20.Draw.exists_canBeDrawn (completeHypergraph n) (isGraph_completeHypergraph n)
  have h92_model : ∀ t : ℕ × ℕ × ℕ,
      ∃ θ_t : ℕ, 1 ≤ θ_t ∧
        ∀ {α : Type u} {β : Type v} (G' : Hypergraph α β), G'.IsGraph →
          ∀ (Γ' : GM17.Painting (SurfaceModel t.1 t.2.1 t.2.2))
            (ιN' : SurfaceModel t.1 t.2.1 t.2.2 → α)
            (α_cell' : Set (SurfaceModel t.1 t.2.1 t.2.2) → Hypergraph α β)
            (α_vert' : SurfaceModel t.1 t.2.1 t.2.2 → Hypergraph α β)
            (θ' : ℕ) (𝒯' : Set (Hypergraph α β × Hypergraph α β)),
            PortraitHasDepthLe21 G' Γ' ιN' α_cell' α_vert' q →
            θ_t ≤ θ' →
            IsTangle G' θ' 𝒯' →
            PortraitSurroundsTangle21 Γ' α_cell' 𝒯' →
            ¬ HasVitalPLinkage G' (p + 2 * ξ) := by
    intro t
    have : ConnectedSpace (SurfaceModel t.1 t.2.1 t.2.2) :=
      (isSurface_model t.1 t.2.1 t.2.2).2
    exact theorem_9_2_shapes (SurfaceModel t.1 t.2.1 t.2.2)
      (isSurface_model t.1 t.2.1 t.2.2).1 (p + 2 * ξ) q hq_pos
  choose θ_fn hθ_fn_pos hθ_fn_spec using h92_model
  let F : Finset (ℕ × ℕ × ℕ) := Finset.Iio L ×ˢ (Finset.Iio L ×ˢ Finset.Iic ρ)
  let θ₂ : ℕ := max 1 (F.sup θ_fn)
  let θ : ℕ := max θ₁ (ξ + θ₂)
  refine ⟨θ, by omega, ?_⟩
  intro α β G θ_G 𝒯 hG hnoKn hθ_le h𝒯 hvit_G
  have hθ₁_le : θ₁ ≤ θ_G := (le_max_left _ _).trans hθ_le
  have hθ₂_le : ξ + θ₂ ≤ θ_G := (le_max_right _ _).trans hθ_le
  obtain ⟨S, topS, hS, hconn, hcuffs_le, hnodraw, Z, Γ, ιN, α_cell, α_vert,
    hZ_sub, hZ_card, hport_depth, hport_surr⟩ :=
    h101 G θ_G 𝒯 hG hnoKn hθ₁_le h𝒯
  letI : TopologicalSpace S := topS
  have : T2Space S := hS.2.1
  obtain ⟨a, b, c, ⟨ψ⟩⟩ := classification S hS hconn
  have : T2Space (SurfaceModel a b c) := (isSurface_model a b c).1.2.1
  have hc_le : c ≤ ρ := by
    rw [← GM17.ncard_cuffs_of_homeo ψ]
    exact hcuffs_le
  have hab : a < L ∧ b < L := by
    by_contra hn
    exact hnodraw (GM20.Draw.CanBeDrawn.map ψ.symm (hL a b c (by omega)))
  have ht_mem : (a, (b, c)) ∈ F := by
    simp only [F, Finset.mem_product, Finset.mem_Iio, Finset.mem_Iic]
    exact ⟨hab.1, hab.2, hc_le⟩
  have hθ_fn_le : θ_fn (a, (b, c)) ≤ θ₂ :=
    (Finset.le_sup ht_mem).trans (le_max_right 1 _)
  have hZ_lt : Z.ncard < θ_G := by omega
  have h𝒯_del : IsTangle (G.deleteVertices Z) (θ_G - Z.ncard) (deleteVerticesTangle G Z 𝒯 θ_G) :=
    theorem_3_2_proof hG h𝒯 hZ_sub hZ_lt
  have hG_del : (G.deleteVertices Z).IsGraph := isGraph_deleteVertices hG Z
  have hdepth_model :=
    portraitHasDepthLe21_map_homeo ψ (isSurface_model a b c).1 (isSurface_model a b c).2 hport_depth
  have hsurr_model :=
    portraitSurroundsTangle21_map_homeo ψ hport_surr
  have hno_vit_del : ¬ HasVitalPLinkage (G.deleteVertices Z) (p + 2 * ξ) :=
    hθ_fn_spec (a, (b, c)) (G.deleteVertices Z) hG_del (mapPaintingHomeo ψ Γ) (ιN ∘ ψ.symm)
      (fun c' => α_cell (ψ.symm '' c')) (α_vert ∘ ψ.symm)
      (θ_G - Z.ncard) (deleteVerticesTangle G Z 𝒯 θ_G)
      hdepth_model (by omega) h𝒯_del hsurr_model
  rcases hvit_G with ⟨L_vit, hL_vit⟩
  have hvit_del_Z : HasVitalPLinkage (G.deleteVertices Z) (p + 2 * Z.ncard) :=
    ⟨L_vit.deleteVertices Z, theorem_2_1_proof hL_vit hZ_sub⟩
  exact hno_vit_del (hasVitalPLinkage_mono (by omega) hvit_del_Z)

/-! ## (10.3) and (10.4): Excluding a `K_n`-minor and the main tangle theorem -/

/-- Every non-null graph `G` (`G.IsGraph`) can be oriented into a `Digraph α β` with the same
underlying hypergraph. -/
theorem exists_digraph_of_isGraph {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG : G.IsGraph) (hne : G.vertexSet.Nonempty) :
    ∃ D : Digraph α β,
      D.vertexSet = G.vertexSet ∧
      D.edgeSet = G.edgeSet ∧
      D.toHypergraph = G ∧
      (∀ e ∈ G.edgeSet, G.ends e = {D.tail e, D.head e}) ∧
      ∀ v : α, (D.deleteVertex v).toHypergraph = G.deleteVertices {v} := by
  classical
  rcases hne with ⟨v₀, hv₀⟩
  have hends_pair : ∀ e : β, e ∈ G.edgeSet →
      ∃ u w : α, u ∈ G.vertexSet ∧ w ∈ G.vertexSet ∧ G.ends e = {u, w} := by
    intro e he
    obtain ⟨⟨u, hu⟩, hcard⟩ := hG e he
    have huV : u ∈ G.vertexSet := G.vertex_mem_of_inc hu
    by_cases hdiff : (G.ends e \ {u}).Nonempty
    · obtain ⟨w, hw_ends, hw_ne⟩ := hdiff
      have hwV : w ∈ G.vertexSet := G.vertex_mem_of_inc hw_ends
      have huw : u ≠ w := Ne.symm (mem_singleton_iff.not.mp hw_ne)
      have hfin_ends : (G.ends e).Finite :=
        G.vertexSet_finite.subset fun _ hx => G.vertex_mem_of_inc hx
      exact ⟨u, w, huV, hwV, eq_pair_of_mem_of_ncard_le_two hfin_ends hcard hu hw_ends huw⟩
    · refine ⟨u, u, huV, huV, ?_⟩
      rw [pair_eq_singleton]
      exact Subset.antisymm (sdiff_eq_empty.mp (not_nonempty_iff_eq_empty.mp hdiff))
        (singleton_subset_iff.mpr hu)
  let tail : β → α := fun e =>
    if he : e ∈ G.edgeSet then Classical.choose (hends_pair e he) else v₀
  let head : β → α := fun e =>
    if he : e ∈ G.edgeSet then Classical.choose (Classical.choose_spec (hends_pair e he)) else v₀
  have htail_mem : ∀ e ∈ G.edgeSet, tail e ∈ G.vertexSet := fun e he => by
    simp only [tail, he, ↓reduceDIte]
    exact (Classical.choose_spec (Classical.choose_spec (hends_pair e he))).1
  have hhead_mem : ∀ e ∈ G.edgeSet, head e ∈ G.vertexSet := fun e he => by
    simp only [head, he, ↓reduceDIte]
    exact (Classical.choose_spec (Classical.choose_spec (hends_pair e he))).2.1
  have hends_eq : ∀ e ∈ G.edgeSet, G.ends e = {tail e, head e} := fun e he => by
    simp only [tail, head, he, ↓reduceDIte]
    exact (Classical.choose_spec (Classical.choose_spec (hends_pair e he))).2.2
  let D : Digraph α β :=
    { vertexSet := G.vertexSet
      edgeSet := G.edgeSet
      vertexSet_finite := G.vertexSet_finite
      edgeSet_finite := G.edgeSet_finite
      tail := tail
      head := head
      tail_mem := htail_mem
      head_mem := hhead_mem }
  have htoG : D.toHypergraph = G := by
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq ?_ le_rfl rfl rfl
    refine ⟨Subset.rfl, Subset.rfl, fun e he => ?_⟩
    rw [hends_eq e he]
    ext x
    simp only [Hypergraph.ends, Digraph.toHypergraph, mem_ofPred_eq, mem_insert_iff,
      mem_singleton_iff]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩
  refine ⟨D, rfl, rfl, htoG, hends_eq, fun v => ?_⟩
  have hle1 : (D.deleteVertex v).toHypergraph ≤ G := by
    rw [← htoG]
    refine ⟨sdiff_subset, fun _ h => h.1, fun e he => ?_⟩
    ext x
    simp only [Hypergraph.ends, Digraph.toHypergraph, Digraph.deleteVertex, mem_ofPred_eq]
    exact ⟨fun h => ⟨he, h.2⟩, fun h => ⟨he.1, h.2⟩⟩
  have hle2 : G.deleteVertices {v} ≤ G := GM10.deleteVertices_le G {v}
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle1 hle2 rfl ?_
  ext e
  simp only [Digraph.toHypergraph, Digraph.deleteVertex, deleteVertices, mem_ofPred_eq,
    mem_singleton_iff, forall_eq]
  constructor
  · rintro ⟨he, hne_t, hne_h⟩
    refine ⟨he, fun hinc => ?_⟩
    have hv_ends : v ∈ G.ends e := hinc
    rw [hends_eq e he] at hv_ends
    rcases hv_ends with rfl | rfl
    · exact hne_t rfl
    · exact hne_h rfl
  · rintro ⟨he, hnot_inc⟩
    have hv_not_ends : v ∉ G.ends e := hnot_inc
    rw [hends_eq e he] at hv_not_ends
    exact ⟨he, fun h => hv_not_ends (Or.inl h.symm), fun h => hv_not_ends (Or.inr h.symm)⟩

/-- By pigeonhole, if `SubG : Fin n → Hypergraph α β` are pairwise vertex-disjoint and `Z.ncard < n`,
then `Disjoint Z (SubG i).vertexSet` for some `i : Fin n`. -/
theorem exists_disjoint_subG_of_ncard_lt {α : Type u} {β : Type v}
    {n : ℕ} {SubG : Fin n → Hypergraph α β}
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (SubG i).vertexSet (SubG j).vertexSet)
    {Z : Set α} (hZ_fin : Z.Finite) (hZ_lt : Z.ncard < n) :
    ∃ i : Fin n, Disjoint Z (SubG i).vertexSet := by
  by_contra hall
  push Not at hall
  have hex : ∀ i : Fin n, ∃ z : α, z ∈ Z ∧ z ∈ (SubG i).vertexSet := fun i =>
    Set.not_disjoint_iff.mp (hall i)
  choose f hf using hex
  have hf_inj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact Set.disjoint_left.mp (hdisj i j hne) (hf i).2 (hij ▸ (hf j).2)
  have hrange_sub : Set.range f ⊆ Z := by
    rintro _ ⟨i, rfl⟩
    exact (hf i).1
  have hcard_range : (Set.range f).ncard = n := by
    rw [Set.ncard_range_of_injective hf_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle := ncard_le_ncard hrange_sub hZ_fin
  omega

/-- Existence of a separation `(A, B)` of `G` satisfying conditions (i)–(iv) of Graph Minors XIII,
`(6.1)`. -/
theorem exists_min_max_separation {α : Type u} {β : Type v}
    {G : Hypergraph α β} {n : ℕ} {SubG : Fin n → Hypergraph α β}
    {Z : Set α} (hZ_sub : Z ⊆ G.vertexSet)
    (hi₀ : ∃ i : Fin n, Disjoint Z (SubG i).vertexSet) :
    ∃ A B : Hypergraph α β,
      G.IsSeparation A B ∧
      (∃ i : Fin n, Disjoint A.vertexSet (SubG i).vertexSet) ∧
      Z ⊆ A.vertexSet ∧
      (∀ A' B' : Hypergraph α β,
        G.IsSeparation A' B' →
        (∃ i : Fin n, Disjoint A'.vertexSet (SubG i).vertexSet) →
        Z ⊆ A'.vertexSet →
        separationOrder A B ≤ separationOrder A' B') ∧
      (∀ A' B' : Hypergraph α β,
        G.IsSeparation A' B' →
        (∃ i : Fin n, Disjoint A'.vertexSet (SubG i).vertexSet) →
        Z ⊆ A'.vertexSet →
        separationOrder A' B' ≤ separationOrder A B →
        A ≤ A' →
        A' = A) := by
  classical
  let P (A B : Hypergraph α β) : Prop :=
    G.IsSeparation A B ∧
    (∃ i : Fin n, Disjoint A.vertexSet (SubG i).vertexSet) ∧
    Z ⊆ A.vertexSet
  let A₀ : Hypergraph α β :=
    { vertexSet := Z
      edgeSet := ∅
      Inc := fun _ _ => False
      vertex_mem_of_inc := fun _ _ h => h.elim
      edge_mem_of_inc := fun _ _ h => h.elim
      vertexSet_finite := G.vertexSet_finite.subset hZ_sub
      edgeSet_finite := finite_empty }
  have hA₀_le : A₀ ≤ G := ⟨hZ_sub, empty_subset _, fun _ h => h.elim⟩
  have hP₀ : P A₀ G := by
    refine ⟨⟨hA₀_le, le_rfl,
      GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.union_le hA₀_le le_rfl) le_rfl
        (union_eq_self_of_subset_left hZ_sub) (empty_union _),
      empty_inter _⟩,
      hi₀, Subset.rfl⟩
  have hex_ord : ∃ k : ℕ, ∃ A B : Hypergraph α β, P A B ∧ separationOrder A B = k :=
    ⟨separationOrder A₀ G, A₀, G, hP₀, rfl⟩
  let k₀ : ℕ := Nat.find hex_ord
  have hk₀_spec : ∃ A B : Hypergraph α β, P A B ∧ separationOrder A B = k₀ :=
    Nat.find_spec hex_ord
  have hk₀_min : ∀ A' B' : Hypergraph α β, P A' B' → k₀ ≤ separationOrder A' B' :=
    fun A' B' hP' => Nat.find_min' hex_ord ⟨A', B', hP', rfl⟩
  let N_max : ℕ := G.vertexSet.ncard + G.edgeSet.ncard
  rcases hk₀_spec with ⟨A₁, B₁, hP₁, hord₁⟩
  have hex_deficit : ∃ d : ℕ, ∃ A B : Hypergraph α β,
      P A B ∧ separationOrder A B = k₀ ∧
      N_max - (A.vertexSet.ncard + A.edgeSet.ncard) = d :=
    ⟨N_max - (A₁.vertexSet.ncard + A₁.edgeSet.ncard), A₁, B₁, hP₁, hord₁, rfl⟩
  let d₀ : ℕ := Nat.find hex_deficit
  obtain ⟨A, B, hP_AB, hord_AB, hd₀_AB⟩ := Nat.find_spec hex_deficit
  have hd₀_min : ∀ A' B' : Hypergraph α β, P A' B' → separationOrder A' B' = k₀ →
      d₀ ≤ N_max - (A'.vertexSet.ncard + A'.edgeSet.ncard) :=
    fun A' B' hP' hord' => Nat.find_min' hex_deficit ⟨A', B', hP', hord', rfl⟩
  refine ⟨A, B, hP_AB.1, hP_AB.2.1, hP_AB.2.2, ?_, ?_⟩
  · intro A' B' hsep' hdisj' hZ'
    rw [hord_AB]
    exact hk₀_min A' B' ⟨hsep', hdisj', hZ'⟩
  · intro A' B' hsep' hdisj' hZ' hord_le hA_le
    have hP' : P A' B' := ⟨hsep', hdisj', hZ'⟩
    have hord_eq : separationOrder A' B' = k₀ :=
      le_antisymm (hord_AB ▸ hord_le) (hk₀_min A' B' hP')
    have hd_le := hd₀_min A' B' hP' hord_eq
    have hA'_V_le : A'.vertexSet.ncard ≤ G.vertexSet.ncard :=
      ncard_le_ncard hsep'.1.vertexSet_subset G.vertexSet_finite
    have hA'_E_le : A'.edgeSet.ncard ≤ G.edgeSet.ncard :=
      ncard_le_ncard hsep'.1.edgeSet_subset G.edgeSet_finite
    have hV_le : A.vertexSet.ncard ≤ A'.vertexSet.ncard :=
      ncard_le_ncard hA_le.vertexSet_subset A'.vertexSet_finite
    have hE_le : A.edgeSet.ncard ≤ A'.edgeSet.ncard :=
      ncard_le_ncard hA_le.edgeSet_subset A'.edgeSet_finite
    have hV_eq : A.vertexSet = A'.vertexSet :=
      eq_of_subset_of_ncard_le hA_le.vertexSet_subset (by omega) A'.vertexSet_finite
    have hE_eq : A.edgeSet = A'.edgeSet :=
      eq_of_subset_of_ncard_le hA_le.edgeSet_subset (by omega) A'.edgeSet_finite
    exact (GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hA_le le_rfl hV_eq hE_eq).symm

/-- Given `x₁ ≠ x₂` reachable in `H.skeleton` (`H.IsGraph`), there is a path subgraph `P ≤ H`
(`IsPathGraph P`) whose degree-`≤ 1` vertices are `{x₁, x₂}`. -/
theorem exists_path_subgraph_between {α : Type u} {β : Type v}
    {H : Hypergraph α β} (hH : H.IsGraph)
    {x₁ x₂ : α} (hx₁ : x₁ ∈ H.vertexSet) (bne : x₁ ≠ x₂)
    (hreach : H.skeleton.Reachable x₁ x₂) :
    ∃ P : Hypergraph α β,
      P ≤ H ∧
      IsPathGraph P ∧
      {x ∈ P.vertexSet | (incidentEdges P x).ncard ≤ 1} = {x₁, x₂} := by
  classical
  rcases hreach with ⟨q⟩
  let p := q.bypass
  have hp : p.IsPath := q.bypass_isPath
  let m : ℕ := p.length
  have hm_ge1 : 1 ≤ m := by
    by_contra hm0
    have h0 : p.length = 0 := by omega
    have h_eq : x₁ = x₂ := by
      have h1 : p.getVert 0 = x₁ := p.getVert_zero
      have h2 : p.getVert p.length = x₂ := p.getVert_length
      rw [h0] at h2
      exact h1.symm.trans h2
    exact bne h_eq
  let w : Fin (m + 1) → α := fun i => p.getVert i.1
  have hw_inj : Function.Injective w := by
    intro i j hij
    ext
    exact hp.getVert_injOn (Nat.le_of_lt_succ i.2) (Nat.le_of_lt_succ j.2) hij
  have hw0 : w 0 = x₁ := p.getVert_zero
  have hwm : w ⟨m, Nat.lt_succ_self m⟩ = x₂ := p.getVert_length
  have hw_mem : ∀ i : Fin (m + 1), w i ∈ H.vertexSet :=
    fun i => mem_vertexSet_of_mem_walk_support hx₁ p (p.getVert_mem_support i.1)
  have hex_edge : ∀ k : Fin m, ∃ e ∈ H.edgeSet,
      H.ends e = {w ⟨k.1, by omega⟩, w ⟨k.1 + 1, by omega⟩} := by
    intro k
    have hadj : H.skeleton.Adj (w ⟨k.1, by omega⟩) (w ⟨k.1 + 1, by omega⟩) :=
      p.adj_getVert_succ k.2
    rcases hadj with ⟨hne_k, e, hinc1, hinc2⟩
    have heH : e ∈ H.edgeSet := H.edge_mem_of_inc hinc1
    have hfin_ends : (H.ends e).Finite :=
      H.vertexSet_finite.subset fun _ hx => H.vertex_mem_of_inc hx
    exact ⟨e, heH, eq_pair_of_mem_of_ncard_le_two hfin_ends (hH e heH).2 hinc1 hinc2 hne_k⟩
  choose e_step he_mem he_ends using hex_edge
  let P : Hypergraph α β :=
    { vertexSet := Set.range w
      edgeSet := Set.range e_step
      Inc := fun e x => e ∈ Set.range e_step ∧ H.Inc e x
      vertex_mem_of_inc := by
        rintro e x ⟨⟨k, rfl⟩, hinc⟩
        have hx_ends : x ∈ H.ends (e_step k) := hinc
        rw [he_ends k] at hx_ends
        rcases hx_ends with rfl | rfl <;> exact mem_range_self _
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := Set.finite_range w
      edgeSet_finite := Set.finite_range e_step }
  have hP_le : P ≤ H := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨i, rfl⟩; exact hw_mem i
    · rintro _ ⟨k, rfl⟩; exact he_mem k
    · intro e he
      ext x
      simp only [Hypergraph.ends, P, mem_ofPred_eq]
      exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩
  have hP_graph : P.IsGraph := fun e he => by
    rw [← hP_le.ends_eq e he]
    exact hH e (hP_le.edgeSet_subset he)
  have hP_ends2 : ∀ e ∈ P.edgeSet, (P.ends e).ncard = 2 := by
    rintro _ ⟨k, rfl⟩
    rw [← hP_le.ends_eq (e_step k) (mem_range_self k), he_ends k]
    have hne_k : w ⟨k.1, by omega⟩ ≠ w ⟨k.1 + 1, by omega⟩ := fun h_eq => by
      have := congrArg Fin.val (hw_inj h_eq)
      change k.1 = k.1 + 1 at this; omega
    exact ncard_pair hne_k
  have hP_injE : ∀ e₁ ∈ P.edgeSet, ∀ e₂ ∈ P.edgeSet, P.ends e₁ = P.ends e₂ → e₁ = e₂ := by
    rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩ hends_eq
    rw [← hP_le.ends_eq (e_step k₁) (mem_range_self k₁),
      ← hP_le.ends_eq (e_step k₂) (mem_range_self k₂),
      he_ends k₁, he_ends k₂] at hends_eq
    have h1 : w ⟨k₁.1, by omega⟩ ∈ ({w ⟨k₂.1, by omega⟩, w ⟨k₂.1 + 1, by omega⟩} : Set α) := by
      rw [← hends_eq]; exact Or.inl rfl
    have h2 : w ⟨k₁.1 + 1, by omega⟩ ∈ ({w ⟨k₂.1, by omega⟩, w ⟨k₂.1 + 1, by omega⟩} : Set α) := by
      rw [← hends_eq]; exact Or.inr rfl
    have hk_eq : k₁ = k₂ := by
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · have a := congrArg Fin.val (hw_inj h1)
        have b := congrArg Fin.val (hw_inj h2)
        dsimp at a b; omega
      · have a := congrArg Fin.val (hw_inj h1)
        ext; exact a
      · have a := congrArg Fin.val (hw_inj h1)
        have b := congrArg Fin.val (hw_inj h2)
        dsimp at a b; omega
      · have a := congrArg Fin.val (hw_inj h1)
        have b := congrArg Fin.val (hw_inj h2)
        dsimp at a b; omega
    rw [hk_eq]
  have hP_idx : IsIndexedPath P x₁ x₂ := by
    refine ⟨m, hm_ge1, w, hw_inj, hw0, hwm, rfl, fun i j => ?_⟩
    constructor
    · rintro ⟨hne_ij, e, ⟨⟨k, rfl⟩, hinc_i⟩, ⟨_, hinc_j⟩⟩
      have hi_ends : w i ∈ H.ends (e_step k) := hinc_i
      have hj_ends : w j ∈ H.ends (e_step k) := hinc_j
      rw [he_ends k] at hi_ends hj_ends
      rcases hi_ends with hi_eq | hi_eq <;> rcases hj_ends with hj_eq | hj_eq
      · exact (hne_ij (hi_eq.trans hj_eq.symm)).elim
      · left
        have a := congrArg Fin.val (hw_inj hi_eq)
        have b := congrArg Fin.val (hw_inj hj_eq)
        dsimp at a b; omega
      · right
        have a := congrArg Fin.val (hw_inj hi_eq)
        have b := congrArg Fin.val (hw_inj hj_eq)
        dsimp at a b; omega
      · exact (hne_ij (hi_eq.trans hj_eq.symm)).elim
    · rintro (h_eq | h_eq)
      · let k : Fin m := ⟨i.1, by omega⟩
        have hj_eq : j = ⟨k.1 + 1, by omega⟩ := Fin.ext h_eq.symm
        have hne_ij : w i ≠ w j := fun h => by
          have := congrArg Fin.val (hw_inj h); omega
        have hinc_i : H.Inc (e_step k) (w i) := by
          change w i ∈ H.ends (e_step k)
          rw [he_ends k]; exact Or.inl rfl
        have hinc_j : H.Inc (e_step k) (w j) := by
          change w j ∈ H.ends (e_step k)
          rw [he_ends k, hj_eq]; exact Or.inr rfl
        exact ⟨hne_ij, e_step k, ⟨mem_range_self k, hinc_i⟩, ⟨mem_range_self k, hinc_j⟩⟩
      · let k : Fin m := ⟨j.1, by omega⟩
        have hi_eq : i = ⟨k.1 + 1, by omega⟩ := Fin.ext h_eq.symm
        have hne_ij : w i ≠ w j := fun h => by
          have := congrArg Fin.val (hw_inj h); omega
        have hinc_i : H.Inc (e_step k) (w i) := by
          change w i ∈ H.ends (e_step k)
          rw [he_ends k, hi_eq]; exact Or.inr rfl
        have hinc_j : H.Inc (e_step k) (w j) := by
          change w j ∈ H.ends (e_step k)
          rw [he_ends k]; exact Or.inl rfl
        exact ⟨hne_ij, e_step k, ⟨mem_range_self k, hinc_i⟩, ⟨mem_range_self k, hinc_j⟩⟩
  obtain ⟨hP_path, hP_deg1⟩ := isPathGraph_of_isIndexedPath hP_graph hP_ends2 hP_injE hP_idx
  refine ⟨P, hP_le, hP_path, ?_⟩
  ext x
  simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨hxP, hdeg⟩
    exact (hP_deg1 x hxP).mp hdeg
  · rintro (h_eq | h_eq)
    · subst h_eq
      have hx₁P : x ∈ P.vertexSet := by change x ∈ Set.range w; rw [← hw0]; exact mem_range_self 0
      exact ⟨hx₁P, (hP_deg1 x hx₁P).mpr (Or.inl rfl)⟩
    · subst h_eq
      have hx₂P : x ∈ P.vertexSet := by
        change x ∈ Set.range w; rw [← hwm]; exact mem_range_self (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
      exact ⟨hx₂P, (hP_deg1 x hx₂P).mpr (Or.inr rfl)⟩

/-- Given a component `Q` of a linkage `L` and a connected subgraph `H` of `G'` with
`terminals L ∩ H.vertexSet = terminals L ∩ Q.vertexSet`, there is a path subgraph `P ≤ H` whose
degree-`≤ 1` vertices are `terminals L ∩ Q.vertexSet`. -/
theorem exists_path_subgraph_matching_component {α : Type u} {β : Type v}
    {L Q H : Hypergraph α β}
    (hL_graph : L.IsGraph) (hH_graph : H.IsGraph)
    (hQ : IsComponentOf L Q) (hP_Q : IsPathGraph Q)
    (hH_conn : ∀ x ∈ H.vertexSet, ∀ y ∈ H.vertexSet, H.skeleton.Reachable x y)
    (hterm_eq : terminals L ∩ H.vertexSet = terminals L ∩ Q.vertexSet) :
    ∃ P : Hypergraph α β,
      P ≤ H ∧
      IsPathGraph P ∧
      {x ∈ P.vertexSet | (incidentEdges P x).ncard ≤ 1} = terminals L ∩ Q.vertexSet := by
  have hterm_Q : terminals L ∩ Q.vertexSet = {x ∈ Q.vertexSet | (incidentEdges Q x).ncard ≤ 1} := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact ⟨fun ⟨ht, hxQ⟩ => ⟨hxQ, (mem_terminals_iff_of_isComponentOf hL_graph hQ hP_Q hxQ).mp ht⟩,
      fun ⟨hxQ, hdeg⟩ => ⟨(mem_terminals_iff_of_isComponentOf hL_graph hQ hP_Q hxQ).mpr hdeg, hxQ⟩⟩
  by_cases hQ_emp : Q.edgeSet = ∅
  · obtain ⟨x₁, hx₁_eq, _⟩ := isPathGraph_empty_edgeSet hP_Q hQ_emp
    have hterm_Q_sing : terminals L ∩ Q.vertexSet = {x₁} := by
      rw [hterm_Q]
      ext x
      simp only [mem_ofPred_eq, hx₁_eq, mem_singleton_iff]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have hemp_inc : incidentEdges Q x = ∅ := by ext e; simp [incidentEdges, hQ_emp]
      rw [hemp_inc, ncard_empty]; omega
    have hx₁_H : x₁ ∈ H.vertexSet := by
      have : x₁ ∈ terminals L ∩ H.vertexSet := by rw [hterm_eq, hterm_Q_sing]; rfl
      exact this.2
    let P : Hypergraph α β :=
      { vertexSet := {x₁}
        edgeSet := ∅
        Inc := fun _ _ => False
        vertex_mem_of_inc := fun _ _ h => h.elim
        edge_mem_of_inc := fun _ _ h => h.elim
        vertexSet_finite := finite_singleton x₁
        edgeSet_finite := finite_empty }
    have hP_le : P ≤ H :=
      ⟨singleton_subset_iff.mpr hx₁_H, empty_subset _, fun _ h => h.elim⟩
    have hP_path : IsPathGraph P := by
      refine ⟨fun _ h => h.elim, ⟨x₁, rfl⟩, ?_, fun _ h => h.elim, fun _ h => h.elim, ?_,
        fun _ hHP ⟨_, he⟩ => (hHP.edgeSet_subset he).elim⟩
      · intro x hx y hy
        rw [mem_singleton_iff.mp hx, mem_singleton_iff.mp hy]
      · intro x _
        have hemp_inc : incidentEdges P x = ∅ := by ext e; simp [incidentEdges, P]
        rw [hemp_inc, ncard_empty]; omega
    refine ⟨P, hP_le, hP_path, ?_⟩
    rw [hterm_Q_sing]
    ext x
    simp only [P, mem_ofPred_eq, mem_singleton_iff]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    have hemp_inc : incidentEdges P x = ∅ := by ext e; simp [incidentEdges, P]
    rw [hemp_inc, ncard_empty]; omega
  · have hQ_ne : Q.edgeSet.Nonempty := nonempty_iff_ne_empty.mpr hQ_emp
    obtain ⟨x₁, hx₁_Q, x₂, hx₂_Q, hne_12, _, hdeg1_Q⟩ :=
      exists_isIndexedPath_of_isPathGraph hP_Q hQ_ne
    have hterm_Q_pair : terminals L ∩ Q.vertexSet = {x₁, x₂} := by
      rw [hterm_Q]
      ext x
      simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
      exact ⟨fun ⟨hxQ, hdeg⟩ => (hdeg1_Q x hxQ).mp hdeg,
        fun h => by
          rcases h with h_eq | h_eq
          · subst h_eq; exact ⟨hx₁_Q, (hdeg1_Q x hx₁_Q).mpr (Or.inl rfl)⟩
          · subst h_eq; exact ⟨hx₂_Q, (hdeg1_Q x hx₂_Q).mpr (Or.inr rfl)⟩⟩
    have hx₁_H : x₁ ∈ H.vertexSet := by
      have : x₁ ∈ terminals L ∩ H.vertexSet := by
        rw [hterm_eq, hterm_Q_pair]; exact Or.inl rfl
      exact this.2
    have hx₂_H : x₂ ∈ H.vertexSet := by
      have : x₂ ∈ terminals L ∩ H.vertexSet := by
        rw [hterm_eq, hterm_Q_pair]; exact Or.inr rfl
      exact this.2
    obtain ⟨P, hP_le, hP_path, hP_deg1⟩ :=
      exists_path_subgraph_between hH_graph hx₁_H hne_12 (hH_conn x₁ hx₁_H x₂ hx₂_H)
    rw [hterm_Q_pair]
    exact ⟨P, hP_le, hP_path, hP_deg1⟩

/-- Every path graph `Q` has a vertex of degree `≤ 1`. -/
theorem exists_deg_le_one_of_isPathGraph {α : Type u} {β : Type v}
    {Q : Hypergraph α β} (hP : IsPathGraph Q) :
    ∃ z ∈ Q.vertexSet, (incidentEdges Q z).ncard ≤ 1 := by
  by_cases hemp : Q.edgeSet = ∅
  · obtain ⟨v, hv_eq, hdeg0⟩ := isPathGraph_empty_edgeSet hP hemp
    exact ⟨v, hv_eq ▸ rfl, by omega⟩
  · obtain ⟨v, hv_mem, hv_deg1⟩ := hP.2.2.2.2.2.2 Q le_rfl (nonempty_iff_ne_empty.mpr hemp)
    exact ⟨v, hv_mem, hv_deg1.le⟩

/-- **Graph Minors XXI, (10.3)** (page 42 of the preprint):
"**10.3** *For every integer* $p \ge 0$, *no graph with a* $K_n$*-minor has a vital* $p$*-linkage,
where* $n = \lfloor\frac{5}{2}p\rfloor + 1$." -/
theorem theorem_10_3_proof (p : ℕ)
    {α : Type u} {β : Type v} (G : Hypergraph α β) (hG : G.IsGraph)
    (hKn : HasCliqueMinor G ((5 * p) / 2 + 1)) :
    ¬ HasVitalPLinkage G p := by
  classical
  have hGM13 : GM13Theorem61Statement.{u, v} := gm13Theorem61.{u, v}
  rintro ⟨L, hL_vit, hL_link, hL_card⟩
  let Z : Set α := terminals L
  have hZ_card : Z.ncard ≤ p := hL_card
  have hL_le : L ≤ G := hL_link.1
  have hL_graph : L.IsGraph := fun e he => by
    rw [← hL_le.ends_eq e he]
    exact hG e (hL_le.edgeSet_subset he)
  have hZ_sub_L : Z ⊆ L.vertexSet := fun _ hz => hz.1
  have hZ_sub_G : Z ⊆ G.vertexSet := hZ_sub_L.trans hL_le.vertexSet_subset
  have hZ_fin : Z.Finite := G.vertexSet_finite.subset hZ_sub_G
  let n : ℕ := (5 * p) / 2 + 1
  rcases hKn with ⟨SubG, hSubG_conn, hSubG_disj, hSubG_edges⟩
  have hG_ne : G.vertexSet.Nonempty := by
    let i₀ : Fin n := ⟨0, by omega⟩
    exact (hSubG_conn i₀).2.1.mono (hSubG_conn i₀).1.vertexSet_subset
  obtain ⟨D, hD_V, hD_E, hD_toG, hD_ends, hD_del⟩ := exists_digraph_of_isGraph hG hG_ne
  have hSubG_digraph : ∀ i : Fin n, D.IsConnectedSubgraph (SubG i) := fun i =>
    ⟨hD_toG.symm ▸ (hSubG_conn i).1, (hSubG_conn i).2.1, (hSubG_conn i).2.2⟩
  have hSubG_dedges : ∀ i j : Fin n, i < j →
      ∃ e ∈ D.edgeSet,
        ((D.tail e ∈ (SubG i).vertexSet ∧ D.head e ∈ (SubG j).vertexSet) ∨
         (D.tail e ∈ (SubG j).vertexSet ∧ D.head e ∈ (SubG i).vertexSet)) := by
    intro i j hij
    obtain ⟨e, heG, u, hu_i, w, hw_j, hinc_u, hinc_w⟩ := hSubG_edges i j hij
    have huw : u ≠ w :=
      fun h_eq => Set.disjoint_left.mp (hSubG_disj i j (ne_of_lt hij)) hu_i (h_eq ▸ hw_j)
    have hu_ends : u ∈ G.ends e := hinc_u
    have hw_ends : w ∈ G.ends e := hinc_w
    rw [hD_ends e heG] at hu_ends hw_ends
    refine ⟨e, hD_E.symm ▸ heG, ?_⟩
    rcases hu_ends with rfl | rfl <;> rcases hw_ends with rfl | rfl
    · exact (huw rfl).elim
    · exact Or.inl ⟨hu_i, hw_j⟩
    · exact Or.inr ⟨hw_j, hu_i⟩
    · exact (huw rfl).elim
  have hi₀ : ∃ i : Fin n, Disjoint Z (SubG i).vertexSet :=
    exists_disjoint_subG_of_ncard_lt hSubG_disj hZ_fin (by omega)
  obtain ⟨A, B, hsep_AB, hdisj_AB, hZ_A, hmin_AB, hmax_AB⟩ :=
    exists_min_max_separation hZ_sub_G hi₀
  rcases hdisj_AB with ⟨i_star, hi_star_disj⟩
  obtain ⟨v, hv_sub⟩ := (hSubG_conn i_star).2.1
  have hv_G : v ∈ G.vertexSet := (hSubG_conn i_star).1.vertexSet_subset hv_sub
  have hv_not_A : v ∉ A.vertexSet :=
    fun hvA => Set.disjoint_left.mp hi_star_disj hvA hv_sub
  have hv_B_diff_A : v ∈ B.vertexSet \ A.vertexSet := by
    have hv_union : v ∈ (A ∪ B).vertexSet := hsep_AB.union_eq.symm ▸ hv_G
    exact ⟨hv_union.resolve_left hv_not_A, hv_not_A⟩
  have hv_L : v ∈ L.vertexSet := hL_vit.2.1.symm ▸ hv_G
  have hcomp_v := (isComponentOf_componentOf hL_graph hv_L).1
  have hP_v : IsPathGraph (componentOf L v) := hL_link.2.2 (componentOf L v) hcomp_v
  obtain ⟨z₀, hz₀_comp, hz₀_deg⟩ := exists_deg_le_one_of_isPathGraph hP_v
  have hz₀_Z : z₀ ∈ Z :=
    (mem_terminals_iff_of_isComponentOf hL_graph hcomp_v hP_v hz₀_comp).mpr hz₀_deg
  have hZ_pos : 0 < Z.ncard := (ncard_pos hZ_fin).mpr ⟨z₀, hz₀_Z⟩
  have hp_pos : 1 ≤ p := by omega
  obtain ⟨e₀, _, _⟩ :=
    hSubG_edges ⟨0, by omega⟩ ⟨1, by omega⟩ (by show (0 : ℕ) < 1; omega)
  have : Nonempty β := ⟨e₀⟩
  have hD_fin : D.IsFinite := ⟨D.vertexSet_finite, D.edgeSet_finite⟩
  have hn_eq : (5 * p) / 2 + 3 * 0 + 1 = n := rfl
  have hirrel : IsIrrelevantToDigraphFolio D Z 0 v :=
    hGM13 D Z p 0 hD_fin (hD_V.symm ▸ hZ_sub_G) hZ_card SubG hSubG_digraph hSubG_disj hSubG_dedges
      A B (hD_toG.symm ▸ hsep_AB) ⟨i_star, hi_star_disj⟩ hZ_A
      (fun A' B' hsep' => hmin_AB A' B' (hD_toG ▸ hsep'))
      (fun A' B' hsep' => hmax_AB A' B' (hD_toG ▸ hsep'))
      v hv_B_diff_A
  -- Choose canonical representatives `rep : α → α` for the components of `L` meeting `Z`.
  let repComp (C : Hypergraph α β) : α :=
    if h : (Z ∩ C.vertexSet).Nonempty then Classical.choose h else v
  let rep (z : α) : α := repComp (componentOf L z)
  have hrep_mem : ∀ z ∈ Z, rep z ∈ Z ∧ rep z ∈ (componentOf L z).vertexSet := by
    intro z hz
    have hz_comp : z ∈ (componentOf L z).vertexSet := mem_reachSet_self (hZ_sub_L hz)
    have hne : (Z ∩ (componentOf L z).vertexSet).Nonempty := ⟨z, hz, hz_comp⟩
    simp only [rep, repComp, hne, ↓reduceDIte]
    exact Classical.choose_spec hne
  have hrep_comp : ∀ z ∈ Z, componentOf L (rep z) = componentOf L z := by
    intro z hz
    obtain ⟨_, hrep_in⟩ := hrep_mem z hz
    have hcomp_z := (isComponentOf_componentOf hL_graph (hZ_sub_L hz)).1
    exact (eq_componentOf_of_isComponentOf hL_graph hcomp_z hrep_in).symm
  have hrep_eq_iff : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z,
      rep z₁ = rep z₂ ↔ componentOf L z₁ = componentOf L z₂ := by
    intro z₁ hz₁ z₂ hz₂
    constructor
    · intro h_eq
      rw [← hrep_comp z₁ hz₁, h_eq, hrep_comp z₂ hz₂]
    · intro h_comp
      dsimp [rep]
      rw [h_comp]
  let U : Set α := rep '' Z
  have hU_sub_Z : U ⊆ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrep_mem z hz).1
  have hU_fin : U.Finite := hZ_fin.subset hU_sub_Z
  have hrep_id_on_U : ∀ u ∈ U, rep u = u := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hrep_eq_iff (rep z) (hrep_mem z hz).1 z hz).mpr (hrep_comp z hz)
  -- Enumerate `Z` by `roots : Fin k → α` where `k = Z.ncard`.
  let k : ℕ := Z.ncard
  have hk_eq : k = Fintype.card hZ_fin.toFinset := by
    rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card Z hZ_fin]
  let eZ : Fin k ≃ hZ_fin.toFinset :=
    (finCongr hk_eq).trans (Fintype.equivFin hZ_fin.toFinset).symm
  let roots : Fin k → α := fun i => (eZ i).1
  have hrange_roots : Set.range roots = Z := by
    ext x
    simp only [roots, mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact hZ_fin.mem_toFinset.mp (eZ i).2
    · intro hx
      exact ⟨eZ.symm ⟨x, hZ_fin.mem_toFinset.mpr hx⟩, by simp⟩
  have hG_roots : ∀ i : Fin k, roots i ∈ D.vertexSet := by
    intro i
    rw [hD_V]
    apply hZ_sub_G
    rw [← hrange_roots]
    exact mem_range_self i
  have hGv_roots : ∀ i : Fin k, roots i ∈ (D.deleteVertex v).vertexSet := by
    intro i
    have hi_Z : roots i ∈ Z := by rw [← hrange_roots]; exact mem_range_self i
    exact ⟨hG_roots i, fun h_eq => hirrel.v_not_mem_Z (mem_singleton_iff.mp h_eq ▸ hi_Z)⟩
  -- Build the edgeless target rooted digraph `RH` of detail `≤ 0`.
  let RH_G : Digraph α β :=
    { vertexSet := U
      edgeSet := ∅
      vertexSet_finite := hU_fin
      edgeSet_finite := finite_empty
      tail := D.tail
      head := D.head
      tail_mem := fun _ h => h.elim
      head_mem := fun _ h => h.elim }
  let RH : RootedDigraph α β k :=
    { G := RH_G
      roots := fun i => rep (roots i)
      roots_mem := fun i => ⟨roots i, by rw [← hrange_roots]; exact mem_range_self i, rfl⟩ }
  have hdetail : HasDetailLe RH 0 := by
    refine ⟨by simp [RH, RH_G], ?_⟩
    have hrange_RH : Set.range RH.roots = U := by
      change Set.range (rep ∘ roots) = rep '' Z
      rw [Set.range_comp, hrange_roots]
    change (U \ Set.range RH.roots).ncard ≤ 0
    rw [hrange_RH, Set.sdiff_self, ncard_empty]
  -- `L` gives a rooted digraph model of `RH` in `D`.
  have hminor_D : IsRootedDigraphMinor ⟨D, roots, hG_roots⟩ RH := by
    refine ⟨componentOf L, id, ⟨?_, ?_, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩, ?_⟩
    · intro u hu
      have hu_Z : u ∈ Z := hU_sub_Z hu
      have hcomp_u := (isComponentOf_componentOf hL_graph (hZ_sub_L hu_Z)).1
      exact ⟨hD_toG.symm ▸ (hcomp_u.1.trans hL_le), hcomp_u.2.1, hcomp_u.2.2.1⟩
    · intro u₁ hu₁ u₂ hu₂ hne
      have hu₁_Z : u₁ ∈ Z := hU_sub_Z hu₁
      have hu₂_Z : u₂ ∈ Z := hU_sub_Z hu₂
      have hcomp₁ := (isComponentOf_componentOf hL_graph (hZ_sub_L hu₁_Z)).1
      have hcomp₂ := (isComponentOf_componentOf hL_graph (hZ_sub_L hu₂_Z)).1
      have hne_comp : componentOf L u₁ ≠ componentOf L u₂ := by
        intro h_eq
        have := (hrep_eq_iff u₁ hu₁_Z u₂ hu₂_Z).mpr h_eq
        rw [hrep_id_on_U u₁ hu₁, hrep_id_on_U u₂ hu₂] at this
        exact hne this
      exact (disjoint_of_isComponentOf_ne hL_graph hcomp₁ hcomp₂ hne_comp).1
    · intro i
      have hi_Z : roots i ∈ Z := by rw [← hrange_roots]; exact mem_range_self i
      change roots i ∈ (componentOf L (rep (roots i))).vertexSet
      rw [hrep_comp (roots i) hi_Z]
      exact mem_reachSet_self (hZ_sub_L hi_Z)
  -- By irrelevance of `v`, `RH` is also a rooted digraph minor of `D.deleteVertex v`.
  have hminor_Dv : IsRootedDigraphMinor ⟨D.deleteVertex v, roots, hGv_roots⟩ RH :=
    (hirrel.folio_eq k roots hG_roots hGv_roots rfl hrange_roots RH hdetail).mp hminor_D
  rcases hminor_Dv with ⟨φV', _, hmodel', hroots'⟩
  have hroots'_Z : ∀ z ∈ Z, z ∈ (φV' (rep z)).vertexSet := by
    intro z hz
    have : z ∈ Set.range roots := hrange_roots.symm ▸ hz
    rcases this with ⟨i, rfl⟩
    exact hroots' i
  have hφV'_inter_Z : ∀ u ∈ U, Z ∩ (φV' u).vertexSet = Z ∩ (componentOf L u).vertexSet := by
    intro u hu
    have hu_Z : u ∈ Z := hU_sub_Z hu
    ext z
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hz_Z, hz_φ⟩
      refine ⟨hz_Z, ?_⟩
      have hrep_z_U : rep z ∈ U := ⟨z, hz_Z, rfl⟩
      have hz_φ_rep : z ∈ (φV' (rep z)).vertexSet := hroots'_Z z hz_Z
      have hrep_eq_u : rep z = u := by
        by_contra hne
        exact Set.disjoint_left.mp (hmodel'.vert_disjoint (rep z) hrep_z_U u hu hne) hz_φ_rep hz_φ
      have hcomp_eq : componentOf L z = componentOf L u := by
        rw [← hrep_comp z hz_Z, hrep_eq_u]
      rw [← hcomp_eq]
      exact mem_reachSet_self (hZ_sub_L hz_Z)
    · rintro ⟨hz_Z, hz_comp⟩
      refine ⟨hz_Z, ?_⟩
      have hcomp_u := (isComponentOf_componentOf hL_graph (hZ_sub_L hu_Z)).1
      have hcomp_eq : componentOf L z = componentOf L u :=
        (eq_componentOf_of_isComponentOf hL_graph hcomp_u hz_comp).symm
      have hrep_eq : rep z = u := by
        rw [← hrep_id_on_U u hu]
        exact (hrep_eq_iff z hz_Z u hu_Z).mpr hcomp_eq
      rw [← hrep_eq]
      exact hroots'_Z z hz_Z
  -- For each `u ∈ U`, extract a path subgraph `P u ≤ φV' u` with ends `Z ∩ (componentOf L u).vertexSet`.
  have hex_P : ∀ u ∈ U, ∃ P : Hypergraph α β,
      P ≤ φV' u ∧
      IsPathGraph P ∧
      {x ∈ P.vertexSet | (incidentEdges P x).ncard ≤ 1} = Z ∩ (componentOf L u).vertexSet := by
    intro u hu
    have hu_Z : u ∈ Z := hU_sub_Z hu
    have hcomp_u := (isComponentOf_componentOf hL_graph (hZ_sub_L hu_Z)).1
    have hP_comp : IsPathGraph (componentOf L u) := hL_link.2.2 (componentOf L u) hcomp_u
    have hφ_le_Gv : φV' u ≤ G.deleteVertices {v} :=
      hD_del v ▸ (hmodel'.vert_conn u hu).le_toHypergraph
    have hφ_le_G : φV' u ≤ G := hφ_le_Gv.trans (GM10.deleteVertices_le G {v})
    have hφ_graph : (φV' u).IsGraph := fun e he => by
      rw [← hφ_le_G.ends_eq e he]
      exact hG e (hφ_le_G.edgeSet_subset he)
    exact exists_path_subgraph_matching_component hL_graph hφ_graph hcomp_u hP_comp
      (hmodel'.vert_conn u hu).connected (hφV'_inter_Z u hu)
  let P_fn (u : α) : Hypergraph α β :=
    if hu : u ∈ U then Classical.choose (hex_P u hu) else componentOf L u
  have hP_le : ∀ u ∈ U, P_fn u ≤ φV' u := fun u hu => by
    simp only [P_fn, hu, ↓reduceDIte]
    exact (Classical.choose_spec (hex_P u hu)).1
  have hP_path : ∀ u ∈ U, IsPathGraph (P_fn u) := fun u hu => by
    simp only [P_fn, hu, ↓reduceDIte]
    exact (Classical.choose_spec (hex_P u hu)).2.1
  have hP_deg1 : ∀ u ∈ U,
      {x ∈ (P_fn u).vertexSet | (incidentEdges (P_fn u) x).ncard ≤ 1} =
        Z ∩ (componentOf L u).vertexSet := fun u hu => by
    simp only [P_fn, hu, ↓reduceDIte]
    exact (Classical.choose_spec (hex_P u hu)).2.2
  have hP_le_Gv : ∀ u ∈ U, P_fn u ≤ G.deleteVertices {v} := fun u hu =>
    (hP_le u hu).trans (hD_del v ▸ (hmodel'.vert_conn u hu).le_toHypergraph)
  have hP_le_G : ∀ u ∈ U, P_fn u ≤ G := fun u hu =>
    (hP_le_Gv u hu).trans (GM10.deleteVertices_le G {v})
  have hP_disj_V : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ ≠ u₂ →
      Disjoint (P_fn u₁).vertexSet (P_fn u₂).vertexSet := fun u₁ hu₁ u₂ hu₂ hne =>
    (hmodel'.vert_disjoint u₁ hu₁ u₂ hu₂ hne).mono
      (hP_le u₁ hu₁).vertexSet_subset (hP_le u₂ hu₂).vertexSet_subset
  have hP_disj_E : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ ≠ u₂ →
      Disjoint (P_fn u₁).edgeSet (P_fn u₂).edgeSet := by
    intro u₁ hu₁ u₂ hu₂ hne
    refine Set.disjoint_left.mpr fun e he₁ he₂ => ?_
    obtain ⟨⟨x, hx_inc⟩, _⟩ := (hP_path u₁ hu₁).1 e he₁
    have hx₁ : x ∈ (P_fn u₁).vertexSet := (P_fn u₁).vertex_mem_of_inc hx_inc
    have hx_G : G.Inc e x := (GM10.inc_iff_of_le (hP_le_G u₁ hu₁) he₁).mp hx_inc
    have hx₂ : x ∈ (P_fn u₂).vertexSet :=
      (P_fn u₂).vertex_mem_of_inc ((GM10.inc_iff_of_le (hP_le_G u₂ hu₂) he₂).mpr hx_G)
    exact Set.disjoint_left.mp (hP_disj_V u₁ hu₁ u₂ hu₂ hne) hx₁ hx₂
  -- Assemble `L'` as the union of `P_fn u` over `u ∈ U`.
  let L' : Hypergraph α β :=
    { vertexSet := ⋃ u ∈ U, (P_fn u).vertexSet
      edgeSet := ⋃ u ∈ U, (P_fn u).edgeSet
      Inc := fun e x => (∃ u ∈ U, e ∈ (P_fn u).edgeSet) ∧ G.Inc e x
      vertex_mem_of_inc := by
        rintro e x ⟨⟨u, hu, he⟩, hincG⟩
        have hinc_u : (P_fn u).Inc e x := (GM10.inc_iff_of_le (hP_le_G u hu) he).mpr hincG
        exact mem_biUnion hu ((P_fn u).vertex_mem_of_inc hinc_u)
      edge_mem_of_inc := by
        rintro _ _ ⟨⟨u, hu, he⟩, _⟩
        exact mem_biUnion hu he
      vertexSet_finite := hU_fin.biUnion fun u _ => (P_fn u).vertexSet_finite
      edgeSet_finite := hU_fin.biUnion fun u _ => (P_fn u).edgeSet_finite }
  have hL'_le_Gv : L' ≤ G.deleteVertices {v} := by
    refine ⟨iUnion₂_subset fun u hu => (hP_le_Gv u hu).vertexSet_subset,
      iUnion₂_subset fun u hu => (hP_le_Gv u hu).edgeSet_subset, fun e he => ?_⟩
    rcases mem_iUnion₂.mp he with ⟨u, hu, he_u⟩
    have he_Gv : e ∈ (G.deleteVertices {v}).edgeSet := (hP_le_Gv u hu).edgeSet_subset he_u
    rw [← (GM10.deleteVertices_le G {v}).ends_eq e he_Gv]
    ext x
    simp only [Hypergraph.ends, L', mem_ofPred_eq]
    exact ⟨fun h => ⟨⟨u, hu, he_u⟩, h⟩, fun h => h.2⟩
  have hL'_le_G : L' ≤ G := hL'_le_Gv.trans (GM10.deleteVertices_le G {v})
  have hL'_graph : L'.IsGraph := fun e he => by
    rw [← hL'_le_G.ends_eq e he]
    exact hG e (hL'_le_G.edgeSet_subset he)
  have hP_le_L' : ∀ u ∈ U, P_fn u ≤ L' := by
    intro u hu
    refine ⟨fun _ hx => mem_biUnion hu hx, fun _ hx => mem_biUnion hu hx, fun e he => ?_⟩
    have he_L' : e ∈ L'.edgeSet := mem_biUnion hu he
    rw [← hL'_le_G.ends_eq e he_L', ← (hP_le_G u hu).ends_eq e he]
  have hP_isComp : ∀ u ∈ U, IsComponentOf L' (P_fn u) := by
    intro u hu
    have hP_u := hP_path u hu
    refine ⟨hP_le_L' u hu, hP_u.2.1, hP_u.2.2.1, ?_⟩
    intro C' hC'_le _ hC'_conn hle_u
    rcases hP_u.2.1 with ⟨x₀, hx₀⟩
    have hx₀_C' : x₀ ∈ C'.vertexSet := hle_u.vertexSet_subset hx₀
    have hstep : ∀ {a b : α}, L'.skeleton.Adj a b → a ∈ (P_fn u).vertexSet → b ∈ (P_fn u).vertexSet := by
      rintro a b ⟨_, e, ⟨⟨u', hu', he'⟩, hinc_a⟩, ⟨_, hinc_b⟩⟩ ha
      have ha' : a ∈ (P_fn u').vertexSet :=
        (P_fn u').vertex_mem_of_inc ((GM10.inc_iff_of_le (hP_le_G u' hu') he').mpr hinc_a)
      have hb' : b ∈ (P_fn u').vertexSet :=
        (P_fn u').vertex_mem_of_inc ((GM10.inc_iff_of_le (hP_le_G u' hu') he').mpr hinc_b)
      by_cases h_eq : u' = u
      · exact h_eq ▸ hb'
      · exact (Set.disjoint_left.mp (hP_disj_V u' hu' u hu h_eq) ha' ha).elim
    have hV_sub : C'.vertexSet ⊆ (P_fn u).vertexSet := by
      intro y hy
      rcases hC'_conn x₀ hx₀_C' y hy with ⟨q⟩
      have hwalk : ∀ {a b : α} (w : C'.skeleton.Walk a b),
          a ∈ (P_fn u).vertexSet → b ∈ (P_fn u).vertexSet := by
        intro a b w ha
        induction w with
        | nil => exact ha
        | @cons a c b hadj w' ih =>
          rcases hadj with ⟨hne_ac, e, ha_inc, hc_inc⟩
          have heC' : e ∈ C'.edgeSet := C'.edge_mem_of_inc ha_inc
          have hadj_L' : L'.skeleton.Adj a c :=
            ⟨hne_ac, e, (GM10.inc_iff_of_le hC'_le heC').mp ha_inc,
              (GM10.inc_iff_of_le hC'_le heC').mp hc_inc⟩
          exact ih (hstep hadj_L' ha)
      exact hwalk q hx₀
    have hE_sub : C'.edgeSet ⊆ (P_fn u).edgeSet := by
      intro e he
      have heL' : e ∈ L'.edgeSet := hC'_le.edgeSet_subset he
      rcases mem_iUnion₂.mp heL' with ⟨u', hu', he'⟩
      obtain ⟨⟨x, hx_inc⟩, _⟩ := (hP_path u' hu').1 e he'
      have hx_u' : x ∈ (P_fn u').vertexSet := (P_fn u').vertex_mem_of_inc hx_inc
      have hx_G : G.Inc e x := (GM10.inc_iff_of_le (hP_le_G u' hu') he').mp hx_inc
      have hx_L' : L'.Inc e x := ⟨⟨u', hu', he'⟩, hx_G⟩
      have hx_C' : x ∈ C'.vertexSet :=
        C'.vertex_mem_of_inc ((GM10.inc_iff_of_le hC'_le he).mpr hx_L')
      have hx_u : x ∈ (P_fn u).vertexSet := hV_sub hx_C'
      by_cases h_eq : u' = u
      · exact h_eq ▸ he'
      · exact (Set.disjoint_left.mp (hP_disj_V u' hu' u hu h_eq) hx_u' hx_u).elim
    exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hC'_le (hP_le_L' u hu)
      (Subset.antisymm hV_sub hle_u.vertexSet_subset)
      (Subset.antisymm hE_sub hle_u.edgeSet_subset)
  have hcomp_L'_iff : ∀ C' : Hypergraph α β, IsComponentOf L' C' ↔ ∃ u ∈ U, C' = P_fn u := by
    intro C'
    constructor
    · intro hC'
      rcases hC'.2.1 with ⟨x, hxC'⟩
      have hxL' : x ∈ L'.vertexSet := hC'.1.vertexSet_subset hxC'
      rcases mem_iUnion₂.mp hxL' with ⟨u, hu, hxu⟩
      refine ⟨u, hu, ?_⟩
      have h1 := eq_componentOf_of_isComponentOf hL'_graph hC' hxC'
      have h2 := eq_componentOf_of_isComponentOf hL'_graph (hP_isComp u hu) hxu
      exact h1.trans h2.symm
    · rintro ⟨u, hu, rfl⟩
      exact hP_isComp u hu
  have hL'_link : IsLinkage G L' := by
    refine ⟨hL'_le_G, hL'_graph, fun C' hC' => ?_⟩
    rcases (hcomp_L'_iff C').mp hC' with ⟨u, hu, rfl⟩
    exact hP_path u hu
  have hcomp_L_iff : ∀ C : Hypergraph α β, IsComponentOf L C ↔ ∃ u ∈ U, C = componentOf L u := by
    intro C
    constructor
    · intro hC
      have hP_C : IsPathGraph C := hL_link.2.2 C hC
      obtain ⟨z, hzC, hz_deg⟩ := exists_deg_le_one_of_isPathGraph hP_C
      have hz_Z : z ∈ Z :=
        (mem_terminals_iff_of_isComponentOf hL_graph hC hP_C hzC).mpr hz_deg
      refine ⟨rep z, ⟨z, hz_Z, rfl⟩, ?_⟩
      rw [hrep_comp z hz_Z]
      exact eq_componentOf_of_isComponentOf hL_graph hC hzC
    · rintro ⟨u, hu, rfl⟩
      exact (isComponentOf_componentOf hL_graph (hZ_sub_L (hU_sub_Z hu))).1
  have hpat_eq : linkagePattern L' = linkagePattern L := by
    ext B_set
    simp only [linkagePattern, mem_ofPred_eq]
    constructor
    · rintro ⟨C', hC', rfl⟩
      rcases (hcomp_L'_iff C').mp hC' with ⟨u, hu, rfl⟩
      refine ⟨componentOf L u, (hcomp_L_iff (componentOf L u)).mpr ⟨u, hu, rfl⟩, ?_⟩
      have hterm_u : terminals L' ∩ (P_fn u).vertexSet =
          {x ∈ (P_fn u).vertexSet | (incidentEdges (P_fn u) x).ncard ≤ 1} := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun ⟨ht, hxu⟩ =>
          ⟨hxu, (mem_terminals_iff_of_isComponentOf hL'_graph (hP_isComp u hu) (hP_path u hu) hxu).mp ht⟩,
          fun ⟨hxu, hdeg⟩ =>
          ⟨(mem_terminals_iff_of_isComponentOf hL'_graph (hP_isComp u hu) (hP_path u hu) hxu).mpr hdeg, hxu⟩⟩
      exact hterm_u.trans (hP_deg1 u hu)
    · rintro ⟨C, hC, rfl⟩
      rcases (hcomp_L_iff C).mp hC with ⟨u, hu, rfl⟩
      refine ⟨P_fn u, hP_isComp u hu, ?_⟩
      have hterm_u : terminals L' ∩ (P_fn u).vertexSet =
          {x ∈ (P_fn u).vertexSet | (incidentEdges (P_fn u) x).ncard ≤ 1} := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun ⟨ht, hxu⟩ =>
          ⟨hxu, (mem_terminals_iff_of_isComponentOf hL'_graph (hP_isComp u hu) (hP_path u hu) hxu).mp ht⟩,
          fun ⟨hxu, hdeg⟩ =>
          ⟨(mem_terminals_iff_of_isComponentOf hL'_graph (hP_isComp u hu) (hP_path u hu) hxu).mpr hdeg, hxu⟩⟩
      exact (hterm_u.trans (hP_deg1 u hu)).symm
  have hL'_eq_L : L' = L := hL_vit.2.2 L' hL'_link hpat_eq
  have hv_in_L' : v ∈ L'.vertexSet := by
    rw [hL'_eq_L, hL_vit.2.1]
    exact hv_G
  have hv_not_L' : v ∉ L'.vertexSet :=
    fun hvL' => (hL'_le_Gv.vertexSet_subset hvL').2 rfl
  exact hv_not_L' hv_in_L'

/-- **Graph Minors XXI, (10.4)** (page 42 of the preprint):
"**10.4** *For every integer* $p \ge 0$ *there exists* $\theta \ge 1$ *such that, if a graph* $G$
*has a tangle of order* $\ge \theta$ *then* $G$ *has no vital* $p$*-linkage.*" -/
theorem theorem_10_4_proof
    (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v}
        (G : Hypergraph α β) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
        G.IsGraph →
        θ ≤ θ_G →
        IsTangle G θ_G 𝒯 →
        ¬ HasVitalPLinkage G p := by
  let n : ℕ := (5 * p) / 2 + 1
  obtain ⟨θ, hθ_pos, h102⟩ := theorem_10_2_proof n p
  refine ⟨θ, hθ_pos, ?_⟩
  intro α β G θ_G 𝒯 hG hθ_le h𝒯
  by_cases hKn : HasCliqueMinor G n
  · exact theorem_10_3_proof p G hG hKn
  · exact h102 G θ_G 𝒯 hG hKn hθ_le h𝒯

end GM21
end GraphMinor
