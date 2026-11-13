module

public import GraphMinor.GM01.Section4LayerWidths
public import GraphMinor.GM01.QuantitativeBounds
import GraphMinor.GM01.Section4SampledOrder
import GraphMinor.GM01.Section4SampledChoices
import GraphMinor.GM01.SeparatorLayerWidths
import GraphMinor.GM01.QuantitativeFirstEstimates
import GraphMinor.GM01.QuantitativeParity
import GraphMinor.GM01.MaximalComb
import GraphMinor.GM01.BlockParameters
import GraphMinor.GM01.CombSubdivision

/-!
# Part 2 of the rooted path-width induction

Graph Minors I, Section 4, pages 55–59, derives the rooted fork bound
at height `γ` from the rooted comb bound at height `γ−1`. If the
larger comb is absent, apply that preceding bound directly. Otherwise
choose a maximal represented comb, its blocks, and the sampled small
minimal separators. The completed geometric argument excludes the
larger comb in each layer component. Apply the preceding bound to
those components and glue the layers using (1.6). Inequality (3.6)(ii)
gives the required fork width bound.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The actual Part 2 implication in the proof of GM01 (3.7),
pages 55–59. `hPrev` is the preceding-height induction hypothesis
printed at the start of Section 4. All choices, layer exclusions,
and gluing steps of Part 2 are proved inside this implication. -/
theorem pathWidthLE_of_not_rootedFork_of_previous_height
    {α : Type u} {β : Type v} (lam : ℕ) {γ δ : ℕ} (hγ : 0 < γ) (hδ : 2 ≤ δ)
    (hPrev : ∀ (d : ℕ) (hd : 2 ≤ d), ∀ C : RootedGraph α β,
      V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedPathComb (γ - 1) d (by omega)) C) →
      HasPathWidthLE C.graph (pathWidthBound lam (γ - 1) d))
    (G : RootedGraph α β) (hfin : V(G.graph).Finite) (hconn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G) :
    HasPathWidthLE G.graph (forkWidthBound lam γ δ) := by
  classical
  let θ := gm01Theta lam
  let ν := θ ^ (2 * θ)
  let μ := 2 + 4 * ν + 2 * δ
  have hθ : 6 ≤ θ := gm01Theta_ge_six lam
  have hν : 3 ≤ ν := theta_window_ge_three hθ
  have hμ : 2 ≤ μ := by dsimp [μ]; omega
  have hmargin : θ ^ 2 + pathWidthBound lam (γ - 1) μ ≤ forkWidthBound lam γ δ :=
    forkWidthBound_separator lam γ δ
  by_cases hmodel : HasRootedMinor (rootedPathComb (γ - 1) μ (by omega)) G
  · obtain ⟨L, hμL, hL, ⟨M⟩, hmaxL⟩ := exists_max_rootedPathComb G hfin (by omega : 0 < μ) hmodel
    obtain ⟨T, n, hT, hn, _, hmaxT, _, hupper, _⟩ :=
      exists_comb_block_parameters ν δ L (by omega) (by change μ ≤ L; exact hμL)
    have htail : 2 * n - 2 + 2 * δ ≤ L := by dsimp [μ] at hμL; omega
    obtain ⟨N, c, P, R, hN, hc, hV, hE, hPaths, hInter', hR, hMeet, _⟩ :=
      M.pathComb_subdivision (by omega : 2 ≤ L) G
    have hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
        V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f) :=
      fun e f hne ↦ ⟨(hInter' e f hne).2, (hInter' e f hne).1⟩
    have hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root} := by
      rw [Set.inter_comm]
      exact hMeet.subset
    obtain ⟨left, right, hleft, hright, Y, hYG, hcard, hY⟩ := exists_sampled_minimal_comb_separators
      hγ hδ hL htail G hfin hθ (gm01Theta_even lam) hGrid hno hN hc hV hE hPaths hInter hR hmeetR hn
    have horder : ∀ i j, ∀ y ∈ Y j, GraphSeparates G.graph (Y i) {y} {G.root.val} ↔ i ≤ j := by
      intro i j y hy
      exact theorem_4_5_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
        hν left right hleft hright Y hY i j hy
    have hwidth : ∀ i : Fin (T + 1),
        HasPathWidthLE (G.graph.induce (separatorLayer G.graph G.root.val Y i))
          (pathWidthBound lam (γ - 1) μ) :=
      section4_layer_widths hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
        hν left right hleft hright Y hY hn (m := μ) rfl hT hmaxT hmaxL hconn hfin hGrid (hPrev μ hμ)
    have hGlued := hasPathWidthLE_of_separator_layers hfin Y hYG horder
      (fun i ↦ Nat.le_of_lt (hcard i)) hwidth
    apply hGlued.mono
    have hhalf : 2 * (θ ^ 2 / 2) ≤ θ ^ 2 := Nat.mul_div_le _ _
    change pathWidthBound lam (γ - 1) μ + 2 * (θ ^ 2 / 2) ≤ forkWidthBound lam γ δ
    omega
  · exact (hPrev μ hμ G hfin hconn hGrid hmodel).mono (by omega)

end GraphMinor.GM01
