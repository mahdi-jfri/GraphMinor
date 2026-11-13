module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PotentialNeighborhood
import GraphMinor.Thomason.ElevenPotential
import GraphMinor.Thomason.ElevenReducedGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# The eleven-vertex density bound

The first dense-minor reduction yields minimum degree fifty-four and
order at most one hundred eight. The verified integer potential yields a
neighbourhood satisfying the proved nine-vertex clique criterion.
Both neighbourhood centres then provide a eleven-vertex clique minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- Every non-null finite simple graph of density at least fifty-four
has a eleven-vertex clique minor. The integer potential preserves the
order-dependent degree information needed for this finite case. -/
theorem clique_eleven_of_density_fifty_four {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 54 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 11))) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨W, hW, H, hH, hneH, _, hHsize, hHdegree, hHG⟩ :=
    exists_small_dense_minor_with_clique_extension G 54 (by decide) hden
  let := hW
  let := hH
  let := hneH
  have hlarge : 55 ≤ Fintype.card W := by
    let v := Classical.arbitrary W
    have hh := hHdegree v
    have hv := H.degree_lt_card_verts v
    omega
  have hsum : 54 * Fintype.card W ≤ 2 * H.edgeFinset.card := by
    calc
      54 * Fintype.card W = ∑ _ : W, 54 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : W, H.degree v := sum_le_sum (fun v _ => hHdegree v)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hthreshold : elevenPotential (Fintype.card W) ≤ H.edgeFinset.card :=
    (elevenPotential_le_twenty_seven_mul _ hHsize).trans (by omega)
  obtain ⟨n, X, hX, J, hJ, hneJ, hn, hn', he, _, hJsize, hJdegree, hJH⟩ :=
    exists_potential_neighborhood H elevenPotential elevenPotential_monotone 24 (by decide)
      (by omega) elevenPotential_boundary hthreshold
  let := hX
  let := hJ
  let := hneJ
  obtain ⟨hDlow, hNmax, hDgap, hDthree, hDtwelve⟩ :=
    elevenPotential_bounds n hn (hn'.trans hHsize) he
  have hJlow : 26 ≤ Fintype.card X := by
    let v := Classical.arbitrary X
    have hh := hJdegree v
    have hv := J.degree_lt_card_verts v
    omega
  have hgap : ∀ v, Fintype.card X + 17 ≤ 2 * J.degree v := by
    intro v
    have hh := hJdegree v
    omega
  have hthree : ∀ v, 2 * Fintype.card X + 4 ≤ 3 * J.degree v := by
    intro v
    have hh := hJdegree v
    omega
  have htwelve : ∀ v, Fintype.card X ≤ J.degree v + 15 := by
    intro v
    have hh := hJdegree v
    omega
  have hm := clique_nine_of_order_le_fifty_three J hJlow (hJsize.trans hNmax) hgap hthree htwelve
  exact hHG 10 (hJH 9 hm)

end GraphMinor.Thomason
