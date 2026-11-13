module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Thomason.PotentialNeighborhood
import GraphMinor.Thomason.TenPotential
import GraphMinor.Thomason.TenReducedGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Lean.Elab.Tactic.Omega

/-!
# The ten-vertex density bound

The first dense-minor reduction yields minimum degree forty-eight and
order at most ninety-six. The verified integer potential yields a
neighbourhood satisfying the proved eight-vertex clique criterion.
Both neighbourhood centres then provide a ten-vertex clique minor.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- Every non-null finite simple graph of density at least forty-eight
has a ten-vertex clique minor. The integer potential preserves the
order-dependent degree information needed for this finite case. -/
theorem clique_ten_of_density_forty_eight {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hden : 48 * Fintype.card V ≤ G.edgeFinset.card) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 10))) (Graph.ofSimpleGraph G) := by
  classical
  obtain ⟨W, hW, H, hH, hneH, _, hHsize, hHdegree, hHG⟩ :=
    exists_small_dense_minor_with_clique_extension G 48 (by decide) hden
  let := hW
  let := hH
  let := hneH
  have hlarge : 49 ≤ Fintype.card W := by
    let v := Classical.arbitrary W
    have hh := hHdegree v
    have hv := H.degree_lt_card_verts v
    omega
  have hsum : 48 * Fintype.card W ≤ 2 * H.edgeFinset.card := by
    calc
      48 * Fintype.card W = ∑ _ : W, 48 := by simp [Nat.mul_comm]
      _ ≤ ∑ v : W, H.degree v := sum_le_sum (fun v _ => hHdegree v)
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  have hthreshold : tenPotential (Fintype.card W) ≤ H.edgeFinset.card :=
    (tenPotential_le_twenty_four_mul _ hHsize).trans (by omega)
  obtain ⟨n, X, hX, J, hJ, hneJ, hn, hn', he, _, hJsize, hJdegree, hJH⟩ :=
    exists_potential_neighborhood H tenPotential tenPotential_monotone 18 (by decide)
      (by omega) tenPotential_boundary hthreshold
  let := hX
  let := hJ
  let := hneJ
  obtain ⟨hDlow, hNmax, hDgap, hDthree, hDtwelve⟩ :=
    tenPotential_bounds n hn (hn'.trans hHsize) he
  have hJlow : 22 ≤ Fintype.card X := by
    let v := Classical.arbitrary X
    have hh := hJdegree v
    have hv := J.degree_lt_card_verts v
    omega
  have hgap : ∀ v, Fintype.card X + 14 ≤ 2 * J.degree v := by
    intro v
    have hh := hJdegree v
    omega
  have hthree : ∀ v, 2 * Fintype.card X + 3 ≤ 3 * J.degree v := by
    intro v
    have hh := hJdegree v
    omega
  have htwelve : ∀ v, Fintype.card X ≤ J.degree v + 13 := by
    intro v
    have hh := hJdegree v
    omega
  have hm := clique_eight_of_order_le_forty_five J hJlow (hJsize.trans hNmax) hgap hthree htwelve
  exact hHG 9 (hJH 8 hm)

end GraphMinor.Thomason
