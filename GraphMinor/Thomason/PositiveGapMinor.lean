module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import GraphMinor.Thomason.NeighborMinor
import GraphMinor.Thomason.LogPotential
import GraphMinor.Thomason.PotentialDegreeBounds
import GraphMinor.Thomason.MinorOrder
import GraphMinor.Thomason.DensitySubgraphs
import GraphMinor.Thomason.DenseNeighborhood
import GraphMinor.Minor.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
# The positive-gap minor in Thomason's reduction

Use the logarithmic threshold in the proved minimal-potential construction.
Its degree and common-neighbour bounds give a neighbourhood minor whose
order is at most `a r` and whose minimum degree has the required positive
gap above half its order. This is the refined-minor step of Thomason's
Lemma 1 (1984), page 262.
-/

public section

namespace GraphMinor.Thomason

open SimpleGraph Graph

universe u

/-- The refined-minor step in Thomason's Lemma 1, p. 262. A graph of order
at most `2d` and minimum degree at least `d = a r` has a minor of order at
most `d` in which twice every degree minus the order exceeds `r - 4`. -/
theorem exists_minor_with_degree_gap_and_clique_extension {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a r : ℝ) (d : ℕ)
    (hr : 1 < r) (ha : 1 < a) (halog : 1 + Real.log (2 * a) ≤ a)
    (hd : (d : ℝ) = a * r) (hsize : Fintype.card V ≤ 2 * d)
    (hdegree : ∀ v : V, d ≤ G.degree v) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      Fintype.card W ≤ d ∧
      (∀ x : W, r - 4 < 2 * (H.degree x : ℝ) - (Fintype.card W : ℝ)) ∧
      ∀ q : ℕ, IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph H) →
        IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin (q + 1)))) (Graph.ofSimpleGraph G) := by
  classical
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hdgt : r < (d : ℝ) := by nlinarith only [hd, hrpos, ha]
  have hdN : d < Fintype.card V :=
    lt_of_le_of_lt (hdegree (Classical.arbitrary V)) (G.degree_lt_card_verts _)
  have hNpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  have hsizeR : (Fintype.card V : ℝ) ≤ 2 * a * r := by
    have h : (Fintype.card V : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast hsize
    nlinarith only [h, hd]
  let f := logarithmicThreshold r
  let m : ℕ := ⌈r⌉₊
  have hmpos : 0 < m := Nat.ceil_pos.mpr hrpos
  have hmN : m ≤ Fintype.card V := Nat.ceil_le.mpr
    (le_trans hdgt.le (by exact_mod_cast hdN.le))
  have hboundary : m.choose 2 < f m := completeGraph_lt_logarithmicThreshold hr
  have hsum : d * Fintype.card V ≤ 2 * G.edgeFinset.card := by
    calc
      d * Fintype.card V = ∑ _ : V, d := by simp [Nat.mul_comm]
      _ ≤ ∑ v : V, G.degree v := Finset.sum_le_sum fun v _ => hdegree v
      _ = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hsumR : (d : ℝ) * (Fintype.card V : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ) := by
    exact_mod_cast hsum
  have hupper := logarithmicPotential_le_density hrpos hNpos halog hsizeR
  have hden : f (Fintype.card V) ≤ G.edgeFinset.card := Nat.ceil_le.mpr (by
    nlinarith only [hupper, hsumR, hd])
  obtain ⟨X, hX, H, hH, hneH, hmX, hminor, hcard, hvertex, hcommon⟩ :=
    exists_potential_minor_with_degree_bounds G f m hmpos hmN hboundary hden
  let := hX
  let := hH
  let := hneH
  have horder := card_le_of_isIsoMinor_ofSimpleGraph hminor
  have hXpos : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos (α := X)
  have hXm : m ≤ Fintype.card X - 1 := by omega
  have hpredR : r ≤ ((Fintype.card X - 1 : ℕ) : ℝ) :=
    le_trans (Nat.le_ceil r) (by exact_mod_cast hXm)
  have hXone : 1 < Fintype.card X := by
    have hmr : (1 : ℝ) < m := lt_of_lt_of_le hr (Nat.le_ceil r)
    have hmone : 1 < m := by exact_mod_cast hmr
    omega
  have hpredCast : ((Fintype.card X - 1 : ℕ) : ℝ) = (Fintype.card X : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card X), Nat.cast_one]
  have hXoneR : (1 : ℝ) < Fintype.card X := by exact_mod_cast hXone
  have hXtwoR : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast (show 2 ≤ Fintype.card X by omega)
  have hXupper : (Fintype.card X : ℝ) ≤ 2 * a * r := by
    have h : Fintype.card X ≤ 2 * d := le_trans horder hsize
    have hR : (Fintype.card X : ℝ) ≤ 2 * (d : ℝ) := by exact_mod_cast h
    nlinarith only [hR, hd]
  let t := logarithmicPotential r (Fintype.card X : ℝ)
  let s := logarithmicPotential r ((Fintype.card X : ℝ) - 1)
  have hprevNonneg : 0 ≤ s := by
    apply logarithmicPotential_nonneg hrpos
    rwa [← hpredCast]
  have hcurrNonneg : 0 ≤ t := logarithmicPotential_nonneg hrpos
    (le_trans hpredR (by exact_mod_cast Nat.sub_le (Fintype.card X) 1))
  have hceilLo : t ≤ (f (Fintype.card X) : ℝ) := Nat.le_ceil _
  have hceilHi : (f (Fintype.card X) : ℝ) < t + 1 := Nat.ceil_lt_add_one hcurrNonneg
  have hceilPrev : (f (Fintype.card X - 1) : ℝ) < s + 1 := by
    dsimp only [f, logarithmicThreshold, s]
    rw [hpredCast]
    exact Nat.ceil_lt_add_one hprevNonneg
  have hmono : f (Fintype.card X - 1) ≤ f (Fintype.card X) := by
    apply Nat.ceil_mono
    exact logarithmicPotential_mono hrpos hpredR
      (by exact_mod_cast Nat.sub_le (Fintype.card X) 1)
  have hmean : H.minDegree * Fintype.card X ≤ 2 * f (Fintype.card X) := by
    calc
      H.minDegree * Fintype.card X = ∑ _ : X, H.minDegree := by simp [Nat.mul_comm]
      _ ≤ ∑ x : X, H.degree x := Finset.sum_le_sum fun x _ => H.minDegree_le_degree x
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
      _ = 2 * f (Fintype.card X) := by rw [hcard]
  have hmeanR : (H.minDegree : ℝ) * (Fintype.card X : ℝ) ≤
      2 * (f (Fintype.card X) : ℝ) := by exact_mod_cast hmean
  have havg : (H.minDegree : ℝ) < 2 * t / (Fintype.card X : ℝ) + 1 := by
    have hlt : ((H.minDegree : ℝ) - 1) * (Fintype.card X : ℝ) < 2 * t := by
      nlinarith only [hmeanR, hceilHi, hXtwoR]
    have hdiv := (lt_div_iff₀ hXpos).mpr hlt
    linarith only [hdiv]
  have hFupper : 2 * t ≤ (d : ℝ) * (Fintype.card X : ℝ) := by
    have h := logarithmicPotential_le_density hrpos hXpos halog hXupper
    nlinarith only [h, hd]
  have hminle : H.minDegree ≤ d := by
    have hA : 2 * t / (Fintype.card X : ℝ) ≤ d := (div_le_iff₀ hXpos).mpr hFupper
    have hlt : (H.minDegree : ℝ) < (d : ℝ) + 1 := by linarith only [havg, hA]
    have hltNat : H.minDegree < d + 1 := by exact_mod_cast hlt
    omega
  obtain ⟨u, hu⟩ := H.exists_minimal_degree_vertex
  have hdupos : 0 < H.degree u := by
    have hv := hvertex u
    omega
  obtain ⟨w, hw⟩ := (H.degree_pos_iff_exists_adj u).mp hdupos
  have hneN : Nonempty (H.neighborSet u) := ⟨⟨w, hw⟩⟩
  let J := H.induce (H.neighborSet u)
  refine ⟨H.neighborSet u, inferInstance, J, inferInstance, hneN,
    (isIsoMinor_ofSimpleGraph_induce H _).trans hminor, ?_, ?_, ?_⟩
  · rw [H.card_neighborSet_eq_degree, ← hu]
    exact hminle
  · intro x
    have hc : (f (Fintype.card X) : ℝ) ≤ (f (Fintype.card X - 1) : ℝ) +
        ((H.commonNeighbors u x.val).ncard : ℝ) := by
      exact_mod_cast hcommon u x.val x.property
    have hdeg : t - s - 1 < (J.degree x : ℝ) := by
      rw [degree_neighborhood_eq_commonNeighbors H u x]
      linarith only [hc, hceilLo, hceilPrev]
    have hrX : r < (Fintype.card X : ℝ) := by linarith only [hpredR, hpredCast]
    have hgap : r - 1 < 2 * (t - s) - 2 * t / (Fintype.card X : ℝ) :=
      logarithmicPotential_gap_gt hrpos hXoneR hrX
    rw [H.card_neighborSet_eq_degree, ← hu]
    linarith only [hdeg, havg, hgap]

  · intro q hq
    exact (clique_isIsoMinor_of_neighbor_minor H u hq).trans hminor

/-- The refined-minor step in Thomason's Lemma 1, p. 262, retaining
its order bound and positive minimum-degree surplus. -/
theorem exists_minor_with_degree_gap {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a r : ℝ) (d : ℕ)
    (hr : 1 < r) (ha : 1 < a) (halog : 1 + Real.log (2 * a) ≤ a)
    (hd : (d : ℝ) = a * r) (hsize : Fintype.card V ≤ 2 * d)
    (hdegree : ∀ v : V, d ≤ G.degree v) :
    ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (_ : DecidableRel H.Adj)
      (_ : Nonempty W),
      IsIsoMinor (Graph.ofSimpleGraph H) (Graph.ofSimpleGraph G) ∧
      Fintype.card W ≤ d ∧
      ∀ x : W, r - 4 < 2 * (H.degree x : ℝ) - (Fintype.card W : ℝ) := by
  obtain ⟨W, hW, H, hH, hne, hm, horder, hgap, _⟩ :=
    exists_minor_with_degree_gap_and_clique_extension G a r d hr ha halog hd hsize hdegree
  exact ⟨W, hW, H, hH, hne, hm, horder, hgap⟩

end GraphMinor.Thomason
