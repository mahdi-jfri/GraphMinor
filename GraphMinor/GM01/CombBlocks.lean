module

public import GraphMinor.GM01.CombRegions
public import GraphMinor.GM01.RegionPartition
import Lean.Elab.Tactic.Omega

/-!
# The finite blocks of the subdivided comb

Graph Minors I, page 55, uses `S_j = R_{2j−2} − R_{2j}` except that the
last block is the entire remaining region. We truncate the region
sequence at that last block with an empty endpoint. The proved nesting
of the actual spine regions gives disjointness and coverage by the
successive-difference lemma.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- The sets `S_j` on page 55, indexed here from zero. The last block
retains all of `R_{2n−2}` because the next boundary is empty. -/
def combBlock {α β : Type*} {γ δ : ℕ} (hδ : 0 < δ)
    (H : Graph α β) (c : (pathComb γ δ).verts → α) {n : ℕ} (i : Fin n) : Set α :=
  orderedRegionBlock (fun k ↦ if k < n then combSpineRegion hδ H c (2 * k) else ∅) i

private theorem truncated_even_antitone {α : Type*} {F : ℕ → Set α}
    (hF : Antitone F) (n : ℕ) :
    Antitone (fun k ↦ if k < n then F (2 * k) else ∅) := by
  intro a b hab
  by_cases hb : b < n
  · have ha : a < n := lt_of_le_of_lt hab hb
    simp only [ha, hb, ↓reduceIte]
    exact hF (Nat.mul_le_mul_left 2 hab)
  · simp only [hb, ↓reduceIte]
    exact empty_subset _

/-- The actual finite block family on page 55 is pairwise disjoint and
covers the graph formed by the subdivided comb and the separate root
path. Its nesting is proved from the replacing paths, not assumed. -/
theorem combBlock_partition {α β : Type*} {γ δ n : ℕ} (hδ : 0 < δ) (hn : 0 < n)
    {G N R : Graph α β} (hN : N ≤ G) (hR : R ≤ G)
    {c : (pathComb γ δ).verts → α} (hc : Function.Injective c)
    (hcentres : ∀ v, c v ∈ V(N))
    {P : (pathComb γ δ).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (hmeet : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ δ hδ).root}) :
    Pairwise (fun i j : Fin n ↦ Disjoint
      (combBlock hδ (subgraphUnion G N R) c i)
      (combBlock hδ (subgraphUnion G N R) c j)) ∧
    (⋃ i : Fin n, combBlock hδ (subgraphUnion G N R) c i) =
      V(subgraphUnion G N R) := by
  have hreg := combSpineRegion_antitone hδ hN hR hc hcentres hPN hE hPaths hInter hmeet
  let F := fun k ↦ if k < n then combSpineRegion hδ (subgraphUnion G N R) c (2 * k) else ∅
  have hF : Antitone F := truncated_even_antitone hreg n
  have hEnd : F n = ∅ := by simp only [F, lt_self_iff_false, ↓reduceIte]
  refine ⟨orderedRegionBlock_pairwise_disjoint hF n, ?_⟩
  change (⋃ i : Fin n, orderedRegionBlock F i) = _
  rw [iUnion_orderedRegionBlock hF n hEnd]
  simp only [F, hn, ↓reduceIte, Nat.mul_zero, combSpineRegion_zero]

end GraphMinor.GM01
