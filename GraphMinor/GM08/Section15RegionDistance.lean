module

public import GraphMinor.GM07.RegionNest
import GraphMinor.Surface.PlaneSeparation
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Section6

/-!
# Bounding region distance by normal connected sets

If a normal connected set joins two regions and meets the drawing in
`n` vertices, their region distance is at most `n`. Otherwise the region
layers give `n + 1` disjoint separating circuits. Each meets the connected
set in a different drawing vertex, a contradiction. This supplies the
extension of a short tube witness to the cylinder cuffs in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A normal preconnected set joining two regions bounds their region
distance by its vertex count. This supplies the normal arc extension
in the short-tube step of VIII (15.4), page 282. -/
theorem mem_regLayer_of_normal_preconnected {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) {G : Drawing S}
    {A r₀ r₂ : Set S} (hA : IsPreconnected A) (hn : G.IsNormal A)
    (hr₀ : r₀ ∈ G.R) (hr₂ : r₂ ∈ G.R) {p q : S}
    (hpA : p ∈ A) (hqA : q ∈ A) (hp : p ∈ r₀) (hq : q ∈ r₂) :
    r₂ ∈ GM07.regLayer G r₀ (A ∩ G.V).ncard := by
  classical
  have : T2Space S := hS.2.1
  let n := (A ∩ G.V).ncard
  by_contra hnot
  have hfar : ∀ t < n + 1, r₂ ∉ GM07.regLayer G r₀ t := by
    intro t ht hm
    exact hnot (GM07.regLayer_mono (Nat.le_of_lt_succ ht) hm)
  obtain ⟨C, D, hC, hdis⟩ := GM07.exists_region_nest hS hsph hr₀ hr₂ hp hq hfar
  have hmeet : ∀ i : Fin (n + 1), ∃ z, z ∈ A ∩ G.V ∧ z ∈ (C i).V := by
    intro i
    obtain ⟨hcirc, hsub, hdisc, hb, hpD, hqD⟩ := hC i
    obtain ⟨z, hzA, hzfr⟩ := inter_frontier_nonempty_of_isPreconnected hA
      ⟨p, hpA, hpD⟩ ⟨q, hqA, hqD⟩
    have hzC : z ∈ (C i).U := by
      rwa [GM11.IsClosedDisc.frontier_eq_discBd hS hdisc, hb] at hzfr
    have hzV : z ∈ G.V := hn ⟨hzA, hsub.U_subset hzC⟩
    have hzCV : z ∈ (C i).V := by
      by_contra hnCV
      obtain ⟨e, he, hze⟩ := (C i).exists_edge_of_mem hzC hnCV
      exact ((hsub.2 he).2.1 hze).2 hzV
    exact ⟨z, ⟨hzA, hzV⟩, hzCV⟩
  choose z hz hzC using hmeet
  have hinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact disjoint_left.mp (hdis i j hlt).1 (hzC i) (hij ▸ hzC j)
    · exact disjoint_left.mp (hdis j i hlt).1 (hzC j) (hij.symm ▸ hzC i)
  have hcard : n + 1 ≤ n := by
    have h := ncard_le_ncard (show range z ⊆ A ∩ G.V from fun x hx => by
      obtain ⟨i, rfl⟩ := hx
      exact hz i) (G.finite_V.subset inter_subset_right)
    rw [ncard_range_of_injective hinj, Nat.card_fin] at h
    exact h
  exact Nat.not_succ_le_self n hcard

end GraphMinor.GM08
