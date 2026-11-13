module

public import GraphMinor.Surface.SurfaceGraph
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Summing the cut degrees

Every edge of a finite graph has two distinct ends. Counting incidences
first at vertices and then at edges gives twice the edge count. This
sums the local fibre formula in the Euler proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

/-- A subfamily of edges forms a graph on the vertices incident with
those edges. This is the cutting graph inside the source dissection of
VIII (18.2), page 286. -/
theorem isGraph_edge_subfamily {S : Type u} [TopologicalSpace S]
    {V : Set S} {E D : Set (Set S)} (hg : IsGraph V E) (hDE : D ⊆ E) :
    IsGraph (V ∩ ⋃₀ D) D := by
  refine ⟨hg.fin.subset inter_subset_left, hg.fine.subset hDE, ?_, ?_⟩
  · intro e he
    obtain ⟨a, b, hab, hl, hcap⟩ := hg.edge e (hDE he)
    have heD : e ⊆ ⋃₀ D := subset_sUnion_of_mem he
    have hcap' : e ∩ (V ∩ ⋃₀ D) = e ∩ V := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hx.2.1⟩, fun hx => ⟨hx.1, hx.2, heD hx.1⟩⟩
    exact ⟨a, b, hab, hl, hcap'.trans hcap⟩
  · intro e he d hd hne x hx
    exact ⟨hg.disj e (hDE he) d (hDE hd) hne hx, ⟨e, he, hx.1⟩⟩

/-- The sum of the cut degrees equals twice the number of cut edges.
This is the incidence count in the proof of VIII (18.2), page 286. -/
theorem graph_sum_degrees {S : Type u} [TopologicalSpace S] {V : Set S}
    {E : Set (Set S)} (hg : IsGraph V E) :
    ∑ v ∈ hg.fin.toFinset, {e ∈ E | v ∈ e}.ncard = 2 * E.ncard := by
  classical
  have hrow : ∀ v, {e ∈ E | v ∈ e}.ncard =
      ∑ e ∈ hg.fine.toFinset, if v ∈ e then 1 else 0 := by
    intro v
    rw [← Finset.card_filter]
    rw [← ncard_coe_finset]
    congr 1
    ext e
    simp only [Finset.mem_coe, Finset.mem_filter, hg.fine.mem_toFinset, mem_sep_iff]
  have hcol : ∀ e ∈ E, (∑ v ∈ hg.fin.toFinset, if v ∈ e then 1 else 0) = 2 := by
    intro e he
    rw [← Finset.card_filter, ← ncard_coe_finset]
    have hset : (↑(hg.fin.toFinset.filter (fun v => v ∈ e)) : Set S) = e ∩ V := by
      ext v
      simp only [Finset.mem_coe, Finset.mem_filter, hg.fin.mem_toFinset, mem_inter_iff]
      exact and_comm
    rw [hset]
    obtain ⟨a, b, hab, _, hcap⟩ := hg.edge e he
    rw [hcap, ncard_pair hab]
  calc
    (∑ v ∈ hg.fin.toFinset, {e ∈ E | v ∈ e}.ncard) =
        ∑ v ∈ hg.fin.toFinset, ∑ e ∈ hg.fine.toFinset, if v ∈ e then 1 else 0 := by
          exact Finset.sum_congr rfl (fun v _ => hrow v)
    _ = ∑ e ∈ hg.fine.toFinset, ∑ v ∈ hg.fin.toFinset, if v ∈ e then 1 else 0 := Finset.sum_comm
    _ = ∑ _e ∈ hg.fine.toFinset, 2 := by
      exact Finset.sum_congr rfl (fun e he => hcol e (hg.fine.mem_toFinset.mp he))
    _ = 2 * E.ncard := by
      simp only [Finset.sum_const, smul_eq_mul]
      rw [Set.ncard_eq_toFinset_card E hg.fine, Nat.mul_comm]

end GraphMinor.GM08
