module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12LoopRoom
import GraphMinor.GM08.Section12Petals
import GraphMinor.GM08.Section9DiscContext
import Mathlib.Topology.Separation.Hausdorff

/-!
# Placing all cellular loop petals at once

Separate the finitely many loop ends by open neighborhoods. At each
end, take an empty tangent disc and place disjoint petals inside it.
Use a different petal for each loop. Petals at different ends lie in
disjoint neighborhoods. Thus every new loop bounds an empty disc after
the old loops are removed, as needed for VIII, Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v

/-- Place one empty petal disc for each loop, with distinct petals
meeting only at their common ends. This is the simultaneous local
construction of the cellular loops used in VIII, Section 12, page 274. -/
theorem exists_loop_petal_family {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    {ι : Type v} [Finite ι] (e : ι → Set S) (v : ι → S)
    (he : ∀ i, e i ∈ D.E) (hcap : ∀ i, closure (e i) ∩ D.V = {v i}) :
    ∃ E : ι → Set S,
      (∀ i, IsClosedDisc (E i) ∧ v i ∈ discBd (E i) ∧ E i ∩ D.U = {v i} ∧ E i ∩ bd S ⊆ {v i}) ∧
      ∀ i j, i ≠ j → E i ∩ E j ⊆ {v i} ∩ {v j} := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨U, hU, hUU⟩ := (finite_range v).t2_separation
  have hex : ∀ z : range v, ∃ G : Fin (Fintype.card ι) → Set S,
      (∀ a, IsClosedDisc (G a) ∧ G a ⊆ U z ∧ z.1 ∈ discBd (G a) ∧ G a ∩ D.U = {z.1} ∧ G a ∩ bd S ⊆ {z.1}) ∧
      Pairwise (fun a b => G a ∩ G b = {z.1}) := by
    intro z
    obtain ⟨i, hi⟩ := z.2
    obtain ⟨B, hB, hBU, hzB, hBD, hBbd⟩ := exists_empty_disc_at_loop_in_disc hS D (he i) (hcap i)
      (hU z).2 (by rw [hi]; exact (hU z).1)
    obtain ⟨G, hG, hGG⟩ := exists_petal_discs (Fintype.card ι) hB hzB
    refine ⟨G, fun a => ⟨(hG a).1, (hG a).2.1.trans hBU, ?_, ?_, ?_⟩, ?_⟩
    · simpa only [hi] using (hG a).2.2
    · apply Subset.antisymm
      · intro x hx
        have hxv : x ∈ ({v i} : Set S) := hBD ▸ And.intro ((hG a).2.1 hx.1) hx.2
        simpa only [hi] using hxv
      · intro x hx
        have hxv : x = v i := by simpa only [hi] using mem_singleton_iff.mp hx
        have hvpair : v i ∈ closure (e i) ∩ D.V := (hcap i).symm ▸ mem_singleton (v i)
        rw [hxv]
        exact ⟨discBd_subset _ (hG a).2.2, D.V_subset_U hvpair.2⟩
    · intro x hx
      have hxv := hBbd ⟨(hG a).2.1 hx.1, hx.2⟩
      simpa only [hi] using hxv
    · intro a b hab
      simpa only [hi] using hGG hab
  choose G hG hGG using hex
  let f : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E : ι → Set S := fun i => G ⟨v i, mem_range_self i⟩ (f i)
  refine ⟨E, fun i => ⟨(hG _ _).1, (hG _ _).2.2.1, (hG _ _).2.2.2⟩, ?_⟩
  intro i j hij
  by_cases hv : v i = v j
  · have hz : (⟨v j, mem_range_self j⟩ : range v) = ⟨v i, mem_range_self i⟩ := Subtype.ext hv.symm
    change G ⟨v i, mem_range_self i⟩ (f i) ∩ G ⟨v j, mem_range_self j⟩ (f j) ⊆ _
    rw [hz, hGG _ (fun h => hij (f.injective h))]
    intro x hx
    exact ⟨hx, hv ▸ hx⟩
  · have hiU : E i ⊆ U (v i) := (hG ⟨v i, mem_range_self i⟩ (f i)).2.1
    have hjU : E j ⊆ U (v j) := (hG ⟨v j, mem_range_self j⟩ (f j)).2.1
    intro x hx
    exact False.elim (disjoint_left.mp (hUU (mem_range_self i) (mem_range_self j) hv)
      (hiU hx.1) (hjU hx.2))

end GraphMinor.GM08
