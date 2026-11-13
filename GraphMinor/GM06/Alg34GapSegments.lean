module

public import GraphMinor.GM06.Alg34GapSortedPoints
import GraphMinor.GM06.Section3Basic

/-!
# Enumerating all circle segments by their starting vertices

Each following segment has a unique starting vertex. Thus an injective
list of all vertices also enumerates all segments without repetitions.
This supplies the enumeration conditions in the gap input interpretation.
-/

public section
namespace GraphMinor.GM06

open Set Surface

/-- Distinct supplied circle vertices have distinct following segments. -/
theorem alg34_nextSegments_injective {V : Set Circle} (hV : V.Finite)
    {n : ℕ} (z : Fin n → Circle) (hz : Function.Injective z) (hv : ∀ i, z i ∈ V) :
    Function.Injective (fun i => nextSegment V (z i)) := by
  intro i j he
  change nextSegment V (z i) = nextSegment V (z j) at he
  obtain ⟨p, hp⟩ := nextSegment_nonempty hV (hv i)
  have hpj : p ∈ nextSegment V (z j) := he ▸ hp
  have hu := exists_unique_nextSegment_of_mem_compl hV ⟨z i, hv i⟩ (nextSegment_subset_compl hp)
  exact hz (hu.unique ⟨hv i, hp⟩ ⟨hv j, hpj⟩)

/-- A complete finite vertex list supplies every following circle segment. -/
theorem alg34_nextSegments_cover {V : Set Circle} (hV : V.Finite)
    {n : ℕ} (z : Fin n → Circle) (hv : ∀ v ∈ V, ∃ i, z i = v)
    {seg : Set Circle} (hs : seg ∈ segmentsOf (univ : Set Circle) V) :
    ∃ i, nextSegment V (z i) = seg := by
  have hne := nonempty_of_mem_segmentsOf isOArc_univ_circle hs
  obtain ⟨v, hvV, he⟩ := (mem_segmentsOf_univ_iff hV hne).mp hs
  obtain ⟨i, hi⟩ := hv v hvV
  exact ⟨i, by rw [hi, he]⟩

/-- One point in each supplied following segment gives distinct gap points. -/
theorem alg34_nextSegment_points_injective {V : Set Circle} (hV : V.Finite)
    {n : ℕ} (z p : Fin n → Circle) (hz : Function.Injective z)
    (hv : ∀ i, z i ∈ V) (hp : ∀ i, p i ∈ nextSegment V (z i)) :
    Function.Injective p := by
  intro i j he
  have hpj : p i ∈ nextSegment V (z j) := he.symm ▸ hp j
  have hu := exists_unique_nextSegment_of_mem_compl hV ⟨z i, hv i⟩ (nextSegment_subset_compl (hp i))
  exact hz (hu.unique ⟨hv i, hp i⟩ ⟨hv j, hpj⟩)

end GraphMinor.GM06
