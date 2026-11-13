module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM08.Section6
import GraphMinor.GM07.TameDisc
import GraphMinor.Surface.DiscMerge

/-!
# Shrinking the foundation discs

After the uncrossing step on page 267 of VIII, the foundation discs
have disjoint interiors. Shrink each disc slightly, keeping its
intersection with the drawing. To do this, enlarge the complementary
disc on the sphere by the closed-set push-off construction. Its new
boundary meets the old boundary only in the protected closed set.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

private theorem exists_complementary_disc {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) {B : Set S} (hB : IsClosedDisc B) :
    ∃ E : Set S, IsClosedDisc E ∧ discBd E = discBd B ∧
      E = (discInt B)ᶜ ∧ discInt E = Bᶜ := by
  obtain ⟨E, hE, hbd, hcomp⟩ := exists_compl_eq_discInt_of_sphere hS hB
  refine ⟨E, hE, hbd, ?_, hcomp.symm⟩
  ext x
  have hb := discBd_subset E
  have hb' := discBd_subset B
  have he : x ∈ discInt E ↔ x ∉ B := hcomp.symm ▸ Iff.rfl
  change x ∈ E ↔ ¬ (x ∈ B ∧ x ∉ discBd B)
  constructor
  · intro hx hn
    by_cases hxBd : x ∈ discBd E
    · exact hn.2 (hbd ▸ hxBd)
    · exact (he.mp ⟨hx, hxBd⟩) hn.1
  · intro hx
    by_cases hxB : x ∈ B
    · have hxBd : x ∈ discBd B := by
        by_contra hn
        exact hx ⟨hxB, hn⟩
      exact hb (hbd.symm ▸ hxBd)
    · exact (he.mpr hxB).1

/-- The shrinking step of the foundation construction, VIII, page 267.
The smaller disc still surrounds the protected inner disc. Its boundary
keeps exactly the old boundary points in a closed set `Z`, and every
point of `Z` previously inside remains inside. -/
theorem exists_shrunk_disc {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsSphere S) {B K Z : Set S} (hB : IsClosedDisc B) (hK : IsClosedDisc K)
    (hKB : K ⊆ discInt B) (hZ : IsClosed Z) :
    ∃ B' : Set S, IsClosedDisc B' ∧ K ⊆ discInt B' ∧ B' ⊆ B ∧
      discBd B' ∩ Z = discBd B ∩ Z ∧ discBd B' ⊆ discInt B ∪ Z ∧
      ∀ x ∈ Z, x ∈ discInt B → x ∈ discInt B' := by
  obtain ⟨E, hE, hEb, hEi, hEc⟩ := exists_complementary_disc hS hB
  obtain ⟨F, hF, -, -, hFc⟩ := exists_complementary_disc hS hK
  have hEF : E ⊆ discInt F := by
    rw [hFc, hEi]
    exact fun x hx hxK => hx (hKB hxK)
  obtain ⟨E', hE', hEE', hE'F, hdis, hbdE'E, hbdEZ, hbdE'Z⟩ :=
    GM07.exists_disc_push_off hE hF hEF hZ
  obtain ⟨B', hB', hB'b, hB'i, hB'c⟩ := exists_complementary_disc hS hE'
  have hman : ∀ x : S, IsManifoldPoint x := fun x =>
    ((GM11.IsSphere.isClosedSurface hS).1.2.2 x).isManifoldPoint
  have hsub : B' ⊆ B := by
    rw [hB'i]
    intro x hx
    by_contra hxB
    exact hx ((discInt_mono hman hE hEE') (hEc.symm ▸ hxB))
  refine ⟨B', hB', ?_, hsub, ?_, ?_, ?_⟩
  · rw [hB'c]
    intro x hx hxE'
    have hxF : x ∈ discInt F := hE'F hxE'
    rw [hFc] at hxF
    exact hxF hx
  · rw [hB'b, ← hEb]
    exact Subset.antisymm (fun x hx => ⟨hbdE'Z hx, hx.2⟩)
      (fun x hx => ⟨hbdEZ hx, hx.2⟩)
  · intro x hx
    by_cases hxint : x ∈ discInt B
    · exact .inl hxint
    · apply Or.inr
      exact hbdE'E ⟨hB'b ▸ hx, hEi.symm ▸ hxint⟩
  · intro x hxZ hxint
    rw [hB'c]
    intro hxE'
    exact disjoint_left.mp hdis ⟨hxE', by rw [hEi]; exact fun hn => hn hxint⟩ hxZ

end GraphMinor.GM08
