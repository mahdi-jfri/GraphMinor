module

public import GraphMinor.GM19.Defs2
public import Mathlib.Topology.Constructions.SumProd
import GraphMinor.GM19.FragmentExtend
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM19.Section5o

/-!
# Orientations on disjoint unions

For the separating case of Graph Minors V, (8.10), orient each capped
component and take their topological sum. A closed disc lies in one
summand, because it is connected. Read its direction from that summand.
Nested discs lie in the same summand, so their directions agree.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

private theorem orientable_of_open_partition {S : Type} [TopologicalSpace S] [T2Space S]
    {A B : Set S} (hA : IsOpen A) (hB : IsOpen B) (hd : Disjoint A B)
    (hu : A ∪ B=univ) {p q : Set S → S → S → S → Prop}
    (hp : IsPartialOrientation {D | D ⊆ A} p) (hq : IsPartialOrientation {D | D ⊆ B} q) :
    IsOrientableSurface S := by
  classical
  have hpart {D : Set S} (hD : IsClosedDisc D) : D ⊆ A ∨ D ⊆ B :=
    (isPreconnected_of_isClosedDisc hD).subset_or_subset hA hB hd (by rw [hu]; exact subset_univ D)
  let pos : Set S → S → S → S → Prop := fun D a b c ↦ if D ⊆ A then p D a b c else q D a b c
  refine ⟨⟨pos,?_,?_⟩⟩
  · intro D hD
    by_cases hDA : D ⊆ A
    · simpa only [IsDirectionOf,pos,hDA,↓reduceIte] using hp.dir D hDA hD
    · have hDB : D ⊆ B := (hpart hD).resolve_left hDA
      simpa only [IsDirectionOf,pos,hDA,↓reduceIte] using hq.dir D hDB hD
  · intro D₁ D₂ h₁ h₂ hs a b c ha hb hc hab hbc hac
    by_cases hDA₂ : D₂ ⊆ A
    · have hDA₁ : D₁ ⊆ A := hs.trans hDA₂
      simpa only [pos,hDA₁,hDA₂,↓reduceIte] using
        hp.agree D₁ hDA₁ D₂ hDA₂ h₁ h₂ hs a b c ha hb hc hab hbc hac
    · have hDB₂ : D₂ ⊆ B := (hpart h₂).resolve_left hDA₂
      have hDB₁ : D₁ ⊆ B := hs.trans hDB₂
      have hDA₁ : ¬D₁ ⊆ A := by
        intro h
        obtain ⟨x,hx⟩ := h₁.nonempty_discInt
        exact Set.disjoint_left.mp hd (h hx.1) (hDB₁ hx.1)
      simpa only [pos,hDA₁,hDA₂,↓reduceIte] using
        hq.agree D₁ hDB₁ D₂ hDB₂ h₁ h₂ hs a b c ha hb hc hab hbc hac

/-- The topological sum of two nonempty orientable Hausdorff spaces is
orientable. Apply the orientation of the summand that contains the disc. -/
theorem orientable_sum {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space S] [T2Space T] [Nonempty S] [Nonempty T]
    (hS : IsOrientableSurface S) (hT : IsOrientableSurface T) : IsOrientableSurface (S ⊕ T) := by
  classical
  obtain ⟨ωS⟩ := hS
  obtain ⟨ωT⟩ := hT
  let s₀ : S := Classical.choice inferInstance
  let t₀ : T := Classical.choice inferInstance
  let rS : S ⊕ T → S := Sum.elim id (fun _ ↦ s₀)
  let rT : S ⊕ T → T := Sum.elim (fun _ ↦ t₀) id
  have hrS : Continuous rS := continuous_sum_dom.mpr ⟨continuous_id,continuous_const⟩
  have hrT : Continuous rT := continuous_sum_dom.mpr ⟨continuous_const,continuous_id⟩
  have hp : IsPartialOrientation {D : Set (S ⊕ T) | D ⊆ range Sum.inl} (pullPos rS ωS.pos) :=
    (ωS.isPartial univ).pull fun D hD ↦ ⟨hrS.continuousOn,?_,mem_univ _⟩
  · have hq : IsPartialOrientation {D : Set (S ⊕ T) | D ⊆ range Sum.inr} (pullPos rT ωT.pos) :=
      (ωT.isPartial univ).pull fun D hD ↦ ⟨hrT.continuousOn,?_,mem_univ _⟩
    · apply orientable_of_open_partition isOpen_range_inl isOpen_range_inr _ _ hp hq
      · exact Set.disjoint_left.mpr (by rintro _ ⟨x,rfl⟩ ⟨y,hy⟩; cases hy)
      · ext x
        cases x <;> simp
    · intro x hx y hy he
      obtain ⟨x,rfl⟩ := hD hx
      obtain ⟨y,rfl⟩ := hD hy
      exact congrArg Sum.inr he
  · intro x hx y hy he
    obtain ⟨x,rfl⟩ := hD hx
    obtain ⟨y,rfl⟩ := hD hy
    exact congrArg Sum.inl he

/-- Orientability of a topological sum also permits empty summands. -/
theorem orientable_sum_all {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    [T2Space S] [T2Space T] (hS : IsOrientableSurface S) (hT : IsOrientableSurface T) :
    IsOrientableSurface (S ⊕ T) := by
  cases isEmpty_or_nonempty S
  · exact isOrientable_of_homeo (Homeomorph.emptySum T S) hT
  · cases isEmpty_or_nonempty T
    · exact isOrientable_of_homeo (Homeomorph.sumEmpty S T) hS
    · exact orientable_sum hS hT

end GraphMinor.GM05
