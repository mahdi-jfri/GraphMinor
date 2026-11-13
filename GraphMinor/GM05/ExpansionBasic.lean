module

public import GraphMinor.GM05.ExpansionDefs
public import GraphMinor.GM09.Defs
import GraphMinor.GM09.Basic

/-!
# Expansions as witnesses for minors

A minor witness is exactly an expansion subgraph together with its
contracted edges. A vertex set meets every expansion precisely when its
deletion removes all minors of the specified graph. These facts relate the
definitions in Graph Minors V, Section 8, page 109.
-/

public section

namespace GraphMinor.GM05

open Graph Set GM09

variable {α β α' β' : Type*} {H : Graph α' β'} {G A : Graph α β} {X : Set α}

/-- An expansion supplies a minor witness. -/
theorem IsHExpansion.isIsoMinor (h : IsHExpansion H G A) : IsIsoMinor H G :=
  ⟨A,h.1,h.2⟩

/-- A minor exists exactly when an expansion subgraph exists. -/
theorem isIsoMinor_iff_exists_expansion : IsIsoMinor H G ↔ ∃ A, IsHExpansion H G A := by
  constructor
  · rintro ⟨A,hA,F,hF,hIso⟩
    exact ⟨A,hA,F,hF,hIso⟩
  · rintro ⟨A,hA⟩
    exact hA.isIsoMinor

/-- Expansion subgraphs are preserved when the host is enlarged. -/
theorem IsHExpansion.mono {G' : Graph α β} (h : IsHExpansion H G A) (hle : G ≤ G') :
    IsHExpansion H G' A := ⟨h.1.trans hle,h.2⟩

/-- Hitting every expansion is equivalent to excluding the minor after
vertex deletion. This includes expansions with no vertices. -/
theorem hitsExpansions_iff_no_minor_delete :
    HitsExpansions H G X ↔ ¬ IsIsoMinor H (deleteVertices G X) := by
  constructor
  · intro hhit hm
    obtain ⟨A,hA⟩ := isIsoMinor_iff_exists_expansion.mp hm
    obtain ⟨x,hxX,hxA⟩ := hhit A (hA.mono (deleteVertices_le G X))
    exact (hA.1.vertexSet_mono hxA).2 hxX
  · intro hno A hA
    by_contra hn
    have hd : Disjoint V(A) X := by
      rw [Set.disjoint_left]
      intro x hxA hxX
      exact hn ⟨x,hxX,hxA⟩
    exact hno (IsHExpansion.isIsoMinor ⟨le_deleteVertices hA.1 hd,hA.2⟩)

/-- A packing of no expansions is always available. -/
theorem hasDisjointExpansions_zero (H : Graph α' β') (G : Graph α β) :
    HasDisjointExpansions H G 0 :=
  ⟨Fin.elim0, fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩

end GraphMinor.GM05
