module

public import GraphMinor.GM02.SidePieceTerminalAvoidance

/-!
# Reserved separator vertices for the extracted scheme

Among separator vertices absent from all three terminations, reserve for
the first deletion those unused by first-side pieces. Reserve the rest
for the second deletion. Opposite pieces intersect only at new endpoints,
so second-side pieces avoid the latter set. These sets give condition
(iii) of the crossing scheme in II (2.9).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H H' : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- Vertices used by pieces of the indicated side. -/
def sideUsedVertices (side : Bool) : Set α :=
  {a | ∃ i : RunPieceIndex A G H P, i.color A G H P = side ∧ a ∈ (i.path A G H P).vertices}

/-- Separator vertices absent from every termination. -/
def unusedSeparator : Set α := (V(H) ∩ V(H')) \
  (A.support ∪ (sideTermination A G H P hP true).support ∪
    (sideTermination A G H P hP false).support)

/-- Reserve for the first deletion vertices unused by first-side pieces. -/
def sideReservedLeft : Set α := unusedSeparator A G H H' P hP \ sideUsedVertices A G H P true

/-- Reserve for the second deletion the remaining unused separator vertices. -/
def sideReservedRight : Set α := unusedSeparator A G H H' P hP ∩ sideUsedVertices A G H P true

/-- The two reservations partition precisely the unused separator. -/
theorem sideReservations_union : sideReservedLeft A G H H' P hP ∪
    sideReservedRight A G H H' P hP = unusedSeparator A G H H' P hP := by
  ext a
  simp only [sideReservedLeft, sideReservedRight, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
  tauto

/-- The reservation sets are disjoint. -/
theorem sideReservations_disjoint : Disjoint (sideReservedLeft A G H H' P hP)
    (sideReservedRight A G H H' P hP) := by
  exact Set.disjoint_left.2 (fun _ hL hR => hL.2 hR.2)

/-- First-side pieces avoid the first reservation. -/
theorem RunPieceIndex.avoids_reservedLeft (i : RunPieceIndex A G H P)
    (hc : i.color A G H P = true) :
    Disjoint (i.path A G H P).vertices (sideReservedLeft A G H H' P hP) := by
  exact Set.disjoint_left.2 (fun _ hai hz => hz.2 ⟨i, hc, hai⟩)

/-- Second-side pieces avoid the second reservation. -/
theorem RunPieceIndex.avoids_reservedRight (i : RunPieceIndex A G H P)
    (hc : i.color A G H P = false) :
    Disjoint (i.path A G H P).vertices (sideReservedRight A G H H' P hP) := by
  apply Set.disjoint_left.2
  intro a hai hz
  obtain ⟨j, hjc, haj⟩ := hz.2
  have hne : i.color A G H P ≠ j.color A G H P := by rw [hc, hjc]; decide
  have he := i.opposite_inter_mem_support A G H P hP j hne hai haj
  have haR : a ∈ (sideTermination A G H P hP false).support := by
    simpa only [hc] using he.1
  exact hz.1.2 (Or.inr haR)

end GraphMinor.GM02
