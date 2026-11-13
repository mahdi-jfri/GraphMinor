module

public import GraphMinor.Compute.Case3StepsComponentAccess

/-!
# Attachment rows of outside components

For each outside component, its attachments are the core vertices adjacent
to some vertex of that component (XIII, Section 8, page 96). Counting neighbors
in a component therefore gives a direct way to compute its attachment row.
Core seeds have an empty component row and an empty attachment row.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The vertex set encoded by a component row. -/
noncomputable def case3ComponentRowSet (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : Finset (Fin x.n) :=
  if u ∈ Z then ∅ else compOutside x Z u

/-- Attachment vertices read by testing positive degree into the component. -/
noncomputable def case3AttachmentRowSet (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) : Finset (Fin x.n) :=
  Z.filter (fun v => 0 < degInto x.G (case3ComponentRowSet x Z u) v)

/-- The component row is exactly the bitset of its vertex set. -/
theorem case3ComponentRow_eq_bitSetList (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) :
    case3ComponentRow x Z u = bitSetList (case3ComponentRowSet x Z u) := by
  unfold case3ComponentRow case3ComponentRowSet
  split_ifs
  · apply List.ext_getElem (by simp only [List.length_replicate, length_bitSetList])
    intro j hj hj'
    simp only [List.getElem_replicate]
    rw [getElem_bitSetList _ j (by simpa only [List.length_replicate] using hj)]
    simp
  · rfl

/-- Positive degree into a set is equivalent to having a neighbor in it. -/
private theorem positive_degInto_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) :
    0 < degInto G S v ↔ ∃ u ∈ S, G.Adj u v := by
  unfold degInto
  rw [Finset.card_pos]
  constructor
  · rintro ⟨u, hu⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
    exact ⟨u, hu.1, hu.2.symm⟩
  · rintro ⟨u, hu, hadj⟩
    exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu, hadj.symm⟩⟩

/-- For an outside seed, degree tests recover precisely its attachment set. -/
theorem case3AttachmentRowSet_eq_attachOf (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∉ Z) :
    case3AttachmentRowSet x Z u = attachOf x Z u := by
  ext v
  simp only [case3AttachmentRowSet, case3ComponentRowSet, hu, ↓reduceIte,
    Finset.mem_filter, attachOf, positive_degInto_iff]

/-- A core seed contributes no attachment vertices. -/
theorem case3AttachmentRowSet_eq_empty (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (hu : u ∈ Z) :
    case3AttachmentRowSet x Z u = ∅ := by
  ext v
  simp [case3AttachmentRowSet, case3ComponentRowSet, hu, positive_degInto_iff]

end GraphMinor.Compute
