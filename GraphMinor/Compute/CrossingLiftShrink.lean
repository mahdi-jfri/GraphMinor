module

public import GraphMinor.Compute.CrossingLiftBoundedWalk
public import GraphMinor.Compute.SpecsCrossing

/-!
# Recorded lists below the inferred search bound

The records use ambient finite vertices, but the search allocates only the size inferred
from their labels. Shrinking a list to that finite type preserves every numerical label.
The same holds for the directed edge list, so the program reads the same stored words.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- View a recorded vertex list below a smaller valid label bound. -/
def liftShrinkList {N M : ℕ} (L : List (Fin N)) (h : ∀ x ∈ L, x.val < M) : List (Fin M) :=
  L.attach.map (fun x => ⟨x.val.val, h x.val x.property⟩)

/-- Including the smaller vertices back into the ambient type recovers the list. -/
theorem liftShrinkList_cast {N M : ℕ} (L : List (Fin N)) (h : ∀ x ∈ L, x.val < M)
    (hMN : M ≤ N) : (liftShrinkList L h).map (Fin.castLE hMN) = L := by
  unfold liftShrinkList
  rw [List.map_map]
  have he : (Fin.castLE hMN ∘ fun x : {x // x ∈ L} => (⟨x.val.val, h x.val x.property⟩ : Fin M)) =
      Subtype.val := by funext x; exact Fin.ext rfl
  rw [he, List.attach_map_subtype_val]

/-- Shrinking preserves the words of the stored list. -/
theorem liftShrinkList_values {N M : ℕ} (L : List (Fin N)) (h : ∀ x ∈ L, x.val < M) :
    (liftShrinkList L h).map Fin.val = L.map Fin.val := by
  simp only [liftShrinkList, List.map_map, Function.comp_def]
  exact List.attach_map_val

/-- Shrinking preserves the number of component vertices. -/
theorem liftShrinkList_length {N M : ℕ} (L : List (Fin N)) (h : ∀ x ∈ L, x.val < M) :
    (liftShrinkList L h).length = L.length := by simp [liftShrinkList]

/-- View every recorded endpoint below the smaller search label bound. -/
def liftShrinkEdges {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) : List (Fin M × Fin M) :=
  E.attach.map (fun p => (⟨p.val.1.val, (h p.val p.property).1⟩,
    ⟨p.val.2.val, (h p.val p.property).2⟩))

/-- Including smaller endpoint pairs recovers the recorded edge list. -/
theorem liftShrinkEdges_cast {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) (hMN : M ≤ N) :
    (liftShrinkEdges E h).map (fun p => (Fin.castLE hMN p.1, Fin.castLE hMN p.2)) = E := by
  unfold liftShrinkEdges
  rw [List.map_map]
  have he : ((fun p : Fin M × Fin M => (Fin.castLE hMN p.1, Fin.castLE hMN p.2)) ∘
      fun p : {p // p ∈ E} =>
        ((⟨p.val.1.val, (h p.val p.property).1⟩ : Fin M),
          (⟨p.val.2.val, (h p.val p.property).2⟩ : Fin M))) = Subtype.val := by
    funext p
    exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  rw [he, List.attach_map_subtype_val]

/-- Shrinking edge endpoints preserves the exact flat record words. -/
theorem liftShrinkEdges_values {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) :
    (liftShrinkEdges E h).flatMap encPair = E.flatMap encPair := by
  simp only [liftShrinkEdges, List.flatMap_map]
  have he : (fun p : {p // p ∈ E} =>
      encPair ((⟨p.val.1.val, (h p.val p.property).1⟩ : Fin M),
        (⟨p.val.2.val, (h p.val p.property).2⟩ : Fin M))) =
      (fun p => encPair p.val) := by funext p; rfl
  rw [he]
  simpa only [List.flatMap_map, Function.comp_def] using
    congrArg (List.flatMap encPair) (List.attach_map_subtype_val E)

/-- Shrinking does not change the edge count. -/
theorem liftShrinkEdges_length {N M : ℕ} (E : List (Fin N × Fin N))
    (h : ∀ p ∈ E, p.1.val < M ∧ p.2.val < M) :
    (liftShrinkEdges E h).length = E.length := by simp [liftShrinkEdges]

end GraphMinor.Compute.Crossing
