module

public import GraphMinor.Compute.GM06Alg34DualGapDivision
public import GraphMinor.Compute.GM06Alg34DualIncidenceLists

/-!
# Natural word lists for computed dual gap classes

A class row selects gap positions. Relabel each selected position by
its supplied incident-region label. The resulting natural word list
is exactly the mapped finite class used by the dual division array.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A guarded natural-word query of one finite dual gap class. -/
def gm06DualGapClassKeep (x : GM06DrawingData) (L : List (Fin x.n))
    (i : Fin L.length) (j : ℕ) : Bool :=
  if hj : j < L.length then x.dualGapRelated L i ⟨j, hj⟩ else false

/-- The supplied region label at a bounded gap position, with zero outside the list. -/
def gm06DualGapLabel {k n : ℕ} (g : Fin k → Fin n) (j : ℕ) : ℕ :=
  if hj : j < k then (g ⟨j, hj⟩).val else 0

/-- The region-number words of one computed dual division block. -/
def gm06DualGapClassWords (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) : List ℕ :=
  (gm06ClassLabels (x.dualGapRelated L) i).map (fun j => (g j).val)

/-- A guarded natural scan with a label map is the mapped finite selected list. -/
theorem gm06SelectedRange_map_eq_filter {n : ℕ} (p : Fin n → Bool) (keep : ℕ → Bool)
    (f : ℕ → ℕ) (h : Fin n → ℕ)
    (hk : ∀ a : Fin n, keep a.val = p a) (hf : ∀ a : Fin n, f a.val = h a) :
    (List.range n).flatMap (fun y => if keep y then [f y] else []) =
      ((List.finRange n).filter p).map h := by
  have hrange : (List.finRange n).map Fin.val = List.range n := by simp
  rw [← hrange, List.flatMap_map]
  have hlist (L : List (Fin n)) :
      L.flatMap (fun a => if keep a.val then [f a.val] else []) = (L.filter p).map h := by
    induction L with
    | nil => rfl
    | cons a L ih =>
      simp only [hk, hf] at ih
      cases hp : p a <;> simp only [List.flatMap_cons, hk, hf, hp, Bool.false_eq_true,
        ↓reduceIte, List.filter_cons, List.map_cons, List.nil_append, List.singleton_append, ih]
  exact hlist _

/-- The RAM's guarded class scan gives precisely the finite mapped gap block. -/
theorem gm06DualGapClassWords_scan (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) :
    (List.range L.length).flatMap (fun j =>
      if gm06DualGapClassKeep x L i j then [gm06DualGapLabel g j] else []) =
        gm06DualGapClassWords x L g i := by
  apply gm06SelectedRange_map_eq_filter (x.dualGapRelated L i) (gm06DualGapClassKeep x L i)
    (gm06DualGapLabel g) (fun j => (g j).val)
  · intro j; simp only [gm06DualGapClassKeep, j.isLt, ↓reduceDIte]
  · intro j; simp only [gm06DualGapLabel, j.isLt, ↓reduceDIte]

/-- A computed dual block has at most one region word per supplied gap. -/
theorem gm06DualGapClassWords_length_le (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length) :
    (gm06DualGapClassWords x L g i).length ≤ L.length := by
  simpa only [gm06DualGapClassWords, gm06ClassLabels, List.length_map, List.length_finRange] using
    List.length_filter_le (x.dualGapRelated L i) (List.finRange L.length)

/-- Every mapped class word is a bounded supplied region label. -/
theorem gm06DualGapClassWords_lt (x : GM06DrawingData) (L : List (Fin x.n))
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length)
    {y : ℕ} (hy : y ∈ gm06DualGapClassWords x L g i) : y < x.regions.length := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  exact (g j).isLt

end GraphMinor.Compute
