module

public import GraphMinor.Compute.Algorithm86

/-!
# Explicit loop ownership in an ordered division

Every vertex belongs to a division member. To assign its loops, use the last
record containing that vertex. The record order and the containing-member
index are finite data. No choice of a division member is needed in the
output reader. Repeated records cause no problem: ownership refers to the
member they describe, rather than to a second copy of that member.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The last record containing a vertex, numbered from one. Zero means that
none of the records contains it. -/
def gm13LastOwner {n : ℕ} (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (v : Fin n) : ℕ :=
  match L with
  | [] => 0
  | A :: rest =>
    if gm13LastOwner rest v = 0 then (if v ∈ A.1 then 1 else 0)
    else gm13LastOwner rest v + 1

/-- An owner index never exceeds the number of supplied member records. -/
theorem gm13LastOwner_le_length {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (v : Fin n) :
    gm13LastOwner L v ≤ L.length := by
  induction L with
  | nil => exact Nat.le_refl 0
  | cons A rest ih =>
    simp only [gm13LastOwner, List.length_cons]
    split
    · split <;> omega
    · omega

/-- Zero is returned exactly when the vertex belongs to none of the records. -/
theorem gm13LastOwner_eq_zero_iff {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (v : Fin n) :
    gm13LastOwner L v = 0 ↔ ∀ A ∈ L, v ∉ A.1 := by
  induction L with
  | nil => simp [gm13LastOwner]
  | cons A rest ih =>
    by_cases hr : gm13LastOwner rest v = 0
    · constructor
      · intro he B hB
        have hv : v ∉ A.1 := by
          intro hv
          simp [gm13LastOwner, hr, hv] at he
        rcases List.mem_cons.mp hB with rfl | hB
        · exact hv
        · exact ih.mp hr B hB
      · intro hall
        have hv := hall A List.mem_cons_self
        simp [gm13LastOwner, hr, hv]
    · constructor
      · intro he
        simp [gm13LastOwner, hr] at he
      · intro hall
        exact (hr (ih.mpr (fun B hB => hall B (List.mem_cons_of_mem A hB)))).elim

/-- Every nonzero index points to a record that contains the vertex. -/
theorem gm13LastOwner_spec {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (v : Fin n)
    (hp : 0 < gm13LastOwner L v) :
    ∃ hi : gm13LastOwner L v - 1 < L.length,
      v ∈ (L[gm13LastOwner L v - 1]'hi).1 := by
  induction L with
  | nil => exact False.elim (Nat.lt_irrefl 0 hp)
  | cons A rest ih =>
    by_cases hr : gm13LastOwner rest v = 0
    · by_cases hv : v ∈ A.1
      · simp [gm13LastOwner, hr, hv]
      · simp [gm13LastOwner, hr, hv] at hp
    · obtain ⟨hi, hmem⟩ := ih (Nat.pos_of_ne_zero hr)
      have he : gm13LastOwner (A :: rest) v - 1 =
          (gm13LastOwner rest v - 1) + 1 := by
        simp only [gm13LastOwner, hr, ↓reduceIte]
        omega
      refine ⟨by rw [he, List.length_cons]; omega, ?_⟩
      simpa only [he, List.getElem_cons_succ] using hmem

/-- Appending a containing record replaces the owner. Appending any other
record leaves the owner unchanged. This is the update performed by the RAM. -/
theorem gm13LastOwner_append {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (A : Finset (Fin n) × List (Fin n × Fin n)) (v : Fin n) :
    gm13LastOwner (L ++ [A]) v = if v ∈ A.1 then L.length + 1 else gm13LastOwner L v := by
  induction L with
  | nil => simp [gm13LastOwner]
  | cons B rest ih =>
    by_cases hv : v ∈ A.1
    · simp [gm13LastOwner, ih, hv]
    · simp only [List.cons_append, gm13LastOwner, ih, hv, ↓reduceIte]

/-- Scan the remaining member records with a current index and current owner.
This is the data update used by the forward RAM scan. -/
def gm13OwnerFrom {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (k owner : ℕ) (v : Fin n) : ℕ :=
  match L with
  | [] => owner
  | A :: rest => gm13OwnerFrom rest (k + 1) (if v ∈ A.1 then k + 1 else owner) v

/-- The forward scan returns the last containing record, or its supplied
initial owner when the remaining records do not contain the vertex. -/
theorem gm13OwnerFrom_eq {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (k owner : ℕ) (v : Fin n) :
    gm13OwnerFrom L k owner v =
      if gm13LastOwner L v = 0 then owner else k + gm13LastOwner L v := by
  induction L generalizing k owner with
  | nil => simp [gm13OwnerFrom, gm13LastOwner]
  | cons A rest ih =>
    by_cases hr : gm13LastOwner rest v = 0 <;> by_cases hv : v ∈ A.1 <;>
      simp [gm13OwnerFrom, gm13LastOwner, ih, hr, hv, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Starting the forward scan with zero yields the one-based owner table. -/
theorem gm13OwnerFrom_zero {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (v : Fin n) :
    gm13OwnerFrom L 0 0 v = gm13LastOwner L v := by
  rw [gm13OwnerFrom_eq]
  split <;> simp_all

end GraphMinor.Compute
