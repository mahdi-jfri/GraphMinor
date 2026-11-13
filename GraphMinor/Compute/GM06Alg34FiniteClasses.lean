module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# Canonical finite equivalence classes

For a Boolean relation on finite labels, retain the least label of each
class and list the labels related to it. When the relation is an
equivalence, these lists form a division covering all labels. This
finite construction supplies the equivalence classes of the dual gap
relation without choosing representatives from geometric objects.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set GM06

/-- The labels related to a given finite source. -/
def gm06ClassLabels {n : ℕ} (r : Fin n → Fin n → Bool) (a : Fin n) : List (Fin n) :=
  (List.finRange n).filter (r a)

/-- The least finite label of each class, tested by an exhaustive smaller-label scan. -/
def gm06ClassRoots {n : ℕ} (r : Fin n → Fin n → Bool) : List (Fin n) :=
  (List.finRange n).filter (fun a => decide (∀ b : Fin n, b < a → r a b = false))

/-- The finite classes in increasing representative order. -/
def gm06ClassBlocks {n : ℕ} (r : Fin n → Fin n → Bool) : List (List (Fin n)) :=
  (gm06ClassRoots r).map (gm06ClassLabels r)

/-- The corresponding set of class blocks. -/
def gm06ClassDivision {n : ℕ} (r : Fin n → Fin n → Bool) : Set (Set (Fin n)) :=
  GM06DrawingData.block '' {B | B ∈ gm06ClassBlocks r}

/-- Membership of a listed class is exactly the supplied relation bit. -/
theorem gm06MemClassLabels_iff {n : ℕ} (r : Fin n → Fin n → Bool) (a b : Fin n) :
    b ∈ gm06ClassLabels r a ↔ r a b = true := by
  simp only [gm06ClassLabels, List.mem_filter, List.mem_finRange, true_and]

/-- Root membership says that every smaller source has a false relation bit. -/
theorem gm06MemClassRoots_iff {n : ℕ} (r : Fin n → Fin n → Bool) (a : Fin n) :
    a ∈ gm06ClassRoots r ↔ ∀ b : Fin n, b < a → r a b = false := by
  simp only [gm06ClassRoots, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

/-- Related canonical representatives are equal. -/
theorem gm06ClassRoots_eq {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) {a b : Fin n}
    (ha : a ∈ gm06ClassRoots r) (hb : b ∈ gm06ClassRoots r) (hab : r a b = true) : a = b := by
  have hamin := (gm06MemClassRoots_iff r a).mp ha
  have hbmin := (gm06MemClassRoots_iff r b).mp hb
  rcases lt_trichotomy a b with hlt | heq | hgt
  · have hnot := hbmin a hlt
    rw [hE.symm hab] at hnot
    cases hnot
  · exact heq
  · have hnot := hamin b hgt
    rw [hab] at hnot
    cases hnot

/-- Every label belongs to a class with a canonical finite root. -/
theorem gm06ExistsClassRoot {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) (a : Fin n) :
    ∃ b ∈ gm06ClassRoots r, r b a = true := by
  let C := Finset.univ.filter (fun b => r a b = true)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE.refl a⟩
  have hC : C.Nonempty := ⟨a, haC⟩
  let b := C.min' hC
  have hab := (Finset.mem_filter.mp (Finset.min'_mem C hC)).2
  refine ⟨b, (gm06MemClassRoots_iff r b).mpr ?_, hE.symm hab⟩
  intro c hcb
  cases hh : r b c with
  | false => rfl
  | true =>
    have hcC : c ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE.trans hab hh⟩
    exact False.elim ((not_lt_of_ge (Finset.min'_le C c hcC)) hcb)

/-- Every canonical class is nonempty because it contains its root. -/
theorem gm06ClassLabels_nonempty {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) (a : Fin n) :
    (GM06DrawingData.block (gm06ClassLabels r a)).Nonempty :=
  ⟨a, (gm06MemClassLabels_iff r a a).mpr (hE.refl a)⟩

/-- Distinct canonical class blocks have no common label. -/
theorem gm06ClassLabels_disjoint {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) {a b : Fin n}
    (ha : a ∈ gm06ClassRoots r) (hb : b ∈ gm06ClassRoots r) (hne : a ≠ b) :
    Disjoint (GM06DrawingData.block (gm06ClassLabels r a))
      (GM06DrawingData.block (gm06ClassLabels r b)) := by
  apply Set.disjoint_left.mpr
  intro c hac hbc
  have hac' := (gm06MemClassLabels_iff r a c).mp hac
  have hbc' := (gm06MemClassLabels_iff r b c).mp hbc
  exact hne (gm06ClassRoots_eq r hE ha hb (hE.trans hac' (hE.symm hbc')))

/-- A finite equivalence produces a division with no empty or overlapping blocks. -/
theorem gm06ClassDivision_isDivision {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) : IsDivision (gm06ClassDivision r) := by
  have hfinite : (gm06ClassDivision r).Finite :=
    (List.finite_toSet (gm06ClassBlocks r)).image GM06DrawingData.block
  refine ⟨hfinite, ?_, ?_⟩
  · rintro B ⟨L, hL, rfl⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hL
    exact gm06ClassLabels_nonempty r hE a
  · rintro B ⟨L, hL, rfl⟩ C ⟨K, hK, rfl⟩ hne
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hL
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hK
    exact gm06ClassLabels_disjoint r hE ha hb (fun heq => hne (heq ▸ rfl))

/-- The class division covers every finite label. -/
theorem gm06ClassDivision_union {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) :
    divisionUnion (gm06ClassDivision r) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro a
  obtain ⟨b, hb, hba⟩ := gm06ExistsClassRoot r hE a
  exact ⟨_, ⟨_, List.mem_map.mpr ⟨b, hb, rfl⟩, rfl⟩,
    (gm06MemClassLabels_iff r b a).mpr hba⟩

/-- The computed root lists represent exactly all equivalence classes. -/
theorem gm06ClassDivision_eq_classes {n : ℕ} (r : Fin n → Fin n → Bool)
    (hE : Equivalence (fun a b => r a b = true)) :
    gm06ClassDivision r = (fun a : Fin n => {b | r a b = true}) '' Set.univ := by
  apply Set.Subset.antisymm
  · rintro B ⟨L, hL, rfl⟩
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hL
    refine ⟨a, trivial, ?_⟩
    ext b
    exact (gm06MemClassLabels_iff r a b).symm
  · rintro B ⟨a, _, rfl⟩
    obtain ⟨b, hb, hba⟩ := gm06ExistsClassRoot r hE a
    refine ⟨gm06ClassLabels r b, List.mem_map.mpr ⟨b, hb, rfl⟩, ?_⟩
    ext c
    change c ∈ gm06ClassLabels r b ↔ r a c = true
    rw [gm06MemClassLabels_iff]
    exact ⟨fun hbc => hE.trans (hE.symm hba) hbc, fun hac => hE.trans hba hac⟩

end GraphMinor.Compute
