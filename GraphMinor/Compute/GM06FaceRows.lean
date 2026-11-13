module

public import GraphMinor.Compute.GM06FaceOrbit
public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Data.List.Nodup

/-!
# Enumerating all face-permutation rows

Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) scans darts
in label order. A dart already present in a completed row is skipped.
Otherwise its whole successor orbit is appended as a new row.
The proof uses the orbit equivalence relation to show that a new row
is disjoint from every completed row. Thus every dart occurs in
exactly one row when the supplied label list covers all darts.
-/

@[expose] public section
namespace GraphMinor.Compute
open Function

/-- Orbit enumeration with its list of completed rows. -/
def gm06FaceRowsAux {D : Type*} [DecidableEq D] (next : D → D) (fuel : ℕ)
    : List D → List (List D) → List (List D)
  | [], rows => rows
  | d :: ds, rows =>
      gm06FaceRowsAux next fuel ds
        (if d ∈ rows.flatten then rows else rows ++ [gm06OrbitTrace next d fuel])

/-- FACE_ROWS as a pure list function on a supplied successor map.
The label order specifies all deterministic orbit-start choices. -/
def gm06FaceRows {D : Type*} [DecidableEq D] (next : D → D)
    (fuel : ℕ) (labels : List D) : List (List D) :=
  gm06FaceRowsAux next fuel labels []

/-- Forward reachability in a finite permutation is the cycle relation. -/
theorem gm06OrbitTrace_mem_sameCycle {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start d : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    d ∈ gm06OrbitTrace next start fuel ↔ next.SameCycle start d := by
  rw [gm06OrbitTrace_mem_iff next start d fuel hf]
  constructor
  · rintro ⟨j, rfl⟩
    simpa only [Equiv.Perm.iterate_eq_pow] using
      (Equiv.Perm.SameCycle.refl next start).pow_right (n := j)
  · intro h
    obtain ⟨j, hj⟩ := h.exists_nat_pow_eq
    exact ⟨j, by simpa only [Equiv.Perm.iterate_eq_pow] using hj⟩

/-- An unseen start has an orbit disjoint from all completed orbit rows. -/
theorem gm06FaceRows_append_orbit_nodup {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel)
    (rows : List (List D)) (hn : rows.flatten.Nodup)
    (hr : ∀ row ∈ rows, ∃ a, row = gm06OrbitTrace next a fuel)
    (d : D) (hd : d ∉ rows.flatten) :
    (rows ++ [gm06OrbitTrace next d fuel]).flatten.Nodup := by
  rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.nodup_append]
  refine ⟨hn, gm06OrbitTrace_nodup next d fuel hf, ?_⟩
  intro x hx y hy hxy
  obtain ⟨row, hrow, hxrow⟩ := List.mem_flatten.mp hx
  obtain ⟨a, rfl⟩ := hr row hrow
  have hax := (gm06OrbitTrace_mem_sameCycle next a x fuel hf).mp hxrow
  have hdx := (gm06OrbitTrace_mem_sameCycle next d x fuel hf).mp (by simpa only [hxy] using hy)
  apply hd
  exact List.mem_flatten.mpr ⟨_, hrow,
    (gm06OrbitTrace_mem_sameCycle next a d fuel hf).mpr (hax.trans hdx.symm)⟩

/-- Complete disjoint orbit rows and coverage are preserved by every scan suffix. -/
theorem gm06FaceRowsAux_invariant {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel)
    (labels : List D) (rows : List (List D)) (hn : rows.flatten.Nodup)
    (hr : ∀ row ∈ rows, ∃ a, row = gm06OrbitTrace next a fuel) :
    (gm06FaceRowsAux next fuel labels rows).flatten.Nodup ∧
    (∀ row ∈ gm06FaceRowsAux next fuel labels rows, ∃ a, row = gm06OrbitTrace next a fuel) ∧
    (∀ d, d ∈ rows.flatten ∨ d ∈ labels →
      d ∈ (gm06FaceRowsAux next fuel labels rows).flatten) := by
  induction labels generalizing rows with
  | nil =>
    refine ⟨hn, hr, ?_⟩
    intro d hd
    exact hd.resolve_right (by simp)
  | cons a labels ih =>
    dsimp only [gm06FaceRowsAux]
    split_ifs with ha
    · obtain ⟨hn', hr', hc'⟩ := ih rows hn hr
      refine ⟨hn', hr', ?_⟩
      intro d hd
      apply hc' d
      rcases hd with hd | hd
      · exact Or.inl hd
      · rcases List.mem_cons.mp hd with rfl | hd
        · exact Or.inl ha
        · exact Or.inr hd
    · have hn' := gm06FaceRows_append_orbit_nodup next fuel hf rows hn hr a ha
      have hr' : ∀ row ∈ rows ++ [gm06OrbitTrace next a fuel],
          ∃ b, row = gm06OrbitTrace next b fuel := by
        intro row hrow
        rcases List.mem_append.mp hrow with hrow | hrow
        · exact hr row hrow
        · exact ⟨a, List.mem_singleton.mp hrow⟩
      obtain ⟨hn'', hr'', hc''⟩ := ih _ hn' hr'
      refine ⟨hn'', hr'', ?_⟩
      intro d hd
      apply hc'' d
      rcases hd with hd | hd
      · exact Or.inl (by simp [hd])
      · rcases List.mem_cons.mp hd with rfl | hd
        · apply Or.inl
          have hm : d ∈ gm06OrbitTrace next d fuel :=
            (gm06OrbitTrace_mem_sameCycle next d d fuel hf).mpr (.refl _ _)
          simp [hm]
        · exact Or.inr hd

/-- Every output row is a complete orbit, every dart is covered,
and the flattened rows have no repetitions. -/
theorem gm06FaceRows_spec {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel)
    (labels : List D) (hlabels : ∀ d, d ∈ labels) :
    (gm06FaceRows next fuel labels).flatten.Nodup ∧
    (∀ row ∈ gm06FaceRows next fuel labels, ∃ a, row = gm06OrbitTrace next a fuel) ∧
    (∀ d, d ∈ (gm06FaceRows next fuel labels).flatten) := by
  obtain ⟨hn, hr, hc⟩ := gm06FaceRowsAux_invariant next fuel hf labels [] (by simp) (by simp)
  exact ⟨hn, hr, fun d => hc d (Or.inr (hlabels d))⟩

/-- Each dart belongs to exactly one face row. -/
theorem gm06FaceRows_unique_row {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel)
    (labels : List D) (hlabels : ∀ d, d ∈ labels) (d : D) :
    ∃! row, row ∈ gm06FaceRows next fuel labels ∧ d ∈ row := by
  obtain ⟨hn, _, hc⟩ := gm06FaceRows_spec next fuel hf labels hlabels
  obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp (hc d)
  refine ⟨row, ⟨hr, hd⟩, ?_⟩
  intro other ho
  have hp := (List.nodup_flatten.mp hn).2
  by_contra hne
  exact (hp.forall ho.1 hr hne) ho.2 hd

/-- Nat-list input form of FACE_ROWS, scanning active labels in their
supplied order. The successor list includes inactive slots if labels
are permanent. -/
def gm06FaceRowsList (successors active : List ℕ) : List (List ℕ) :=
  gm06FaceRows (fun d => successors[d]?.getD d) successors.length active

end GraphMinor.Compute
