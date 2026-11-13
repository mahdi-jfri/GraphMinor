module

public import GraphMinor.Compute.GM06FirstContact
public import Mathlib.Data.List.Iterate
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# The bounded dart-orbit traversal

Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) follows the
face successor until it returns to its initial dart. This file supplies
the pure traversal and proves that, for a permutation of a finite
type, it lists precisely that orbit, without repetition and in
successor order. A bound by the number of darts suffices, including
fixed darts and the empty dart type.
-/

@[expose] public section
namespace GraphMinor.Compute
open Function

/-- Follow successive darts, stopping after the dart whose successor
is the start. The fuel is a bound on the number of darts. -/
def gm06OrbitTrace {D : Type*} [DecidableEq D] (next : D → D) (start : D) (fuel : ℕ) : List D :=
  (gm06FirstContact (fun d => next d == start) (List.iterate next start fuel)).1

private theorem firstContact_append_of_false {D : Type*} (stop : D → Bool)
    (xs ys : List D) (h : (gm06FirstContact stop xs).2 = false) :
    gm06FirstContact stop (xs ++ ys) =
      (xs ++ (gm06FirstContact stop ys).1, (gm06FirstContact stop ys).2) := by
  induction xs with
  | nil => rfl
  | cons d ds ih =>
    have hd : stop d = false := (gm06FirstContact_false_iff stop (d :: ds)).mp h d (by simp)
    have hds : (gm06FirstContact stop ds).2 = false :=
      (gm06FirstContact_false_iff stop ds).mpr (fun x hx =>
        (gm06FirstContact_false_iff stop (d :: ds)).mp h x (by simp [hx]))
    simp only [List.cons_append, gm06FirstContact, hd, Bool.false_eq_true, ↓reduceIte, ih hds]

/-- The bounded traversal has exactly the least positive period as
its length. It contains every earlier iterate and stops on return. -/
theorem gm06OrbitTrace_eq_iterate {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    gm06OrbitTrace next start fuel = List.iterate next start (minimalPeriod next start) := by
  let p := minimalPeriod next start
  have hp : 0 < p := minimalPeriod_pos_of_mem_periodicPts (next.injective.mem_periodicPts start)
  have hpf : p ≤ fuel := (minimalPeriod_le_card (f := next) (x := start)).trans hf
  have hpadd : p - 1 + 1 = p := Nat.sub_add_cancel hp
  have hsplit : fuel = (p - 1) + ((fuel - p) + 1) := by omega
  have hstop : next (next^[p - 1] start) = start := by
    rw [← Function.iterate_succ_apply' (f := (next : D → D)), show (p - 1).succ = p from hpadd]
    exact iterate_minimalPeriod
  have hno : (gm06FirstContact (fun d => next d == start)
      (List.iterate next start (p - 1))).2 = false := by
    apply (gm06FirstContact_false_iff _ _).mpr
    intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iterate.mp hd
    have hne : next (next^[j] start) ≠ start := by
      intro heq
      have heq' : IsPeriodicPt next (j + 1) start := by
        simpa only [Function.IsPeriodicPt, Function.IsFixedPt, Function.iterate_succ_apply'] using heq
      have hle := heq'.minimalPeriod_le (Nat.succ_pos j)
      change p ≤ j + 1 at hle
      omega
    simpa only [beq_eq_false_iff_ne] using hne
  unfold gm06OrbitTrace
  rw [hsplit, List.iterate_add, firstContact_append_of_false _ _ _ hno]
  simp only [List.iterate, gm06FirstContact, hstop, beq_self_eq_true, ↓reduceIte]
  have hone : [((next : D → D)^[p - 1] start)] = List.iterate next ((next : D → D)^[p - 1] start) 1 := rfl
  rw [hone, ← List.iterate_add, hpadd]

/-- Every orbit row is nonempty, including a fixed dart's singleton row. -/
theorem gm06OrbitTrace_ne_nil {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    gm06OrbitTrace next start fuel ≠ [] := by
  rw [gm06OrbitTrace_eq_iterate next start fuel hf]
  intro hz
  have hzero := List.iterate_eq_nil.mp hz
  exact (Nat.ne_of_gt (minimalPeriod_pos_of_mem_periodicPts (next.injective.mem_periodicPts start))) hzero


/-- The rows contain no repeated dart. -/
theorem gm06OrbitTrace_nodup {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    (gm06OrbitTrace next start fuel).Nodup := by
  rw [gm06OrbitTrace_eq_iterate next start fuel hf, ← List.range_map_iterate]
  apply List.nodup_map_iff_inj_on List.nodup_range |>.mpr
  intro i hi j hj hij
  exact iterate_injOn_Iio_minimalPeriod (List.mem_range.mp hi) (List.mem_range.mp hj) hij

/-- A dart occurs in the row exactly when it is an iterate of its start. -/
theorem gm06OrbitTrace_mem_iff {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start d : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    d ∈ gm06OrbitTrace next start fuel ↔ ∃ j : ℕ, next^[j] start = d := by
  rw [gm06OrbitTrace_eq_iterate next start fuel hf, List.mem_iterate]
  constructor
  · rintro ⟨j, _, hj⟩
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    have hp := minimalPeriod_pos_of_mem_periodicPts (next.injective.mem_periodicPts start)
    exact ⟨j % minimalPeriod next start, Nat.mod_lt _ hp, (iterate_mod_minimalPeriod_eq).symm⟩

private theorem iterate_chain {D : Type*} (next : D → D) (d : D) (n : ℕ) :
    List.IsChain (fun a b => next a = b) (List.iterate next d n) := by
  induction n generalizing d with
  | zero => exact .nil
  | succ n ih =>
    cases n with
    | zero => exact .singleton _
    | succ n => exact List.isChain_cons_cons.mpr ⟨rfl, ih (next d)⟩

/-- Each row follows the successor and its final successor is its start. -/
theorem gm06OrbitTrace_follows {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel) :
    List.IsChain (fun a b => next a = b) (gm06OrbitTrace next start fuel ++ [start]) := by
  rw [gm06OrbitTrace_eq_iterate next start fuel hf]
  have heq : List.iterate next start (minimalPeriod next start + 1) =
      List.iterate next start (minimalPeriod next start) ++ [start] := by
    rw [List.iterate_add, iterate_minimalPeriod]
    rfl
  rw [← heq]
  exact iterate_chain next start _

/-- Nat-list input form of the orbit traversal. Missing successor
entries return the queried dart. For valid inputs every lookup is in bounds. -/
def gm06FaceOrbit (successors : List ℕ) (start : ℕ) : List ℕ :=
  gm06OrbitTrace (fun d => successors[d]?.getD d) start successors.length

end GraphMinor.Compute
