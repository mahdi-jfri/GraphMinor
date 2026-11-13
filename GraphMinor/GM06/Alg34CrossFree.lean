module

public import GraphMinor.Compute.GM06Alg34CrossFree
public import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# The initial RAM check on represented disc instances

A disc has just its boundary as a cuff. The finite cross-free predicate
therefore agrees with cross-freeness on that boundary. Apply the proved
RAM input check to any supplied representation of a Section 3 instance.
When it rejects, the necessity of cross-freeness rules out feasibility,
as required by the first instruction of (3.4), page 121.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u

private theorem alg34_disc_cuffs_eq {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) : Surface.cuffs S = {Surface.bd S} := by
  have hconn : IsConnected (Surface.bd S) := isConnected_of_isOArc hS.isOArc_bd
  ext C
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hconn.2.connectedComponentIn hp
  · rintro rfl
    obtain ⟨p, hp⟩ := hconn.1
    exact ⟨p, hp, hconn.2.connectedComponentIn hp⟩

/-- A supplied disc representation's finite crossing predicate agrees
with cross-freeness on the boundary of the represented disc. -/
theorem alg34_rep_crossFree_iff {x : GM06DrawingData} {I : DiscDivInstance.{u}}
    (h : GM06DrawingRep x I.G I.Δ) : x.crossFree = true ↔ I.IsCrossFreeInst := by
  rw [h.crossFree_iff, alg34_disc_cuffs_eq I.hDisc]
  simp only [mem_singleton_iff, forall_eq]
  rfl

/-- The first phase of VI (3.4) works for every represented disc instance.
It returns one exactly for cross-free divisions. Returning zero proves
that the division is infeasible. No answer or proof-selected value is read
from the input array. -/
theorem alg34_checkCrossFree_exec {x : GM06DrawingData} {I : DiscDivInstance.{u}}
    (h : GM06DrawingRep x I.G I.Δ) {c : ℕ} (hc : 1 ≤ c) {s : State}
    (harr : s.arrs 0 = x.words) :
    ∃ s' t, Exec (wordSize c x.size) gm06CheckCrossFreeProg s s' t ∧
      t ≤ 452 * (x.size + 1) ^ 4 ∧
      (s'.regs 0 = 1 ↔ I.IsCrossFreeInst) ∧
      (s'.regs 0 = 0 → ¬ I.IsFeasibleInst) ∧ s'.arrs 0 = x.words := by
  obtain ⟨L, hL⟩ := h.exists_cuff_list I.hDisc
  have hnd : L.Nodup := h.cuff_nodup L (by simp [hL])
  obtain ⟨s', t, hex, ht, hans, harr'⟩ := gm06CheckCrossFreeProg_exec x hL hnd
    (h.division_isDivision I.hΔ) hc harr
  have hiff := alg34_rep_crossFree_iff h
  refine ⟨s', t, hex, ht, ?_, ?_, harr'⟩
  · rw [hans]
    cases hf : x.crossFree <;> simp_all
  · intro hz hfeas
    have hcf : I.IsCrossFreeInst := isCrossFree_of_isFeasible I.hDisc hfeas
    have htrue := hiff.mpr hcf
    rw [hans, htrue] at hz
    exact Nat.noConfusion hz

end GraphMinor.GM06
