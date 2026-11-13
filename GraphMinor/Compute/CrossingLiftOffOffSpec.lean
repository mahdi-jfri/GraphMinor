module

public import GraphMinor.Compute.CrossingLiftOffOff
public import GraphMinor.Crossing.DefsContract
import GraphMinor.Compute.CrossingLoopCand
import Mathlib.Data.List.GetD

/-!
# The graph specification of the both-off-cycle RAM lift

The numerical neighbour tests agree with the old graph's adjacency tests at the retained
vertex. Mapping Section 11's list computation to vertex numbers therefore gives exactly the
RAM result. A cycle path can use an off-cycle vertex only internally, which supplies the
index bounds needed by the used-vertex branch.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- Numerical vertex membership agrees with membership before the injective numbering. -/
private theorem mem_map_val_iff {N : ℕ} (x : Fin N) (L : List (Fin N)) :
    x.val ∈ L.map Fin.val ↔ x ∈ L := by
  simp only [List.mem_map, Fin.val_injective.eq_iff, exists_eq_right]

/-- The numerical Section 11 computation agrees with the old graph lift after vertex numbering.
The only graph hypothesis identifies the recorded neighbour list. -/
theorem liftOffOffWords_map {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (u v : Fin N) (Nv L : List (Fin N))
    (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) :
    liftOffOffWords u.val v.val (Nv.map Fin.val) (L.map Fin.val) =
      (liftOffOff G u v L).map Fin.val := by
  unfold liftOffOffWords liftOffOff
  simp only [mem_map_val_iff, idxOf_map_val, List.getD_map, hNv]
  by_cases hvL : v ∈ L
  · simp only [hvL, ↓reduceIte]
    by_cases ha : G.Adj v (L.getD (L.idxOf v - 1) v) <;>
      by_cases hb : G.Adj v (L.getD (L.idxOf v + 1) v) <;>
      simp only [ha, hb, ↓reduceIte, List.map_append, List.map_take, List.map_drop,
        List.map_cons, List.map_nil, Fin.val_injective.eq_iff] <;>
      split_ifs <;> rfl
  · simp only [hvL, ↓reduceIte]

/-- A cycle path uses an off-cycle vertex only at an internal index. -/
theorem internal_index_of_isDPathList {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {D L : List V} {v : V}
    (hp : IsDPathList G D L) (hvD : v ∉ D) (hvL : v ∈ L) :
    0 < L.idxOf v ∧ L.idxOf v + 1 < L.length := by
  have hi : L.idxOf v < L.length := List.idxOf_lt_length_iff.mpr hvL
  have helem : L[L.idxOf v]? = some v := List.getElem?_idxOf hvL
  have hzero : L.idxOf v ≠ 0 := by
    intro h
    have hhead : L.head? = some v := by rw [List.head?_eq_getElem?, ← h]; exact helem
    exact hvD (hp.2.2.1 v hhead)
  have hlast : L.idxOf v ≠ L.length - 1 := by
    intro h
    have hend : L.getLast? = some v := by rw [List.getLast?_eq_getElem?, ← h]; exact helem
    exact hvD (hp.2.2.2.1 v hend)
  constructor <;> omega

/-- The RAM both-off-cycle routine computes the exact Section 11 lift on a cycle path.
Its hypotheses contain the stored path and neighbour list, endpoint register values, scratch
separation, an off-cycle retained vertex and the RAM word bound. -/
theorem liftOffOffProg_exec_fin {w N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (D L Nv : List (Fin N)) (u v : Fin N) (src neighbours patch tmp r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (hp : IsDPathList (contractGraph G u v) D L) (hvD : v ∉ D) (hnd : Nv.Nodup)
    (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hnb : s.arrs neighbours = Nv.map Fin.val)
    (hu : s.regs r_u = u.val) (hv : s.regs r_v = v.val)
    (hw : 8 * (N + L.length + Nv.length + 2) < 2 ^ w) :
    ∃ s' t, Exec w (liftOffOffProg src neighbours patch tmp r_u r_v R) s s' t ∧
      t ≤ 70 * (L.length + Nv.length + 1) + 160 ∧
      s'.arrs src = (liftOffOff G u v L).map Fin.val ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hword : ∀ x : Fin N, x.val < 2 ^ w := fun x => x.isLt.trans (by omega)
  have hmapword : ∀ xs : List (Fin N), ∀ x ∈ xs.map Fin.val, x < 2 ^ w := by
    intro xs x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hword y
  have hin : v.val ∈ L.map Fin.val →
      0 < (L.map Fin.val).idxOf v.val ∧ (L.map Fin.val).idxOf v.val + 1 < (L.map Fin.val).length := by
    intro hvL
    have h := internal_index_of_isDPathList hp hvD ((mem_map_val_iff v L).mp hvL)
    simpa only [idxOf_map_val, List.length_map] using h
  obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftOffOffProg_exec
    src neighbours patch tmp r_u r_v R harr huR hvR (L.map Fin.val) (Nv.map Fin.val)
    u.val v.val s hsrc hnb (hnd.map Fin.val_injective) (hp.1.2.1.map Fin.val_injective)
    hu hv hin (hmapword L) (hmapword Nv) (hword u) (hword v)
    (by simp only [List.length_map]; omega)
  refine ⟨s', t, he, ?_, ?_, ha, hr⟩
  · simpa only [List.length_map] using ht
  · exact ho.trans (liftOffOffWords_map G u v Nv L hNv)

end GraphMinor.Compute.Crossing
