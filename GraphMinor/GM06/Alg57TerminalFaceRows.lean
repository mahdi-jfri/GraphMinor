module

public import GraphMinor.GM06.Alg57FiniteFaceOrbit
public import GraphMinor.GM06.Alg57TerminalPathLink
import GraphMinor.GM06.Alg57FilterCornerLabels

/-!
# Rotating the computed face row for terminal tracing

Section 15 of the proof of VI (5.7), page 133, places the reverse
inner cuff end last and removes it before tracing. The computed
face row has exactly its face successor as its cyclic order.
Rotating preserves this order. The relation between the head of
an end and the tail of its successor then gives the required
finite dart walk from the removed end's head to its tail.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- Rotate the selected face so that its chosen cuff end is last,
then remove that final end before terminal tracing. -/
@[expose] def gm06TerminalFaceDarts (c : ℕ) (row : List ℕ) : List ℕ :=
  (row.rotate (row.idxOf c + 1)).dropLast

private theorem formPerm_of_closed_chain {α : Type*} [DecidableEq α]
    (next : α → α) (a : α) (xs : List α) (hn : (a :: xs).Nodup)
    (hc : List.IsChain (fun x y => next x = y) ((a :: xs) ++ [a])) :
    ∀ d ∈ a :: xs, (a :: xs).formPerm d = next d := by
  intro d hd
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
  have hpair := List.isChain_iff_getElem.mp hc j (by simp only [List.length_append, List.length_singleton]; omega)
  rw [List.getElem_append_left hj] at hpair
  rw [List.formPerm_apply_getElem _ hn]
  by_cases hj1 : j + 1 < (a :: xs).length
  · rw [List.getElem_append_left hj1] at hpair
    simpa only [Nat.mod_eq_of_lt hj1] using hpair.symm
  · have he : j + 1 = (a :: xs).length := by omega
    rw [List.getElem_append_right (by omega)] at hpair
    simpa only [he, Nat.mod_self, Nat.sub_self, List.getElem_cons_zero] using hpair.symm

/-- The selected row's cyclic order is exactly the numeric face
successor, with no repeated end. -/
theorem cutFaceIncidence_row_order {n m target : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (ht : target ∈ data.activeDarts) {row : List ℕ}
    (hout : gm06CutFaceIncidence n m data target =
      some (row, gm06IncV n data.origins row, gm06IncE m row)) :
    row.Nodup ∧ target ∈ row ∧ ∀ d ∈ row, row.formPerm d =
      (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm) d := by
  obtain ⟨finrow, hfinout, htrow, start, _, heq, hchain⟩ :=
    gm06CutFaceIncidence_spec data hnd hkeys hactive hcover hpair ht
  have hrow : row = finrow.map Fin.val := by
    exact congrArg Prod.fst (Option.some.inj (hout.symm.trans hfinout))
  have hnfin : finrow.Nodup := by
    rw [heq]
    exact gm06OrbitTrace_nodup _ _ _ (by simp)
  have hhead : finrow.head? = some start := by
    rw [heq, gm06OrbitTrace_eq_iterate _ _ _ (by simp)]
    have hp := Function.minimalPeriod_pos_of_mem_periodicPts
      ((gm06FacePermutation (data.rotations.map (gm06FinLabels (2 * m)))).injective.mem_periodicPts start)
    cases he : Function.minimalPeriod (gm06FacePermutation
      (data.rotations.map (gm06FinLabels (2 * m)))) start with
    | zero => omega
    | succ p => rfl
  obtain ⟨rest, hcons⟩ := List.head?_eq_some_iff.mp hhead
  have hrows := gm06CutFiniteRows_map_val (2 * m) data hkeys
  have hfinite := (gm06CutFiniteRows_valid data hnd hkeys hactive hcover hpair).1
  have hmap : List.IsChain (fun a b =>
      (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm) a = b)
      ((finrow.map Fin.val) ++ [start.val]) := by
    have hh := List.isChain_map_of_isChain Fin.val
      (S := fun a b => (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm) a = b)
      (fun a b hab => by
        have he := facePermutation_val _ hfinite a
        rw [hrows, hab] at he
        exact he.symm) hchain
    simpa only [List.map_append, List.map_cons, List.map_nil] using hh
  refine ⟨hrow.symm ▸ hnfin.map Fin.val_injective, hrow.symm ▸ htrow, ?_⟩
  rw [hcons] at hmap
  rw [hrow, hcons]
  simp only [List.map_cons] at hmap ⊢
  exact formPerm_of_closed_chain _ _ _ (by simpa only [hcons, List.map_cons] using hnfin.map Fin.val_injective) hmap

/-- Rotating at the successor of a present end places that end
last, and it occurs nowhere in the remaining terminal row. -/
theorem terminalFaceDarts_rotate {row : List ℕ} (hn : row.Nodup) {c : ℕ} (hc : c ∈ row) :
    row.rotate (row.idxOf c + 1) = gm06TerminalFaceDarts c row ++ [c] ∧
      c ∉ gm06TerminalFaceDarts c row ∧ (gm06TerminalFaceDarts c row).Nodup := by
  have hi := List.idxOf_lt_length_of_mem hc
  have hh : (row.rotate (row.idxOf c)).head? = some c := by
    rw [List.head?_rotate hi, List.getElem?_eq_getElem hi, List.getElem_idxOf]
  obtain ⟨rest, hrest⟩ := List.head?_eq_some_iff.mp hh
  have hnrot : (c :: rest).Nodup := hrest ▸ List.nodup_rotate.mpr hn
  have hrotate : row.rotate (row.idxOf c + 1) = rest ++ [c] := by
    rw [← List.rotate_rotate, hrest, List.rotate_cons_succ, List.rotate_zero]
  have hds : gm06TerminalFaceDarts c row = rest := by
    simp only [gm06TerminalFaceDarts, hrotate, List.dropLast_concat]
  exact ⟨by rw [hds]; exact hrotate, hds.symm ▸ (List.nodup_cons.mp hnrot).1,
    hds.symm ▸ (List.nodup_cons.mp hnrot).2⟩

/-- A chain of ends from a first end to a last end traces its middle
list from the first end's head to the last end's tail. -/
theorem dartWalk_of_end_chain {D V : Type*} (tail head : D → V) (first last : D)
    (ds : List D) (hc : List.IsChain (fun a b => head a = tail b) (first :: ds ++ [last])) :
    GM06DartWalk tail head (head first) ds (tail last) := by
  induction ds generalizing first with
  | nil =>
    have he := List.isChain_pair.mp hc
    rw [← he]
    exact .nil _
  | cons d ds ih =>
    obtain ⟨hfirst, hrest⟩ := List.isChain_cons_cons.mp hc
    exact .cons hfirst.symm (ih d hrest)

/-- Removing the last cuff end from an ordered face cycle gives
the terminal dart walk prescribed in Section 15. -/
theorem terminalFaceDarts_walk {V : Type*} (tail head : ℕ → V) {row : List ℕ}
    (hn : row.Nodup) {c : ℕ} (hc : c ∈ row)
    (hstep : ∀ d ∈ row, head d = tail (row.formPerm d)) :
    GM06DartWalk tail head (head c) (gm06TerminalFaceDarts c row) (tail c) := by
  obtain ⟨hrotate, _, _⟩ := terminalFaceDarts_rotate hn hc
  let ds := gm06TerminalFaceDarts c row
  have hr : c :: ds ~r row := by
    have h1 : c :: ds ~r ds ++ [c] := by
      exact List.isRotated_append (l := [c]) (l' := ds)
    have h2 : row ~r ds ++ [c] := by
      rw [← hrotate]
      exact (List.IsRotated.forall row _).symm
    exact h1.trans h2.symm
  have hnr : (c :: ds).Nodup := hr.perm.nodup_iff.mpr hn
  have hperm := List.formPerm_eq_of_isRotated hnr hr
  have hchain := formPerm_closed_chain c ds hnr
  apply dartWalk_of_end_chain tail head c c ds
  apply hchain.imp_of_mem_imp
  intro a b ha _ hab
  have ham : a ∈ row := by
    rcases List.mem_append.mp ha with h | h
    · exact hr.perm.mem_iff.mp h
    · exact List.mem_singleton.mp h ▸ hc
  rw [hstep a ham, ← hperm, hab]

end GraphMinor.GM06
