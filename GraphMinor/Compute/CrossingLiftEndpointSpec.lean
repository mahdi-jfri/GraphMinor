module

public import GraphMinor.Compute.CrossingLiftEndpoint
public import GraphMinor.Crossing.DefsContract

/-!
# The graph specification of the endpoint contraction programs

The recorded neighbour list represents precisely the old edges incident with the retained
vertex. This file identifies the numerical start rule with each of Section 11's mathematical
start rules, then carries that equality through the two reversals. Thus both endpoint RAM
programs return exactly the path lists specified by the note.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

private theorem mem_numbered_neighbours {N : ℕ} (Nv : List (Fin N)) (x : Fin N) :
    x.val ∈ Nv.map Fin.val ↔ x ∈ Nv := by
  simp only [List.mem_map, Fin.val_injective.eq_iff, exists_eq_right]

/-- Vertex numbering commutes with either of the Section 11 start rules. -/
theorem liftStartWords_map {N : ℕ} (oneOn : Bool) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (u v : Fin N) (Nv L : List (Fin N))
    (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) :
    liftStartWords oneOn u.val v.val (Nv.map Fin.val) (L.map Fin.val) =
      (if oneOn then liftStartOneOn G u v L else liftStartBothOn G u v L).map Fin.val := by
  rcases L with _ | ⟨x, _ | ⟨b, rest⟩⟩ <;> cases oneOn <;>
    simp only [List.map_nil, List.map_cons, liftStartWords, liftStartOneOn, liftStartBothOn,
      Bool.false_eq_true, ↓reduceIte, Fin.val_injective.eq_iff, mem_numbered_neighbours, hNv] <;>
    split_ifs <;> rfl

/-- Vertex numbering commutes with the start, reversal, start, reversal sequence. -/
theorem liftEndpointWords_map {N : ℕ} (oneOn : Bool) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (u v : Fin N) (Nv L : List (Fin N))
    (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) :
    (liftStartWords oneOn u.val v.val (Nv.map Fin.val)
      (liftStartWords oneOn u.val v.val (Nv.map Fin.val) (L.map Fin.val)).reverse).reverse =
      (if oneOn then liftOneOn G u v L else liftBothOn G u v L).map Fin.val := by
  rw [liftStartWords_map oneOn G u v Nv L hNv, ← List.map_reverse,
    liftStartWords_map oneOn G u v Nv _ hNv, ← List.map_reverse]
  cases oneOn <;> rfl

/-- The endpoint RAM program returns exactly the appropriate Section 11 lift on finite vertices.
No assumptions about an unproved lifting step occur: the path length, neighbour list, register
values, scratch separation and word bound are the whole input specification. -/
theorem liftEndpointProg_exec_fin {w N : ℕ} (oneOn : Bool) (G : SimpleGraph (Fin N))
    [DecidableRel G.Adj] (L Nv : List (Fin N)) (u v : Fin N)
    (src neighbours patch tmp rev r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp, rev].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (hnd : Nv.Nodup) (hNv : ∀ y, y ∈ Nv ↔ G.Adj v y) (huv : u ≠ v)
    (hlen : 2 ≤ L.length) (s : State)
    (hsrc : s.arrs src = L.map Fin.val) (hnb : s.arrs neighbours = Nv.map Fin.val)
    (hu : s.regs r_u = u.val) (hv : s.regs r_v = v.val)
    (hw : 32 * (N + L.length + Nv.length + 3) < 2 ^ w) :
    ∃ s' t, Exec w (liftEndpointProg oneOn src neighbours patch tmp rev r_u r_v R) s s' t ∧
      t ≤ 200 * (L.length + Nv.length + 1) + 600 ∧
      s'.arrs src = (if oneOn then liftOneOn G u v L else liftBothOn G u v L).map Fin.val ∧
      (∀ c, c ∉ [src, patch, tmp, rev] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hword : ∀ x : Fin N, x.val < 2 ^ w := fun x => x.isLt.trans (by omega)
  have hmapword : ∀ xs : List (Fin N), ∀ x ∈ xs.map Fin.val, x < 2 ^ w := by
    intro xs x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact hword y
  obtain ⟨s', t, he, ht, ho, ha, hr⟩ := liftEndpointProg_exec
    oneOn src neighbours patch tmp rev r_u r_v R harr huR hvR
    (L.map Fin.val) (Nv.map Fin.val) u.val v.val s hsrc hnb (hnd.map Fin.val_injective)
    hu hv (fun h => huv (Fin.ext h)) (by simpa using hlen)
    (hmapword L) (hmapword Nv) (hword u) (hword v)
    (by simp only [List.length_map]; omega)
  refine ⟨s', t, he, ?_, ho.trans (liftEndpointWords_map oneOn G u v Nv L hNv), ha, hr⟩
  simpa only [List.length_map] using ht

end GraphMinor.Compute.Crossing
