module

public import GraphMinor.Compute.GM06CutFaceFacts
public import GraphMinor.GM06.Alg57CutEquations

/-!
# The computed selected row is the numeric face orbit

The finite face routine in VI (5.7), page 133, uses bounded dart
labels. Mapping them back to natural numbers preserves each rotation
successor and its inverse. A selected complete orbit row therefore
contains exactly the natural-number orbit of its selecting dart.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

private theorem formPerm_val {q : ℕ} (row : List (Fin q)) (hn : row.Nodup) (d : Fin q) :
    (row.formPerm d).val = (row.map Fin.val).formPerm d.val := by
  classical
  by_cases hd : d ∈ row
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
    rw [List.formPerm_apply_getElem row hn i hi]
    have hm := List.formPerm_apply_getElem (row.map Fin.val) (hn.map Fin.val_injective) i
      (by simpa only [List.length_map] using hi)
    simpa only [List.getElem_map, List.length_map] using hm.symm
  · rw [List.formPerm_apply_of_notMem hd, List.formPerm_apply_of_notMem]
    simpa only [List.mem_map_of_injective Fin.val_injective] using hd

/-- Forgetting finite bounds commutes with a rotation permutation. -/
theorem rotationPermutation_val {q : ℕ} (rows : List (List (Fin q)))
    (hn : rows.flatten.Nodup) (d : Fin q) :
    (gm06RotationPermutation rows d).val =
      gm06RotationPermutation (rows.map (List.map Fin.val)) d.val := by
  classical
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih =>
    have hh := List.nodup_append.mp (show (row ++ rows.flatten).Nodup from hn)
    simp only [gm06RotationPermutation, List.map_cons, Equiv.Perm.mul_apply]
    rw [formPerm_val row hh.1, ih hh.2.1]

/-- Forgetting finite bounds also commutes with the inverse rotation. -/
theorem rotationPermutation_symm_val {q : ℕ} (rows : List (List (Fin q)))
    (hn : rows.flatten.Nodup) (d : Fin q) :
    ((gm06RotationPermutation rows).symm d).val =
      (gm06RotationPermutation (rows.map (List.map Fin.val))).symm d.val := by
  apply (gm06RotationPermutation (rows.map (List.map Fin.val))).injective
  rw [← rotationPermutation_val rows hn, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The finite face successor is the natural-number face successor
on its directed labels. -/
theorem facePermutation_val {m : ℕ} (rows : List (List (Fin (2 * m))))
    (hn : rows.flatten.Nodup) (d : Fin (2 * m)) :
    (gm06FacePermutation rows d).val =
      (dartMatePerm.trans (gm06RotationPermutation (rows.map (List.map Fin.val))).symm) d.val := by
  change ((gm06RotationPermutation rows).symm (gm06DartReversal m d)).val = _
  rw [rotationPermutation_symm_val rows hn]
  simp only [gm06DartReversal, Equiv.coe_fn_mk, Equiv.trans_apply, dartMatePerm_apply]

/-- The same equality holds for every iterate of the face successor. -/
theorem facePermutation_iterate_val {m : ℕ} (rows : List (List (Fin (2 * m))))
    (hn : rows.flatten.Nodup) (n : ℕ) (d : Fin (2 * m)) :
    ((gm06FacePermutation rows)^[n] d).val =
      (dartMatePerm.trans (gm06RotationPermutation (rows.map (List.map Fin.val))).symm)^[n] d.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', facePermutation_val rows hn, ih,
      Function.iterate_succ_apply']

/-- A complete finite orbit row can be read starting at any of its
members, without changing its membership test. -/
theorem mem_orbitTrace_iff_from_member {D : Type*} [Fintype D] [DecidableEq D]
    (next : Equiv.Perm D) (start c d : D) (fuel : ℕ) (hf : Fintype.card D ≤ fuel)
    (hc : c ∈ gm06OrbitTrace next start fuel) :
    d ∈ gm06OrbitTrace next start fuel ↔ ∃ n : ℕ, next^[n] c = d := by
  have hsc := (gm06OrbitTrace_mem_sameCycle next start c fuel hf).mp hc
  rw [gm06OrbitTrace_mem_sameCycle next start d fuel hf]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := (hsc.symm.trans h).exists_nat_pow_eq
    exact ⟨n, by simpa only [Equiv.Perm.iterate_eq_pow] using hn⟩
  · rintro ⟨n, hn⟩
    have hcd : next.SameCycle c d := by
      rw [← hn]
      simpa only [Equiv.Perm.iterate_eq_pow] using
        (Equiv.Perm.SameCycle.refl next c).pow_right (n := n)
    exact hsc.trans hcd

/-- The actual face/incidence query returns a row containing exactly
the natural-number orbit of the selecting dart. -/
theorem cutFaceIncidence_orbit {n m target : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts) (ht : target ∈ data.activeDarts) :
    ∃ row : List ℕ,
      gm06CutFaceIncidence n m data target =
        some (row, gm06IncV n data.origins row, gm06IncE m row) ∧
      ∀ d : ℕ, d ∈ row ↔ ∃ j : ℕ,
        (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j] target = d := by
  obtain ⟨row, hout, htarget, start, hs, heq, _⟩ :=
    gm06CutFaceIncidence_spec data hnd hkeys hactive hcover hpair ht
  have hrows := gm06CutFiniteRows_map_val (2 * m) data hkeys
  have hfin := (gm06CutFiniteRows_valid data hnd hkeys hactive hcover hpair).1
  have hc : (⟨target, hactive target ht⟩ : Fin (2 * m)) ∈ row := by
    obtain ⟨c, hc, hcv⟩ := List.mem_map.mp htarget
    have he : c = (⟨target, hactive target ht⟩ : Fin (2 * m)) := Fin.ext hcv
    exact he ▸ hc
  have horb (d : Fin (2 * m)) : d ∈ row ↔ ∃ j : ℕ,
      (gm06FacePermutation (data.rotations.map (gm06FinLabels (2 * m))))^[j]
        ⟨target, hactive target ht⟩ = d := by
    rw [heq] at hc ⊢
    exact mem_orbitTrace_iff_from_member _ start _ d (2 * m) (by simp) hc
  have hiter (j : ℕ) :
      (((gm06FacePermutation (data.rotations.map (gm06FinLabels (2 * m))))^[j]
        ⟨target, hactive target ht⟩).val) =
      (dartMatePerm.trans (gm06RotationPermutation data.rotations).symm)^[j] target := by
    simpa only [hrows] using facePermutation_iterate_val _ hfin j ⟨target, hactive target ht⟩
  refine ⟨row.map Fin.val, hout, fun d => ?_⟩
  constructor
  · intro hd
    obtain ⟨a, ha, had⟩ := List.mem_map.mp hd
    obtain ⟨j, hj⟩ := (horb a).mp ha
    exact ⟨j, ((hiter j).symm.trans (congrArg Fin.val hj)).trans had⟩
  · rintro ⟨j, hj⟩
    have hval := (hiter j).trans hj
    exact List.mem_map.mpr ⟨_, (horb _).mpr ⟨j, rfl⟩, hval⟩

end GraphMinor.GM06
