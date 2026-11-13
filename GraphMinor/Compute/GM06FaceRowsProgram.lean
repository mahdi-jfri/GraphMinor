module

public import GraphMinor.Compute.GM06FaceEnumerationProgram

/-!
# FACE_ROWS from the actual rotation input

Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes the
inverse rotation, composes it with dart reversal, and enumerates
orbits. This file joins the verified RAM passes. Its only graph
inputs are the encoded rotations, the active dart labels in scan
order, and the size of their permanent label space. The exact row
encoding and owner table are outputs. The proof also covers unused
permanent slots: a reversal-closed active set is preserved by the
face permutation, so no inactive dart enters a returned row.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exact active face rows computed directly from finite rotation lists. -/
def gm06ActiveFaceRows {m : ℕ} (rotations : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) : List (List (Fin (2 * m))) :=
  gm06FaceRows (gm06FacePermutation rotations) (2 * m) active

private theorem faceRowsAux_row_source {D : Type*} [DecidableEq D]
    (next : D → D) (fuel : ℕ) (labels : List D) (rows : List (List D)) (row : List D)
    (hrow : row ∈ gm06FaceRowsAux next fuel labels rows) :
    row ∈ rows ∨ ∃ d ∈ labels, row = gm06OrbitTrace next d fuel := by
  induction labels generalizing rows with
  | nil => exact Or.inl hrow
  | cons d ds ih =>
    simp only [gm06FaceRowsAux] at hrow
    split_ifs at hrow with hd
    · rcases ih rows hrow with h | ⟨e, he, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨e, List.mem_cons_of_mem d he, h⟩
    · rcases ih _ hrow with h | ⟨e, he, h⟩
      · rcases List.mem_append.mp h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨d, List.mem_cons_self, List.mem_singleton.mp h⟩
      · exact Or.inr ⟨e, List.mem_cons_of_mem d he, h⟩

/-- The inverse rotation preserves the darts listed in the rotations. -/
theorem gm06RotationPermutation_symm_mem {D : Type*} [DecidableEq D]
    (rows : List (List D)) (hn : rows.flatten.Nodup) (d : D) (hd : d ∈ rows.flatten) :
    (gm06RotationPermutation rows).symm d ∈ rows.flatten := by
  obtain ⟨row, hrow, hdrow⟩ := List.mem_flatten.mp hd
  let p := row.formPerm.symm d
  have hp : p ∈ row := by
    have hh := List.formPerm_apply_mem_of_mem (l := row.reverse) (x := d) (by simpa using hdrow)
    rw [List.formPerm_reverse] at hh
    simpa only [List.mem_reverse, Equiv.Perm.coe_inv, p] using hh
  have hs : gm06RotationPermutation rows p = d :=
    (gm06RotationPermutation_apply_row rows hn row hrow p hp).trans (row.formPerm.apply_symm_apply d)
  have hsymm : (gm06RotationPermutation rows).symm d = p :=
    (gm06RotationPermutation rows).symm_apply_eq.mpr hs.symm
  rw [hsymm]
  exact List.mem_flatten.mpr ⟨row, hrow, hp⟩

/-- Active dart labels are closed under the computed face successor.
The premises are the encoding's row coverage and paired edge ends. -/
theorem gm06FacePermutation_active {m : ℕ} (rows : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (hn : rows.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rows.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active) :
    ∀ d ∈ active, gm06FacePermutation rows d ∈ active := by
  intro d hd
  apply (hcover _).mpr
  exact gm06RotationPermutation_symm_mem rows hn _ ((hcover _).mp (hmate d hd))

/-- The active rows contain exactly the active darts, each in one row.
Every row is a complete successor orbit and follows sigma inverse tau. -/
theorem gm06ActiveFaceRows_spec {m : ℕ} (rows : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (hn : rows.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rows.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active) :
    let result := gm06ActiveFaceRows rows active
    result.flatten.Nodup ∧
      (∀ d, d ∈ result.flatten ↔ d ∈ active) ∧
      (∀ d ∈ active, ∃! row, row ∈ result ∧ d ∈ row) ∧
      (∀ row ∈ result, ∃ d ∈ active,
        row = gm06OrbitTrace (gm06FacePermutation rows) d (2 * m) ∧
        List.IsChain (fun a b => gm06FacePermutation rows a = b) (row ++ [d])) := by
  let next := gm06FacePermutation rows
  let result := gm06ActiveFaceRows rows active
  have hcard : Fintype.card (Fin (2 * m)) ≤ 2 * m := by simp
  have hinv := gm06FaceRowsAux_invariant next (2 * m) hcard active [] (by simp) (by simp)
  have hsource : ∀ row ∈ result, ∃ d ∈ active, row = gm06OrbitTrace next d (2 * m) := by
    intro row hrow
    rcases faceRowsAux_row_source next (2 * m) active [] row hrow with h | h
    · cases h
    · exact h
  have hclosed := gm06FacePermutation_active rows active hn hcover hmate
  have hiter : ∀ j : ℕ, ∀ d ∈ active, next^[j] d ∈ active := by
    intro j
    induction j with
    | zero => intro d hd; exact hd
    | succ j ih =>
      intro d hd
      rw [Function.iterate_succ_apply']
      exact hclosed _ (ih d hd)
  have hmem : ∀ d, d ∈ result.flatten ↔ d ∈ active := by
    intro d
    constructor
    · intro hd
      obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
      obtain ⟨a, ha, rfl⟩ := hsource row hr
      obtain ⟨j, rfl⟩ := (gm06OrbitTrace_mem_iff next a d (2 * m) hcard).mp hd
      exact hiter j a ha
    · intro hd
      exact hinv.2.2 d (Or.inr hd)
  refine ⟨hinv.1, hmem, ?_, ?_⟩
  · intro d hd
    obtain ⟨row, hr, hdr⟩ := List.mem_flatten.mp ((hmem d).mpr hd)
    refine ⟨row, ⟨hr, hdr⟩, ?_⟩
    intro other ho
    by_contra hne
    exact ((List.nodup_flatten.mp hinv.1).2.forall ho.1 hr hne) ho.2 hdr
  · intro row hrow
    obtain ⟨d, hd, rfl⟩ := hsource row hrow
    exact ⟨d, hd, rfl, gm06OrbitTrace_follows next d (2 * m) hcard⟩

/-- Registers changed by the full rotation-to-face-row program. -/
def gm06FaceRowsRegs : List ℕ := gm06PredecessorRegs ++ [654, 655, 656, 657, 658]

/-- FACE_ROWS: read rotations, compute predecessors and successors,
then return the encoded active face rows and the owner table. -/
def gm06FaceRowsProg : Cmd :=
  .seq gm06PredecessorsProg (.seq gm06FaceSuccessorsProg gm06FaceEnumerationProg)

/-- Exact RAM execution of FACE_ROWS from rotation rows. No predecessor,
successor, orbit or face row is supplied as input. -/
theorem gm06FaceRowsProg_exec {w m : ℕ} (rows : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (s : State) (hnd : rows.flatten.Nodup)
    (hw : 2 < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hcode : (gm06EncodeRows (rows.map (List.map Fin.val))).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows (rows.map (List.map Fin.val)), x < 2 ^ w)
    (hl : active.length < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows (rows.map (List.map Fin.val)))
    (h604 : s.arrs 604 = active.map Fin.val) (h648 : s.regs 648 = 2 * m) :
    let result := gm06ActiveFaceRows rows active
    ∃ sf t, Exec w gm06FaceRowsProg s sf t ∧
      t ≤ 54 + 68 * (2 * m) + 29 * rows.length + 37 * rows.flatten.length +
        active.length * (40 + 18 * (2 * m)) ∧
      Keeps gm06FaceRowsRegs [601, 602, 603, 605, 606, 607] s sf ∧
      sf.arrs 605 = gm06FaceOwners (2 * m) (result.map (List.map Fin.val)) ∧
      sf.arrs 607 = gm06EncodeRows (result.map (List.map Fin.val)) := by
  have hn : 2 * m < 2 ^ w := by omega
  have hkeys : ∀ d ∈ (rows.map (List.map Fin.val)).flatten, d < 2 * m := by
    intro d hd
    rw [← List.map_flatten] at hd
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hd
    exact a.isLt
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06PredecessorsProg_exec (rows.map (List.map Fin.val))
    s (by omega) hn hkeys h600 hcode hwords h648
  let predecessors := gm06RotationPredecessors (2 * m) (rows.map (List.map Fin.val))
  have hpredlen : predecessors.length = 2 * m := by
    simp only [predecessors, gm06RotationPredecessors, gm06Scatter_length, List.length_range]
  have hpredwords : ∀ x ∈ predecessors, x < 2 ^ w := by
    intro x hx
    dsimp only [predecessors] at hx
    rw [gm06RotationPredecessors_eq_inverse rows hnd] at hx
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hx
    exact ((gm06RotationPermutation rows).symm a).isLt.trans hn
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06FaceSuccessorsProg_exec predecessors s₁ hw hn hpredlen hpredwords hd₁
  have hk₁₂ : Keeps gm06FaceRowsRegs [601, 602, 603, 605, 606, 607] s s₂ :=
    (hk₁.mono (fun r hr => List.mem_append.mpr (Or.inl hr)) (by simp)).trans hk₂
      (by simp [gm06PredecessorRegs]) (by simp)
  have hsuc : s₂.arrs 603 = List.ofFn (fun d => (gm06FacePermutation rows d).val) := by
    rw [hd₂]
    exact gm06FaceSuccessors_eq_permutation rows hnd
  obtain ⟨sf, tf, hef, htf, hkf, hdf, hcodef⟩ := gm06FaceEnumerationProg_exec
    (gm06FacePermutation rows) active s₂ hw hcap hl hsuc
    ((hk₁₂.2 604 (by decide)).trans h604)
  refine ⟨sf, t₁ + (t₂ + tf), .seq he₁ (.seq he₂ hef), ?_,
    hk₁₂.trans hkf (by simp [gm06FaceEnumerationRegs, gm06FaceRowsRegs, gm06PredecessorRegs])
      (by simp), hdf, hcodef⟩
  have hfl : (rows.map (List.map Fin.val)).flatten.length = rows.flatten.length := by
    rw [← List.map_flatten, List.length_map]
  simp only [List.length_map, hfl] at ht₁
  omega

/-- A fixed quadratic bound for the face-row program's explicit cost. -/
theorem gm06FaceRows_cost_le_polynomial (n k ell a : ℕ) :
    54 + 68 * n + 29 * k + 37 * ell + a * (40 + 18 * n) ≤
      300 * (n + k + ell + a + 1) ^ 2 := by
  let N := n + k + ell + a + 1
  have hn : n ≤ N := by dsimp only [N]; omega
  have hk : k ≤ N := by dsimp only [N]; omega
  have hl : ell ≤ N := by dsimp only [N]; omega
  have ha : a ≤ N := by dsimp only [N]; omega
  have h1 : 1 ≤ N := by dsimp only [N]; omega
  have han := Nat.mul_le_mul ha hn
  have hNN := Nat.le_mul_self N
  change _ ≤ 300 * N ^ 2
  nlinarith

/-- FACE_ROWS has a quadratic RAM time bound in the finite input sizes. -/
theorem gm06FaceRowsProg_exec_polynomial {w m : ℕ} (rows : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (s : State) (hnd : rows.flatten.Nodup)
    (hw : 2 < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hcode : (gm06EncodeRows (rows.map (List.map Fin.val))).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows (rows.map (List.map Fin.val)), x < 2 ^ w)
    (hl : active.length < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows (rows.map (List.map Fin.val)))
    (h604 : s.arrs 604 = active.map Fin.val) (h648 : s.regs 648 = 2 * m) :
    let result := gm06ActiveFaceRows rows active
    ∃ sf t, Exec w gm06FaceRowsProg s sf t ∧
      t ≤ 300 * (2 * m + rows.length + rows.flatten.length + active.length + 1) ^ 2 ∧
      Keeps gm06FaceRowsRegs [601, 602, 603, 605, 606, 607] s sf ∧
      sf.arrs 605 = gm06FaceOwners (2 * m) (result.map (List.map Fin.val)) ∧
      sf.arrs 607 = gm06EncodeRows (result.map (List.map Fin.val)) := by
  obtain ⟨sf, t, he, ht, hk, ho, hr⟩ := gm06FaceRowsProg_exec rows active s hnd hw hcap hcode hwords hl h600 h604 h648
  exact ⟨sf, t, he, ht.trans (gm06FaceRows_cost_le_polynomial _ _ _ _), hk, ho, hr⟩

end GraphMinor.Compute
