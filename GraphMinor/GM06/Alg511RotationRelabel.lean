module

public import GraphMinor.GM06.Alg511PositiveRotationImage
public import GraphMinor.Compute.GM06Alg511ReflectDrawing
import Mathlib.Tactic

/-!
# Changing the cuff parameters and directed labels

The orientation step of VI (5.11), page 134, keeps ordinary edge
parameters and reverses the prescribed parameters on the two cuffs.
Changing an edge parameter exchanges its two half-edges, without
moving either spoke or changing a polar chart. Reindexing the edges
then changes only their finite labels. These facts transport positive
rotation rows and apply to loops as well as edges with distinct ends.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Reverse precisely those edge parameters marked by the supplied
mask. The mask describes directions, rather than drawing points. -/
@[expose] noncomputable def alg511ReverseEdgePar {S : Type*}
    (γ : Set S → I → S) (flip : Set S → Bool) (e : Set S) (t : I) : S :=
  γ e (if flip e then σ t else t)

/-- Reversing a parameter exchanges its Boolean end. -/
@[expose] def alg511ReverseEnd (f b : Bool) : Bool := if f then !b else b

private theorem reverseEnd_involutive (f b : Bool) :
    alg511ReverseEnd f (alg511ReverseEnd f b) = b := by
  cases f <;> cases b <;> rfl

private theorem reverse_end_parameter (f b : Bool) :
    (if f then σ (endOf (alg511ReverseEnd f b)) else endOf (alg511ReverseEnd f b)) = endOf b := by
  cases f <;> cases b <;> simp [alg511ReverseEnd, endOf]

private theorem reverse_half_parameter (f b : Bool) (t : I) :
    (if f then σ (halfPar (alg511ReverseEnd f b) t) else halfPar (alg511ReverseEnd f b) t) =
      halfPar b t := by
  cases f <;> cases b <;> simp [alg511ReverseEnd, halfPar]

/-- Parameter reversal exchanges exactly the two ends of each
marked edge. Its inverse exchanges those same ends again. -/
@[expose] noncomputable def alg511ReverseHalfEdges {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (γ : Set S → I → S) (flip : Set S → Bool) (v : S) :
    halfEdges Γ γ v ≃ halfEdges Γ (alg511ReverseEdgePar γ flip) v where
  toFun a := ⟨(a.val.1, alg511ReverseEnd (flip a.val.1) a.val.2), a.property.1, by
    change γ a.val.1 (if flip a.val.1 then σ (endOf (alg511ReverseEnd _ _)) else
      endOf (alg511ReverseEnd _ _)) = v
    rw [reverse_end_parameter]
    exact a.property.2⟩
  invFun a := ⟨(a.val.1, alg511ReverseEnd (flip a.val.1) a.val.2), a.property.1, by
    have he := reverse_end_parameter (flip a.val.1) (alg511ReverseEnd (flip a.val.1) a.val.2)
    rw [reverseEnd_involutive] at he
    change γ a.val.1 (endOf (alg511ReverseEnd _ _)) = v
    rw [← he]
    exact a.property.2⟩
  left_inv a := by exact Subtype.ext (Prod.ext rfl (reverseEnd_involutive _ _))
  right_inv a := by exact Subtype.ext (Prod.ext rfl (reverseEnd_involutive _ _))

/-- The exchanged half-edge has exactly its old spoke at every
parameter, so the same chart and direction still describe it. -/
theorem alg511ReverseHalfEdges_spoke {S : Type*} [TopologicalSpace S]
    (Γ : Drawing S) (γ : Set S → I → S) (flip : Set S → Bool) (v : S)
    (a : halfEdges Γ γ v) (t : I) :
    spoke (alg511ReverseEdgePar γ flip) (alg511ReverseHalfEdges Γ γ flip v a).val t =
      spoke γ a.val t := by
  exact congrArg (γ a.val.1) (reverse_half_parameter (flip a.val.1) a.val.2 t)

/-- Reversing selected parameters still parametrizes every actual
edge, including the open interval and both vertex ends. -/
theorem alg511_reverse_edgePar {S : Type*} [TopologicalSpace S]
    {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ) (flip : Set S → Bool) :
    EdgePar Γ (alg511ReverseEdgePar γ flip) := by
  have hσ (t : I) : σ t ∈ Ioo (0 : I) 1 ↔ t ∈ Ioo (0 : I) 1 := by
    change 0 < σ t ∧ σ t < 1 ↔ 0 < t ∧ t < 1
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨by simpa using unitInterval.strictAnti_symm h1,
        by simpa using unitInterval.strictAnti_symm h0⟩
    · rintro ⟨h0, h1⟩
      exact ⟨by simpa using unitInterval.strictAnti_symm h1,
        by simpa using unitInterval.strictAnti_symm h0⟩
  constructor
  · intro e he
    change Continuous (fun t => γ e (if flip e then σ t else t))
    cases hf : flip e
    · simpa only [hf, Bool.false_eq_true, ite_false] using hγ.cont e he
    · simpa only [hf, ite_true, Function.comp_def] using
        (hγ.cont e he).comp unitInterval.continuous_symm
  · intro e he
    cases hf : flip e <;> simp only [alg511ReverseEdgePar, hf, Bool.false_eq_true,
      ite_false, ite_true, unitInterval.symm_zero]
    · exact hγ.zero e he
    · exact hγ.one e he
  · intro e he
    cases hf : flip e <;> simp only [alg511ReverseEdgePar, hf, Bool.false_eq_true,
      ite_false, ite_true, unitInterval.symm_one]
    · exact hγ.one e he
    · exact hγ.zero e he
  · intro e he s hs t ht hst
    cases hf : flip e
    · exact hγ.inj e he hs ht (by simpa only [alg511ReverseEdgePar, hf,
        Bool.false_eq_true, ite_false] using hst)
    · apply unitInterval.symm_involutive.injective
      exact hγ.inj e he ((hσ s).mpr hs) ((hσ t).mpr ht)
        (by simpa only [alg511ReverseEdgePar, hf, ite_true] using hst)
  · intro e he
    change (fun t => γ e (if flip e then σ t else t)) '' Ioo (0 : I) 1 = e
    cases hf : flip e
    · simpa only [hf, Bool.false_eq_true, ite_false] using hγ.image e he
    · simp only [ite_true]
      change (fun t => γ e (σ t)) '' Ioo (0 : I) 1 = e
      rw [← image_image]
      have hi : σ '' Ioo (0 : I) 1 = Ioo (0 : I) 1 := by
        ext t
        constructor
        · rintro ⟨s, hs, rfl⟩; exact (hσ s).mpr hs
        · intro ht
          exact ⟨σ t, (hσ t).mpr ht, unitInterval.symm_symm t⟩
      rw [hi, hγ.image e he]

/-- Reindexing edges and reversing selected parameters changes
only the directed labels in a positive rotation row. The finite
compatibility equation specifies the labels of the two actual ends. -/
theorem alg511_positive_rotation_relabel
    {Γ : Drawing (OnePoint EuclideanPlane)} {n : ℕ}
    (edge : Fin n ≃ Γ.E) (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (flip : Set (OnePoint EuclideanPlane) → Bool) (q : Equiv.Perm (Fin n))
    (d : Equiv.Perm ℕ)
    (hd : ∀ (j : Fin n) (b : Bool), d (2 * j.val + b.toNat) =
      2 * (q.symm j).val + (alg511ReverseEnd (flip (edge j).val) b).toNat)
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) :
    GM06SuccessorRotationRowRep (q.trans edge) (alg511ReverseEdgePar γ flip) v (xs.map d) := by
  let η := alg511ReverseHalfEdges Γ γ flip v
  have hlabel (a : halfEdges Γ γ v) :
      halfEdgeLabel (q.trans edge) (η a) = d (halfEdgeLabel edge a) := by
    let j := edge.symm ⟨a.val.1, a.property.1⟩
    have hj : (edge j).val = a.val.1 := congrArg Subtype.val (edge.apply_symm_apply _)
    rw [show halfEdgeLabel edge a = 2 * j.val + a.val.2.toNat from rfl, hd]
    change 2 * (q.symm j).val + (alg511ReverseEnd (flip a.val.1) a.val.2).toNat = _
    rw [hj]
  have hend (r : ℕ) (j : Fin n) :
      (r = 2 * (q j).val ∨ r = 2 * (q j).val + 1) ↔
        (d r = 2 * j.val ∨ d r = 2 * j.val + 1) := by
    constructor
    · intro hr
      rcases hr with rfl | rfl
      · have hh := hd (q j) false
        rw [q.symm_apply_apply] at hh
        simp only [Bool.toNat_false, Nat.add_zero] at hh
        rw [hh]
        cases alg511ReverseEnd (flip (edge (q j)).val) false <;> simp
      · have hh := hd (q j) true
        rw [q.symm_apply_apply] at hh
        simp only [Bool.toNat_true] at hh
        rw [hh]
        cases alg511ReverseEnd (flip (edge (q j)).val) true <;> simp
    · intro hr
      cases hf : flip (edge (q j)).val
      · have h0 := hd (q j) false
        have h1 := hd (q j) true
        simp only [hf, alg511ReverseEnd, Bool.false_eq_true, ite_false,
          Bool.toNat_false, Bool.toNat_true, q.symm_apply_apply, Nat.add_zero] at h0 h1
        exact hr.elim (fun h => Or.inl (d.injective (h.trans h0.symm)))
          (fun h => Or.inr (d.injective (h.trans h1.symm)))
      · have h0 := hd (q j) false
        have h1 := hd (q j) true
        simp only [hf, alg511ReverseEnd, ite_true, Bool.not_false, Bool.not_true,
          Bool.toNat_false, Bool.toNat_true, q.symm_apply_apply, Nat.add_zero] at h0 h1
        exact hr.elim (fun h => Or.inr (d.injective (h.trans h1.symm)))
          (fun h => Or.inl (d.injective (h.trans h0.symm)))
  obtain ⟨hnd, hmem, horder⟩ := hrow
  refine ⟨hnd.map d.injective, ?_, ?_⟩
  · intro r
    constructor
    · rintro hr
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      obtain ⟨a, rfl⟩ := (hmem s).mp hs
      exact ⟨η a, hlabel a⟩
    · rintro ⟨a', ha'⟩
      obtain ⟨a, rfl⟩ := η.surjective a'
      exact List.mem_map.mpr ⟨halfEdgeLabel edge a, (hmem _).mpr ⟨a, rfl⟩,
        (hlabel a).symm.trans ha'⟩
  · rcases horder with hshort | ⟨Φ, z, hp, hpos, hzi, hs, hspoke, hrim⟩
    · exact Or.inl (by simpa only [List.length_map] using hshort)
    · refine Or.inr ⟨Φ, fun r => z (d.symm r), hp, hpos, ?_, ?_, ?_, ?_⟩
      · intro r hr s hs heq
        obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        obtain ⟨s', hs', rfl⟩ := List.mem_map.mp hs
        simp only [d.symm_apply_apply] at heq
        exact congrArg d (hzi hr' hs' heq)
      · simpa only [List.pairwise_map, d.symm_apply_apply] using hs
      · intro a' t ht
        obtain ⟨a, rfl⟩ := η.surjective a'
        simp only [hlabel, d.symm_apply_apply]
        obtain ⟨u, hu⟩ := hspoke a t ht
        exact ⟨u, (alg511ReverseHalfEdges_spoke Γ γ flip v a u).trans hu⟩
      · intro j w
        change polarRimMap Φ w ∈ (edge (q j)).val ↔ _
        rw [hrim]
        constructor
        · rintro ⟨r, hr, hz, he⟩
          exact ⟨d r, List.mem_map.mpr ⟨r, hr, rfl⟩, by simpa only [d.symm_apply_apply] using hz,
            (hend r j).mp he⟩
        · rintro ⟨r, hr, hz, he⟩
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
          exact ⟨s, hs, by simpa only [d.symm_apply_apply] using hz, (hend s j).mpr he⟩

/-- The three edge-label blocks under reflection: ordinary labels
stay fixed and both cuff-gap blocks reverse independently. -/
@[expose] def alg511CuffEdgeReflectionIndex (m k j : ℕ) : ℕ :=
  if j < m then j else if j < m + k then
    m + (k - 1 - (j - m)) else m + k + (k - 1 - (j - (m + k)))

private theorem cuffIndex_lt (m k j : ℕ) (hj : j < m + (k + k)) :
    alg511CuffEdgeReflectionIndex m k j < m + (k + k) := by
  dsimp only [alg511CuffEdgeReflectionIndex]
  split_ifs <;> omega

private theorem cuffIndex_involutive (m k j : ℕ) (hj : j < m + (k + k)) :
    alg511CuffEdgeReflectionIndex m k (alg511CuffEdgeReflectionIndex m k j) = j := by
  dsimp only [alg511CuffEdgeReflectionIndex]
  split_ifs <;> omega

/-- The actual edge permutation fixes ordinary edges and reverses
both blocks of cuff gaps. It is its own inverse. -/
@[expose] def alg511CuffEdgeReflection (m k : ℕ) : Equiv.Perm (Fin (m + (k + k))) where
  toFun j := ⟨alg511CuffEdgeReflectionIndex m k j.val, by exact cuffIndex_lt m k j.val j.isLt⟩
  invFun j := ⟨alg511CuffEdgeReflectionIndex m k j.val, by exact cuffIndex_lt m k j.val j.isLt⟩
  left_inv j := by exact Fin.ext (cuffIndex_involutive m k j.val j.isLt)
  right_inv j := by exact Fin.ext (cuffIndex_involutive m k j.val j.isLt)

/-- The inverse edge permutation has the same explicit three blocks. -/
theorem alg511CuffEdgeReflection_symm_val (m k : ℕ) (j : Fin (m + (k + k))) :
    ((alg511CuffEdgeReflection m k).symm j).val =
      if j.val < m then j.val else if j.val < m + k then
        m + (k - 1 - (j.val - m)) else m + k + (k - 1 - (j.val - (m + k))) := by
  rfl

/-- The cuff mask reads the actual edge's supplied original index.
Only the two appended cuff families reverse parameter direction. -/
@[expose] noncomputable def alg511CuffParameterMask
    {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (e : Set (OnePoint EuclideanPlane)) : Bool := by
  classical
  exact if he : e ∈ Γ.E then decide (m ≤ (edge.symm ⟨e, he⟩).val) else false

/-- At an indexed edge the mask tests precisely the cuff prefix
boundary, including the one-edge loop on a one-vertex cuff. -/
theorem alg511CuffParameterMask_edge
    {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (j : Fin (m + (k + k))) :
    alg511CuffParameterMask m k edge (edge j).val = decide (m ≤ j.val) := by
  classical
  unfold alg511CuffParameterMask
  rw [dite_eq_left (edge j).property, edge.symm_apply_apply]

/-- The two directed labels of each actual edge transform by
exactly the finite permutation computed by the reflection program. -/
theorem alg511_cuff_reflection_dart_labels
    {Γ : Drawing (OnePoint EuclideanPlane)} (m k : ℕ)
    (edge : Fin (m + (k + k)) ≃ Γ.E) (j : Fin (m + (k + k))) (b : Bool) :
    Compute.gm06Alg511ReflectAugmentedDart m k (2 * j.val + b.toNat) =
      2 * ((alg511CuffEdgeReflection m k).symm j).val +
        (alg511ReverseEnd (alg511CuffParameterMask m k edge (edge j).val) b).toNat := by
  rw [alg511CuffParameterMask_edge, alg511CuffEdgeReflection_symm_val]
  have hb : b.toNat < 2 := by cases b <;> decide
  by_cases hG : j.val < m
  · rw [Compute.gm06Alg511ReflectAugmentedDart_old (by omega : 2 * j.val + b.toNat < 2 * m)]
    simp only [hG, ite_true, decide_eq_false (by omega : ¬ m ≤ j.val),
      alg511ReverseEnd, Bool.false_eq_true, ite_false]
  · by_cases hI : j.val < m + k
    · have hi : j.val - m < k := by omega
      have he : 2 * j.val + b.toNat = 2 * (m + (j.val - m)) + b.toNat := by omega
      rw [he, Compute.gm06Alg511ReflectAugmentedDart_inner m k _ _ hi hb]
      simp only [hG, ite_false, hI, ite_true,
        decide_eq_true (by omega : m ≤ j.val), alg511ReverseEnd]
      cases b <;> rfl
    · have hi : j.val - (m + k) < k := by omega
      have he : 2 * j.val + b.toNat = 2 * (m + k + (j.val - (m + k))) + b.toNat := by omega
      rw [he, Compute.gm06Alg511ReflectAugmentedDart_outer m k _ _ hi hb]
      simp only [hG, ite_false, hI,
        decide_eq_true (by omega : m ≤ j.val), alg511ReverseEnd, ite_true]
      cases b <;> rfl

/-- Exchanging the cuff parameter ends and restoring the fixed gap
indices realizes the computed directed-label map on a positive row.
The original chart and all its spoke points are retained. -/
theorem alg511_positive_rotation_cuff_relabel
    {Γ : Drawing (OnePoint EuclideanPlane)} {m k : ℕ}
    (edge : Fin (m + (k + k)) ≃ Γ.E)
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) :
    GM06SuccessorRotationRowRep ((alg511CuffEdgeReflection m k).trans edge)
      (alg511ReverseEdgePar γ (alg511CuffParameterMask m k edge)) v
      (xs.map (Compute.gm06Alg511ReflectAugmentedDart m k)) := by
  exact alg511_positive_rotation_relabel edge γ (alg511CuffParameterMask m k edge)
    (alg511CuffEdgeReflection m k)
    ((Compute.gm06Alg511ReflectAugmentedDart_involutive m k).toPerm
      (Compute.gm06Alg511ReflectAugmentedDart m k))
    (alg511_cuff_reflection_dart_labels m k edge) hrow

/-- The full finite reflected row has the computed reversed order,
ordinary edge labels unchanged, and both cuff families reindexed
with their fixed increasing parameters. Its polar chart is positive. -/
theorem alg511_positive_rotation_reflected_cuffs (phase : ℝ)
    {Γ : Drawing (OnePoint EuclideanPlane)} {m k : ℕ}
    (edge : Fin (m + (k + k)) ≃ Γ.E)
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06SuccessorRotationRowRep edge γ v xs) :
    let H := (alg511PlaneReflection phase).onePointCongr
    let edge' := edge.trans (alg511ImageEdgeEquiv H Γ)
    GM06SuccessorRotationRowRep ((alg511CuffEdgeReflection m k).trans edge')
      (alg511ReverseEdgePar (alg511ImageEdgePar H γ) (alg511CuffParameterMask m k edge'))
      (H v) (xs.reverse.map (Compute.gm06Alg511ReflectAugmentedDart m k)) := by
  exact alg511_positive_rotation_cuff_relabel _ _ (alg511_positive_rotation_image phase hrow)

end GraphMinor.GM06
