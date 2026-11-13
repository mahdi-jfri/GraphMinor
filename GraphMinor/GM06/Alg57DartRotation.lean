module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Finite rotation systems and their face orbits

The algorithm (5.7) of Graph Minors VI, page 133, works on a drawing through its rotation rows. Our
proof of it (outlined in `Alg57Algorithm.lean`) reads them as a finite set of darts, that is,
directed edge ends. A dart `d` has its reverse `rev d` and the next dart `rot d` counterclockwise
around its vertex. The boundary of a face is then traced by the permutation
`face d = rot⁻¹ (rev d)`, formula (1) of that proof.

This file sets up these objects with no geometry. Vertices, edges and faces are the orbits of
`rot`, `rev` and `face`. The main result is the counting bound of a connected rotation system:
`#faces + #vertices ≤ #edges + 2`. In the proof of Lemma 3 it is compared with Euler's formula
for the drawing, and this makes the map from face orbits to regions a bijection.

The proof is linear algebra over `ZMod 2`. Let `M` be the vertex-edge incidence matrix. Its
transpose has kernel the constant functions, by connectivity, so `M` has rank at least
`#vertices - 1`. Each set of faces gives the set of edges with its two sides on different sides
of the set. At every vertex this set of edges has even degree, since going around the vertex
the side changes an even number of times. So these cuts lie in the kernel of `M`, and only the
constant sets of faces give the empty cut.
-/

@[expose] public section

namespace GraphMinor.GM06

open Equiv

universe u

/-- A finite rotation system: darts with the reversal `rev` and the counterclockwise rotation
`rot` around their vertex. Both darts of a loop are distinct darts. This is the data `τ` and
`σ` of Section 1 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`). -/
structure DartRotation (D : Type u) where
  /-- The next dart counterclockwise around the same vertex, `σ` in our proof of (5.7). -/
  rot : Perm D
  /-- The reverse of a dart, `τ` in our proof of (5.7). -/
  rev : Perm D
  rev_rev : ∀ d, rev (rev d) = d
  rev_ne : ∀ d, rev d ≠ d

namespace DartRotation

variable {D : Type u} (R : DartRotation D)

/-- The successor along a face boundary, with the face on the left: `φ = σ⁻¹ τ`, as in our
proof of (5.7). -/
def face : Perm D := R.rev.trans R.rot.symm

theorem face_apply (d : D) : R.face d = R.rot.symm (R.rev d) := rfl

/-- The darts are connected by rotation and reversal steps. -/
def Connected : Prop :=
  ∀ a b : D, Relation.ReflTransGen (fun x y => y = R.rot x ∨ y = R.rev x) a b

/-- The vertices: orbits of the rotation. -/
abbrev Vertices : Type u := Quotient (Perm.SameCycle.setoid R.rot)

/-- The edges: orbits of the reversal. -/
abbrev Edges : Type u := Quotient (Perm.SameCycle.setoid R.rev)

/-- The faces: orbits of `face`. -/
abbrev Faces : Type u := Quotient (Perm.SameCycle.setoid R.face)

/-- The vertex of a dart. -/
abbrev vertexOf (d : D) : R.Vertices := Quotient.mk _ d

/-- The edge of a dart. -/
abbrev edgeOf (d : D) : R.Edges := Quotient.mk _ d

/-- The face of a dart. -/
abbrev faceOf (d : D) : R.Faces := Quotient.mk _ d

theorem vertexOf_rot (d : D) : R.vertexOf (R.rot d) = R.vertexOf d :=
  Quotient.sound (show Perm.SameCycle R.rot (R.rot d) d from
    (Perm.SameCycle.refl R.rot d).apply_left)

theorem vertexOf_rot_symm (d : D) : R.vertexOf (R.rot.symm d) = R.vertexOf d := by
  have h := R.vertexOf_rot (R.rot.symm d)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem edgeOf_rev (d : D) : R.edgeOf (R.rev d) = R.edgeOf d :=
  Quotient.sound (show Perm.SameCycle R.rev (R.rev d) d from
    (Perm.SameCycle.refl R.rev d).apply_left)

theorem faceOf_face (d : D) : R.faceOf (R.face d) = R.faceOf d :=
  Quotient.sound (show Perm.SameCycle R.face (R.face d) d from
    (Perm.SameCycle.refl R.face d).apply_left)

/-- Around a vertex, the clockwise neighbour of a dart lies in the face of its reverse:
`φ (τ d) = σ⁻¹ d`. -/
theorem faceOf_rot_symm (d : D) : R.faceOf (R.rot.symm d) = R.faceOf (R.rev d) := by
  have h := R.faceOf_face (R.rev d)
  rwa [face_apply, R.rev_rev] at h

theorem rev_pow_apply (n : ℕ) (d : D) : (R.rev ^ n) d = d ∨ (R.rev ^ n) d = R.rev d := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply]
    rcases ih with h | h
    · rw [h]; exact Or.inr rfl
    · rw [h, R.rev_rev]; exact Or.inl rfl

/-- The two darts of an edge are its only darts. -/
theorem edgeOf_eq_iff [Finite D] {d d' : D} :
    R.edgeOf d' = R.edgeOf d ↔ d' = d ∨ d' = R.rev d := by
  constructor
  · intro h
    have hs : Perm.SameCycle R.rev d d' := (Quotient.exact h).symm
    obtain ⟨i, -, hi⟩ := hs.exists_pow_eq'
    rcases R.rev_pow_apply i d with h' | h'
    · exact Or.inl (hi ▸ h')
    · exact Or.inr (hi ▸ h')
  · rintro (rfl | rfl)
    · rfl
    · exact R.edgeOf_rev d

/-- A function constant along rotation and reversal steps is constant on a connected rotation
system. -/
theorem eq_of_invariant {β : Type*} (hc : R.Connected) {g : D → β}
    (hrot : ∀ d, g (R.rot d) = g d) (hrev : ∀ d, g (R.rev d) = g d) (a b : D) : g a = g b := by
  induction hc a b with
  | refl => rfl
  | tail _ hyz ih =>
    rcases hyz with rfl | rfl
    · rw [hrot]; exact ih
    · rw [hrev]; exact ih

section Count

open Matrix Module

open scoped Classical

variable [Fintype D]

private noncomputable instance : Fintype R.Vertices := Fintype.ofFinite _
private noncomputable instance : Fintype R.Edges := Fintype.ofFinite _
private noncomputable instance : Fintype R.Faces := Fintype.ofFinite _

/-- A sum over the darts of the edge of `d` has two terms. -/
private theorem sum_edge (g : D → ZMod 2) (d : D) {P : D → Prop} {dP : DecidablePred P}
    (hP : ∀ d', P d' ↔ R.edgeOf d' = R.edgeOf d) :
    (∑ d', if P d' then g d' else 0) = g d + g (R.rev d) := by
  rw [← Finset.sum_filter]
  have hfil : Finset.univ.filter P = {d, R.rev d} := by
    ext d'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, hP]
    exact R.edgeOf_eq_iff
  rw [hfil, Finset.sum_pair (R.rev_ne d).symm]

/-- The vertex-edge incidence matrix over `ZMod 2`. -/
private noncomputable def incid : Matrix R.Vertices R.Edges (ZMod 2) :=
  fun v e => ∑ d, if R.vertexOf d = v ∧ R.edgeOf d = e then 1 else 0

/-- The edge-face incidence matrix over `ZMod 2`. -/
private noncomputable def cut : Matrix R.Edges R.Faces (ZMod 2) :=
  fun e f => ∑ d, if R.edgeOf d = e ∧ R.faceOf d = f then 1 else 0

private theorem sum_incid {α : Type*} [Fintype α] (k : D → α) (Q : D → α → Prop)
    {dQ : ∀ d a, Decidable (Q d a)} (P : D → Prop) {dP : DecidablePred P}
    (hQ : ∀ d a, Q d a ↔ P d ∧ k d = a) (z : α → ZMod 2) :
    (∑ a, (∑ d, if Q d a then (1 : ZMod 2) else 0) * z a) =
      ∑ d, if P d then z (k d) else 0 := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hP : P d
  · rw [Finset.sum_eq_single (k d)]
    · simp [(hQ d (k d)).2 ⟨hP, rfl⟩, hP]
    · intro a _ ha
      have : ¬ Q d a := fun h => ha ((hQ d a).1 h).2.symm
      simp [this]
    · simp
  · simp only [hP, ↓reduceIte]
    refine Finset.sum_eq_zero fun a _ => ?_
    have : ¬ Q d a := fun h => hP ((hQ d a).1 h).1
    simp [this]

private theorem transpose_mulVec_apply (z : R.Vertices → ZMod 2) (d : D) :
    ((R.incid)ᵀ *ᵥ z) (R.edgeOf d) = z (R.vertexOf d) + z (R.vertexOf (R.rev d)) := by
  simp only [mulVec, dotProduct, transpose_apply, incid]
  rw [sum_incid R.vertexOf _ (fun d' => R.edgeOf d' = R.edgeOf d) (fun _ _ => and_comm) z]
  exact R.sum_edge (fun d' => z (R.vertexOf d')) d (fun _ => Iff.rfl)

private theorem cut_mulVec_apply (y : R.Faces → ZMod 2) (d : D) :
    (R.cut *ᵥ y) (R.edgeOf d) = y (R.faceOf d) + y (R.faceOf (R.rev d)) := by
  simp only [mulVec, dotProduct, cut]
  rw [sum_incid R.faceOf _ (fun d' => R.edgeOf d' = R.edgeOf d) (fun _ _ => Iff.rfl) y]
  exact R.sum_edge (fun d' => y (R.faceOf d')) d (fun _ => Iff.rfl)

private theorem incid_mul_cut : R.incid * R.cut = 0 := by
  ext v f
  simp only [mul_apply, incid, cut, Matrix.zero_apply]
  rw [sum_incid R.edgeOf _ (fun d => R.vertexOf d = v) (dP := inferInstance) (fun _ _ => Iff.rfl)]
  have hpair : ∀ d, (∑ d', if R.edgeOf d' = R.edgeOf d ∧ R.faceOf d' = f then (1 : ZMod 2)
      else 0) = (if R.faceOf d = f then 1 else 0) +
        (if R.faceOf (R.rot.symm d) = f then 1 else 0) := by
    intro d
    rw [R.faceOf_rot_symm]
    rw [← R.sum_edge (fun d' => if R.faceOf d' = f then (1 : ZMod 2) else 0) d (dP := inferInstance)
      (fun _ => Iff.rfl)]
    refine Finset.sum_congr rfl fun d' _ => ?_
    by_cases h1 : R.edgeOf d' = R.edgeOf d
    · simp [h1]
    · simp [h1]
  simp only [hpair]
  rw [← Finset.sum_filter, Finset.sum_add_distrib]
  have hre : (∑ d ∈ Finset.univ.filter (fun d => R.vertexOf d = v),
      (if R.faceOf (R.rot.symm d) = f then (1 : ZMod 2) else 0)) =
      ∑ d ∈ Finset.univ.filter (fun d => R.vertexOf d = v),
        (if R.faceOf d = f then (1 : ZMod 2) else 0) := by
    refine Finset.sum_nbij' (fun d => R.rot.symm d) (fun d => R.rot d) ?_ ?_ ?_ ?_ ?_
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      rw [R.vertexOf_rot_symm, hd]
    · intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
      rw [R.vertexOf_rot, hd]
    · intro d _
      simp
    · intro d _
      simp
    · intro d _
      rfl
  rw [hre, ← two_mul]
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [h2, zero_mul]

private theorem zmod_two_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have : a = -b := eq_neg_of_add_eq_zero_left h
  rwa [ZMod.neg_eq_self_mod_two] at this

private theorem finrank_le_one_of_const {α : Type*} [Fintype α]
    (W : Submodule (ZMod 2) (α → ZMod 2)) (hW : ∀ z ∈ W, ∀ a b, z a = z b) :
    finrank (ZMod 2) W ≤ 1 := by
  have hle : W ≤ Submodule.span (ZMod 2) {fun _ => (1 : ZMod 2)} := by
    intro z hz
    by_cases hα : Nonempty α
    · obtain ⟨a₀⟩ := hα
      rw [Submodule.mem_span_singleton]
      refine ⟨z a₀, funext fun a => ?_⟩
      simp [hW z hz a₀ a]
    · have : z = 0 := funext fun a => (hα ⟨a⟩).elim
      rw [this]
      exact Submodule.zero_mem _
  exact (Submodule.finrank_mono hle).trans (finrank_span_le_card _ |>.trans (by simp))

/-- **Counting bound for a connected rotation system.** For a connected finite rotation
system, `#faces + #vertices ≤ #edges + 2`. Compared with Euler's formula for a drawing in the
sphere, this is the count behind Lemma 3 of our proof of VI (5.7) (outlined in
`Alg57Algorithm.lean`). -/
theorem card_faces_add_card_vertices_le (hc : R.Connected) :
    Nat.card R.Faces + Nat.card R.Vertices ≤ Nat.card R.Edges + 2 := by
  let M := R.incid
  let N := R.cut
  have h1 := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
  have h3 := LinearMap.finrank_range_add_finrank_ker N.mulVecLin
  rw [finrank_fintype_fun_eq_card] at h1 h2 h3
  have hrank : finrank (ZMod 2) (LinearMap.range Mᵀ.mulVecLin) =
      finrank (ZMod 2) (LinearMap.range M.mulVecLin) :=
    rank_transpose M
  have hkerT : finrank (ZMod 2) (LinearMap.ker Mᵀ.mulVecLin) ≤ 1 := by
    refine finrank_le_one_of_const _ fun z hz a b => ?_
    rw [LinearMap.mem_ker, mulVecLin_apply] at hz
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    refine R.eq_of_invariant hc (g := fun d => z (R.vertexOf d)) (fun d => ?_) (fun d => ?_) a b
    · exact congrArg z (R.vertexOf_rot d)
    · have h := congrFun hz (R.edgeOf d)
      rw [R.transpose_mulVec_apply] at h
      exact (zmod_two_eq_of_add_eq_zero h).symm
  have hkerN : finrank (ZMod 2) (LinearMap.ker N.mulVecLin) ≤ 1 := by
    refine finrank_le_one_of_const _ fun y hy a b => ?_
    rw [LinearMap.mem_ker, mulVecLin_apply] at hy
    have hrev : ∀ d, y (R.faceOf (R.rev d)) = y (R.faceOf d) := fun d => by
      have h := congrFun hy (R.edgeOf d)
      rw [R.cut_mulVec_apply] at h
      exact (zmod_two_eq_of_add_eq_zero h).symm
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    refine R.eq_of_invariant hc (g := fun d => y (R.faceOf d)) (fun d => ?_) hrev a b
    have h := R.faceOf_rot_symm (R.rot d)
    rw [Equiv.symm_apply_apply] at h
    show y (R.faceOf (R.rot d)) = y (R.faceOf d)
    rw [← hrev (R.rot d), ← h]
  have hcut : LinearMap.range N.mulVecLin ≤ LinearMap.ker M.mulVecLin := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, mulVec_mulVec]
    change (R.incid * R.cut) *ᵥ y = 0
    rw [R.incid_mul_cut, zero_mulVec]
  have h4 := Submodule.finrank_mono hcut
  simp only [Nat.card_eq_fintype_card]
  omega

end Count

end DartRotation

end GraphMinor.GM06
