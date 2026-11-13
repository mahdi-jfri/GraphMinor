module

public import GraphMinor.GM06.Alg57CyclicRowCut
public import GraphMinor.Compute.GM06SpliceRotations
import Mathlib.Tactic.IntervalCases

/-!
# The three source-row forms and their computed splice

In Reduction 3 of VI (5.7), page 133, the initial vertex has one
ordinary end and its two cuff ends. The positive order proved
geometrically leaves exactly three choices of the first label.
For each choice the finite splice replaces the ordinary end by
the target suffix and prefix in the same cyclic position. These
list calculations keep the permanent labels and also cover the
two distinct ends of a one-path cuff loop.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

private theorem cyclic_of_arg_lt {a b c : Circle}
    (hab : Complex.arg (a : ℂ) < Complex.arg (b : ℂ))
    (hbc : Complex.arg (b : ℂ) < Complex.arg (c : ℂ)) : CircleCyclic a b c := by
  have hlo := Complex.neg_pi_lt_arg (a : ℂ)
  have hhi := Complex.arg_le_pi (c : ℂ)
  have hh := circleCyclic_exp_of_lt hab hbc
    (show Complex.arg (c : ℂ) < Complex.arg (a : ℂ) + 2 * Real.pi by linarith only [hlo, hhi])
  simpa only [Circle.exp_arg] using hh

/-- A positive source row with its one ordinary end and two signed
cuff ends is exactly one of the three cyclic forms. -/
theorem three_end_source_row_forms
    {xs : List ℕ} {neg edge pos : ℕ} (hne : neg ≠ edge) (hnp : neg ≠ pos) (hep : edge ≠ pos)
    (hnd : xs.Nodup) (hmem : ∀ r, r ∈ xs ↔ r = neg ∨ r = edge ∨ r = pos)
    (z : ℕ → Circle)
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    (hcyclic : CircleCyclic (z neg) (z edge) (z pos)) :
    xs = [neg, edge, pos] ∨ xs = [edge, pos, neg] ∨ xs = [pos, neg, edge] := by
  have htrip : ([neg, edge, pos] : List ℕ).Nodup := by simp [hne, hnp, hep]
  have hperm : xs.Perm [neg, edge, pos] :=
    (List.perm_ext_iff_of_nodup hnd htrip).2 (fun r => by simpa using hmem r)
  have hlen : xs.length = 3 := hperm.length_eq
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  have ha := (hmem a).mp (by simp)
  have hb := (hmem b).mp (by simp)
  have hc := (hmem c).mp (by simp)
  have hab : Complex.arg (z a : ℂ) < Complex.arg (z b : ℂ) :=
    List.pairwise_iff_getElem.mp hs 0 1 (by simp) (by simp) (by decide)
  have hbc : Complex.arg (z b : ℂ) < Complex.arg (z c : ℂ) :=
    List.pairwise_iff_getElem.mp hs 1 2 (by simp) (by simp) (by decide)
  have horder := cyclic_of_arg_lt hab hbc
  rcases ha with rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl
  all_goals try simp_all only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_true_eq_false,
    false_and, and_false, not_false_eq_true, and_true, or_true, true_or]
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr rfl)
    | exact False.elim (not_circleCyclic_both hcyclic horder)
    | exact False.elim (not_circleCyclic_both hcyclic (circleCyclic_cycle horder))
    | exact False.elim (not_circleCyclic_both hcyclic (circleCyclic_cycle (circleCyclic_cycle horder)))

/-- In each of the three actual source-row forms, the computed
splice is the corresponding cyclic form of the retained target
row between the two cuff ends. -/
theorem spliced_three_end_source_row_forms
    {xs ys : List ℕ} {neg edge pos p q : ℕ}
    (hne : neg ≠ edge) (hep : edge ≠ pos)
    (hxs : xs = [neg, edge, pos] ∨ xs = [edge, pos, neg] ∨ xs = [pos, neg, edge])
    (hp : p < xs.length) (hget : xs[p] = edge) :
    gm06SplicedRotation xs ys p q = neg :: (ys.drop (q + 1) ++ ys.take q ++ [pos]) ∨
      gm06SplicedRotation xs ys p q = ys.drop (q + 1) ++ ys.take q ++ [pos, neg] ∨
      gm06SplicedRotation xs ys p q = pos :: neg :: (ys.drop (q + 1) ++ ys.take q) := by
  rcases hxs with rfl | rfl | rfl
  · have hp3 : p < 3 := hp
    interval_cases p
    · simp only [List.getElem_cons_zero] at hget
      exact False.elim (hne hget)
    · exact Or.inl (by simp [gm06SplicedRotation, List.append_assoc])
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hget
      exact False.elim (hep hget.symm)
  · have hp3 : p < 3 := hp
    interval_cases p
    · exact Or.inr (Or.inl (by simp [gm06SplicedRotation, List.append_assoc]))
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hget
      exact False.elim (hep hget.symm)
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hget
      exact False.elim (hne hget)
  · have hp3 : p < 3 := hp
    interval_cases p
    · simp only [List.getElem_cons_zero] at hget
      exact False.elim (hep hget.symm)
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero] at hget
      exact False.elim (hne hget)
    · exact Or.inr (Or.inr (by simp [gm06SplicedRotation, List.append_assoc]))


/-- Each finite splice form is a cyclic shift of the retained
block between the negative and positive cuff words. -/
theorem three_cuff_forms_perm
    {xs tail : List ℕ} {neg pos : ℕ}
    (hforms : xs = neg :: (tail ++ [pos]) ∨ xs = tail ++ [pos, neg] ∨ xs = pos :: neg :: tail) :
    xs.Perm (neg :: (tail ++ [pos])) := by
  rcases hforms with rfl | rfl | rfl
  · exact List.Perm.refl _
  · have hh : (neg :: (tail ++ [pos])).rotate 1 = tail ++ [pos, neg] := by
      simp [List.rotate_cons_succ, List.append_assoc]
    rw [← hh]
    exact List.rotate_perm _ _
  · change ([pos] ++ (neg :: tail)).Perm ((neg :: tail) ++ [pos])
    exact List.perm_append_comm

/-- The proved polar order of the retained block between the cuff
ends gives the positive permanent-row interpretation of every
numeric source splice form. All ray and rim labels are kept. -/
theorem persistent_rotation_row_of_three_cuff_forms
    {Γ : Drawing (OnePoint EuclideanPlane)} (label : Γ.E ↪ ℕ)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ p Φ) (hpos : GM06PositivePolar Φ)
    {xs tail : List ℕ} {neg pos : ℕ}
    (hforms : xs = neg :: (tail ++ [pos]) ∨ xs = tail ++ [pos, neg] ∨ xs = pos :: neg :: tail)
    (z : ℕ → Circle) (hnd : xs.Nodup)
    (hmem : ∀ r, r ∈ xs ↔ ∃ a : halfEdges Γ γ p, gm06PersistentHalfEdgeLabel label a = r)
    (hi : InjOn z {r | r ∈ xs})
    (hblock : tail.Pairwise (fun a b => CircleCyclic (z neg) (z a) (z b)))
    (hlast : ∀ a ∈ tail, CircleCyclic (z neg) (z a) (z pos))
    (hspoke : ∀ a : halfEdges Γ γ p, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (z (gm06PersistentHalfEdgeLabel label a))) ∈ range (spoke γ a.val))
    (hlabel : ∀ (f : Γ.E) (w : Circle), polarRimMap Φ w ∈ f.val ↔
      ∃ r ∈ xs, z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1)) :
    GM06PersistentRotationRowRep label γ p xs := by
  let canonical := neg :: (tail ++ [pos])
  have hperm : xs.Perm canonical := three_cuff_forms_perm hforms
  have hcmem (r : ℕ) : r ∈ canonical ↔ r ∈ xs := hperm.mem_iff.symm
  have hcnd : canonical.Nodup := hperm.nodup_iff.mp hnd
  have hci : InjOn z {r | r ∈ canonical} := fun _ ha _ hb heq =>
    hi ((hcmem _).mp ha) ((hcmem _).mp hb) heq
  have horder : canonical.Pairwise (fun a b =>
      a = neg ∨ CircleCyclic (z neg) (z a) (z b)) := by
    apply List.pairwise_cons.mpr
    refine ⟨fun _ _ => Or.inl rfl, ?_⟩
    apply List.pairwise_append.mpr
    refine ⟨List.Pairwise.imp (fun h => Or.inr h) hblock, by simp, ?_⟩
    intro a ha b hb
    have hb' : b = pos := List.mem_singleton.mp hb
    subst b
    exact Or.inr (hlast a ha)
  have hclabel (f : Γ.E) (w : Circle) : polarRimMap Φ w ∈ f.val ↔
      ∃ r ∈ canonical, z r = w ∧ (r = 2 * label f ∨ r = 2 * label f + 1) := by
    rw [hlabel]
    simp only [hcmem]
  have hcanon : GM06PersistentRotationRowRep label γ p canonical :=
    persistent_rotation_row_of_cyclic_order label hp hpos neg (tail ++ [pos]) z hcnd
      (fun r => (hcmem r).trans (hmem r)) hci horder hspoke hclabel
  rcases hforms with rfl | rfl | rfl
  · exact hcanon
  · have hh := hcanon.rotate 1
    simpa only [canonical, List.rotate_cons_succ, List.rotate_zero, List.cons_append,
      List.append_assoc, List.nil_append] using hh
  · have hh := hcanon.rotate (neg :: tail).length
    change GM06PersistentRotationRowRep label γ p
      (((neg :: tail) ++ [pos]).rotate (neg :: tail).length) at hh
    rw [List.rotate_append_length_eq] at hh
    exact hh

end GraphMinor.GM06
