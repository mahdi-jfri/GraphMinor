module

public import GraphMinor.Compute.GM06SelectedIncidenceProgram
public import GraphMinor.Compute.GM06CutDataProgram

/-!
# Incidence queries on permanent cut graph labels

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) applies face
selection to the cut components while retaining copied labels. This
file converts bounded list labels to finite darts, proves that the
conversion preserves the represented rotations and active ends, and
transfers the selected-incidence program to that list interface.
The reverse inner cuff dart is computed from the original edge base
and component index, rather than supplied as an output certificate.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Retain finite labels with their bound proofs, preserving list order. -/
def gm06FinLabels (q : ℕ) (labels : List ℕ) : List (Fin q) :=
  labels.filterMap (fun d => if h : d < q then some ⟨d, h⟩ else none)

/-- Properly bounded input labels are unchanged by finite-label conversion. -/
theorem gm06FinLabels_map_val (q : ℕ) (labels : List ℕ) (h : ∀ d ∈ labels, d < q) :
    (gm06FinLabels q labels).map Fin.val = labels := by
  induction labels with
  | nil => rfl
  | cons d labels ih =>
    have hd := h d List.mem_cons_self
    have ht := ih (fun e he => h e (List.mem_cons_of_mem _ he))
    simp only [gm06FinLabels, List.filterMap_cons, hd, ↓reduceDIte, List.map_cons]
    exact congrArg (d :: ·) ht

/-- Membership is preserved at every valid finite label. -/
theorem gm06FinLabels_mem_iff {q : ℕ} (labels : List ℕ) (h : ∀ d ∈ labels, d < q) (d : Fin q) :
    d ∈ gm06FinLabels q labels ↔ d.val ∈ labels := by
  calc
    _ ↔ d.val ∈ (gm06FinLabels q labels).map Fin.val := (List.mem_map_of_injective Fin.val_injective).symm
    _ ↔ d.val ∈ labels := by rw [gm06FinLabels_map_val q labels h]

/-- The exact selected-face/incidence query on ordinary cut-data lists. -/
def gm06CutFaceIncidence (n m : ℕ) (data : GM06CutData) (reverseInner : ℕ) :
    Option (List ℕ × List ℕ × List ℕ) :=
  if h : reverseInner < 2 * m then
    gm06SelectedFaceIncidence n data.origins (data.rotations.map (gm06FinLabels (2 * m)))
      (gm06FinLabels (2 * m) data.activeDarts) ⟨reverseInner, h⟩
  else none

/-- Reverse copied inner cuff dart at original base 672 and gap index 673. -/
def gm06ReverseInnerCuffExpr : Expr :=
  .op .add (.op .mul (.const 4) (.op .add (.reg 672) (.reg 673))) (.const 1)

/-- Every address operation for the reverse inner cuff dart is in range. -/
theorem gm06ReverseInnerCuffExpr_eval {w base i : ℕ} (s : State)
    (hw : 4 < 2 ^ w) (hfit : 4 * (base + i) + 1 < 2 ^ w)
    (h672 : s.regs 672 = base) (h673 : s.regs 673 = i) :
    gm06ReverseInnerCuffExpr.eval w s = some (4 * (base + i) + 1) := by
  exact GraphMinor.Compute.Crossing.eval_add
    (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h672 (by omega))
        (GraphMinor.Compute.Crossing.eval_reg h673 (by omega)) (by omega)) (by omega))
    (GraphMinor.Compute.Crossing.eval_const (by omega)) hfit

/-- Compute the reverse inner cuff dart, then its face row and incidence. -/
def gm06CutFaceIncidenceProg : Cmd :=
  .seq (.assign 667 gm06ReverseInnerCuffExpr) gm06SelectedIncidenceProg

/-- Exact incidence on the list representation of a cut component.
The hypotheses specify its finite graph encoding, not a selected face
or any intermediate table. -/
theorem gm06CutFaceIncidenceProg_exec {w n m base i : ℕ} (data : GM06CutData) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hcap : 1 + 2 * (2 * m) < 2 ^ w)
    (hnd : data.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts)
    (horigLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hquery : 4 * (base + i) + 1 < 2 * m)
    (hcode : (gm06EncodeRows data.rotations).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows data.rotations, x < 2 ^ w)
    (hl : data.activeDarts.length < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows data.rotations) (h604 : s.arrs 604 = data.activeDarts)
    (h626 : s.arrs 626 = data.origins) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m)
    (h672 : s.regs 672 = base) (h673 : s.regs 673 = i) :
    ∃ sf t, Exec w gm06CutFaceIncidenceProg s sf t ∧
      t ≤ 172 + n + m + 221 * (2 * m) + 29 * data.rotations.length + 37 * data.rotations.flatten.length +
        data.activeDarts.length * (40 + 18 * (2 * m)) ∧
      Keeps (667 :: gm06SelectedIncidenceRegs) [600, 601, 602, 603, 604, 605, 606, 607] s sf ∧
      gm06SelectedIncidenceResult sf = gm06CutFaceIncidence n m data (4 * (base + i) + 1) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hq : 2 * m < 2 ^ w := by omega
  let rotations := data.rotations.map (gm06FinLabels (2 * m))
  let active := gm06FinLabels (2 * m) data.activeDarts
  have hrotations : rotations.map (List.map Fin.val) = data.rotations := by
    simp only [rotations, List.map_map]
    calc
      _ = data.rotations.map id := by
        apply List.map_congr_left
        intro row hr
        exact gm06FinLabels_map_val _ row (fun d hd => hkeys d (List.mem_flatten.mpr ⟨row, hr, hd⟩))
      _ = _ := List.map_id _
  have hactiveMap : active.map Fin.val = data.activeDarts := gm06FinLabels_map_val _ _ hactive
  have hrotFlatten : rotations.flatten.map Fin.val = data.rotations.flatten := by
    rw [List.map_flatten, hrotations]
  have hndFin : rotations.flatten.Nodup := List.Nodup.of_map Fin.val (hrotFlatten ▸ hnd)
  have hcoverFin : ∀ d, d ∈ active ↔ d ∈ rotations.flatten := by
    intro d
    rw [← List.mem_map_of_injective Fin.val_injective, hactiveMap,
      ← List.mem_map_of_injective Fin.val_injective, hrotFlatten]
    exact hcover d.val
  have hpairFin : ∀ d ∈ active, gm06DartReversal m d ∈ active := by
    intro d hd
    apply (gm06FinLabels_mem_iff data.activeDarts hactive (gm06DartReversal m d)).mpr
    exact hpair d.val ((gm06FinLabels_mem_iff data.activeDarts hactive d).mp hd)
  let origin : Fin (2 * m) → Fin n := fun d =>
    ⟨data.origins[d.val]'(by rw [horigLen]; exact d.isLt), hvalues _ (List.getElem_mem _)⟩
  have horgFn : List.ofFn (fun d => (origin d).val) = data.origins := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, horigLen]
    · intro j hj hj'
      simp only [List.getElem_ofFn, origin]
  let s₀ := s.setReg 667 (4 * (base + i) + 1)
  have he₀ : Exec w (.assign 667 gm06ReverseInnerCuffExpr) s s₀ 8 :=
    .assign (gm06ReverseInnerCuffExpr_eval s hw (hquery.trans hq) h672 h673)
  obtain ⟨sf, tf, hef, htf, hkf, houtf⟩ := gm06SelectedIncidenceProg_exec origin rotations active
    ⟨4 * (base + i) + 1, hquery⟩ s₀ hndFin hcoverFin hpairFin hw2 hn hcap
    (by simpa only [hrotations] using hcode) (by simpa only [hrotations] using hwords)
    (by have heq := congrArg List.length hactiveMap; simp only [List.length_map] at heq; omega)
    (by simpa only [hrotations, s₀, State.setReg_arrs] using h600)
    (by simpa only [hactiveMap, s₀, State.setReg_arrs] using h604)
    (by simpa only [horgFn, s₀, State.setReg_arrs] using h626)
    (by simpa [s₀] using h648) (by simpa [s₀] using h649) (by simp [s₀])
  have hrotLen : rotations.length = data.rotations.length := List.length_map _
  have hflatLen : rotations.flatten.length = data.rotations.flatten.length := by
    simpa only [List.length_map] using congrArg List.length hrotFlatten
  have hactLen : active.length = data.activeDarts.length := by
    simpa only [List.length_map] using congrArg List.length hactiveMap
  refine ⟨sf, 8 + tf, .seq he₀ hef, ?_,
    ((Keeps.refl _ _ s).setReg (by simp) _).trans hkf
      (by intro r hr; exact List.mem_cons_of_mem _ hr) (fun _ h => h), ?_⟩
  · rw [hrotLen, hflatLen, hactLen] at htf
    omega
  · simpa only [gm06CutFaceIncidence, hquery, ↓reduceDIte, horgFn] using houtf

/-- A uniform quadratic bound includes the actual reverse-cuff address calculation. -/
theorem gm06CutFaceIncidence_cost_le_polynomial (n m r d a : ℕ) :
    172 + n + m + 221 * (2 * m) + 29 * r + 37 * d + a * (40 + 18 * (2 * m)) ≤
      1100 * (n + 2 * m + r + d + a + 1) ^ 2 := by
  have h := gm06SelectedIncidence_cost_le_polynomial n m r d a
  have hN : 1 ≤ (n + 2 * m + r + d + a + 1) ^ 2 := by
    have hn : 1 ≤ n + 2 * m + r + d + a + 1 := by omega
    exact one_le_pow₀ hn
  omega

end GraphMinor.Compute
