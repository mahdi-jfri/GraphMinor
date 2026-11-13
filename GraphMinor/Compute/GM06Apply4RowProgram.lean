module

public import GraphMinor.Compute.GM06Reduction4Finite
public import GraphMinor.Compute.GM06CutRotations
public import GraphMinor.Compute.GM06WordRows
public import GraphMinor.Compute.GM13SocietyTabulate
import GraphMinor.Compute.CrossingOpsReplLists
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# Copying the projected Reduction 4 replacement and retained suffix

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) replaces the
old prefix by the projected directed candidate path. Copied edge labels
have two consecutive copy slots, each with two directed ends. Projection
forgets the copy slot and keeps the direction. This program computes
that map, copies the old edge suffix after the contact and concatenates
the two rows. The graph and its rotation rows are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Forget a copied edge's side while retaining its directed end. -/
def gm06ProjectCutDart (d : ℕ) : ℕ := 2 * (d / 4) + d % 2

/-- Projection is a left inverse of either directed ordinary-edge copy. -/
theorem gm06ProjectCutDart_cutDart (d tag : ℕ) (htag : tag ≤ 1) :
    gm06ProjectCutDart (gm06CutDart d tag) = d := by
  have hm := Nat.mod_lt d (by decide : 0 < 2)
  have hd := Nat.mod_add_div d 2
  unfold gm06ProjectCutDart gm06CutDart
  omega

/-- Projection never increases a permanent dart label. -/
theorem gm06ProjectCutDart_le (d : ℕ) : gm06ProjectCutDart d ≤ d := by
  have h₄ := Nat.mod_add_div d 4
  have h₂ := Nat.mod_add_div d 2
  have hm₄ := Nat.mod_lt d (by decide : 0 < 4)
  have hm₂ := Nat.mod_lt d (by decide : 0 < 2)
  unfold gm06ProjectCutDart
  omega

/-- Word arithmetic for the directed copy projection. -/
def gm06ProjectCutDartExpr (d : Expr) : Expr :=
  .op .add (.op .mul (.const 2) (.op .div d (.const 4))) (.op .mod d (.const 2))

/-- The projection expression and every intermediate value are exact. -/
theorem gm06ProjectCutDartExpr_eval {w d : ℕ} (D : Expr) (s : State)
    (hw : 4 < 2 ^ w) (hd : D.eval w s = some d) :
    (gm06ProjectCutDartExpr D).eval w s = some (gm06ProjectCutDart d) := by
  have hdWord := Expr.eval_lt hd
  have hdiv := GraphMinor.Compute.Crossing.eval_div hd (GraphMinor.Compute.Crossing.eval_const hw)
    (by decide) (by omega)
  have hmod := GraphMinor.Compute.Crossing.eval_mod hd (GraphMinor.Compute.Crossing.eval_const (by omega : 2 < 2 ^ w))
    (by decide)
  have hproj := gm06ProjectCutDart_le d
  exact GraphMinor.Compute.Crossing.eval_add
    (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const (by omega : 2 < 2 ^ w)) hdiv
      (by unfold gm06ProjectCutDart at hproj; omega)) hmod (hproj.trans_lt hdWord)

/-- Project the candidate row, copy the old suffix and join both rows. -/
def gm06Apply4RowProg : Cmd :=
  .seq (gm13TabulateProg 650 (.len 635) (gm06ProjectCutDartExpr (.read 635 (.reg 650))) 613)
    (.seq (gm13TabulateProg 650 (.op .sub (.len 610) (.reg 678))
      (.read 610 (.op .add (.reg 678) (.reg 650))) 611)
      (gm06ConcatWordsProg 613 611 637))

/-- The exact row splice of APPLY_4 is computed in linear time from
its candidate darts, old linkage row and contact position. -/
theorem gm06Apply4RowProg_exec {w j : ℕ} (replacement old : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hfit : replacement.length + old.length + 2 < 2 ^ w) (hj : j ≤ old.length)
    (hnew : ∀ d ∈ replacement, d < 2 ^ w) (hold : ∀ d ∈ old, d < 2 ^ w)
    (h635 : s.arrs 635 = replacement) (h610 : s.arrs 610 = old) (h678 : s.regs 678 = j) :
    ∃ sf t, Exec w gm06Apply4RowProg s sf t ∧ t ≤ 40 + 50 * (replacement.length + old.length) ∧
      Keeps [650, 651, 652, 655] [613, 611, 637] s sf ∧
      sf.arrs 637 = gm06Apply4Row gm06ProjectCutDart replacement old j := by
  let projected := replacement.map gm06ProjectCutDart
  have hpLen : projected.length = replacement.length := List.length_map _
  have hpWords : ∀ d ∈ projected, d < 2 ^ w := by
    intro d hd
    obtain ⟨dart, hmem, rfl⟩ := List.mem_map.mp hd
    exact (gm06ProjectCutDart_le dart).trans_lt (hnew dart hmem)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩  := gm13TabulateProg_exec (w := w)
    650 (.len 635) (gm06ProjectCutDartExpr (.read 635 (.reg 650))) 613 projected s (by omega) (by rw [hpLen]; omega)
    (fun st hk => by
      rw [hpLen]
      exact GraphMinor.Compute.Crossing.eval_len ((hk.2 635 (by decide)).trans h635) (by omega))
    (fun st i hi hk hr => by
      have hi' : i < replacement.length := hpLen ▸ hi
      have ha := (hk.2 635 (by decide)).trans h635
      have he := GraphMinor.Compute.Crossing.eval_read (a := 635)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
        (by simpa only [ha] using hi') (by simpa only [ha] using hnew _ (List.getElem_mem hi'))
      simpa only [projected, List.getElem_map, ha] using gm06ProjectCutDartExpr_eval _ st hw he)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩  := gm13TabulateProg_exec (w := w)
    650 (.op .sub (.len 610) (.reg 678)) (.read 610 (.op .add (.reg 678) (.reg 650))) 611
    (old.drop j) s₁ (by omega) (by rw [List.length_drop]; omega)
    (fun st hk => by
      rw [List.length_drop]
      exact GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len ((hk.2 610 (by decide)).trans ((hk₁.2 610 (by decide)).trans h610)) (by omega))
        (GraphMinor.Compute.Crossing.eval_reg (w := w) ((hk.1 678 (by decide)).trans ((hk₁.1 678 (by decide)).trans h678)) (by omega)))
    (fun st i hi hk hr => by
      have hi' : i < old.length - j := by simpa only [List.length_drop] using hi
      have hidx : j + i < old.length := by omega
      have ha := (hk.2 610 (by decide)).trans ((hk₁.2 610 (by decide)).trans h610)
      have he := GraphMinor.Compute.Crossing.eval_read (a := 610)
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (w := w) ((hk.1 678 (by decide)).trans ((hk₁.1 678 (by decide)).trans h678)) (by omega))
          (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega)) (by omega))
        (by simpa only [ha] using hidx) (by simpa only [ha] using hold _ (List.getElem_mem hidx))
      simpa only [ha, List.getElem_drop, Nat.add_comm] using he)
  have hk₁₂ : Keeps [650] [613, 611] s s₂ :=
    (hk₁.mono (fun _ h => h) (by simp)).trans hk₂ (fun _ h => h) (by simp)
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06ConcatWordsProg_exec (by decide : 613 ≠ 637) (by decide : 611 ≠ 637)
    projected (old.drop j) s₂ (by omega) (by rw [hpLen, List.length_drop]; omega) hpWords
    (fun d hd => hold d (List.mem_of_mem_drop hd)) ((hk₂.2 613 (by decide)).trans hd₁) hd₂
  refine ⟨sf, t₁ + (t₂ + tf), .seq he₁ (.seq he₂ hef), ?_,
    (hk₁₂.mono (by simp) (by simp)).trans hkf (fun _ h => h) (by simp), hdf⟩
  simp only [Expr.cost, hpLen, List.length_drop] at ht₁ ht₂ htf
  have hc : (gm06ProjectCutDartExpr (.read 635 (.reg 650))).cost ≤ 15 := by decide
  have hmul := Nat.mul_le_mul_left replacement.length hc
  simp only [Nat.mul_add, Nat.mul_one] at ht₁
  omega

end GraphMinor.Compute
