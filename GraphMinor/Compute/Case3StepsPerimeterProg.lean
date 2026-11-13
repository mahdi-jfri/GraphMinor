module

public import GraphMinor.Compute.Algorithm94Unpack
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Reading the original wall perimeter for the interior test

The fixed-height wall parser writes its vertex and perimeter bitsets in the
original labels. Its registers are shifted above all member-routing registers.
The original vertex count is read from the retained compass rank array's
length. This prepares the perimeter data for XIII (9.9), step 6, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Parse the given wall without successor arrays, retaining its original perimeter. -/
def case3PerimeterProg {h : ℕ} (h2 : 2 ≤ h) (a_W a_base r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 101) (.len (a_base + 2)))
    (.seq (.assign (r_base + 115) (.const 0))
      ((parseFixedWallProg h h2 false 0 a_W (a_base + 44) (a_base + 45) 15).shift 0 (r_base + 100)))

/-- The perimeter bitset is computed in linear vertex work for fixed wall
height, with the original input and all earlier routing data preserved. -/
theorem case3PerimeterProg_exec {w h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (hW : W.IsValid)
    (a_W a_base r_base : ℕ) (haW : a_W < a_base)
    (hw : 1 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hc : 3 + elemWallNumVerts h < 2 ^ w) (hwall : W.encList.length < 2 ^ w)
    {s : State} (hin : s.arrs a_W = W.encList) (hrank : (s.arrs (a_base + 2)).length = n) :
    ∃ s' t, Exec w (case3PerimeterProg h2 a_W a_base r_base) s s' t ∧
      t ≤ parseWallCost h n + 4 ∧
      IsBitSet W.vertexFinset (a_base + 44) s' ∧ IsBitSet W.perimeterFinset (a_base + 45) s' ∧
      (∀ a, a ≠ a_base + 44 → a ≠ a_base + 45 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 100, s'.regs r = s.regs r) := by
  have hnw : n < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 101) n
  let s₂ := s₁.setReg (r_base + 115) 0
  have hex₁ : Exec w (.assign (r_base + 101) (.len (a_base + 2))) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrank, hnw, ↓reduceIte])
  have hex₂ : Exec w (.assign (r_base + 115) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hinput : (s₂.unshift 0 (r_base + 100)).arrs a_W = [] ++ W.encList ++ [] := by
    simpa only [State.unshift_arrs, Nat.add_zero, s₂, s₁, State.setReg_arrs,
      List.nil_append, List.append_nil] using hin
  have hrn : (s₂.unshift 0 (r_base + 100)).regs 1 = n := by
    simp only [State.unshift_regs, show 1 + (r_base + 100) = r_base + 101 by omega,
      s₂, s₁, State.setReg_regs_ne _ _ (show r_base + 101 ≠ r_base + 115 by omega), State.setReg_regs_self]
  have hrpos : (s₂.unshift 0 (r_base + 100)).regs 15 = 0 := by
    simp only [State.unshift_regs, show 15 + (r_base + 100) = r_base + 115 by omega,
      s₂, State.setReg_regs_self]
  obtain ⟨s_sub, t, hex, ht, _, _, hverts, hperim, _, harr, _⟩ :=
    parseFixedWallProg_exec h2 le_rfl W hW false 0 a_W (a_base + 44) (a_base + 45) 15
      (by romega) (by romega) (by romega) (by intro hf; cases hf) (by decide) [] []
      hw hn hc (by simpa only [List.nil_append] using hwall) hinput hrn hrpos
  let s' := s₂.applyShifted 0 (r_base + 100) s_sub
  have hshift (a : ℕ) : s'.arrs a = s_sub.arrs a := by
    simpa only [s', Nat.add_zero] using State.applyShifted_arrs_add 0 (r_base + 100) s₂ s_sub a
  refine ⟨s', 2 + (2 + t), .seq hex₁ (.seq hex₂ (Exec.shift_from 0 (r_base + 100) hex)),
    by omega, hverts.of_arr_eq (hshift _), hperim.of_arr_eq (hshift _), ?_, ?_⟩
  · intro a h44 h45
    rw [hshift a, harr a h44 h45 (by intro hf; cases hf), State.unshift_arrs, Nat.add_zero]
    rfl
  · intro r hr
    rw [State.applyShifted_regs_lt _ _ _ _ hr, State.setReg_regs_ne _ _ (by romega),
      State.setReg_regs_ne _ _ (by romega)]

end GraphMinor.Compute
