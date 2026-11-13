module

public import GraphMinor.Compute.Case3StepsCoreMath
import GraphMinor.Compute.Case3StepsRamArrayBounds
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Writing the society input and running (8.6)

In step (5) of XIII (9.9), page 104, the compact input is followed by the
(8.6) call. Flatness excludes a cross. The output therefore gives a valid core
and its simple rural division. The compact multigraph and rank array are kept
below the call's shifted scratch region for computing the lifted members.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem case3BaseSize_lower (n e : ℕ) :
    n + e + 1 ≤ (n + 1) * (e + n + 1) := by nlinarith

private theorem case3InputCost_le {a n e N : ℕ} (ha : a ≤ e) (hN : n + e + 1 ≤ N) :
    400 * a + 40 * n + 500 ≤ 1000 * N := by omega

private theorem case3Linear_le_cube {a N : ℕ} (ha : a ≤ N) :
    8 + 3 * a ≤ (N + 2) ^ 3 := by nlinarith [Nat.zero_le (N ^ 3)]

/-- The input construction followed by the shifted (8.6) call. This computes
the core; the members still have to be written from that core. -/
def case3CoreProg {h : ℕ} (h2 : 2 ≤ h) (shiloachProg : Cmd)
    (a_G a_VK a_W a_base r_base : ℕ) : Cmd :=
  .seq (case3SocietyInputProg h2 a_G a_VK a_W a_base r_base)
    (.seq (.alloc (a_base + 9) (.const 0))
      ((alg86Prog shiloachProg).shift (a_base + 8) (r_base + 16)))

/-- Execution and time bound for constructing the input and calling (8.6).
The global assumption is precisely the supplied (8.6) computation theorem.
No rural-division or core-construction claim is assumed separately. -/
theorem case3CoreProg_exec (h : ℕ) (h2 : 2 ≤ h) (he : Even h) (shiloachProg : Cmd)
    (h86 : ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out))
      (alg86Prog shiloachProg) (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (a_G a_VK a_W a_base r_base : ℕ),
        a_G < a_base → a_VK < a_base → a_W < a_base →
        ∀ (w n : ℕ) (G : MultiDigraph n) (X : Finset (Fin n))
          (W : WallOfHeight h (G.deleteVertices X)) (hW : W.IsValid),
          W.IsFlatWall h2 → Disjoint W.compassFinset X →
          wordSize c ((n + 1) * (G.numEdges + n + 1)) ≤ w →
          ∀ s : State, s.arrs a_G = G.enc → s.arrs a_VK = bitSetList W.compassFinset →
            s.arrs a_W = W.encList →
            ∃ (s' : State) (t : ℕ)
              (d : Alg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)),
              Exec w (case3CoreProg h2 shiloachProg a_G a_VK a_W a_base r_base) s s' t ∧
              t ≤ C * (n + 1) * (G.numEdges + n + 1) ∧
              decAlg86Out (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW)
                (s'.arrs (a_base + 9)) = Sum.inr d ∧
              IsValidAlg86DivisionOutput (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) d ∧
              (s'.arrs (a_base + 9)).length < 2 ^ w ∧
              s'.arrs (a_base + 3) = (case3CompactCompassMultigraph (G.deleteVertices X) W).enc ∧
              s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1) ∧
              (∀ a < a_base, s'.arrs a = s.arrs a) ∧
              (∀ r < r_base, s'.regs r = s.regs r) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hrun⟩ := h86
  let c := max c₀ (3 + elemWallNumVerts h)
  have hc₃ : 3 ≤ c := le_trans (by omega) (Nat.le_max_right _ _)
  refine ⟨C₀ + 1001, c, by omega, by omega, ?_⟩
  intro a_G a_VK a_W a_base r_base haG haVK haW w n G X W hW hflat hdisj hw s hin hVK hWall
  let N := (n + 1) * (G.numEdges + n + 1)
  let x := case3CompactSocietyInput (G.deleteVertices X) W h2 he hW
  have hN : n + G.numEdges + 1 ≤ N := case3BaseSize_lower n G.numEdges
  have hactive : G.numActivePairs ≤ G.numEdges := G.numActivePairs_le_numEdges
  have hpow : (N + 2) ^ c < 2 ^ w :=
    (pow_lt_two_pow_wordSize (by omega) N).trans_le (Nat.pow_le_pow_right (by decide) hw)
  have hn : n < 2 ^ w :=
    (lt_two_pow_wordSize_of_le (c := c) (n := N) (by omega) (by omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  have hew : G.numEdges < 2 ^ w :=
    (lt_two_pow_wordSize_of_le (c := c) (n := N) (by omega) (by omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  have hmw : 8 + 3 * G.numActivePairs < 2 ^ w := by
    apply lt_of_le_of_lt (case3Linear_le_cube (N := N) (by omega))
    exact (Nat.pow_le_pow_right (by omega : 1 ≤ N + 2) hc₃).trans_lt hpow
  have hcw : c ≤ w := (Nat.le_mul_of_pos_right c (by omega : 0 < Nat.log 2 (N + 2) + 1)).trans hw
  have hidx : 3 + elemWallNumVerts h < 2 ^ w :=
    (Nat.le_max_right _ _).trans_lt ((Nat.lt_two_pow_self (n := c)).trans_le
      (Nat.pow_le_pow_right (by decide) hcw))
  obtain ⟨s₁, t₁, hex₁, ht₁, hinput₁, hcompact₁, hrank₁, harr₁, hreg₁⟩ :=
    case3SocietyInputProg_exec G X W h2 he hW hdisj a_G a_VK a_W a_base r_base
      haG haVK haW hn hmw hew hidx hin hVK hWall
  let s₂ := s₁.setArr (a_base + 9) []
  have h0w : 0 < 2 ^ w := by omega
  have hexClear : Exec w (.alloc (a_base + 9) (.const 0)) s₁ s₂ 1 :=
    Exec.alloc (m := 0) (by simp only [Expr.eval, checkWord, h0w, ↓reduceIte])
  have hinput : (s₂.unshift (a_base + 8) (r_base + 16)).arrs inArr = encAlg81In x := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add] using (State.setArr_arrs_ne s₁ [] (show a_base + 8 ≠ a_base + 9 by omega)).trans hinput₁
  obtain ⟨s_sub, t₂, hex₂, ht₂, hout₂⟩ := hrun x (s₂.unshift (a_base + 8) (r_base + 16)) hinput
  have hsize : alg81Size x ≤ N := case3CompactSocietyInput_size_le G X W h2 he hW
  have hw₂ : wordSize c₀ (alg81Size x) ≤ w :=
    (wordSize_mono_right c₀ hsize).trans ((wordSize_mono_left (Nat.le_max_left _ _) N).trans hw)
  obtain ⟨d, hdec, hd⟩ := case3Alg86Output_division (s_sub.arrs outArr)
    (case3CompactSocietyInput_noCross _ W h2 he hW hflat) hout₂
  have hlenSub : (s_sub.arrs outArr).length < 2 ^ w :=
    case3Exec_array_length_lt (hex₂.mono_wordSize hw₂) outArr (by
      simp only [State.unshift_arrs, outArr, s₂, show 1 + (a_base + 8) = a_base + 9 by omega,
        State.setArr_arrs_self, List.length_nil]
      exact h0w)
  have hex₂' := Exec.shift_from (a_base + 8) (r_base + 16) (hex₂.mono_wordSize hw₂)
  have ht₁' : t₁ ≤ 1000 * N := ht₁.trans (case3InputCost_le hactive hN)
  have ht₂' : t₂ ≤ C₀ * N := ht₂.trans (Nat.mul_le_mul_left C₀ hsize)
  refine ⟨s₂.applyShifted (a_base + 8) (r_base + 16) s_sub, t₁ + (1 + t₂), d,
    .seq hex₁ (.seq hexClear hex₂'), ?_, ?_, hd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.mul_assoc]
    change t₁ + (1 + t₂) ≤ (C₀ + 1001) * N
    rw [Nat.add_mul]
    omega
  · have hs := State.applyShifted_arrs_add' (a_base + 8) (r_base + 16) s₂ s_sub 1
    simpa only [Nat.add_assoc, Nat.reduceAdd, outArr] using (congrArg (decAlg86Out x) hs).trans hdec
  · have hs := State.applyShifted_arrs_add' (a_base + 8) (r_base + 16) s₂ s_sub 1
    have heq : ((s₂.applyShifted (a_base + 8) (r_base + 16) s_sub).arrs (a_base + 9)).length =
        (s_sub.arrs outArr).length := by
      simpa only [Nat.add_assoc, Nat.reduceAdd, outArr] using congrArg List.length hs
    exact heq ▸ hlenSub
  · rw [State.applyShifted_arrs_lt _ _ _ _ (show a_base + 3 < a_base + 8 by omega)]
    exact (State.setArr_arrs_ne s₁ [] (show a_base + 3 ≠ a_base + 9 by omega)).trans hcompact₁
  · rw [State.applyShifted_arrs_lt _ _ _ _ (show a_base + 2 < a_base + 8 by omega)]
    exact (State.setArr_arrs_ne s₁ [] (show a_base + 2 ≠ a_base + 9 by omega)).trans hrank₁
  · intro a ha
    rw [State.applyShifted_arrs_lt _ _ _ _ (by omega)]
    exact (State.setArr_arrs_ne s₁ [] (show a ≠ a_base + 9 by omega)).trans (harr₁ a ha)
  · intro r hr
    rw [State.applyShifted_regs_lt _ _ _ _ (by omega)]
    exact hreg₁ r hr

end GraphMinor.Compute
