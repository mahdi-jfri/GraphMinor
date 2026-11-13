module

public import GraphMinor.Compute.Case3StepsCollectVerticesProg
public import GraphMinor.Compute.Case3StepsMemberVertexOrder

/-!
# The inverse list of original compass vertex labels

Scanning the supplied compass bitset writes its original labels in increasing
order. The retained rank array supplies the ambient vertex count. This list
maps compact compass labels back to the original graph for the branch or
wall output of XIII (9.9), step 6.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Collect original compass labels into array 32 above the scratch base. -/
def case3CompassVerticesProg (a_VK a_base r_base : ℕ) : Cmd :=
  .seq (.assign (r_base + 90) (.len (a_base + 2)))
    (case3CollectVerticesProg a_VK (a_base + 32) (r_base + 90) (r_base + 91) (r_base + 92))

/-- The original compass inverse list and its count are computed in linear
ambient vertex time, preserving all earlier scratch arrays. -/
theorem case3CompassVerticesProg_exec {w n : ℕ} (S : Finset (Fin n))
    (a_VK a_base r_base : ℕ) (haVK : a_VK < a_base)
    (hw : 4 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    {s : State} (hVK : s.arrs a_VK = bitSetList S) (hrank : (s.arrs (a_base + 2)).length = n) :
    ∃ s' t, Exec w (case3CompassVerticesProg a_VK a_base r_base) s s' t ∧
      t ≤ 20 * n + 10 ∧
      s'.arrs (a_base + 32) = (case3BoundaryVertices S).map Fin.val ++ List.replicate (n - S.card) 0 ∧
      s'.regs (r_base + 92) = S.card ∧
      (∀ a, a ≠ a_base + 32 → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base + 90, s'.regs r = s.regs r) := by
  have hnw : n < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 90) n
  have hex₁ : Exec w (.assign (r_base + 90) (.len (a_base + 2))) s s₁ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hrank, hnw, ↓reduceIte])
  obtain ⟨s₂, t₂, hex₂, ht₂, hlist₂, hcount₂, harr₂, hreg₂⟩ :=
    case3CollectVerticesProg_exec S a_VK (a_base + 32) (r_base + 90) (r_base + 91) (r_base + 92)
      (by omega) (by omega) (by omega) (by omega) hw hn
      (s := s₁) (IsBitSet.of_bitSetList _ _ _ hVK) (State.setReg_regs_self ..)
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hlist₂, hcount₂, ?_, ?_⟩
  · intro a ha
    exact harr₂ a ha
  · intro r hr
    rw [hreg₂ r (by romega) (by romega), State.setReg_regs_ne _ _ (by romega)]

/-- Reading the inverse buffer maps a compact index to its original vertex label. -/
theorem case3CompassVerticesProg_lookup {n : ℕ} (S : Finset (Fin n))
    (a_base : ℕ) (s : State)
    (hlist : s.arrs (a_base + 32) = (case3BoundaryVertices S).map Fin.val ++ List.replicate (n - S.card) 0)
    (i : Fin S.card) :
    (s.arrs (a_base + 32)).getD i.1 0 = (S.orderEmbOfFin rfl i).1 := by
  rw [hlist]
  exact case3PaddedVertices_getD_orderEmb S i

end GraphMinor.Compute
