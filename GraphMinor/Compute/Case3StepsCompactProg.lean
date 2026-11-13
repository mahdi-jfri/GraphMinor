module

public import GraphMinor.Compute.Case3StepsInputMath
public import GraphMinor.Compute.Algorithm94Aux

/-!
# Writing the compact compass multigraph

Step (5) of XIII (9.9), page 104, first restricts the input to the compass and
numbers its vertices consecutively. The input compass bitset is complemented
and passed to the existing deletion and renumbering program. The program also
keeps the rank array for numbering the four wall corners.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Write the compact compass graph in `a_base + 3` and its original-label
rank array in `a_base + 2`, using scratch arrays `a_base` through `a_base + 3`. -/
def case3CompactCompassProg (a_G a_VK a_base r_base : ℕ) : Cmd :=
  .seq (.assign r_base (.read a_G (.const 0)))
    (.seq (complBitSetProg a_VK a_base r_base (r_base + 1))
      (deleteVerticesCompactProg a_G a_base (a_base + 1) (a_base + 2) (a_base + 3) (r_base + 2)))

/-- The compact compass construction takes linear time and preserves all
arrays and registers below its bases. This lemma applies to any selected
vertex set, so it also supplies compact input graphs for member calls. -/
theorem case3CompactCompassProg_exec {w n : ℕ} (G : MultiDigraph n)
    (S : Finset (Fin n)) (a_G a_VK a_base r_base : ℕ)
    (haG : a_G < a_base) (haVK : a_VK < a_base)
    (hw3 : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hm3 : 2 + 3 * G.numActivePairs < 2 ^ w) (he : G.numEdges < 2 ^ w)
    {s : State} (hG : s.arrs a_G = G.enc) (hVK : s.arrs a_VK = bitSetList S) :
    ∃ s' t,
      Exec w (case3CompactCompassProg a_G a_VK a_base r_base) s s' t ∧
      t ≤ 160 * G.numActivePairs + 34 * n + 129 ∧
      s'.arrs (a_base + 3) = (G.deleteVerticesCompact Sᶜ).enc ∧
      s'.arrs (a_base + 2) = List.ofFn (fun v : Fin n => compactRank Sᶜ v.1) ∧
      (∀ a < a_base, s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by romega
  have hw : 1 < 2 ^ w := by romega
  have hin : s.arrs a_G = G.enc ++ [] := by simpa only [List.append_nil] using hG
  obtain ⟨hlen, hval⟩ := enc_getElem_zero G [] hin
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_G (.const 0))) s s₁ 3 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte, ↓reduceDIte, hlen, hval, hn])
  have hVK₁ : IsBitSet S a_VK s₁ :=
    IsBitSet.of_bitSetList S a_VK s₁ (by simpa only [s₁, State.setReg_arrs] using hVK)
  obtain ⟨s₂, t₂, hex₂, ht₂, hbits₂, harr₂, hreg₂⟩ :=
    complBitSetProg_exec S a_VK a_base r_base (r_base + 1) (by romega) (by romega)
      hw hn hVK₁ (by simp only [s₁, State.setReg_regs_self])
  have hcompl : s₂.arrs a_base = bitSetList Sᶜ := by
    rw [Finset.compl_eq_univ_sdiff]
    exact hbits₂.arr_eq_bitSetList
  have hG₂ : s₂.arrs a_G = G.enc := by
    rw [harr₂ a_G (by romega)]
    exact hG
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃, hrank₃, harr₃, hreg₃⟩ :=
    deleteVerticesCompactProg_exec G Sᶜ a_G a_base (a_base + 1) (a_base + 2) (a_base + 3)
      (r_base + 2) (by romega) (by romega) (by romega) (by romega) (by romega) (by romega)
      hw3 hn hm3 he hG₂ hcompl
  refine ⟨s₃, 3 + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by romega, hdst₃, hrank₃, ?_, ?_⟩
  · intro a ha
    rw [harr₃ a (by romega) (by romega) (by romega), harr₂ a (by romega)]
    rfl
  · intro r hr
    rw [hreg₃ r (by romega), hreg₂ r (by romega)]
    exact State.setReg_regs_ne s n (show r ≠ r_base by romega)

end GraphMinor.Compute
