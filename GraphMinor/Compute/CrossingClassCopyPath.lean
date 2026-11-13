module

public import GraphMinor.Compute.CrossingClassPathAllowed

/-!
# Saving the first bridge path

The second search in Section 5.2 of `docs/crossing/crossing_extractor.tex` reuses the path array.
This file
copies the completed first path to its output array before that search starts.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.Compute.TwoPaths

/-- Copy the current path to its output array. -/
def copyBridgePathProg (dst : Arr) : Cmd := copyArr aPath dst 148

/-- Save a simple path in linear time. Only its output array and register 148 change. -/
theorem copyBridgePathProg_exec {w n : ℕ} {G : SimpleGraph (Fin n)} {x y : Fin n}
    (P : G.Walk x y) (hP : P.IsPath) (dst : Arr) (hdst : dst ≠ aPath) (s : State)
    (hpath : s.arrs aPath = P.support.map Fin.val) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) :
    ∃ s' t, Exec w (copyBridgePathProg dst) s s' t ∧ t ≤ 6 + 12 * n ∧
      s'.arrs dst = P.support.map Fin.val ∧
      (∀ a ≠ dst, s'.arrs a = s.arrs a) ∧
      (∀ r ≠ 148, s'.regs r = s.regs r) := by
  have hlen : (P.support.map Fin.val).length ≤ n := by
    simpa using hP.support_nodup.length_le_card
  obtain ⟨s', t, hex, ht, hout, _⟩ :=
    Triple.copyArr_spec aPath dst 148 (P.support.map Fin.val) hdst hw
      (lt_of_le_of_lt hlen hn)
      (by intro v hv; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv; exact lt_trans u.2 hn) s hpath
  dsimp only at ht
  refine ⟨s', t, hex, by omega, hout, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [copyArr, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [copyArr, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
