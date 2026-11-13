module

public import GraphMinor.Compute.Case3StepsCornerProg

/-!
# Copying the original wall corners into the final block

The wall section begins with its three header words and branch vertices.
Read the four designated corner entries directly. Their cyclic order is
already the order required by the block parser.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Copy the four original corner labels from wall array 59 to array 58. -/
def case3BlockCornersProg {h : ℕ} (h2 : 2 ≤ h) : Cmd :=
  .seq (.alloc 58 (.const 4))
    (.seq (.write 58 (.const 0) (.read 59 (.const (3 + (elemWallCornerIdx h2 0).1))))
      (.seq (.write 58 (.const 1) (.read 59 (.const (3 + (elemWallCornerIdx h2 1).1))))
        (.seq (.write 58 (.const 2) (.read 59 (.const (3 + (elemWallCornerIdx h2 2).1))))
          (.write 58 (.const 3) (.read 59 (.const (3 + (elemWallCornerIdx h2 3).1)))))))

/-- All four corner words are read exactly, with no register changes. -/
theorem case3BlockCornersProg_exec {w h n : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (hw : 4 < 2 ^ w)
    (hn : n < 2 ^ w) (hidx : 3 + elemWallNumVerts h < 2 ^ w)
    {s : State} (hW : s.arrs 59 = W.encList) :
    ∃ s', Exec w (case3BlockCornersProg h2) s s' 21 ∧
      s'.arrs 58 = List.ofFn (fun i : Fin 4 => (W.cornerVert h2 i).1) ∧
      (∀ a, a ≠ 58 → s'.arrs a = s.arrs a) ∧
      (∀ r, s'.regs r = s.regs r) := by
  let s₀ := s.setArr 58 (List.replicate 4 0)
  let s₁ := s₀.writeArr 58 0 (W.cornerVert h2 0).1
  let s₂ := s₁.writeArr 58 1 (W.cornerVert h2 1).1
  let s₃ := s₂.writeArr 58 2 (W.cornerVert h2 2).1
  let s₄ := s₃.writeArr 58 3 (W.cornerVert h2 3).1
  have hex₀ : Exec w (.alloc 58 (.const 4)) s s₀ 5 :=
    .alloc (m := 4) (by simp only [Expr.eval, checkWord, hw, ↓reduceIte])
  have hwrite (i : Fin 4) {st : State} (hwall : st.arrs 59 = W.encList)
      (hlen : (st.arrs 58).length = 4) :
      Exec w (.write 58 (.const i.1) (.read 59 (.const (3 + (elemWallCornerIdx h2 i).1))))
        st (st.writeArr 58 i.1 (W.cornerVert h2 i).1) 4 := by
    have hi : i.1 < 2 ^ w := i.2.trans hw
    have hj : 3 + (elemWallCornerIdx h2 i).1 < 2 ^ w :=
      (Nat.add_lt_add_left (elemWallCornerIdx h2 i).2 3).trans hidx
    have hget := case3Corner_enc_getElem W h2 i
    obtain ⟨hjl, hjv⟩ := List.getElem?_eq_some_iff.mp hget
    refine .write (by simp only [Expr.eval, checkWord, hi, ↓reduceIte]) ?_ (by rw [hlen]; exact i.2)
    simp only [Expr.eval, checkWord, hj, ↓reduceIte, hwall, hjl, ↓reduceDIte,
      hjv, lt_trans (W.cornerVert h2 i).2 hn]
  have hex₁ := hwrite 0 (st := s₀) (by exact hW) (by simp [s₀])
  have hex₂ := hwrite 1 (st := s₁) (by simpa [s₁, s₀] using hW) (by simp [s₁, s₀])
  have hex₃ := hwrite 2 (st := s₂) (by simpa [s₂, s₁, s₀] using hW) (by simp [s₂, s₁, s₀])
  have hex₄ := hwrite 3 (st := s₃) (by simpa [s₃, s₂, s₁, s₀] using hW) (by simp [s₃, s₂, s₁, s₀])
  have hex : Exec w (case3BlockCornersProg h2) s s₄ 21 :=
    .seq hex₀ (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)))
  refine ⟨s₄, hex, ?_, ?_, ?_⟩
  · simp [s₄, s₃, s₂, s₁, s₀, List.ofFn_succ, List.ofFn_zero,
      List.replicate_succ, List.replicate_zero]
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3BlockCornersProg, Cmd.writtenArrs, ha])
  · intro r
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3BlockCornersProg, Cmd.writtenRegs])

end GraphMinor.Compute
