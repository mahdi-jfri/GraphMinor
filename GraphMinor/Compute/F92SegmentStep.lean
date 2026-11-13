module

public import GraphMinor.Compute.F92Cut
public import GraphMinor.Compute.F92Unpack

/-!
# Writing one segment and extending its vertex bitset

Scan the stored path to determine its retained prefix, mark that prefix in the current
segment bitset, then copy it into a separate segment array. The execution theorem identifies
both outputs with the same prefix, which is the operation used by `f92Segments`.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- The retained prefix is the initial slice of the original path of the same length. -/
theorem f92Prefix_eq_take_length {n h : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (F : Finset (Fin n)) :
    ∀ P, f92Prefix W F P = P.take (f92Prefix W F P).length
  | [] => rfl
  | y :: ys => by
    simp only [f92Prefix]
    split_ifs
    · simp
    · simp only [List.length_cons, List.take_succ_cons]
      exact congrArg (List.cons y) (f92Prefix_eq_take_length W F ys)

/-- Compute, mark and write the new segment. -/
def f92SegmentStepProg (a_path a_H a_F a_seg r_base : ℕ) : Cmd :=
  .seq (f92CutProg a_path a_H a_F r_base)
    (.seq (.assign (r_base + 4) (.const 0))
      (.seq (markSliceGenProg a_path a_F (r_base + 4) (r_base + 2) (r_base + 5))
        (readSliceProg a_path (.const 0) a_seg (.reg (r_base + 2)) (r_base + 6))))

/-- This step writes the new segment and adds exactly its vertices to the current bitset,
with time linear in the original path length. -/
theorem f92SegmentStepProg_exec {w n h : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (F : Finset (Fin n)) (P : List (Fin n))
    (a_path a_H a_F a_seg r_base : ℕ)
    (hpF : a_path ≠ a_F) (hps : a_path ≠ a_seg) (hFs : a_F ≠ a_seg)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hP : P.length < 2 ^ w)
    {s : State} (hsrc : s.arrs a_path = P.map Fin.val)
    (hH : IsBitSet W.vertexFinset a_H s) (hF : IsBitSet F a_F s) :
    ∃ s' t, Exec w (f92SegmentStepProg a_path a_H a_F a_seg r_base) s s' t ∧
      t ≤ 25 + 60 * P.length ∧
      IsBitSet (F ∪ (f92Prefix W F P).toFinset) a_F s' ∧
      s'.arrs a_seg = (f92Prefix W F P).map Fin.val ∧
      (∀ a : ℕ, a ≠ a_F → a ≠ a_seg → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  let Q := f92Prefix W F P
  have hQlen : Q.length ≤ P.length := length_f92Prefix_le W F P
  have hQw : Q.length < 2 ^ w := hQlen.trans_lt hP
  have hQsplit : P = Q ++ P.drop Q.length := by
    rw [show Q = P.take Q.length from f92Prefix_eq_take_length W F P]
    rw [List.length_take, Nat.min_eq_left hQlen, List.take_append_drop]
  have hsplit : P.map Fin.val = Q.map Fin.val ++ (P.drop Q.length).map Fin.val := by
    conv_lhs => rw [hQsplit]
    rw [List.map_append]
  obtain ⟨s₁, t₁, hex₁, ht₁, hcut₁, harr₁, hreg₁⟩ :=
    f92CutProg_exec W F P a_path a_H a_F r_base hw hn hP hsrc hH hF
  let s₂ := s₁.setReg (r_base + 4) 0
  have hex₂ : Exec w (.assign (r_base + 4) (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hsrc₂ : s₂.arrs a_path = [] ++ Q.map Fin.val ++ (P.drop Q.length).map Fin.val := by
    rw [State.setReg_arrs, harr₁ a_path, hsrc, hsplit, List.nil_append]
  obtain ⟨s₃, t₃, hex₃, ht₃, hF₃, harr₃, hreg₃⟩ :=
    markSliceGenProg_exec a_path a_F (r_start := r_base + 4) (r_len := r_base + 2)
      (r_idx := r_base + 5) hpF (by omega) (by omega) [] Q ((P.drop Q.length).map Fin.val) F
      hw hn (by simpa using hQw) hsrc₂ (by simp [s₂])
      (by simpa [s₂] using hcut₁)
      (by rw [State.setReg_arrs, harr₁ a_F]; exact hF.arr_eq_bitSetList)
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩ :=
    readSliceProg_exec a_path a_seg (.const 0) (r_base + 2) (r_base + 6) hps (by omega)
      [] (Q.map Fin.val) ((P.drop Q.length).map Fin.val) rfl rfl
      (by intro v hv; obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv; exact u.isLt.trans hn)
      hw (by simpa using hQw)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      ((harr₃ a_path hpF).trans hsrc₂)
      (by rw [hreg₃ (r_base + 2) (by omega)]; simpa [s₂] using hcut₁)
  dsimp only [Expr.cost] at ht₄
  have hbit : IsBitSet (F ∪ Q.toFinset) a_F s₄ :=
    (IsBitSet.of_bitSetList _ _ _ hF₃).of_arr_eq (harr₄ a_F hFs)
  refine ⟨s₄, t₁ + (2 + (t₃ + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by simp only [List.length_map] at ht₄; omega, hbit, hout₄, ?_, ?_⟩
  · intro a haF haS
    rw [harr₄ a haS, harr₃ a haF, State.setReg_arrs, harr₁ a]
  · intro q hq
    rw [hreg₄ q (by omega), hreg₃ q (by omega)]
    dsimp [s₂]
    rw [State.setReg_regs_ne _ _ (by omega : (q : ℕ) ≠ r_base + 4),
      hreg₁ q (Or.inl hq)]

end GraphMinor.Compute.Alg92
