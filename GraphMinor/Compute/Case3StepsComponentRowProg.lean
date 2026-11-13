module

public import GraphMinor.Compute.Case3StepsComponentRows

/-!
# Writing one outside-component row

For a core vertex, the preallocated zero row is retained. For another vertex,
a breadth-first search finds its component outside the core and the program
copies that component's bitset into the row. This is the component part of
step (5) of XIII (9.9), page 104.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- The row index is in `r_base + 1`, and the vertex count in `r_base`.
The search uses shifted storage above `a_off` and `r_base + 32`. -/
def case3ComponentRowProg (a_Z a_mat a_off r_base : ℕ) : Cmd :=
  .ite (.read a_Z (.reg (r_base + 1))) .skip
    (.seq (.assign (1 + (r_base + 32)) (.reg r_base))
      (.seq (.assign (14 + (r_base + 32)) (.reg (r_base + 1)))
        (.seq (case3ComponentSearchProg a_off (r_base + 32))
          (writeSliceProg (32 + a_off) (.const 0) a_mat
            (.op .mul (.reg (r_base + 1)) (.reg r_base)) r_base (r_base + 8)))))

/-- Execution of one row, with the untouched matrix prefix and suffix made
explicit. The adjacency lists are already restricted to vertices outside `Z`. -/
theorem case3ComponentRowProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (lists : Fin x.n → List ℕ)
    (a_Z a_mat a_off r_base : ℕ)
    (_haZ : a_Z < a_off) (haM : a_mat < a_off) (_haZM : a_Z ≠ a_mat)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (k : ℕ) (hk : k < x.n) (pre suf : List ℕ) (hpre : pre.length = k * x.n)
    {s : State} (hZ : s.arrs a_Z = bitSetList Z)
    (hmat : s.arrs a_mat = pre ++ List.replicate x.n 0 ++ suf)
    (hadj : IsAdjList (restrictGraph x.G (Finset.univ \ Z))
      (36 + a_off) (37 + a_off) (38 + a_off) lists s)
    (hent : (s.arrs (38 + a_off)).length < 2 ^ w)
    (hrn : s.regs r_base = x.n) (hrk : s.regs (r_base + 1) = k) :
    ∃ s' t, Exec w (case3ComponentRowProg a_Z a_mat a_off r_base) s s' t ∧
      t ≤ 38 * x.n + 26 * totalAdjEntries lists + 40 ∧
      s'.arrs a_mat = pre ++ case3ComponentRow x Z ⟨k, hk⟩ ++ suf ∧
      s'.regs r_base = x.n ∧ s'.regs (r_base + 1) = k ∧
      (∀ a, a ≠ a_mat → a ≠ 31 + a_off → a ≠ 32 + a_off → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  have hkw : k < 2 ^ w := by omega
  have hkZ : k < (s.arrs a_Z).length := by rw [hZ, length_bitSetList]; exact hk
  have hbit : (s.arrs a_Z)[k]'hkZ = if (⟨k, hk⟩ : Fin x.n) ∈ Z then 1 else 0 := by
    simpa only [hZ] using getElem_bitSetList Z k hk
  by_cases huZ : (⟨k, hk⟩ : Fin x.n) ∈ Z
  · have hc : (Expr.read a_Z (.reg (r_base + 1))).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hrk, hkw, hkZ, hbit, huZ, hw]
    refine ⟨s, 3, .ite_true (t := 1) hc (by decide) (.skip s), by omega, ?_, hrn, hrk,
      fun _ _ _ _ => rfl, fun _ _ => rfl⟩
    simpa only [case3ComponentRow, huZ, ↓reduceIte] using hmat
  · have hc : (Expr.read a_Z (.reg (r_base + 1))).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hrk, hkw, hkZ, hbit, huZ, h0]
    let s₁ := s.setReg (1 + (r_base + 32)) x.n
    let s₂ := s₁.setReg (14 + (r_base + 32)) k
    have hex₁ : Exec w (.assign (1 + (r_base + 32)) (.reg r_base)) s s₁ 2 :=
      .assign (by simp only [Expr.eval, hrn, checkWord, hnw, ↓reduceIte])
    have hex₂ : Exec w (.assign (14 + (r_base + 32)) (.reg (r_base + 1))) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₁, State.setReg, show r_base + 1 ≠ 1 + (r_base + 32) by omega, hrk, hkw])
    obtain ⟨s₃, t₃, hex₃, ht₃, hbits₃, harr₃, hreg₃⟩ :=
      case3ComponentSearchProg_exec x Z ⟨k, hk⟩ huZ lists a_off (r_base + 32) hw hnw
        (s := s₂) (hadj.of_arrs_eq rfl rfl rfl) hent
        (by simp [s₂, s₁, State.setReg]) (by simp [s₂, State.setReg])
    have hrn₃ : s₃.regs r_base = x.n := by
      rw [hreg₃ r_base (by omega)]
      simp [s₂, s₁, State.setReg, show r_base ≠ 14 + (r_base + 32) by omega, show r_base ≠ 1 + (r_base + 32) by omega, hrn]
    have hrk₃ : s₃.regs (r_base + 1) = k := by
      rw [hreg₃ (r_base + 1) (by omega)]
      simp [s₂, s₁, State.setReg, show r_base + 1 ≠ 14 + (r_base + 32) by omega, show r_base + 1 ≠ 1 + (r_base + 32) by omega, hrk]
    have hmat₃ : s₃.arrs a_mat = pre ++ List.replicate x.n 0 ++ suf := by
      rw [harr₃ a_mat (by omega) (by omega)]
      exact hmat
    have hkn : k * x.n + x.n ≤ x.n * x.n := by
      have h := Nat.mul_le_mul_right x.n (Nat.succ_le_of_lt hk)
      simpa only [Nat.succ_mul] using h
    have hoff : k * x.n < 2 ^ w := by omega
    have hsrc : s₃.arrs (32 + a_off) = [] ++ bitSetList (compOutside x Z ⟨k, hk⟩) ++ [] := by
      simpa only [List.nil_append, List.append_nil] using hbits₃
    obtain ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩ :=
      writeSliceProg_exec (len := x.n) (src_off := 0) (dst_off := k * x.n)
        (32 + a_off) a_mat (.const 0) (.op .mul (.reg (r_base + 1)) (.reg r_base))
        r_base (r_base + 8) (by omega) (by omega)
        [] (bitSetList (compOutside x Z ⟨k, hk⟩)) [] pre (List.replicate x.n 0) suf
        rfl (length_bitSetList _) hpre (List.length_replicate ..)
        (by simpa only [case3ComponentRow, huZ, ↓reduceIte] using case3ComponentRow_words x Z ⟨k, hk⟩ hw)
        hw (by omega) (hkn.trans_lt hsq)
        (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg,
          hrk₃, hrn₃, hkw, hnw, hoff]) hsrc hmat₃ hrn₃
    dsimp only [Expr.cost] at ht₄
    refine ⟨s₄, 2 + (2 + (2 + (t₃ + t₄))), .ite_false hc (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))),
      by omega, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [case3ComponentRow, huZ, ↓reduceIte] using hdst₄
    · rw [hreg₄ r_base (Or.inl (by omega))]
      exact hrn₃
    · rw [hreg₄ (r_base + 1) (Or.inl (by omega))]
      exact hrk₃
    · intro a hM h31 h32
      rw [harr₄ a hM, harr₃ a h31 h32]
      rfl
    · intro r hr
      rw [hreg₄ r (Or.inl (by omega)), hreg₃ r (by omega)]
      simp [s₂, s₁, State.setReg, show r ≠ 14 + (r_base + 32) by omega,
        show r ≠ 1 + (r_base + 32) by omega]

end GraphMinor.Compute
