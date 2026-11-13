module

public import GraphMinor.Compute.Join41

/-!
# Packing the core input from prepared arrays

The existing input-packing command only copies word arrays. This lemma states
that behavior for arbitrary prepared head, tail, root, parent, and leaf arrays,
so it can also pack the caller's multigraph edge order.
-/

public section
namespace GraphMinor.Compute

/-- The core input packer concatenates its prepared arrays in linear time. -/
theorem packCoreLists72_exec {w : ℕ} (n m tc b : ℕ) (hb : 0 < b)
    (htc_le : tc ≤ 2 * m + 1)
    (L_head L_tail L_Z L_par L_tau : List ℕ)
    (hlen_head : L_head.length = m) (hlen_tail : L_tail.length = m)
    (hlen_Z : L_Z.length = n) (hlen_par : L_par.length = tc) (hlen_tau : L_tau.length = m)
    (hhead_w : ∀ u ∈ L_head, u < 2 ^ w) (htail_w : ∀ u ∈ L_tail, u < 2 ^ w)
    (hZ_w : ∀ u ∈ L_Z, u < 2 ^ w) (hpar_w : ∀ u ∈ L_par, u < 2 ^ w)
    (htau_w : ∀ u ∈ L_tau, u < 2 ^ w)
    (hw3 : 3 < 2 ^ w) (hsz_w : 5 * (m + n + 1) < 2 ^ w)
    {s : State} (hr26 : s.regs 26 = n) (hr28 : s.regs 28 = m) (hr52 : s.regs 52 = tc)
    (hb1 : s.arrs (b + 1) = L_Z) (hb2 : s.arrs (b + 2) = L_par)
    (hb3 : s.arrs (b + 3) = L_tau) (hb5 : s.arrs (b + 5) = L_tail)
    (hb6 : s.arrs (b + 6) = L_head) :
    ∃ s' time, Exec w (packAlg41InProg b) s s' time ∧
      time ≤ 150 * (n + m + 1) ∧
      s'.arrs inArr = [n, m, tc] ++ L_head ++ L_tail ++ L_Z ++ L_par ++ L_tau := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : m < 2 ^ w := by omega
  have htc_w : tc < 2 ^ w := by omega
  have h3m_w : 3 * m < 2 ^ w := by omega
  have hntc_w : n + tc < 2 ^ w := by omega
  have h3m_ntc_w : 3 * m + (n + tc) < 2 ^ w := by omega
  have htot_w : 3 + (3 * m + (n + tc)) < 2 ^ w := by omega
  set tot := 3 + (3 * m + (n + tc))
  let s₁ := s.setReg 55 tot
  have hex₁ : Exec w (.assign 55 (.op .add (.const 3)
      (.op .add (.op .mul (.const 3) (.reg 28))
        (.op .add (.reg 26) (.reg 52))))) s s₁ 10 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr28, hr26, hr52, hw3, hm_w, hn_w, htc_w, h3m_w, hntc_w, h3m_ntc_w, htot_w, tot])
  let s₂ := s₁.setArr inArr (List.replicate tot 0)
  have hex₂ : Exec w (.alloc inArr (.reg 55)) s₁ s₂ (1 + tot) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, htot_w])
  let s₃ := s₂.writeArr inArr 0 n
  have hex₃ : Exec w (.write inArr (.const 0) (.reg 26)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₂, s₁, Expr.eval, checkWord, hr26, hn_w])
      (by simp [s₂, tot])
  let s₄ := s₃.writeArr inArr 1 m
  have hex₄ : Exec w (.write inArr (.const 1) (.reg 28)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h1_w])
      (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr28, hm_w])
      (by simp [s₃, s₂, tot]; omega)
  let s₅ := s₄.writeArr inArr 2 tc
  have hex₅ : Exec w (.write inArr (.const 2) (.reg 52)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h2_w])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr52, htc_w])
      (by simp [s₄, s₃, s₂, tot]; omega)
  let s₆ := s₅.setReg 57 3
  have hex₆ : Exec w (.assign 57 (.const 3)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw3])
  let L_hdr : List ℕ := [n, m, tc]
  have hin₆ : s₆.arrs inArr = L_hdr ++ List.replicate (L_head.length + (m + n + tc + m)) 0 := by
    have htot_eq : tot = (L_head.length + (m + n + tc + m)) + 3 := by
      rw [hlen_head]; dsimp [tot]; omega
    change (((List.replicate tot 0).set 0 n).set 1 m).set 2 tc =
      [n, m, tc] ++ List.replicate (L_head.length + (m + n + tc + m)) 0
    rw [htot_eq]
    rfl
  have hne1 : b + 1 ≠ inArr := by dsimp [inArr, Arr]; omega
  have hne2 : b + 2 ≠ inArr := by dsimp [inArr, Arr]; omega
  have hne3 : b + 3 ≠ inArr := by dsimp [inArr, Arr]; omega
  have hne5 : b + 5 ≠ inArr := by dsimp [inArr, Arr]; omega
  have hne6 : b + 6 ≠ inArr := by dsimp [inArr, Arr]; omega
  have hs6_arr : ∀ a : Arr, a ≠ inArr → s₆.arrs a = s.arrs a := by
    intro a ha
    simp [s₆, s₅, s₄, s₃, s₂, s₁, State.writeArr, ha]
  rcases appendSliceProg_exec L_hdr L_head (m + n + tc + m) (b + 6) inArr 28
      hne6 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head]; omega) hhead_w (s := s₆)
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_head])
      (by simp [s₆, L_hdr])
      ((hs6_arr (b + 6) hne6).trans hb6)
      hin₆ with
    ⟨s₇, t₇, hex₇, ht₇, hin₇, hr57_7, harr₇, hreg₇⟩
  have hin₇' : s₇.arrs inArr = (L_hdr ++ L_head) ++ List.replicate (L_tail.length + (n + tc + m)) 0 := by
    rw [hin₇, hlen_tail, show m + n + tc + m = m + (n + tc + m) by omega]
  rcases appendSliceProg_exec (L_hdr ++ L_head) L_tail (n + tc + m) (b + 5) inArr 28
      hne5 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail]; omega) htail_w (s := s₇)
      (by rw [hreg₇ 28 (by decide) (by decide) (by decide)]; simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_tail])
      (by rw [hr57_7]; simp)
      ((harr₇ (b + 5) hne5).trans ((hs6_arr (b + 5) hne5).trans hb5))
      hin₇' with
    ⟨s₈, t₈, hex₈, ht₈, hin₈, hr57_8, harr₈, hreg₈⟩
  have hin₈' : s₈.arrs inArr = (L_hdr ++ L_head ++ L_tail) ++ List.replicate (L_Z.length + (tc + m)) 0 := by
    rw [hin₈, hlen_Z, Nat.add_assoc]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail) L_Z (tc + m) (b + 1) inArr 26
      hne1 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z]; omega) hZ_w (s := s₈)
      (by rw [hreg₈ 26 (by decide) (by decide) (by decide), hreg₇ 26 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr26, hlen_Z])
      (by rw [hr57_8]; simp; omega)
      ((harr₈ (b + 1) hne1).trans ((harr₇ (b + 1) hne1).trans ((hs6_arr (b + 1) hne1).trans hb1)))
      hin₈' with
    ⟨s₉, t₉, hex₉, ht₉, hin₉, hr57_9, harr₉, hreg₉⟩
  have hin₉' : s₉.arrs inArr = (L_hdr ++ L_head ++ L_tail ++ L_Z) ++ List.replicate (L_par.length + m) 0 := by
    rw [hin₉, hlen_par]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail ++ L_Z) L_par m (b + 2) inArr 52
      hne2 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z, hlen_par]; omega) hpar_w (s := s₉)
      (by rw [hreg₉ 52 (by decide) (by decide) (by decide),
              hreg₈ 52 (by decide) (by decide) (by decide),
              hreg₇ 52 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr52, hlen_par])
      (by rw [hr57_9]; simp; omega)
      ((harr₉ (b + 2) hne2).trans ((harr₈ (b + 2) hne2).trans
        ((harr₇ (b + 2) hne2).trans ((hs6_arr (b + 2) hne2).trans hb2))))
      hin₉' with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hin₁₀, hr57_10, harr₁₀, hreg₁₀⟩
  have hin₁₀' : s₁₀.arrs inArr = (L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_par) ++ List.replicate (L_tau.length + 0) 0 := by
    rw [hin₁₀, hlen_tau, Nat.add_zero]
  rcases appendSliceProg_exec (L_hdr ++ L_head ++ L_tail ++ L_Z ++ L_par) L_tau 0 (b + 3) inArr 28
      hne3 (by decide) (by decide) (by decide)
      h1_w (by simp [L_hdr, hlen_head, hlen_tail, hlen_Z, hlen_par, hlen_tau]; omega) htau_w (s := s₁₀)
      (by rw [hreg₁₀ 28 (by decide) (by decide) (by decide),
              hreg₉ 28 (by decide) (by decide) (by decide),
              hreg₈ 28 (by decide) (by decide) (by decide),
              hreg₇ 28 (by decide) (by decide) (by decide)];
          simp [s₆, s₅, s₄, s₃, s₂, s₁, hr28, hlen_tau])
      (by rw [hr57_10]; simp; omega)
      ((harr₁₀ (b + 3) hne3).trans ((harr₉ (b + 3) hne3).trans ((harr₈ (b + 3) hne3).trans
        ((harr₇ (b + 3) hne3).trans ((hs6_arr (b + 3) hne3).trans hb3)))))
      hin₁₀' with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hin₁₁, _, _, _⟩
  rw [List.replicate_zero, List.append_nil] at hin₁₁
  rw [hlen_head] at ht₇
  rw [hlen_tail] at ht₈
  rw [hlen_Z] at ht₉
  rw [hlen_par] at ht₁₀
  rw [hlen_tau] at ht₁₁
  refine ⟨s₁₁,
    10 + ((1 + tot) + (3 + (3 + (3 + (2 + (t₇ + (t₈ + (t₉ + (t₁₀ + t₁₁))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by dsimp [tot]; omega,
    hin₁₁⟩

end GraphMinor.Compute
