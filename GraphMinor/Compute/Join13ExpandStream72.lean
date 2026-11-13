module

public import GraphMinor.Compute.Join13ExpandList72

/-!
# Reading the graph triple stream for (7.2)

For each input triple the loop reads its two endpoints and multiplicity, expands
that multiplicity, and advances by three source words. The resulting endpoint
stream has one pair for every individual edge.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Expand one triple. Registers `r + 4` and `r + 5` hold the source position
and the remaining triple count. -/
def expandPairStream72Body (a_src a_buf r : ℕ) : Cmd :=
  .seq (.assign (r + 1) (.read a_src (.reg (r + 4))))
  (.seq (.assign (r + 2) (.read a_src (.op .add (.reg (r + 4)) (.const 1))))
  (.seq (.assign (r + 3) (.read a_src (.op .add (.reg (r + 4)) (.const 2))))
  (.seq (repeatEndpoints72Prog a_buf r)
  (.seq (.assign (r + 4) (.op .add (.reg (r + 4)) (.const 3)))
        (.assign (r + 5) (.op .sub (.reg (r + 5)) (.const 1)))))))

/-- Expand all remaining triples. -/
def expandPairStream72Loop (a_src a_buf r : ℕ) : Cmd :=
  .while (.reg (r + 5)) (expandPairStream72Body a_src a_buf r)

private theorem getD_pairTriple72 (pre post : List ℕ) (u v m j : ℕ) (hj : j < 3) :
    (pre ++ [u, v, m] ++ post).getD (pre.length + j) 0 = [u, v, m].getD j 0 := by
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ (by simpa using hj)]

/-- Expanding a triple stream takes time linear in the number of triples plus
the number of individual edges. -/
theorem expandPairStream72Loop_exec {w n : ℕ} (G : MultiDigraph n)
    (ps : List (Fin n × Fin n)) (a_src a_buf r : ℕ) (hne : a_src ≠ a_buf)
    (pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hcap : pre_dst.length + 2 * G.sumEdgeMult ps + rem < 2 ^ w)
    (hsrc_len : (pre_src ++ G.flatTriples ps ++ post_src).length < 2 ^ w)
    (hsrc : s.arrs a_src = pre_src ++ G.flatTriples ps ++ post_src)
    (hbuf : s.arrs a_buf = pre_dst ++ List.replicate (2 * G.sumEdgeMult ps + rem) 0)
    (hr_pos : s.regs r = pre_dst.length) (hr_src : s.regs (r + 4) = pre_src.length)
    (hr_count : s.regs (r + 5) = ps.length) :
    ∃ s' t, Exec w (expandPairStream72Loop a_src a_buf r) s s' t ∧
      t ≤ 100 * (G.sumEdgeMult ps + ps.length) + 1 ∧
      s'.arrs a_buf = pre_dst ++ expandedPairs72 G ps ++ List.replicate rem 0 ∧
      s'.regs r = (pre_dst ++ expandedPairs72 G ps).length ∧
      s'.regs (r + 4) = (pre_src ++ G.flatTriples ps).length ∧
      s'.regs (r + 5) = 0 ∧ Keeps [r, r + 1, r + 2, r + 3, r + 4, r + 5] [a_buf] s s' := by
  induction ps generalizing pre_src pre_dst s with
  | nil =>
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hr_count]), by simp [MultiDigraph.sumEdgeMult],
      ?_, ?_, ?_, hr_count, Keeps.refl _ _ s⟩
    · simpa [expandedPairs72, MultiDigraph.sumEdgeMult] using hbuf
    · simpa [expandedPairs72] using hr_pos
    · simpa [MultiDigraph.flatTriples] using hr_src
  | cons p ps ih =>
    let u := p.1.1
    let v := p.2.1
    let mult := G.edgeMult p.1 p.2
    let words := (List.replicate mult [u, v]).flatten
    have hu : u < 2 ^ w := p.1.2.trans hn
    have hv : v < 2 ^ w := p.2.2.trans hn
    have hcap' : pre_dst.length + 2 * mult + 2 * G.sumEdgeMult ps + rem < 2 ^ w := by
      simpa only [MultiDigraph.sumEdgeMult, Nat.mul_add, Nat.add_assoc] using hcap
    have hm : mult < 2 ^ w := by omega
    have hsource : s.arrs a_src = pre_src ++ [u, v, mult] ++ (G.flatTriples ps ++ post_src) := by
      simpa [MultiDigraph.flatTriples, u, v, mult, List.append_assoc] using hsrc
    have hsource_sz : pre_src.length + 3 + 3 * ps.length + post_src.length < 2 ^ w := by
      have hh := hsrc_len
      simp only [List.length_append, MultiDigraph.length_flatTriples, List.length_cons] at hh
      omega
    have hsource_bound : pre_src.length + 2 < (s.arrs a_src).length := by
      rw [hsource]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
    have hget0 : (s.arrs a_src).getD pre_src.length 0 = u := by
      rw [hsource]
      simp
    have hget1 : (s.arrs a_src).getD (pre_src.length + 1) 0 = v := by
      rw [hsource]
      simp
    have hget2 : (s.arrs a_src).getD (pre_src.length + 2) 0 = mult := by
      rw [hsource]
      simp
    let s₁ := s.setReg (r + 1) u
    have hex₁ : Exec w (.assign (r + 1) (.read a_src (.reg (r + 4)))) s s₁ 3 :=
      exec_assign_read_getD (r + 1) a_src (r + 4) hr_src (by omega) (by omega) hget0 hu
    let s₂ := s₁.setReg (r + 2) v
    have hex₂ : Exec w (.assign (r + 2) (.read a_src (.op .add (.reg (r + 4)) (.const 1)))) s₁ s₂ 5 := by
      apply Exec.assign
      have hi : (.op .add (.reg (r + 4)) (.const 1) : Expr).eval w s₁ = some (pre_src.length + 1) := by
        simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_src,
          show pre_src.length < 2 ^ w by omega, show pre_src.length + 1 < 2 ^ w by omega,
          show 1 < 2 ^ w by omega]
      have hb : pre_src.length + 1 < (s₁.arrs a_src).length := by change pre_src.length + 1 < (s.arrs a_src).length; omega
      have hg : (s₁.arrs a_src)[pre_src.length + 1] = v := by rw [← List.getD_eq_getElem _ _ hb]; exact hget1
      simpa only [hg] using read_eval hi hb (by rw [hg]; exact hv)
    let s₃ := s₂.setReg (r + 3) mult
    have hex₃ : Exec w (.assign (r + 3) (.read a_src (.op .add (.reg (r + 4)) (.const 2)))) s₂ s₃ 5 := by
      apply Exec.assign
      have hi : (.op .add (.reg (r + 4)) (.const 2) : Expr).eval w s₂ = some (pre_src.length + 2) := by
        simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_src,
          show pre_src.length < 2 ^ w by omega, show pre_src.length + 2 < 2 ^ w by omega,
          show 2 < 2 ^ w by omega]
      have hb : pre_src.length + 2 < (s₂.arrs a_src).length := hsource_bound
      have hg : (s₂.arrs a_src)[pre_src.length + 2] = mult := by rw [← List.getD_eq_getElem _ _ hb]; exact hget2
      simpa only [hg] using read_eval hi hb (by rw [hg]; exact hm)
    obtain ⟨s₄, t₄, hex₄, ht₄, hd₄, hp₄, _, hk₄⟩ :=
      repeatEndpoints72Prog_exec a_buf r u v mult (2 * G.sumEdgeMult ps + rem) pre_dst s₃
        (by omega) hu hv (by omega)
        (by
          change s.arrs a_buf = _
          simpa only [mult, MultiDigraph.sumEdgeMult, Nat.mul_add, Nat.add_assoc] using hbuf)
        (by simp [s₃, s₂, s₁, hr_pos]) (by simp [s₃, s₂, s₁])
        (by simp [s₃, s₂]) (by simp [s₃])
    have hr_source₄ : s₄.regs (r + 4) = pre_src.length := by
      rw [hk₄.1 (r + 4) (by simp)]
      simp [s₃, s₂, s₁, hr_src]
    let s₅ := s₄.setReg (r + 4) (pre_src.length + 3)
    have hex₅ : Exec w (.assign (r + 4) (.op .add (.reg (r + 4)) (.const 3))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_source₄, hw,
        show pre_src.length < 2 ^ w by omega, show pre_src.length + 3 < 2 ^ w by omega])
    have hr_count₅ : s₅.regs (r + 5) = ps.length + 1 := by
      rw [State.setReg_regs_ne _ _ (show (r + 5 : ℕ) ≠ r + 4 by omega), hk₄.1 _ (by simp)]
      simp [s₃, s₂, s₁, hr_count]
    let s₆ := s₅.setReg (r + 5) ps.length
    have hex₆ : Exec w (.assign (r + 5) (.op .sub (.reg (r + 5)) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_count₅,
        show ps.length + 1 < 2 ^ w by omega, show ps.length < 2 ^ w by omega,
        show 1 < 2 ^ w by omega])
    have ha₆ (a : ℕ) (ha : a ≠ a_buf) : s₆.arrs a = s.arrs a := hk₄.2 a (by simpa using ha)
    have hwords : words.length = 2 * mult := by simp [words, List.length_flatten, List.map_replicate, List.sum_replicate, Nat.mul_comm]
    obtain ⟨s', t', hex', ht', hd', hp', hs', hc', hk'⟩ :=
      ih (pre_src ++ [u, v, mult]) (pre_dst ++ words) s₆
        (by simp only [List.length_append, hwords]; omega)
        (by simpa [MultiDigraph.flatTriples, u, v, mult, List.append_assoc] using hsrc_len)
        (by rw [ha₆ a_src hne, hsource]; simp [List.append_assoc])
        hd₄
        (by rw [State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 5 by omega),
          State.setReg_regs_ne _ _ (show (r : ℕ) ≠ r + 4 by omega)]; exact hp₄)
        (by simp [s₆, s₅, List.length_append])
        (by simp [s₆])
    have hcount_w : ps.length + 1 < 2 ^ w := by omega
    have hcond : (.reg (r + 5) : Expr).eval w s = some (ps.length + 1) := by
      simp [Expr.eval, checkWord, hr_count, hcount_w]
    have hbody : Exec w (expandPairStream72Body a_src a_buf r) s s₆ (3 + (5 + (5 + (t₄ + (4 + 4))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
    refine ⟨s', 1 + (3 + (5 + (5 + (t₄ + (4 + 4))))) + t',
      .while_true hcond (by omega) hbody hex', ?_, ?_, ?_, ?_, hc', ?_⟩
    · simp only [MultiDigraph.sumEdgeMult, List.length_cons, Nat.mul_add] at ht' ⊢
      omega
    · simpa only [expandedPairs72, List.flatMap_cons, words, u, v, mult, List.append_assoc] using hd'
    · simpa only [expandedPairs72, List.flatMap_cons, words, u, v, mult, List.append_assoc] using hp'
    · simpa [MultiDigraph.flatTriples, u, v, mult, List.append_assoc] using hs'
    · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
      · have hne0 : j ≠ r := by simp only [List.mem_cons, not_or] at hj; tauto
        have hne1 : j ≠ r + 1 := by simp only [List.mem_cons, not_or] at hj; tauto
        have hne2 : j ≠ r + 2 := by simp only [List.mem_cons, not_or] at hj; tauto
        have hne3 : j ≠ r + 3 := by simp only [List.mem_cons, not_or] at hj; tauto
        have hne4 : j ≠ r + 4 := by simp only [List.mem_cons, not_or] at hj; tauto
        have hne5 : j ≠ r + 5 := by simp only [List.mem_cons, not_or] at hj; tauto
        rw [hk'.1 j hj, State.setReg_regs_ne _ _ hne5, State.setReg_regs_ne _ _ hne4,
          hk₄.1 j (by simp [hne0, hne3])]
        simp [s₃, s₂, s₁, hne1, hne2, hne3]
      · rw [hk'.2 a ha]
        exact ha₆ a (by simpa using ha)

end GraphMinor.Compute
