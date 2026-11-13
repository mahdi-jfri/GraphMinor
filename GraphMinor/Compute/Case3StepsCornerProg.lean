module

public import GraphMinor.Compute.Case3StepsInputMath

/-!
# Writing the four compact corner numbers

The input to (8.6) in step (5) of XIII (9.9), page 104, ends with the boundary
list. This program reads the original corner labels from the wall encoding
and their compact numbers from the rank array. It writes the length four and
these four numbers, in perimeter order, without changing any register.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read one original wall corner and then its compact rank. -/
def case3CornerRead {h : ℕ} (h2 : 2 ≤ h) (a_W a_rank : ℕ) (i : Fin 4) : Expr :=
  .read a_rank (.read a_W (.const (3 + (elemWallCornerIdx h2 i).1)))

private theorem case3Read_eval {w v j : ℕ} {s : State} (a : ℕ) (e : Expr)
    (he : e.eval w s = some j) (hg : (s.arrs a)[j]? = some v) (hv : v < 2 ^ w) :
    (Expr.read a e).eval w s = some v := by
  obtain ⟨hj, hval⟩ := List.getElem?_eq_some_iff.mp hg
  simp only [Expr.eval, he, hj, ↓reduceDIte, hval, checkWord, hv, ↓reduceIte]

/-- The double read returns the corner's compact number. -/
theorem case3CornerRead_eval {h n w : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h)
    (a_W a_rank : ℕ) (i : Fin 4)
    (hn : n < 2 ^ w) (hidx : 3 + elemWallNumVerts h < 2 ^ w)
    {s : State} (hW : s.arrs a_W = W.encList)
    (hrank : s.arrs a_rank = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1)) :
    (case3CornerRead h2 a_W a_rank i).eval w s = some (compactCorner W h2 he i).1 := by
  have hindex : 3 + (elemWallCornerIdx h2 i).1 < 2 ^ w :=
    (Nat.add_lt_add_left (elemWallCornerIdx h2 i).2 3).trans hidx
  have hread : (Expr.read a_W (.const (3 + (elemWallCornerIdx h2 i).1))).eval w s =
      some (W.cornerVert h2 i).1 := by
    apply case3Read_eval (j := 3 + (elemWallCornerIdx h2 i).1)
      (v := (W.cornerVert h2 i).1) a_W (.const (3 + (elemWallCornerIdx h2 i).1))
      (by simp only [Expr.eval, checkWord, hindex, ↓reduceIte])
    · rw [hW]
      exact case3Corner_enc_getElem W h2 i
    · exact (W.cornerVert h2 i).2.trans hn
  have hget : (s.arrs a_rank)[(W.cornerVert h2 i).1]? = some (compactCorner W h2 he i).1 := by
    rw [hrank]
    have hlt : (W.cornerVert h2 i).1 <
        (List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1)).length := by
      simpa only [List.length_ofFn] using (W.cornerVert h2 i).2
    rw [List.getElem?_eq_getElem hlt, List.getElem_ofFn, case3CompactRank_corner W h2 he i]
  have hcompact : (compactCorner W h2 he i).1 < n :=
    (compactCorner W h2 he i).2.trans_le (by
      change W.compassFinset.card ≤ n
      exact (Finset.card_le_univ _).trans (Finset.card_fin n).le)
  exact case3Read_eval a_rank _ hread hget (hcompact.trans hn)

/-- Write the boundary list suffix `[4, c₀, c₁, c₂, c₃]` of the compact
society input. Scratch registers are not needed. -/
def case3CornerRanksProg {h : ℕ} (h2 : 2 ≤ h) (a_W a_rank a_out : ℕ) : Cmd :=
  .seq (.alloc a_out (.const 5))
    (.seq (.write a_out (.const 0) (.const 4))
      (.seq (.write a_out (.const 1) (case3CornerRead h2 a_W a_rank 0))
        (.seq (.write a_out (.const 2) (case3CornerRead h2 a_W a_rank 1))
          (.seq (.write a_out (.const 3) (case3CornerRead h2 a_W a_rank 2))
            (.write a_out (.const 4) (case3CornerRead h2 a_W a_rank 3))))))

private theorem case3CornerWrite_exec {h n w : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h)
    (a_W a_rank a_out : ℕ) (i : Fin 4)
    (hn : n < 2 ^ w) (hidx : 3 + elemWallNumVerts h < 2 ^ w) (hw5 : 5 < 2 ^ w)
    {s : State} (hlen : (s.arrs a_out).length = 5) (hW : s.arrs a_W = W.encList)
    (hrank : s.arrs a_rank = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1)) :
    Exec w (.write a_out (.const (i.1 + 1)) (case3CornerRead h2 a_W a_rank i)) s
      (s.writeArr a_out (i.1 + 1) (compactCorner W h2 he i).1) 5 := by
  apply Exec.write
  · have hi : i.1 + 1 < 2 ^ w := (Nat.add_lt_add_right i.2 1).trans hw5
    simp only [Expr.eval, checkWord, hi, ↓reduceIte]
  · exact case3CornerRead_eval W h2 he a_W a_rank i hn hidx hW hrank
  · rw [hlen]
    exact Nat.add_lt_add_right i.2 1

/-- Execution and exact time of writing the compact boundary-list suffix. -/
theorem case3CornerRanksProg_exec {h n w : ℕ} {D : MultiDigraph n}
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h)
    (a_W a_rank a_out : ℕ) (hWOut : a_W ≠ a_out) (hROut : a_rank ≠ a_out)
    (hn : n < 2 ^ w) (hidx : 3 + elemWallNumVerts h < 2 ^ w) (hw5 : 5 < 2 ^ w)
    {s : State} (hW : s.arrs a_W = W.encList)
    (hrank : s.arrs a_rank = List.ofFn (fun v : Fin n => compactRank W.compassFinsetᶜ v.1)) :
    ∃ s', Exec w (case3CornerRanksProg h2 a_W a_rank a_out) s s' 29 ∧
      s'.arrs a_out = 4 :: (List.ofFn (compactCorner W h2 he)).map Fin.val ∧
      (∀ a, a ≠ a_out → s'.arrs a = s.arrs a) ∧ (∀ r, s'.regs r = s.regs r) := by
  let s₀ := s.setArr a_out (List.replicate 5 0)
  let s₁ := s₀.writeArr a_out 0 4
  let s2 := s₁.writeArr a_out 1 (compactCorner W h2 he 0).1
  let s3 := s2.writeArr a_out 2 (compactCorner W h2 he 1).1
  let s4 := s3.writeArr a_out 3 (compactCorner W h2 he 2).1
  let s5 := s4.writeArr a_out 4 (compactCorner W h2 he 3).1
  have hex₀ : Exec w (.alloc a_out (.const 5)) s s₀ 6 :=
    .alloc (by simp only [Expr.eval, checkWord, hw5, ↓reduceIte])
  have h0 : 0 < 2 ^ w := by omega
  have h4 : 4 < 2 ^ w := by omega
  have hex₁ : Exec w (.write a_out (.const 0) (.const 4)) s₀ s₁ 3 :=
    .write (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp only [Expr.eval, checkWord, h4, ↓reduceIte]) (by simp [s₀])
  have hex2 : Exec w (.write a_out (.const 1) (case3CornerRead h2 a_W a_rank 0))
      s₁ s2 5 :=
    case3CornerWrite_exec W h2 he a_W a_rank a_out 0 hn hidx hw5
      (by simp only [s₁, s₀, State.writeArr_arrs_self, State.setArr_arrs_self,
        List.length_set, List.length_replicate])
      (by simpa only [s₁, s₀, State.writeArr_arrs_ne _ _ _ hWOut,
        State.setArr_arrs_ne _ _ hWOut] using hW)
      (by simpa only [s₁, s₀, State.writeArr_arrs_ne _ _ _ hROut,
        State.setArr_arrs_ne _ _ hROut] using hrank)
  have hex3 : Exec w (.write a_out (.const 2) (case3CornerRead h2 a_W a_rank 1))
      s2 s3 5 :=
    case3CornerWrite_exec W h2 he a_W a_rank a_out 1 hn hidx hw5
      (by simp only [s2, s₁, s₀, State.writeArr_arrs_self, State.setArr_arrs_self,
        List.length_set, List.length_replicate])
      (by simpa only [s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hWOut,
        State.setArr_arrs_ne _ _ hWOut] using hW)
      (by simpa only [s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hROut,
        State.setArr_arrs_ne _ _ hROut] using hrank)
  have hex4 : Exec w (.write a_out (.const 3) (case3CornerRead h2 a_W a_rank 2))
      s3 s4 5 :=
    case3CornerWrite_exec W h2 he a_W a_rank a_out 2 hn hidx hw5
      (by simp only [s3, s2, s₁, s₀, State.writeArr_arrs_self, State.setArr_arrs_self,
        List.length_set, List.length_replicate])
      (by simpa only [s3, s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hWOut,
        State.setArr_arrs_ne _ _ hWOut] using hW)
      (by simpa only [s3, s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hROut,
        State.setArr_arrs_ne _ _ hROut] using hrank)
  have hex5 : Exec w (.write a_out (.const 4) (case3CornerRead h2 a_W a_rank 3))
      s4 s5 5 :=
    case3CornerWrite_exec W h2 he a_W a_rank a_out 3 hn hidx hw5
      (by simp only [s4, s3, s2, s₁, s₀, State.writeArr_arrs_self, State.setArr_arrs_self,
        List.length_set, List.length_replicate])
      (by simpa only [s4, s3, s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hWOut,
        State.setArr_arrs_ne _ _ hWOut] using hW)
      (by simpa only [s4, s3, s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ hROut,
        State.setArr_arrs_ne _ _ hROut] using hrank)
  refine ⟨s5, .seq hex₀ (.seq hex₁ (.seq hex2 (.seq hex3 (.seq hex4 hex5)))), ?_, ?_, ?_⟩
  · simp only [s5, s4, s3, s2, s₁, s₀, State.writeArr_arrs_self, State.setArr_arrs_self]
    rfl
  · intro a ha
    simp only [s5, s4, s3, s2, s₁, s₀, State.writeArr_arrs_ne _ _ _ ha,
      State.setArr_arrs_ne _ _ ha]
  · intro r
    rfl

end GraphMinor.Compute
