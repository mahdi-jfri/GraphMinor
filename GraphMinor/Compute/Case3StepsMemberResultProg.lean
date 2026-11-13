module

public import GraphMinor.Compute.Case3StepsWriteBranchRecordProg
public import GraphMinor.Compute.Case3StepsWallResultDataProg

/-!
# Dispatching the result of a member call

The leading word of the returned (7.2) code selects branch-record writing
or original-label wall data. Register 0 records which result was written,
so the outer member scan can stop at the first wall.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the selected member result and set the wall-found flag. -/
def case3MemberResultProg (h : ℕ) : Cmd :=
  .ite (.read 129 (.const 0))
    (.seq (case3WallResultDataProg h) (.assign 0 (.const 1)))
    (.seq case3WriteBranchRecordProg (.assign 0 (.const 0)))

/-- Reading a nonempty returned code reads its leading tag. -/
theorem case3MemberTag_eval {w b : ℕ} {code : List ℕ} {s : State}
    (hsrc : s.arrs 129 = b :: code) (hb : b < 2 ^ w) :
    (Expr.read 129 (.const 0)).eval w s = some b := by
  have h0 := Nat.two_pow_pos w
  simp only [Expr.eval, checkWord, h0, hsrc, List.length_cons, Nat.zero_lt_succ,
    List.getElem_cons_zero, hb, ↓reduceIte, ↓reduceDIte]

/-- A returned branch code writes the exact original-label record and
leaves the wall-found flag zero. -/
theorem case3MemberResultProg_branch_exec {w h n N B : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w) (hsize : n + 6 * G.numEdges + 4 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ x ∈ code, x < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code) (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) :
    ∃ s' t, Exec w (case3MemberResultProg h) s s' t ∧
      t ≤ 1200 * (n + G.numEdges + G.numActivePairs + 1) + 4 ∧
      s'.regs 0 = 0 ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      s'.arrs 51 = r.enc ∧ r.enc.length ≤ n + 6 * G.numEdges + 4 ∧
      (∀ z ∈ s'.arrs 51, z < 2 ^ w) ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → s'.arrs a = s.arrs a) ∧
      (∀ r < 70, r ≠ 0 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hrec, hrecsize, hrecwords, harr, hreg⟩ :=
    case3WriteBranchRecordProg_exec G orig hinj code hcode hw hn hN hA hsize hlen hwords hsrc hG hlabels
  let s₂ := s₁.setReg 0 0
  have hex₂ : Exec w (.assign 0 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, Nat.two_pow_pos, ↓reduceIte])
  refine ⟨s₂, 2 + (t₁ + 2), .ite_false (case3MemberTag_eval hsrc (Nat.two_pow_pos _))
    (.seq hex₁ hex₂), by omega, State.setReg_regs_self .., hrec, hrecsize, hrecwords, harr, ?_⟩
  intro r hr hne
  dsimp only [Reg] at hr
  rw [State.setReg_regs_ne _ _ hne]
  exact hreg r (by dsimp only [Reg]; omega)

/-- A returned wall writes the four original-label data arrays and sets
the wall-found flag to one. -/
theorem case3MemberResultProg_wall_exec {w h N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (T bd : Finset (Fin S.card)) (hbd : bd.card ≤ 3)
    (W : WallOfHeight h (D.induce (T.orderEmbOfFin rfl))) (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid)
    (hw : 6 < 2 ^ w) (hcard : S.card + 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hlen : (1 :: W.encList).length < 2 ^ w) (hwords : ∀ x ∈ W.encList, x < 2 ^ w)
    {s : State} (hwall : s.arrs 129 = 1 :: W.encList) (hD : s.arrs 39 = D.enc)
    (hrank : (s.arrs 2).length = N)
    (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin S.card, (s.arrs 32).getD i.1 0 = (S.orderEmbOfFin rfl i).1)
    (hmember : s.arrs 31 = (case3BoundaryVertices T).map Fin.val ++ List.replicate (S.card - T.card) 0)
    (hcount : s.regs 62 = T.card) (hkey : s.arrs 25 = case3BoundaryKey bd)
    (horig : s.arrs 47 = List.ofFn (fun i : Fin T.card =>
      (S.orderEmbOfFin rfl (T.orderEmbOfFin rfl i)).1)) :
    ∃ s' t, Exec w (case3MemberResultProg h) s s' t ∧
      t ≤ 60 * W.encList.length + 38 * D.numActivePairs + 14 * T.card + 2 * N + 128 ∧
      s'.regs 0 = 1 ∧
      let P := case3PushMultigraph S D
      let V := T.image (S.orderEmbOfFin rfl)
      s'.arrs 54 = P.enc ∧ IsBitSet V 55 s' ∧ IsBitSet (bd.image (S.orderEmbOfFin rfl)) 56 s' ∧
      (∃ W_A : WallOfHeight h (P.deleteVerticesCompact Vᶜ), W_A.IsValid ∧
        ∃ hnext : (W_A.moveOrig P (compactEmb Vᶜ)).IsValid,
          ((W_A.moveOrig P (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
            P.toGMDigraph.toGraph.induce V.toNatSet ∧
          s'.arrs 46 = (W_A.moveOrig P (compactEmb Vᶜ)).encList) ∧
      (∀ a, a ≠ 46 → a ≠ 54 → a ≠ 55 → a ≠ 56 → s'.arrs a = s.arrs a) ∧
      (∀ r < 70, r ≠ 0 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hgraph, hV, hBd, hwall₁, harr, hreg⟩ :=
    case3WallResultDataProg_exec S D T bd hbd W h2 heven hW hw hcard hN hA he
      hlen hwords hwall hD hrank hlistlen hlist hmember hcount hkey horig
  let s₂ := s₁.setReg 0 1
  have h1 : 1 < 2 ^ w := by omega
  have hex₂ : Exec w (.assign 0 (.const 1)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h1, ↓reduceIte])
  refine ⟨s₂, 2 + (t₁ + 2), .ite_true (case3MemberTag_eval hwall h1) (by decide)
    (.seq hex₁ hex₂), by omega, State.setReg_regs_self .., hgraph, ?_, ?_, ?_, harr, ?_⟩
  · exact hV
  · exact hBd
  · exact hwall₁
  · intro r hr hne
    dsimp only [Reg] at hr
    rw [State.setReg_regs_ne _ _ hne]
    exact hreg r (by dsimp only [Reg]; omega)

end GraphMinor.Compute
