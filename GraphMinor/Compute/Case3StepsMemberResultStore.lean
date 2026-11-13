module

public import GraphMinor.Compute.Case3StepsMemberResultProg
public import GraphMinor.Compute.Case3StepsStoreMemberRecord

/-!
# Writing and retaining a member result

After dispatching the returned code, copy a branch record into the shared
buffer. A wall result skips this copy and leaves the stopping flag set.
The branch case below accounts for both record writing and storage.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Dispatch the member result and store its record when no wall was found. -/
def case3MemberResultStoreProg (h : ℕ) : Cmd :=
  .seq (case3MemberResultProg h) (.ite (.reg 0) .skip case3StoreMemberRecordProg)

/-- A returned branch decomposition is serialized and appended in linear
member size, with the exact prefix and record counters. -/
theorem case3MemberResultStoreProg_branch_exec {w h n N B count : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code pre rest : List ℕ)
    (hcode : IsValidBranchDecompCode B G code) (hw : 3 < 2 ^ w)
    (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hsize : pre.length + (n + 6 * G.numEdges + 4) < 2 ^ w)
    (hcount : count + 1 < 2 ^ w)
    (hlen : (0 :: code).length < 2 ^ w) (hwords : ∀ z ∈ code, z < 2 ^ w)
    {s : State} (hsrc : s.arrs 129 = 0 :: code) (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 57 = pre ++ List.replicate
      (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code).enc.length 0 ++ rest)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w (case3MemberResultStoreProg h) s s' t ∧
      t ≤ 1500 * (n + G.numEdges + G.numActivePairs + 1) ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      s'.arrs 57 = pre ++ r.enc ++ rest ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ r < 70, r ≠ 0 → r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  obtain ⟨s₁, t₁, hex₁, ht₁, hflag, hrec, hrecsize, hrecwords, harr₁, hreg₁⟩ :=
    case3MemberResultProg_branch_exec (h := h) G orig hinj code hcode hw hn hN hA
      (by omega) hlen hwords hsrc hG hlabels
  change r.enc.length ≤ n + 6 * G.numEdges + 4 at hrecsize
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hused₂, hnum₂, harr₂, hreg₂⟩ :=
    case3StoreMemberRecordProg_exec (w := w) (count := count) pre r.enc rest (by omega)
      (by omega) hcount (by rw [← hrec]; exact hrecwords) hrec
      ((harr₁ 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbuf)
      ((hreg₁ 1 (by decide) (by decide)).trans hused)
      ((hreg₁ 2 (by decide) (by decide)).trans hnum)
  have htest : (Expr.reg 0).eval w s₁ = some 0 := by
    simp only [Expr.eval, checkWord, hflag, Nat.two_pow_pos, ↓reduceIte]
  refine ⟨s₂, t₁ + (1 + t₂), .seq hex₁ (.ite_false htest hex₂), by omega,
    hbuf₂, (hreg₂ 0 (by decide) (by decide) (by decide)).trans hflag, hused₂, hnum₂, ?_, ?_⟩
  · intro a h48 h49 h50 h51 h52 h53 h57
    exact (harr₂ a h57).trans (harr₁ a h48 h49 h50 h51 h52 h53)
  · intro j hj h0 h1 h2
    exact (hreg₂ j (by romega) h1 h2).trans (hreg₁ j hj h0)

/-- A wall result stops the record scan without changing the record buffer. -/
theorem case3MemberResultStoreProg_wall_exec {w h N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
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
    ∃ s' t, Exec w (case3MemberResultStoreProg h) s s' t ∧
      t ≤ 60 * W.encList.length + 38 * D.numActivePairs + 14 * T.card + 2 * N + 130 ∧
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
  obtain ⟨s₁, t₁, hex₁, ht₁, hflag, hgraph, hV, hBd, hwall₁, harr, hreg⟩ :=
    case3MemberResultProg_wall_exec S D T bd hbd W h2 heven hW hw hcard hN hA he
      hlen hwords hwall hD hrank hlistlen hlist hmember hcount hkey horig
  have h1 : 1 < 2 ^ w := by omega
  have htest : (Expr.reg 0).eval w s₁ = some 1 := by
    simp only [Expr.eval, checkWord, hflag, h1, ↓reduceIte]
  exact ⟨s₁, t₁ + (1 + 1), .seq hex₁ (.ite_true htest (by decide) (.skip s₁)),
    by omega, hflag, hgraph, hV, hBd, hwall₁, harr, hreg⟩

end GraphMinor.Compute
