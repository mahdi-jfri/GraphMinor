module

public import GraphMinor.Compute.Case3StepsMemberResultCapacity
public import GraphMinor.Compute.Specs13

/-!
# Processing either returned member code

A valid (7.2) output supplies either a branch code or a compact wall. The
result program handles both cases. A branch record consumes only its own
part of the shared buffer. A wall leaves the buffer unchanged and writes
the four original-label arrays, with the exact moved-wall graph.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Every valid returned member code can be processed, with a bound that
charges copying the wall to the returned code length. -/
theorem case3MemberResultStoreProg_exec {w h N ω count remaining : ℕ}
    (S : Finset (Fin N)) (D : MultiDigraph S.card) (T bd : Finset (Fin S.card))
    (hbd : bd.card ≤ 3) (h2 : 2 ≤ h) (heven : Even h)
    (hw : 6 < 2 ^ w) (hcard : S.card + 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hCA : 2 + 3 * (D.induce (T.orderEmbOfFin rfl)).numActivePairs < 2 ^ w)
    (pre : List ℕ)
    (hremaining : T.card + 6 * (D.induce (T.orderEmbOfFin rfl)).numEdges + 4 ≤ remaining)
    (hcapacity : pre.length + remaining < 2 ^ w) (hcount : count + 1 < 2 ^ w)
    {s : State}
    (hout : IsAlgorithm72Output ω h ⟨T.card, D.induce (T.orderEmbOfFin rfl)⟩ (s.arrs 129))
    (hlen : (s.arrs 129).length < 2 ^ w) (hwords : ∀ z ∈ s.arrs 129, z < 2 ^ w)
    (hD : s.arrs 39 = D.enc) (hcompact : s.arrs 38 = (D.induce (T.orderEmbOfFin rfl)).enc)
    (hrank : (s.arrs 2).length = N) (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin S.card, (s.arrs 32).getD u.1 0 = (S.orderEmbOfFin rfl u).1)
    (hmember : s.arrs 31 = (case3BoundaryVertices T).map Fin.val ++ List.replicate (S.card - T.card) 0)
    (hmembercount : s.regs 62 = T.card) (hkey : s.arrs 25 = case3BoundaryKey bd)
    (horig : s.arrs 47 = List.ofFn (fun u : Fin T.card =>
      (S.orderEmbOfFin rfl (T.orderEmbOfFin rfl u)).1))
    (hbuf : s.arrs 57 = pre ++ List.replicate remaining 0)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w (case3MemberResultStoreProg h) s s' t ∧
      t ≤ 1500 * (T.card + (D.induce (T.orderEmbOfFin rfl)).numEdges +
          (D.induce (T.orderEmbOfFin rfl)).numActivePairs + 1) +
        60 * (s.arrs 129).length + 38 * D.numActivePairs + 14 * T.card + 2 * N + 130 ∧
      ((∃ code : List ℕ, IsValidBranchDecompCode ω (D.induce (T.orderEmbOfFin rfl)) code ∧
        let orig := fun u : Fin T.card => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl u)
        let r := case3BranchRecord (D.induce (T.orderEmbOfFin rfl))
          (origVertexEmb orig ((S.orderEmbOfFin rfl).injective.comp (T.orderEmbOfFin rfl).injective))
          (origEdgeEmb orig ((S.orderEmbOfFin rfl).injective.comp (T.orderEmbOfFin rfl).injective)) code
        s'.regs 0 = 0 ∧ s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
        s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0) ∨
      (s'.regs 0 = 1 ∧
        let P := case3PushMultigraph S D
        let V := T.image (S.orderEmbOfFin rfl)
        s'.arrs 54 = P.enc ∧ IsBitSet V 55 s' ∧ IsBitSet (bd.image (S.orderEmbOfFin rfl)) 56 s' ∧
        (∃ WA : WallOfHeight h (P.deleteVerticesCompact Vᶜ), WA.IsValid ∧
          ∃ hnext : (WA.moveOrig P (compactEmb Vᶜ)).IsValid,
            ((WA.moveOrig P (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
              P.toGMDigraph.toGraph.induce V.toNatSet ∧
            s'.arrs 46 = (WA.moveOrig P (compactEmb Vᶜ)).encList))) ∧
      (∀ a, a ≠ 46 → a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 →
        a ≠ 54 → a ≠ 55 → a ≠ 56 → a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ r < 70, r ≠ 0 → r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  let Gm := D.induce (T.orderEmbOfFin rfl)
  let orig := fun u : Fin T.card => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl u)
  have hinj : Function.Injective orig :=
    (S.orderEmbOfFin rfl).injective.comp (T.orderEmbOfFin rfl).injective
  have hTcard : T.card ≤ S.card := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  rcases hout with ⟨code, hsrc, hcode⟩ | ⟨W, hW, hsrc⟩
  · have hcodewords : ∀ z ∈ code, z < 2 ^ w := by
      intro z hz
      exact hwords z (hsrc ▸ List.mem_cons_of_mem 0 hz)
    obtain ⟨s', t, hex, ht, hbuffer, hflag, hused', hnum', harr, hreg⟩ :=
      case3MemberResultStoreProg_branch_capacity_exec (h := h) (remaining := remaining)
        Gm orig hinj code pre hcode (by omega) (by omega) hN hCA hremaining hcapacity hcount
        (hsrc ▸ hlen) hcodewords hsrc hcompact horig hbuf hused hnum
    dsimp only [Gm] at ht
    refine ⟨s', t, hex, by omega, Or.inl ⟨code, hcode, hflag, hused', hnum', hbuffer⟩, ?_, hreg⟩
    intro a _ h48 h49 h50 h51 h52 h53 _ _ _ h57
    exact harr a h48 h49 h50 h51 h52 h53 h57
  · have hwallwords : ∀ z ∈ W.encList, z < 2 ^ w := by
      intro z hz
      exact hwords z (hsrc ▸ List.mem_cons_of_mem 1 hz)
    obtain ⟨s', t, hex, ht, hflag, hgraph, hV, hBd, hwall, harr, hreg⟩ :=
      case3MemberResultStoreProg_wall_exec (w := w) (s := s) S D T bd hbd W h2 heven hW
        hw hcard hN hA he (hsrc ▸ hlen) hwallwords hsrc hD hrank hlistlen hlist
        hmember hmembercount hkey horig
    have hlength : (s.arrs 129).length = W.encList.length + 1 := by rw [hsrc, List.length_cons]
    refine ⟨s', t, hex, by omega, Or.inr ⟨hflag, hgraph, hV, hBd, hwall⟩, ?_, ?_⟩
    · intro a h46 _ _ _ _ _ _ h54 h55 h56 _
      exact harr a h46 h54 h55 h56
    · intro r hr h0 _ _
      exact hreg r hr h0

end GraphMinor.Compute
