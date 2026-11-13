module

public import GraphMinor.Compute.Case3StepsParseProg

/-!
# Component searches from an encoded graph

Parsing the simple graph and preparing its outside adjacency lists give a
single program that reads an encoded graph and core bitset and writes the
component table. All vertex labels remain those of the compact graph.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Parse array 16, initialize the restriction parameters, and compute rows. -/
def case3EncodedComponentsProg : Cmd :=
  .seq case3ParseProg
    (.seq (.assign 1 (.reg 32))
      (.seq (.assign 2 (.op .mul (.const 2) (.reg 33))) case3AllComponentsProg))

/-- The complete component computation from a simple graph encoding. Its
bound uses the simple edge count, and arrays below 10 are preserved. -/
theorem case3EncodedComponentsProg_exec {w : ℕ} (x : Alg81Input)
    (Z : Finset (Fin x.n)) (hw : 2 < 2 ^ w)
    (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hm : 2 + 2 * (edgeListOf x.G).length < 2 ^ w)
    {s : State} (hinput : s.arrs 16 = encGraph x.G) (hZ : IsBitSet Z 10 s) :
    ∃ s' t, Exec w case3EncodedComponentsProg s s' t ∧
      t ≤ x.n * x.n + x.n * (38 * x.n + 52 * (edgeListOf x.G).length + 47) +
        64 * x.n + 140 * (edgeListOf x.G).length + 59 ∧
      s'.arrs 12 = case3ComponentRows x Z ∧ s'.arrs 10 = bitSetList Z ∧
      (∀ a < 10, s'.arrs a = s.arrs a) ∧
      IsAdjList x.G 19 20 21 (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs 21).length = 2 * (edgeListOf x.G).length ∧ s'.regs 14 = x.n := by
  have hnw : x.n < 2 ^ w := by omega
  have hmw : (edgeListOf x.G).length < 2 ^ w := by omega
  have h2mw : 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hadj₁, hlen₁, hrn₁, hrm₁, harr₁, _⟩ :=
    case3ParseProg_exec x hw hnw hm hinput
  let s₂ := s₁.setReg 1 x.n
  let s₃ := s₂.setReg 2 (2 * (edgeListOf x.G).length)
  have hex₂ : Exec w (.assign 1 (.reg 32)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₁, hnw])
  have hex₃ : Exec w (.assign 2 (.op .mul (.const 2) (.reg 33))) s₂ s₃ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, State.setReg,
      hrm₁, hw, hmw, h2mw])
  have hcard : x.G.edgeFinset.card = (edgeListOf x.G).length := by
    have h₁ := totalAdjEntries_eq_two_mul_card_edgeFinset hadj₁.2
    have h₂ := totalAdjEntries_edgeNeighbors (edgeListOf x.G) (isSimpleEdgeList_edgeListOf x.G).1
    omega
  have hbound : 2 * (edgesInSet x.G (Finset.univ \ Z)).card ≤
      2 * (edgeListOf x.G).length := by
    rw [← hcard]
    exact Nat.mul_le_mul_left 2 (card_edgesInSet_le_card_edgeFinset x.G _)
  obtain ⟨s₄, t₄, hex₄, ht₄, hdst₄, hZ₄, _, harr₄, _, hfull₄, hr14₄⟩ :=
    case3AllComponentsProg_exec x Z (edgeNeighbors (edgeListOf x.G))
      (2 * (edgeListOf x.G).length) (by omega) hn hsq h2mw hbound
      (s := s₃) (hadj₁.of_arrs_eq rfl rfl rfl)
      (by change (s₁.arrs 21).length < 2 ^ w; rw [hlen₁]; exact h2mw)
      (hZ.of_arr_eq (harr₁ 10 (by decide)))
      (by simp [s₃, s₂, State.setReg]) (State.setReg_regs_self ..)
  have htot := totalAdjEntries_edgeNeighbors (edgeListOf x.G) (isSimpleEdgeList_edgeListOf x.G).1
  rw [htot] at ht₄
  have hmul : 26 * (2 * (edgeListOf x.G).length) = 52 * (edgeListOf x.G).length := by omega
  rw [hmul] at ht₄
  refine ⟨s₄, t₁ + (2 + (4 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, hdst₄, hZ₄, ?_, ?_, ?_, hr14₄⟩
  · intro a ha
    rw [harr₄ a ha]
    exact harr₁ a (by romega)
  · exact hadj₁.of_arrs_eq
      (hfull₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hfull₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hfull₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  · rw [hfull₄ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hlen₁

end GraphMinor.Compute
