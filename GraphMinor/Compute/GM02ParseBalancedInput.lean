module

public import GraphMinor.Compute.GM02BalancedSeparationInput
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Parsing the plain balanced-separation input

Read the simple graph's edge-list prefix with the standard CSR parser,
then copy the supplied subset membership bits into array five. No
separator, component, or answer is encoded in the input. The result is
the adjacency representation and subset array used by the RAM search
for II (3.1), page 316.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- Read one supplied subset bit after the ordinary graph prefix. -/
def gm02InputSubsetExpr : Expr := .read inArr
  (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 41))) (.reg 180))

/-- Parse graph adjacency and copy the supplied subset bits. -/
def gm02ParseBalancedInputProg : Cmd :=
  .seq (parseGraphProg 9 10 11 12 40) (gm13TabulateProg 180 (.reg 40) gm02InputSubsetExpr 5)

/-- The appended words are exactly the supplied subset bits. -/
theorem GM02Alg31Input.enc_subset {i : ℕ} (x : GM02Alg31Input) (hi : i < x.n) :
    x.enc[2 + 2 * (edgeListOf x.G).length + i]'(by rw [x.enc_length]; omega) =
      (gm02VertexBits x.Q)[i]'(by simpa only [gm02VertexBits, List.length_ofFn] using hi) := by
  have hpre : (encGraph x.G).length ≤ 2 + 2 * (edgeListOf x.G).length + i := by
    rw [length_encGraph]
    omega
  simp only [GM02Alg31Input.enc, List.getElem_append_right hpre]
  have hidx : 2 + 2 * (edgeListOf x.G).length + i - (encGraph x.G).length = i := by
    rw [length_encGraph]
    omega
  simp only [hidx]

/-- The parser runs in linear time in the edge-list length plus vertex
count and produces exactly the graph and subset arrays used by the search. -/
theorem gm02ParseBalancedInputProg_exec {w : ℕ} (x : GM02Alg31Input) (s : State)
    (hw : 4 < 2 ^ w) (hlen : x.enc.length < 2 ^ w) (hin : s.arrs inArr = x.enc) :
    ∃ s' t, Exec w gm02ParseBalancedInputProg s s' t ∧
      t ≤ 43 * x.n + 88 * (edgeListOf x.G).length + 33 ∧
      s'.regs 40 = x.n ∧ s'.regs 41 = (edgeListOf x.G).length ∧
      IsAdjList x.G 10 11 12 (edgeNeighbors (edgeListOf x.G)) s' ∧
      (s'.arrs 12).length = 2 * (edgeListOf x.G).length ∧
      s'.arrs 5 = gm02VertexBits x.Q ∧ s'.arrs inArr = x.enc := by
  have hl := x.enc_length
  have hn : x.n < 2 ^ w := (show x.n ≤ x.enc.length by omega).trans_lt hlen
  have hp : 2 + 2 * (edgeListOf x.G).length < 2 ^ w :=
    (show 2 + 2 * (edgeListOf x.G).length ≤ x.enc.length by omega).trans_lt hlen
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hrn₁, hrm₁, hadj₁, hent₁, _⟩ :=
    Triple.parseGraphProg_spec (w := w) x.G (edgeListOf x.G) (gm02VertexBits x.Q)
      9 10 11 12 40 (isSimpleEdgeList_edgeListOf x.G)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) hn hp s (by simpa only [GM02Alg31Input.enc, encGraph, List.append_assoc] using hin)
  have hin₁' : s₁.arrs inArr = x.enc := by
    simpa only [GM02Alg31Input.enc, encGraph, List.append_assoc] using hin₁
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hq₂⟩ := gm13TabulateProg_exec (w := w) 180 (.reg 40)
    gm02InputSubsetExpr 5 (gm02VertexBits x.Q) s₁ (by omega)
    (by simpa only [gm02VertexBits, List.length_ofFn] using hn)
    (fun st hk => by
      simp only [gm02VertexBits, List.length_ofFn]
      exact eval_reg ((hk.1 _ (by decide)).trans hrn₁) hn)
    (fun st i hi hk hri => by
      have hinV : i < x.n := by simpa only [gm02VertexBits, List.length_ofFn] using hi
      have hinput : st.arrs inArr = x.enc := (hk.2 _ (by decide)).trans hin₁'
      have hm : st.regs 41 = (edgeListOf x.G).length := (hk.1 _ (by decide)).trans hrm₁
      have hmw : (edgeListOf x.G).length < 2 ^ w := by omega
      have h2m : 2 * (edgeListOf x.G).length < 2 ^ w := by omega
      have hidx : 2 + 2 * (edgeListOf x.G).length + i < x.enc.length := by omega
      have hidxw := hidx.trans hlen
      have heidx := eval_add (eval_add (eval_const (show 2 < 2 ^ w by omega))
        (eval_mul (eval_const (show 2 < 2 ^ w by omega)) (eval_reg hm hmw) h2m) hp)
        (eval_reg hri (hinV.trans hn)) hidxw
      have hread := eval_read (a := inArr) heidx (by simpa only [hinput] using hidx)
        (by
          simp only [hinput, x.enc_subset hinV, gm02VertexBits, List.getElem_ofFn]
          split_ifs <;> omega)
      simpa only [gm02InputSubsetExpr, hinput, x.enc_subset hinV] using hread)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, (hk₂.1 _ (by decide)).trans hrn₁,
    (hk₂.1 _ (by decide)).trans hrm₁, hadj₁.of_arrs_eq (hk₂.2 _ (by decide))
      (hk₂.2 _ (by decide)) (hk₂.2 _ (by decide)), ?_, hq₂, (hk₂.2 _ (by decide)).trans hin₁'⟩
  · dsimp only at ht₁
    simp only [Expr.cost, gm02InputSubsetExpr, gm02VertexBits, List.length_ofFn] at ht₂
    omega
  · simpa only [hk₂.2 12 (by decide)] using hent₁

end GraphMinor.Compute
