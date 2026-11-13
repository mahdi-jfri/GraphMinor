module

public import GraphMinor.Compute.GM13SocietyPrograms
public import GraphMinor.Compute.GM13SocietyDivisionRestore
public import GraphMinor.Compute.GM13SocietyNaturalCross

/-!
# Graph Minors XIII (8.6) for every encoded society

The full cross algorithm first writes either an actual-edge cross or the
zero tag. Only in the zero-tag case do we compute the simple division and
its loop-owner table. The reader restores every parallel edge and loop.
Both outputs refer to the original multigraph society, with integer vertex
names as stored in the input, and both branches have the original O(vε)
time bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GM09 Transport

/-- The cross output of (8.6), with explicit actual edges on the stored
integer vertex names. The four endpoint arrays encode edge number zero in
each chosen ordered parallel class. -/
def GM13Actual86CrossOutput (x : GM13SocietyInput) (s : State) : Prop :=
  ∃ c : CrossWitness x.G.toSimpleGraph x.omega,
    c.IsValid ∧ s.arrs 65 = gm13CrossCode c ∧
    s.arrs 10 = gm13PathEdgeEnds x.G c.P.support false ∧
    s.arrs 11 = gm13PathEdgeEnds x.G c.P.support true ∧
    s.arrs 12 = gm13PathEdgeEnds x.G c.Q.support false ∧
    s.arrs 13 = gm13PathEdgeEnds x.G c.Q.support true ∧
    (case3MultigraphSociety x.G x.omega x.nodup_omega).IsCross
      (relabelGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _)
        (walkSubgraph (gm13LiftWalk x c.P)))
      (relabelGraph ⟨Fin.val, Fin.val_injective⟩ (Function.Embedding.refl _)
        (walkSubgraph (gm13LiftWalk x c.Q)))

/-- Either an actual-edge cross or a decoded rural division of the given
multigraph society, with all its original edges. -/
def GM13Actual86Output (x : GM13SocietyInput) (s : State) : Prop :=
  GM13Actual86CrossOutput x s ∨ GM13ActualRuralOutput x s

/-- Graph Minors XIII, Algorithm (8.6), page 96, for every encoded society:
"Either a cross in $(G, \Omega)$, or a rural division of $(G, \Omega)$."

The plain input is the multigraph and its cyclic order. The program
simplifies the graph and runs the proved simple programs. It writes actual
cross edges, or writes a loop-owner table and reads the division by restoring
all parallel copies and loops. The bound is O(vε) in the given graph.
`algorithm_8_6_proved` is the simple-input version.
XIII, page 68: "Thus each edge has a head and a tail (the same, for a loop)." -/
theorem algorithm_8_6_full :
    ∃ P : Cmd, ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      GM13Actual86Output P (fun s => s) := by
  obtain ⟨Pcross, Ccross, ccross, hCcross, hccross, hcross⟩ := algorithm_8_1_full
  obtain ⟨Prural, Crural, crural, hCrural, hcrural, hrural⟩ := gm13SocietyRuralProgram
  refine ⟨.seq Pcross (.ite (.read 65 (.const 0)) .skip Prural),
    Ccross + Crural + 10, ccross + crural + 4, by omega, by omega, ?_⟩
  intro x s hin
  dsimp only
  have hS : 1 ≤ x.size := Nat.mul_pos (by omega) (by omega)
  have hwc : wordSize ccross x.size ≤ wordSize (ccross + crural + 4) x.size :=
    wordSize_mono_left (by omega) _
  have hwr : wordSize crural x.size ≤ wordSize (ccross + crural + 4) x.size :=
    wordSize_mono_left (by omega) _
  have hw4 : wordSize 4 x.size ≤ wordSize (ccross + crural + 4) x.size :=
    wordSize_mono_left (by omega) _
  have hwords := (gm13_section8_word_bound x.size hS).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw4)
  have h0 : 0 < 2 ^ wordSize (ccross + crural + 4) x.size := by omega
  have h1 : 1 < 2 ^ wordSize (ccross + crural + 4) x.size := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hout₁, horig₁⟩ := hcross x s hin
  dsimp only at ht₁
  rcases hout₁ with ⟨hcode, hno⟩ | ⟨c, hc, hcode, hpt, hph, hqt, hqh, hcx⟩
  · have htag : (Expr.read 65 (.const 0)).eval
        (wordSize (ccross + crural + 4) x.size) s₁ = some 0 := by
      apply gm13_read_eval (Crossing.eval_const h0)
      · simp [hcode]
      · exact h0
    obtain ⟨s₂, t₂, he₂, ht₂, hout₂⟩ := hrural x s₁ ⟨horig₁, hno⟩
    dsimp only at ht₂
    refine ⟨s₂, t₁ + (2 + t₂), .seq (he₁.mono_wordSize hwc)
      (.ite_false htag (he₂.mono_wordSize hwr)), ?_, Or.inr hout₂⟩
    rw [Nat.add_mul, Nat.add_mul]
    omega
  · have htag : (Expr.read 65 (.const 0)).eval
        (wordSize (ccross + crural + 4) x.size) s₁ = some 1 := by
      apply gm13_read_eval (Crossing.eval_const h0)
      · simp [hcode, gm13CrossCode]
      · exact h1
    refine ⟨s₁, t₁ + 3, .seq (he₁.mono_wordSize hwc)
      (.ite_true htag (by decide) (.skip s₁)), ?_, Or.inl ?_⟩
    · rw [Nat.add_mul, Nat.add_mul]
      omega
    · exact ⟨c, hc, hcode, hpt, hph, hqt, hqh, gm13Cross_natural x hcx⟩

end GraphMinor.Compute
