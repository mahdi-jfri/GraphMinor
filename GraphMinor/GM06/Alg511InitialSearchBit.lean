module

public import GraphMinor.Compute.GM06Alg511SearchInput
public import GraphMinor.GM06.Alg511FlowLinkage
public import GraphMinor.GM06.Alg511FlowOfLinkage
import GraphMinor.Compute.GM06Alg511FlowBit
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# A linkage-existence bit for the initial phase of VI (5.11)

Load the supplied graph layout and run the verified maximum-flow
program. Its raw output head is a Boolean, and one means that a
full path family exists. The two geometric path transfers identify
this with a cylinder linkage. Copy the head to output register zero.
The full drawing remains available for the winding computation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem menger_preserves_saved_input :
    (1000 : ℕ) ∉ disjointPathsEndToEndProg.writtenArrs := by decide

/-- The first linkage search of VI (5.11), page 134, produces an
actual Boolean in register zero that decides (5.10)(ii). Its input
contains only the supplied finite drawing and ordinary graph data. -/
theorem alg511_initialSearchBit_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511WindingInput)
      (G : Drawing ClosedCylinder)
      (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G.toGraph)
      (source : Fin x.drawing.pathCount → Fin x.drawing.vertexCount),
      (∀ a ∈ x.drawing.flowInput.A, ∃ i, source i = a) →
      (∀ i, (rep.vertex (source i)).val = cylinderM1Point x.drawing.pathCount i) →
      (∀ a : Fin x.drawing.vertexCount,
        a.val ∈ x.drawing.innerCuff ↔ (rep.vertex a).val ∈ cylinderM1 x.drawing.pathCount) →
      (∀ b : Fin x.drawing.vertexCount,
        b.val ∈ x.drawing.outerCuff ↔ (rep.vertex b).val ∈ cylinderM2 x.drawing.pathCount) →
      ∀ (s : State) (w : ℕ), 1 < 2 ^ w →
      wordSize c (disjointPathsSize x.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511SearchWords x →
      (gm06Alg511SearchWords x).length < 2 ^ w →
      (∀ v ∈ gm06Alg511SearchWords x, v < 2 ^ w) →
      ∃ s' t, Exec w gm06Alg511InitialSearchBitProg s s' t ∧
        t ≤ 16 + 44 * (gm06Alg511SearchWords x).length +
          C * (x.drawing.pathCount + x.drawing.vertexCount + 1) ^ 3 ∧
        s'.arrs 1000 = gm06Alg511WindingWords x ∧
        (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
        (s'.regs 0 = 1 ↔ Nonempty (CylinderLinkage x.drawing.pathCount G)) ∧
        IsValidDisjointPathsOutput x.drawing.flowInput
          (decDisjointPathsOut x.drawing.flowInput (s'.arrs outArr)) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := gm06Alg511FlowBit_computesInTime
  refine ⟨C, c, hC, hc, ?_⟩
  intro x G rep source hsource hpoints hinner houter s w hw hwflow ha hn hwords
  obtain ⟨s₁, t₁, he₁, ht₁, hinput, hsaved⟩ :=
    gm06Alg511LoadSearchProg_exec x s hw ha hn hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hvalid, _, hbool, hflag⟩ := hflow x.drawing.flowInput s₁ hinput
  have hgeom :
      (∃ P : Fin x.drawing.pathCount →
        ABWalk x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B,
        PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ↔
      Nonempty (CylinderLinkage x.drawing.pathCount G) := by
    constructor
    · rintro ⟨P, hPdisj, hPsimple⟩
      exact alg511_exists_linkage_of_flowPaths x.drawing rep source hsource hpoints
        (fun b hb => (houter b).mp (Finset.mem_filter.mp hb).2) P hPdisj hPsimple
    · rintro ⟨L⟩
      exact alg511_exists_flowPaths_of_linkage x.drawing rep hinner houter L
  obtain ⟨bit, hbit, hhead⟩ : ∃ bit : ℕ, (bit = 0 ∨ bit = 1) ∧
      (s₂.arrs outArr).head? = some bit := by
    rcases hbool with h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr rfl, h⟩
  have hbitfit : bit < 2 ^ w := by rcases hbit with h | h <;> rw [h] <;> omega
  have hget : (s₂.arrs outArr)[0]? = some bit := by
    simpa only [List.head?_eq_getElem?] using hhead
  obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hget
  have hread : (Expr.read outArr (.const 0)).eval w s₂ = some bit := by
    have hh := GraphMinor.Compute.Crossing.eval_read
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hbound
      (show (s₂.arrs outArr)[0]'hbound < 2 ^ w by rw [hvalue]; exact hbitfit)
    simpa only [hvalue] using hh
  let s₃ := s₂.setReg 0 bit
  have ht₂' := ht₂.trans (Nat.mul_le_mul_left C (gm06Alg511FlowSize_le x.drawing))
  refine ⟨s₃, (t₁ + t₂) + 3,
    .seq (.seq he₁ (he₂.mono_wordSize hwflow)) (.assign hread), by omega, ?_, ?_, ?_, ?_⟩
  · rw [show s₃.arrs = s₂.arrs from rfl,
      Exec.arrs_eq_of_not_mem_writtenArrs he₂ menger_preserves_saved_input]
    exact hsaved
  · simpa only [s₃, State.setReg_regs_self] using hbit
  · have hh : bit = 1 ↔ (s₂.arrs outArr).head? = some 1 := by
      simp only [hhead, Option.some.injEq]
    exact hh.trans (hflag.trans hgeom)
  · exact hvalid

end GraphMinor.GM06
