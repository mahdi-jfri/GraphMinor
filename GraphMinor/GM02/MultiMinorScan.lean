module

public import GraphMinor.Compute.GM02CapEdgeList
public import GraphMinor.Compute.GM02MinorPatternScan
public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.Planar.Defs
import GraphMinor.Compute.GM02MinorPatternList
import GraphMinor.Compute.GM13ClassFolio
import GraphMinor.GM02.MinorWidth
import GraphMinor.GM05.FullPlanar

/-!
# The (4.9) program on the multigraph encoding

Graph Minors II proves (1.1), (1.2) and (5.3)–(5.5) by running the program of
(4.9) for finitely many fixed graphs. This file prepares that step.

- `theorem_4_10` is II (4.10), cited from V: excluding a planar graph bounds
  the tree-width. It is V (1.5).
- `exists_multiMinorScan` runs (4.9) for every graph of a finite set `B` on the
  multigraph encoding. It first caps the multiplicities at a bound `δ` larger
  than every member of `B`, writes out the edge list, and scans the patterns of
  (4.8) for all members of `B`. Capping keeps every minor with at most `δ`
  vertices and edges, and cannot raise the tree-width.
- `ComputesRelInTime.seq_isZero` turns the answer "zero" into one and every
  other answer into zero.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set GraphMinor.Compute

universe u v u' v'

/-- Graph Minors II, (4.10), page 320, cited from Graph Minors V:
"For every planar graph $H$ there is a number $w$ such that every graph with no
minor isomorphic to $H$ has tree-width $\le w$."
This is V (1.5) (`GM05.Full.theorem_1_5`). V's vertex bags satisfy II's
(W1)–(W3). -/
theorem theorem_4_10_proof {α' : Type u'} {β' : Type v'} (H : Graph α' β') (hH : IsPlanar H)
    {α : Type u} {β : Type v} :
    ∃ w : ℕ, ∀ G : Graph α β, V(G).Finite → E(G).Finite →
      ¬ IsIsoMinor H G → TreeWidthLE G w := by
  obtain ⟨w, hw⟩ := GM05.Full.theorem_1_5_proof (α := α) (β := β) H hH
  refine ⟨w, fun G hV hE hno => ?_⟩
  obtain ⟨ι, hι, T, χ, hD, hwidth⟩ := hw G hV hE hno
  exact ⟨ι, hι, T, χ, ⟨hD.isTree, hD.iUnion_eq, hD.edge_mem, hD.inter_subset⟩, hwidth⟩

/-- The (4.9) program for every member of a finite set `B` of graphs, on the
multigraph encoding. Output one means that some member of `B` is a minor, zero
that none is, and two that the tree-width is more than `w`. -/
theorem exists_multiMinorScan (B : Finset (Graph ℕ (ℕ × ℕ × ℕ)))
    (hB : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ), ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
      (fun x s =>
        (s.regs outReg = 1 ∧ ∃ H ∈ B, IsIsoMinor H x.G.toGMDigraph.toGraph) ∨
        (s.regs outReg = 0 ∧ ∀ H ∈ B, ¬ IsIsoMinor H x.G.toGMDigraph.toGraph) ∨
        (s.regs outReg = 2 ∧
          ∀ k : ℕ, (k : ℤ) ≤ w → ¬ TreeWidthLE x.G.toGMDigraph.toGraph k))
      P (fun n => (n + 1) ^ c) := by
  classical
  choose ps hps using fun H : B => exists_gm02MinorPatternList H.1 (hB H.1 H.2).1 (hB H.1 H.2).2
  let L := B.attach.toList.flatMap ps
  have hL : ∀ y : GM02EdgeListInput, (∃ H ∈ B, IsIsoMinor H y.graph) ↔
      ∃ J ∈ L, ∃ L' : Graph ℕ ℕ, TopologicallyContains y.graph L' ∧ Nonempty (Iso J.graph L') := by
    intro y
    constructor
    · rintro ⟨H, hH, hm⟩
      obtain ⟨J, hJ, hrest⟩ := (hps ⟨H, hH⟩ y).1 hm
      exact ⟨J, List.mem_flatMap.2 ⟨⟨H, hH⟩, by simp, hJ⟩, hrest⟩
    · rintro ⟨J, hJ, hrest⟩
      obtain ⟨H, -, hJ⟩ := List.mem_flatMap.1 hJ
      exact ⟨H.1, H.2, (hps H y).2 ⟨J, hJ, hrest⟩⟩
  let δ := B.sup fun H => V(H).ncard + E(H).ncard
  obtain ⟨C, cw, hC, hcw, run⟩ := (gm02MinorPatternScan_computes L w).capEdgeList δ
  refine ⟨.seq (capEdgeListProg δ) (gm02MinorPatternScanProg L w),
    gm02PatternListExponent L w + 1, C, cw, hC, hcw, fun x s hs => ?_⟩
  obtain ⟨s', t, he, ht, hout⟩ := run x s hs
  refine ⟨s', t, he, ht, ?_⟩
  obtain ⟨n, G⟩ := x
  let y := (G.cap δ).toEdgeListInput
  let φ := (G.cap δ).edgeListIso
  have hfolio : GM13.HasSameDeltaFolioRel G.toGMDigraph (G.cap δ).toGMDigraph δ ∅ := by
    simpa only [Finset.toNatSet, Finset.coe_empty, Set.image_empty] using
      hasSameDeltaFolioRel_cap δ G ∅
  have hminor : ∀ H ∈ B, IsIsoMinor H y.graph ↔ IsIsoMinor H G.toGMDigraph.toGraph := by
    intro H hH
    have hle : V(H).ncard + E(H).ncard ≤ δ :=
      Finset.le_sup (f := fun H => V(H).ncard + E(H).ncard) hH
    rw [GM13.isIsoMinor_iff_of_hasSameDeltaFolioRel_empty G.isFinite_toGMDigraph
      (G.cap δ).isFinite_toGMDigraph hfolio (hB H hH).1 (hB H hH).2 (by omega) (by omega)]
    exact ⟨fun h => Iso.isIsoMinor_right h φ, fun h => Iso.isIsoMinor_right h φ.symm⟩
  rcases hout with ⟨h1, hJ⟩ | ⟨h0, hJ⟩ | ⟨h2, hlt⟩
  · obtain ⟨H, hH, hm⟩ := (hL y).2 hJ
    exact Or.inl ⟨h1, H, hH, (hminor H hH).1 hm⟩
  · refine Or.inr (Or.inl ⟨h0, fun H hH hm => hJ ((hL y).1 ⟨H, hH, (hminor H hH).2 hm⟩)⟩)
  · refine Or.inr (Or.inr ⟨h2, fun k hk htw => ?_⟩)
    have hfin := G.isFinite_toGMDigraph
    have hfin' := (G.cap δ).isFinite_toGMDigraph
    have hcap : TreeWidthLE (G.cap δ).toGMDigraph.toGraph k :=
      htw.of_isIsoMinor hfin.finite_V hfin.finite_E (isIsoMinor_of_multi_le43 (G.cap_le δ))
    have hy : TreeWidthLE y.graph k :=
      hcap.of_isIsoMinor hfin'.finite_V hfin'.finite_E
        (Iso.isIsoMinor_right (IsIsoMinor.refl y.graph) φ)
    have hle := (treeWidth_le_iff y.graph y.finite_vertices y.finite_edges k).2 hy
    have : ((treeWidth y.graph y.finite_vertices y.finite_edges : ℕ) : ℤ) ≤ k := by exact_mod_cast hle
    change w < ((treeWidth y.graph y.finite_vertices y.finite_edges : ℕ) : ℤ) at hlt
    omega

/-- Replace the answer in the output register by one if it was zero, and by
zero otherwise. -/
def isZeroOutProg : Cmd :=
  .assign outReg (.op .eq (.reg outReg) (.const 0))

/-- Running `isZeroOutProg` after a program whose answer is at most two. -/
theorem ComputesRelInTime.seq_isZero {α : Type*} {size : α → ℕ}
    {In Out : α → State → Prop} {P : Cmd} {c : ℕ}
    (h : ComputesRelInTime size In Out P (fun n => (n + 1) ^ c))
    (hb : ∀ x s, Out x s → s.regs outReg ≤ 2) :
    ComputesRelInTime size In
      (fun x s => ∃ s₀, Out x s₀ ∧ s.regs outReg = if s₀.regs outReg = 0 then 1 else 0)
      (.seq P isZeroOutProg) (fun n => (n + 1) ^ c) := by
  obtain ⟨C, cw, hC, hcw, run⟩ := h
  refine ⟨C + 5, cw, by omega, hcw, fun x s hs => ?_⟩
  obtain ⟨s₀, t, he, ht, hout⟩ := run x s hs
  have hW : 2 ≤ wordSize cw (size x) := by
    unfold wordSize
    have : 1 ≤ Nat.log 2 (size x + 2) := Nat.le_log_of_pow_le (by norm_num) (by omega)
    nlinarith
  have hpow : 4 ≤ 2 ^ wordSize cw (size x) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hW)
  have hv := hb x s₀ hout
  let v := if s₀.regs outReg = 0 then 1 else 0
  have he₂ : Exec (wordSize cw (size x)) isZeroOutProg s₀ (s₀.setReg outReg v) 4 := by
    refine .assign ?_
    simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, v]
    split_ifs <;> simp_all <;> omega
  refine ⟨s₀.setReg outReg v, t + 4, .seq he he₂, ?_, s₀, hout, by simp [v]⟩
  have h1 : 1 ≤ (size x + 1) ^ c := Nat.one_le_pow _ _ (by omega)
  nlinarith

end GraphMinor.GM02
