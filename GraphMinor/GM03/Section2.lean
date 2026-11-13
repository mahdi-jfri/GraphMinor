module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2f
public import GraphMinor.GM03.Section2g
public import GraphMinor.GM03.Section2n
public import GraphMinor.GM03.Section3a

/-!
# Graph Minors III, Section 2: Radius ((2.1)–(2.8))

This file formalizes Section 2 ("Radius", pages 51–56) of N. Robertson and P. D. Seymour,
*Graph Minors. III. Planar Tree-Width*, J. Combin. Theory Ser. B **36** (1984), 49–64:
- `(2.1)` (`theorem_2_1`, page 52): any planar graph of radius $\le d$ is isomorphic to a minor of
  a simple planar graph with radius $\le d$.
- `(2.2)` (`theorem_2_2`, page 52): any simple planar graph of radius $\le d$ is isomorphic to a
  minor of a simple planar graph $G'$ with a drawing $M'$ of radius $\le d$ that has a $d$-shell.
- `(2.3)` (`theorem_2_3`, page 55): any simple planar graph with a drawing $M$ of radius $\le d$
  and a $d$-shell is isomorphic to a minor of $N(d, \lambda)$ for some $\lambda \ge 1$.
- `(2.4)` (`theorem_2_4`, page 55): any planar graph with radius $\le d$ is isomorphic to a minor
  of $N(d, \lambda)$ for some $\lambda \ge 1$.
- `(2.5)` (`theorem_2_5`, page 55): for all $d \ge 0$, $\lambda \ge 1$, the graph $N(d, \lambda)$
  has tree-width $\le 3d + 1$.
- `(2.6)` (`theorem_2_6`, page 56): if $G'$ is isomorphic to a minor of $G$ then the tree-width of
  $G'$ is not greater than the tree-width of $G$.
- `(2.7)` (`theorem_2_7`, page 56): if $G$ is planar and has radius $\le d$ then its tree-width is
  at most $3d + 1$.
- `(2.8)` (`theorem_2_8`, page 56): if $G$ is a planar graph with radius $\ge d$ and $M$ is a
  drawing of $G$, then there is a nested sequence $C_1, \dots, C_d$ of circuits of $M$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM11 GraphMinor.GM22

universe u v u₁ v₁ u₂ v₂

variable {α : Type u} {β : Type v}

/-! ## (2.1) Subdivision to a Simple Planar Graph of the Same Radius (page 52) -/

/-- Every drawing `D : Drawing S` in a nonempty T2 space `S` admits a single edge-subdivision
`SplitData D D₂ A B m x y`. -/
theorem exists_splitData_of_drawing {S : Type} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (D : Drawing S) :
    ∃ (D₂ : Drawing S) (A B : Set S → Set S) (m x y : Set S → S),
      SplitData D D₂ A B m x y := by
  obtain ⟨D₂, A, B, m, x, y, hU, hV, hE, hall⟩ := GM11.exists_split D
  exact ⟨D₂, A, B, m, x, y, splitData_of_exists_split_spec hU hV hE hall⟩

/-- **Graph Minors III, (2.1)** (page 52):
"(2.1) *Any planar graph of radius $\le d$ is isomorphic to a minor of a simple planar graph with
radius $\le d$.*"

*Proof.* Replace each edge of $G$ by three edges in series (obtained by splitting all edges of a
radius-$\le d$ drawing $M$ of $G$ twice via `GM11.exists_split`). The resulting graph $G'$ is
planar, has the same regions and hence drawing radius $\le d$, is simple
(`simple_of_double_splitData`), and has $G$ as a minor (`isIsoMinor_of_splitData`). -/
theorem theorem_2_1_proof {G : Graph α β} {d : ℕ}
    (_hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ (α' : Type) (β' : Type) (G' : Graph α' β'),
      G'.Simple ∧ IsPlanar G' ∧ HasRadiusLE G' d ∧ IsIsoMinor G G' := by
  obtain ⟨M, hMrad⟩ := hrad
  have : T2Space M.S := M.isClosedSurface.2.1
  have : Nonempty M.S := by
    obtain ⟨p, _⟩ := region_nonempty M.infRegion_mem
    exact ⟨p⟩
  obtain ⟨D₂, A₁, B₁, m₁, x₁, y₁, hd₁⟩ := exists_splitData_of_drawing M.drawing
  obtain ⟨D₃, A₂, B₂, m₂, x₂, y₂, hd₂⟩ := exists_splitData_of_drawing D₂
  have hU₃ : D₃.U = M.drawing.U := hd₂.U_eq.trans hd₁.U_eq
  have hV₃ : M.drawing.V ⊆ D₃.V := fun z hz => hd₂.V_sub (hd₁.V_sub hz)
  let M' : PlanarDrawing D₃.toGraph := planarDrawingOfUEq M D₃ hU₃
  have hM'rad : HasDrawingRadiusLE M' d :=
    hasDrawingRadiusLE_of_UEq_VSub M D₃ hU₃ hV₃ hMrad
  have hSimple : D₃.toGraph.Simple := simple_of_double_splitData hd₁ hd₂
  have hMinor₁ : IsIsoMinor M.drawing.toGraph D₂.toGraph := isIsoMinor_of_splitData hd₁
  have hMinor₂ : IsIsoMinor D₂.toGraph D₃.toGraph := isIsoMinor_of_splitData hd₂
  have hMinor : IsIsoMinor G D₃.toGraph :=
    M.graphDrawing.iso.isIsoMinor_left (hMinor₁.trans hMinor₂)
  exact ⟨M.S, Set M.S, D₃.toGraph, hSimple, M'.isPlanar, ⟨M', hM'rad⟩, hMinor⟩

/-! ## (2.2) Existence of a $d$-Shell Extension (pages 52–54) -/

/-- Base case $d' = 0$ of the induction in the proof of (2.2) (page 52):
every drawing $M$ of $G$ has a $0$-shell. -/
theorem isDShell_zero {G : Graph α β} (M : PlanarDrawing G) :
    IsDShell M 0 Fin.elim0 where
  isNested := ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  vertex_in_or_inside hd := (Nat.lt_irrefl 0 hd).elim
  edge_induced j := Fin.elim0 j

/-- **Graph Minors III, (2.2)** (page 52):
"(2.2) *Let $G$ be a simple planar graph of radius $\le d$, where $d \ge 0$ is an integer. Then
there exist a simple planar graph $G'$ with a minor isomorphic to $G$ and a drawing $M'$ of $G'$
such that $\rho(M') \le d$ and $M'$ has a $d$-shell.*" -/
theorem theorem_2_2_proof {G : Graph α β} {d : ℕ}
    (hSimple : G.Simple) (_hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ (α' : Type) (β' : Type) (G' : Graph α' β') (M' : PlanarDrawing G')
      (C : Fin d → Graph α' β'),
      G'.Simple ∧ IsPlanar G' ∧ IsIsoMinor G G' ∧ HasDrawingRadiusLE M' d ∧
      IsDShell M' d C := by
  obtain ⟨α', β', G', M', C, hS', hMin', hRad', hShell'⟩ :=
    exists_dShell_le hSimple hrad d le_rfl
  exact ⟨α', β', G', M', C, hS', M'.isPlanar, hMin', hRad', hShell'⟩

/-! ## (2.3) Minor Embedding of a $d$-Shell Drawing into $N(d, \lambda)$ (page 55) -/

/-- Step 1 of `(2.3)` (page 55):
"We observe that the graph obtained from $G$ by deleting $V(C_1), \dots, V(C_d)$ is a forest,
since if the corresponding drawing had a finite region $R$, we would have $d(R) > d$ in $M$
which is impossible." -/
theorem lemma_2_3_delete_shell_no_circuit {G : Graph α β} {M : PlanarDrawing G} {d : ℕ}
    {C : Fin d → Graph α β}
    (hrad : HasDrawingRadiusLE M d) (hShell : IsDShell M d C) :
    GM09.deleteVertices G (⋃ i : Fin d, V(C i)) ≤ G ∧
      (∀ i : Fin d, Disjoint V(GM09.deleteVertices G (⋃ i : Fin d, V(C i))) V(C i)) ∧
      ∀ C' ≤ GM09.deleteVertices G (⋃ i : Fin d, V(C i)), ¬ GM09.IsGraphCircuit G C' := by
  refine ⟨GM09.deleteVertices_le G (⋃ i : Fin d, V(C i)), fun i => ?_, fun C' hC' hCirc => ?_⟩
  · rw [Set.disjoint_left]
    intro v hvF hvCi
    exact hvF.2 (Set.mem_iUnion.mpr ⟨i, hvCi⟩)
  · obtain ⟨R, hR, hno_chain⟩ :=
      exists_region_no_chain_of_circuit_delete_shell hShell C' hC' hCirc
    obtain ⟨k, hkd, hchain⟩ := hrad R hR
    exact hno_chain k hkd hchain

/-- **Graph Minors III, (2.3)** (page 55):
"(2.3) *Let $G$ be a simple planar graph, with a drawing $M$ such that $\rho(M) \le d$ and $M$ has
a $d$-shell $C_1, \dots, C_d$. Then $G$ is isomorphic to a minor of $N(d, \lambda)$ for some
sufficiently large $\lambda$.*" -/
theorem theorem_2_3_proof {G : Graph α β} {M : PlanarDrawing G} {d : ℕ} {C : Fin d → Graph α β}
    (hSimple : G.Simple) (hrad : HasDrawingRadiusLE M d) (hShell : IsDShell M d C) :
    ∃ lam : ℕ, 1 ≤ lam ∧ IsIsoMinor G (graphN d lam) := by
  obtain ⟨hF_le, _hF_disj, hF_no_circ⟩ :=
    lemma_2_3_delete_shell_no_circuit hrad hShell
  have hF_simple : (GM09.deleteVertices G (⋃ i : Fin d, V(C i))).Simple :=
    Simple.mono hSimple hF_le
  have hF_finV : V(GM09.deleteVertices G (⋃ i : Fin d, V(C i))).Finite :=
    M.graphDrawing.finite_V.subset hF_le.vertexSet_mono
  have hF_finE : E(GM09.deleteVertices G (⋃ i : Fin d, V(C i))).Finite :=
    M.graphDrawing.finite_E.subset hF_le.edgeSet_mono
  obtain ⟨lam₀, hlam₀, hMinY⟩ :=
    exists_treeY_minor_of_forest _ hF_simple hF_finV hF_finE
      (fun C' hC' => by rw [isGraphCircuit_iff_of_le hF_le hC']; exact hF_no_circ C' hC')
  obtain ⟨lam, hlam_ge, hMinN⟩ := glue_shell_and_tree hSimple hrad hShell lam₀ hlam₀ hMinY
  exact ⟨lam, le_trans hlam₀ hlam_ge, hMinN⟩

/-! ## (2.4) Planar Graphs of Radius $\le d$ Are Minors of $N(d, \lambda)$ (page 55) -/

/-- **Graph Minors III, (2.4)** (page 55):
"(2.4) *If $G$ is a planar graph with radius $\le d$ then $G$ is isomorphic to a minor of
$N(d, \lambda)$ for some sufficiently large $\lambda$.*
This follows from (2.1), (2.2), and (2.3)." -/
theorem theorem_2_4_proof {G : Graph α β} {d : ℕ}
    (hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    ∃ lam : ℕ, 1 ≤ lam ∧ IsIsoMinor G (graphN d lam) := by
  obtain ⟨α₁, β₁, G₁, hS₁, hP₁, hRad₁, hMin₁⟩ := theorem_2_1_proof hPlanar hrad
  obtain ⟨α₂, β₂, G₂, M₂, C₂, hS₂, _, hMin₂, hRad₂, hShell₂⟩ :=
    theorem_2_2_proof hS₁ hP₁ hRad₁
  obtain ⟨lam, hlam, hMin₃⟩ := theorem_2_3_proof hS₂ hRad₂ hShell₂
  exact ⟨lam, hlam, (hMin₁.trans hMin₂).trans hMin₃⟩

/-! ## (2.5) Tree-Width of $N(d, \lambda)$ Is at Most $3d + 1$ (page 55) -/

/-- **Graph Minors III, (2.5)** (page 55):
"(2.5) *For all $d \ge 0$, $\lambda \ge 1$, the graph $N(d, \lambda)$ has tree-width
$\le 3d + 1$.*" -/
theorem theorem_2_5_proof (d lam : ℕ) (_hlam : 1 ≤ lam) :
    TreeWidthLE (graphN d lam) (3 * d + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact treeWidthLE_graphN_zero rfl lam
  · exact treeWidthLE_graphN_pos hd lam

/-! ## (2.6) Monotonicity of Tree-Width Under Minors (page 56) -/

/-- **Graph Minors III, (2.6)** (page 56):
"(2.6) *If $G'$ is isomorphic to a minor of $G$ then the tree-width of $G'$ is not greater than
the tree-width of $G$.*" -/
theorem theorem_2_6_proof {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {G' : Graph α₁ β₁} {G : Graph α₂ β₂} {w : ℕ}
    (hVG : V(G).Finite) (hMinor : IsIsoMinor G' G) (hw : TreeWidthLE G w) :
    TreeWidthLE G' w := by
  have hVG' : V(G).Finite := hVG
  have hMin' : IsIsoMinor G' G := hMinor
  exact treeWidthLE_of_isIsoMinor hVG' hMin' hw

/-! ## (2.7) Tree-Width of Planar Graphs of Radius $\le d$ (page 56) -/

/-- **Graph Minors III, (2.7)** (page 56), proved without extra hypotheses:
"(2.7) *If $G$ is planar and has radius $\le d$ then its tree-width is at most $3d + 1$.*
From (2.4), (2.5), and (2.6) we deduce (2.7)." -/
theorem theorem_2_7_proved {G : Graph α β} {d : ℕ}
    (hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    TreeWidthLE G (3 * d + 1) := by
  obtain ⟨lam, hlam, hMinor⟩ := theorem_2_4_proof hPlanar hrad
  have hTW_N : TreeWidthLE (graphN d lam) (3 * d + 1) := theorem_2_5_proof d lam hlam
  exact theorem_2_6_proof (Set.toFinite _) hMinor hTW_N

/-- **Graph Minors III, (2.7)** (page 56):
"(2.7) *If $G$ is planar and has radius $\le d$ then its tree-width is at most $3d + 1$.*
From (2.4), (2.5), and (2.6) we deduce (2.7)." -/
theorem theorem_2_7_proof {G : Graph α β} {d : ℕ}
    (hPlanar : IsPlanar G) (hrad : HasRadiusLE G d) :
    TreeWidthLE G (3 * d + 1) :=
  theorem_2_7_proved hPlanar hrad

/-! ## (2.8) Existence of a Nested Sequence of $d$ Circuits (page 56) -/

/-- **Graph Minors III, (2.8)** (page 56):
"(2.8) *Let $G$ be a planar graph with radius $\ge d$, and let $M$ be a drawing of $G$. Then there
is a nested sequence $C_1, C_2, \dots, C_d$ of circuits of $M$.*" -/
theorem theorem_2_8_proof {G : Graph α β} (M : PlanarDrawing G) (d : ℕ)
    (hrad : ∀ _ : 0 < d, ¬ HasRadiusLE G (d - 1)) :
    ∃ C : Fin d → Graph α β, IsNestedCircuitSeq M d C := by
  have hnot_draw : ∀ _ : 0 < d, ¬ HasDrawingRadiusLE M (d - 1) := by
    intro hd hdraw
    exact hrad hd ⟨M, hdraw⟩
  exact exists_nestedCircuitSeq_of_not_hasDrawingRadiusLE M d hnot_draw

end GraphMinor.GM03
