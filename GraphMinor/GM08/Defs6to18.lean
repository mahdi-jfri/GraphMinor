module

public import GraphMinor.GM08.Defs
public import GraphMinor.Surface.DiscArcs
public import GraphMinor.Surface.SphereDisc
public import GraphMinor.Surface.DiscGrow
public import GraphMinor.GM11.SphereRegion

@[expose] public section

/-!
# Definitions for Graph Minors VIII, Sections 6–18

Definitions from Robertson and Seymour, *Graph Minors. VIII. A Kuratowski theorem for general
surfaces*, J. Combin. Theory Ser. B **48** (1990), 255–288, Sections 6–18.
-/

namespace GraphMinor
namespace GM08

open Set Topology Surface

universe u v

variable {S : Type u} [TopologicalSpace S]

/-!
## Section 6: Foundations on a Disc (pages 263–267)
-/

/-- In a closed disc `Δ ⊆ S`, a point `x` is *inside* an O-arc `F ⊆ Δ` (GM VIII Section 6,
page 263) if `x` lies in the interior `discInt D = D \ F` of the closed disc `D ⊆ Δ` bounded by `F`. -/
def InsideOArc (Δ F : Set S) (x : S) : Prop :=
  ∃ D : Set S, Surface.IsInsideDisc Δ F D ∧ x ∈ Surface.discInt D

/-- In a closed disc `Δ ⊆ S`, a set `X ⊆ Δ` is *inside* an O-arc `F ⊆ Δ` (GM VIII Section 6,
page 263) if `x` is inside `F` for all `x ∈ X`. -/
def SetInsideOArc (Δ F X : Set S) : Prop :=
  ∀ x ∈ X, InsideOArc Δ F x

/-- In a closed disc `Δ ⊆ S`, an O-arc `F ⊆ Δ` *encloses* a set `X ⊆ Δ` (GM VIII Section 6,
page 263) if `X \ F` is inside `F`. -/
def OArcEncloses (Δ F X : Set S) : Prop :=
  SetInsideOArc Δ F (X \ F)

/-- Two O-arcs `F₁, F₂` in a closed disc `Δ ⊆ S` *bound disjoint open discs* (GM VIII Section 6,
(6.5), page 265) if the open discs of points inside `F₁` and inside `F₂` are disjoint. -/
def BoundDisjointOpenDiscs (Δ F₁ F₂ : Set S) : Prop :=
  Disjoint {x : S | InsideOArc Δ F₁ x} {x : S | InsideOArc Δ F₂ x}

/-- A circuit `C` of a surface drawing `D` in a closed disc `Δ ⊆ S` (GM VIII Section 6, page 263),
represented by its O-arc `U ⊆ U(D) ∩ Δ` together with its inside closed disc `ins ⊆ Δ`. -/
structure DiscCircuit (D : Surface.Drawing S) (Δ : Set S) where
  /-- The point set (O-arc) of the circuit `C`. -/
  U : Set S
  /-- The inside closed disc of `C` in `Δ`. -/
  ins : Set S
  /-- `U` is a subset of `U(D)`. -/
  U_sub_drawing : U ⊆ D.U
  /-- `U` is contained in `Δ`. -/
  U_sub_disc : U ⊆ Δ
  /-- `U` is an O-arc. -/
  isOArc_U : Surface.IsOArc U
  /-- `ins` is the closed disc inside `Δ` bounded by `U`. -/
  isInside : Surface.IsInsideDisc Δ U ins

/-- For a circuit `C` of a drawing `D` in a closed disc `Δ`, `ρ(C)` (GM VIII Section 6, page 263)
is the minimum of `|V(D) ∩ F|` taken over all `D`-normal O-arcs `F ⊆ Δ` enclosing `C`. -/
noncomputable def circuitRho {D : Surface.Drawing S} {Δ : Set S} (C : DiscCircuit D Δ) : ℕ :=
  sInf {k : ℕ | ∃ F : Set S, F ⊆ Δ ∧ Surface.IsOArc F ∧ D.IsNormal F ∧
    OArcEncloses Δ F C.U ∧ (D.V ∩ F).ncard = k}

/-- A `C`-ring for a circuit `C` of a drawing `D` in a closed disc `Δ` (GM VIII Section 6,
page 263): a `D`-normal O-arc `F ⊆ Δ` enclosing `C` which attains the minimum
`|V(D) ∩ F| = ρ(C)`. -/
def IsCRing {D : Surface.Drawing S} {Δ : Set S} (C : DiscCircuit D Δ) (F : Set S) : Prop :=
  F ⊆ Δ ∧ Surface.IsOArc F ∧ D.IsNormal F ∧ OArcEncloses Δ F C.U ∧
    (D.V ∩ F).ncard = circuitRho C

/-- For a drawing `D` in a closed disc `Δ` and a `D`-normal O-arc `F ⊆ Δ`, `Γ(F)`
(`edgesInsideOArc D Δ F`, GM VIII Section 6, page 265) is the set of all edges of `D` inside `F`. -/
def edgesInsideOArc (D : Surface.Drawing S) (Δ F : Set S) : Set (Set S) :=
  {e ∈ D.E | SetInsideOArc Δ F e}

/-- A `C`-ring `F` is a *minimal `C`-ring* (GM VIII Section 6, page 265) if there is no `C`-ring
`F'` with `Γ(F') ⊂ Γ(F)`. -/
def IsMinimalCRing {D : Surface.Drawing S} {Δ : Set S}
    (C : DiscCircuit D Δ) (F : Set S) : Prop :=
  IsCRing C F ∧
  ∀ F' : Set S, IsCRing C F' → ¬ (edgesInsideOArc D Δ F' ⊂ edgesInsideOArc D Δ F)

/-- For a circuit `C` of a drawing `D` in a closed disc `Δ`, `Δ(C)` (`bossDelta D Δ C`,
GM VIII Section 6, page 266) is the common value of `Γ(F)` taken over all minimal `C`-rings `F`. -/
def bossDelta (D : Surface.Drawing S) (Δ : Set S) (C : DiscCircuit D Δ) : Set (Set S) :=
  ⋃ (F : Set S) (_ : IsMinimalCRing C F), edgesInsideOArc D Δ F

/-- An `(r, s)`-nest in a drawing `D` in a closed disc `Δ` (GM VIII Section 6, page 266):
a sequence `(C₁, ..., C_s)` of circuits of `D` in `Δ` such that
(i) for `1 ≤ i < i' ≤ s`, `C_i` is inside `C_{i'}`, and
(ii) there are `r` mutually vertex-disjoint paths of `D` between `C₁` and `C_s`. -/
structure DrawingNest (D : Surface.Drawing S) (Δ : Set S) (r s : ℕ) where
  /-- The sequence of circuits `C₁, ..., C_s`. -/
  circuit : Fin s → DiscCircuit D Δ
  /-- For `i < j`, `C_i` is inside `C_j`. -/
  inside_of_lt : ∀ {i j : Fin s}, i < j → SetInsideOArc Δ (circuit j).U (circuit i).U
  /-- Point sets of `r` mutually vertex-disjoint paths of `D` between `C₁` and `C_s`. -/
  radialPath : Fin r → Set S
  /-- Each radial path is preconnected. -/
  isPreconnected_radialPath : ∀ p : Fin r, IsPreconnected (radialPath p)
  /-- Each radial path is contained in `U(D)`. -/
  radialPath_sub_U : ∀ p : Fin r, radialPath p ⊆ D.U
  /-- Each radial path is contained in `Δ`. -/
  radialPath_sub_disc : ∀ p : Fin r, radialPath p ⊆ Δ
  /-- The radial paths are mutually vertex-disjoint. -/
  pairwise_disjoint_paths :
    Pairwise (fun p q => Disjoint (radialPath p ∩ D.V) (radialPath q ∩ D.V))
  /-- Each radial path meets the innermost circuit `C₁`. -/
  meets_inner : ∀ (p : Fin r) (h : 0 < s), (radialPath p ∩ (circuit ⟨0, h⟩).U).Nonempty
  /-- Each radial path meets the outermost circuit `C_s`. -/
  meets_outer : ∀ (p : Fin r) (h : 0 < s),
    (radialPath p ∩ (circuit ⟨s - 1, Nat.sub_lt h Nat.one_pos⟩).U).Nonempty

/-- A circuit `C` of a drawing `D` in a closed disc `Δ` is a *boss* (GM VIII Section 6, page 266)
if `ρ(C) < k` (where `k = |V(D) ∩ bd Δ|`) and there is a `((1 + ρ(C)), k)`-nest `(C₁, ..., C_k)`
with `C₁ = C`. -/
structure IsBoss (D : Surface.Drawing S) (Δ : Set S) (C : DiscCircuit D Δ) : Prop where
  /-- `ρ(C) < |V(D) ∩ bd Δ|`. -/
  rho_lt : circuitRho C < (D.V ∩ Surface.discBd Δ).ncard
  /-- Existence of a `((1 + ρ(C)), k)`-nest starting at `C`. -/
  exists_nest : ∃ N : DrawingNest D Δ (1 + circuitRho C) (D.V ∩ Surface.discBd Δ).ncard,
    ∀ h : 0 < (D.V ∩ Surface.discBd Δ).ncard, N.circuit ⟨0, h⟩ = C

universe u' v' w

/-- A *foundation* `{F₁, ..., F_t}` for a drawing `D` in a closed disc `Δ ⊆ S`
(GM VIII Section 6, page 267: "We call the set $\{F_1, \dots, F_t\}$ a *foundation* for
$\Gamma$."). -/
def IsFoundation (D : Surface.Drawing S) (Δ : Set S) {t : ℕ} (F : Fin t → Set S) : Prop :=
  ∃ C : Fin t → DiscCircuit D Δ,
    (∀ i, IsBoss D Δ (C i)) ∧
    Pairwise (fun i j => Disjoint (bossDelta D Δ (C i)) (bossDelta D Δ (C j))) ∧
    (∀ B : DiscCircuit D Δ, IsBoss D Δ B → ∃ i : Fin t, bossDelta D Δ B ⊆ bossDelta D Δ (C i)) ∧
    (∀ i, IsMinimalCRing (C i) (F i)) ∧
    Pairwise (fun i j => BoundDisjointOpenDiscs Δ (F i) (F j)) ∧
    Pairwise (fun i j => F i ∩ F j ⊆ D.V) ∧
    (∀ i, F i ∩ Surface.discBd Δ ⊆ D.V)

/-!
## Section 7: Tree-Width (page 267)
-/

/-- A hypertree `(V, T, ℱ)` (GM VIII Section 7, page 267):
"A hypertree is a triple $(V, T, \mathcal{F})$ where $V$ is a finite set, $T$ is a tree, and
$\mathcal{F} = (X_t ; t \in V(T))$ is a family of subsets of $V$, such that
(i) $\bigcup (X_t ; t \in V(T)) = V$
(ii) for $t, t', t'' \in V(T)$, if $t'$ lies on the path of $T$ between $t$ and $t''$ then
$X_t \cap X_{t''} \subseteq X_{t'}$." -/
structure IsHypertree {α : Type u} {ι : Type w} [Fintype ι]
    (V₀ : Set α) (T : SimpleGraph ι) (X : ι → Set α) : Prop where
  /-- `V` is a finite set. -/
  finite_V : V₀.Finite
  /-- `T` is a tree. -/
  isTree : T.IsTree
  /-- `(i) ⋃ (X_t ; t ∈ V(T)) = V`. -/
  iUnion_eq : (⋃ t : ι, X t) = V₀
  /-- `(ii)` For `t, t', t'' ∈ V(T)`, if `t'` lies on the path of `T` between `t` and `t''` then
  `X_t ∩ X_{t''} ⊆ X_{t'}`. -/
  inter_subset : ∀ ⦃t t' t'' : ι⦄, GM05.OnTreePath T t t'' t' → X t ∩ X t'' ⊆ X t'

/-- Condition `(i)` in the definition of tree-width (GM VIII Section 7, page 267):
"$|X_t| \le w + 1$ for each $t \in V(T)$". -/
def HypertreeWidthLE {α : Type u} {ι : Type w} (X : ι → Set α) (w : ℕ) : Prop :=
  ∀ t : ι, (X t).ncard ≤ w + 1

/-- A graph `G` has tree-width `≤ w` (GM VIII Section 7, page 267):
"there is a hypertree $(V, T, \mathcal{F})$ with $V = V(G)$, and with
(i) $|X_t| \le w + 1$ for each $t \in V(T)$, and
(ii) for each edge $e$ of $G$ some $X_t$ contains both ends of $e$." -/
def GraphTreeWidthLE {α : Type u} {β : Type v} (G : Graph α β) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set α),
    IsHypertree (Graph.vertexSet G) T X ∧ HypertreeWidthLE X w ∧
      ∀ ⦃e : β⦄ ⦃u v : α⦄, G.IsLink e u v → ∃ t : ι, u ∈ X t ∧ v ∈ X t

/-- The tree-width of a graph `G` (GM VIII Section 7, page 267):
"A graph $G$ is said to have *tree-width* $w$ if $w \ge 0$ is minimum such that there is a hypertree
$(V, T, \mathcal{F})$ with $V = V(G)$". -/
noncomputable def graphTreeWidth {α : Type u} {β : Type v} (G : Graph α β) : ℕ :=
  sInf {w : ℕ | GraphTreeWidthLE G w}

/-- A surface drawing `D` has tree-width `≤ w` if its underlying graph `D.toGraph` has tree-width
`≤ w` (GM VIII Section 7, page 267: "We define the *tree-width* of a drawing of a graft $(G, S)$
to be the tree-width of $G$."). -/
def DrawingTreeWidthLE (D : Surface.Drawing S) (w : ℕ) : Prop :=
  GraphTreeWidthLE D.toGraph w

/-- The tree-width of a surface drawing `D` (GM VIII Section 7, page 267). -/
noncomputable def drawingTreeWidth (D : Surface.Drawing S) : ℕ :=
  graphTreeWidth D.toGraph

/-!
## Section 8: Centred O-Arcs (pages 267–269)
-/

/-- A `D`-normal O-arc `F ⊆ Δ` is *centred* in a drawing `D` in a disc `Δ`
(GM VIII Section 8, pages 267–268: "We say that $F$ is *centred* if $\Gamma$ has a $(r, s)$-nest
$(C_1, \dots, C_s)$ where $s = \lceil \frac{1}{2}r \rceil$ such that each $C_i$ is inside $F$ and
such that there are $r$ mutually disjoint paths of $\Gamma$ between $C_1$ and $F$."). -/
def IsCentredOArc (D : Surface.Drawing S) (Δ F : Set S) : Prop :=
  F ⊆ Δ ∧ Surface.IsOArc F ∧ D.IsNormal F ∧
    ∃ N : DrawingNest D Δ (D.V ∩ F).ncard (((D.V ∩ F).ncard + 1) / 2),
      (∀ j, SetInsideOArc Δ F (N.circuit j).U) ∧
      ∃ P : Fin (D.V ∩ F).ncard → Surface.Drawing S,
        (∀ i, ∃ (hs : 0 < ((D.V ∩ F).ncard + 1) / 2) (u v : S),
          (P i).IsSubdrawing D ∧ u ∈ (N.circuit ⟨0, hs⟩).U ∧ v ∈ F ∧
          (P i).IsPathBetween u v) ∧
        Pairwise (fun i i' => Disjoint (P i).V (P i').V)

/-- Witness data `(C₁, ..., C_s)` and `(P₁, ..., P_r)` for **(8.1)** and a *sleeve* of `F`
(GM VIII Section 8, page 268). -/
structure SleeveData (D : Surface.Drawing S) (Δ F : Set S) where
  /-- The `(r, s)`-nest `(C₁, ..., C_s)` with `r = |V(D) ∩ F|` and `s = ⌈r / 2⌉`. -/
  nest : DrawingNest D Δ (D.V ∩ F).ncard (((D.V ∩ F).ncard + 1) / 2)
  /-- Circuit subdrawings `C₁, ..., C_s` realizing the nest circuits. -/
  circuitDraw : Fin (((D.V ∩ F).ncard + 1) / 2) → Surface.Drawing S
  /-- Each `circuitDraw j` is a circuit subdrawing of `D` with point set `(nest.circuit j).U`. -/
  isCircuit_draw : ∀ j, (circuitDraw j).IsSubdrawing D ∧ (circuitDraw j).IsCircuit ∧
    (circuitDraw j).U = (nest.circuit j).U
  /-- Each `C_j` is inside `F`. -/
  circuit_inside : ∀ j, SetInsideOArc Δ F (nest.circuit j).U
  /-- The `r` mutually disjoint paths `P₁, ..., P_r` of `D` between `C₁` and `F`. -/
  spoke : Fin (D.V ∩ F).ncard → Surface.Drawing S
  /-- Each `spoke i` is a path subdrawing of `D` between `C₁` and `F`, enclosed by `F`
  (meeting `F` only at its outer endpoint). -/
  isPath_spoke : ∀ i, ∃ (hs : 0 < ((D.V ∩ F).ncard + 1) / 2) (u v : S),
    (spoke i).IsSubdrawing D ∧ u ∈ (nest.circuit ⟨0, hs⟩).U ∧ v ∈ F ∧
    (spoke i).IsPathBetween u v ∧ OArcEncloses Δ F (spoke i).U ∧ (spoke i).V ∩ F = {v}
  /-- `P₁, ..., P_r` are mutually vertex-disjoint. -/
  pairwise_disjoint_spokes : Pairwise (fun i i' => Disjoint (spoke i).V (spoke i').V)
  /-- For each `i` and `j`, the intersection of `P_i` and `C_j` is a path. -/
  inter_isPath : ∀ i j, ∃ (Q : Surface.Drawing S) (a b : S),
    Q.IsSubdrawing D ∧ Q.V = (spoke i).V ∩ (circuitDraw j).V ∧
    Q.E = (spoke i).E ∩ (circuitDraw j).E ∧ Q.IsPathBetween a b

/-- A subdrawing `Γ'` of `D` is a *sleeve* for `F` (GM VIII Section 8, page 268:
"If $C_1, \dots, C_s$ and $P_1, \dots, P_r$ are as in (8.1), the subdrawing
$C_1 \cup \dots \cup C_s \cup P_1 \cup \dots \cup P_r$ is called a *sleeve* for $F$.") if `F` is a
`D`-normal O-arc in `Δ` and `Γ'` is the union of `C₁, ..., C_s` and `P₁, ..., P_r` for some
`SleeveData D Δ F`. -/
def IsSleeve (D : Surface.Drawing S) (Δ F : Set S) (Γ' : Surface.Drawing S) : Prop :=
  F ⊆ Δ ∧ Surface.IsOArc F ∧ D.IsNormal F ∧ Γ'.IsSubdrawing D ∧
    ∃ sd : SleeveData D Δ F,
      Γ'.V = (⋃ j, (sd.circuitDraw j).V) ∪ (⋃ i, (sd.spoke i).V) ∧
      Γ'.E = (⋃ j, (sd.circuitDraw j).E) ∪ (⋃ i, (sd.spoke i).E)

/-!
## Section 9: Boundary-Linked Nests and Truncations (pages 269–270)
-/

/-- Lift a `DiscCircuit` of a subdrawing `D'` to `D`. -/
def DiscCircuit.ofSubdrawing {D' D : Surface.Drawing S} {Δ : Set S}
    (hsub : D'.IsSubdrawing D) (C : DiscCircuit D' Δ) : DiscCircuit D Δ where
  U := C.U
  ins := C.ins
  U_sub_drawing := C.U_sub_drawing.trans hsub.U_subset
  U_sub_disc := C.U_sub_disc
  isOArc_U := C.isOArc_U
  isInside := C.isInside

/-- Lift a `DrawingNest` of a subdrawing `D'` to `D`. -/
def DrawingNest.ofSubdrawing {D' D : Surface.Drawing S} {Δ : Set S} {r s : ℕ}
    (hsub : D'.IsSubdrawing D) (N : DrawingNest D' Δ r s) : DrawingNest D Δ r s where
  circuit j := (N.circuit j).ofSubdrawing hsub
  inside_of_lt hlt := N.inside_of_lt hlt
  radialPath := N.radialPath
  isPreconnected_radialPath := N.isPreconnected_radialPath
  radialPath_sub_U p := (N.radialPath_sub_U p).trans hsub.U_subset
  radialPath_sub_disc := N.radialPath_sub_disc
  pairwise_disjoint_paths p q hpq := by
    refine Set.disjoint_left.mpr fun x ⟨hxp, hxV⟩ ⟨hxq, _⟩ => ?_
    have hxV' : x ∈ D'.V := by
      by_contra hxnot
      obtain ⟨e, he, hxe⟩ := D'.exists_edge_of_mem (N.radialPath_sub_U p hxp) hxnot
      exact ((hsub.2 he).2.1 hxe).2 hxV
    exact Set.disjoint_left.mp (N.pairwise_disjoint_paths hpq) ⟨hxp, hxV'⟩ ⟨hxq, hxV'⟩
  meets_inner := N.meets_inner
  meets_outer := N.meets_outer

/-- An `(r, s)`-nest `N` in a drawing `D` in a closed disc `Δ` is *boundary-linked*
(GM VIII Section 9, page 269: "An $(r, s)$-nest $(C_1, \dots, C_s)$ is *boundary-linked* if there
are $k$ mutually disjoint paths of $\Gamma$ between $C_1$ and $bd\ \Sigma$.", where
`k = |V(D) ∩ bd Δ|`). -/
def IsBoundaryLinkedNest (D : Surface.Drawing S) (Δ : Set S) {r s : ℕ}
    (N : DrawingNest D Δ r s) : Prop :=
  ∃ P : Fin (D.V ∩ Surface.discBd Δ).ncard → Surface.Drawing S,
    (∀ i, ∃ (hs : 0 < s) (u v : S),
      (P i).IsSubdrawing D ∧ u ∈ (N.circuit ⟨0, hs⟩).U ∧ v ∈ Surface.discBd Δ ∧
      (P i).IsPathBetween u v) ∧
    Pairwise (fun i j => Disjoint (P i).V (P j).V)

/-- A subdrawing `Dstar` of `D` is a *truncation* of `D` in `Δ` induced by a foundation
`F : Fin t → Set S` (GM VIII Section 9, page 269: "We call $\Gamma^*$ a *truncation* of $\Gamma$
(induced by $\{F_1, \dots, F_t\}$)."). -/
def IsTruncationInducedBy (D : Surface.Drawing S) (Δ : Set S) {t : ℕ}
    (F : Fin t → Set S) (Dstar : Surface.Drawing S) : Prop :=
  IsFoundation D Δ F ∧
  Dstar.IsSubdrawing D ∧
  ∃ Γ_sleeve : Fin t → Surface.Drawing S,
    (∀ i, IsSleeve D Δ (F i) (Γ_sleeve i)) ∧
    Dstar.V = {v ∈ D.V | ∀ i : Fin t, ¬ InsideOArc Δ (F i) v} ∪ ⋃ i : Fin t, (Γ_sleeve i).V ∧
    Dstar.E = {e ∈ D.E | ∀ i : Fin t, ¬ SetInsideOArc Δ (F i) e} ∪ ⋃ i : Fin t, (Γ_sleeve i).E

/-- A subdrawing `Dstar` of `D` is a *truncation* of `D` in `Δ` if it is induced by some
foundation `{F₁, ..., F_t}` for `D` in `Δ` (GM VIII Section 9, page 269). -/
def IsTruncation (D : Surface.Drawing S) (Δ : Set S) (Dstar : Surface.Drawing S) : Prop :=
  ∃ (t : ℕ) (F : Fin t → Set S), IsTruncationInducedBy D Δ F Dstar

/-!
## Section 10: Paintings and Q-Portraits (pages 270–271)
-/

/-- A *painting* `Γ = (U(Γ), N(Γ))` in a disc `S` (GM VIII Section 10, page 270):
`U(Γ) ⊆ S` is closed, `N(Γ) ⊆ U(Γ)` is finite,
`(i)` `U(Γ) \ N(Γ)` has only finitely many components, called *cells*,
`(ii)` for each cell `e`, `closure e` is a closed disc with `closure e \ e ⊆ discBd (closure e)`
(so `(closure e, e)` is homeomorphic to `(S, S \ {x₁, ..., x_k})` for `k = |closure e \ e|`
distinct boundary points `x₁, ..., x_k ∈ bd S`), and
`(iii)` for each cell `e`, `e ∩ bd S = ∅`. -/
structure PaintingInDisc (S : Type u) [TopologicalSpace S] where
  /-- The underlying closed subset `U(Γ) ⊆ S`. -/
  U : Set S
  /-- The finite node set `N(Γ) ⊆ U(Γ)`. -/
  N : Set S
  /-- `U(Γ)` is closed in `S`. -/
  isClosed_U : IsClosed U
  /-- `N(Γ) ⊆ U(Γ)`. -/
  N_subset_U : N ⊆ U
  /-- `N(Γ)` is finite. -/
  finite_N : N.Finite
  /-- `(i)` `U(Γ) \ N(Γ)` has only finitely many components, called *cells*. -/
  finite_cells : (Surface.componentsIn (U \ N)).Finite
  /-- `(ii)` For each cell `e`, `closure e` is a closed disc with `closure e \ e` in its boundary. -/
  cell_disc : ∀ e ∈ Surface.componentsIn (U \ N),
    Surface.IsClosedDisc (closure e) ∧ closure e \ e ⊆ Surface.discBd (closure e)
  /-- `(iii)` For each cell `e`, `e ∩ bd S = ∅`. -/
  cell_disjoint_bd : ∀ e ∈ Surface.componentsIn (U \ N), Disjoint e (Surface.bd S)

/-- The set of *cells* `componentsIn (U \ N)` of a painting `(U, N)` in a disc `S`
(GM VIII Section 10, page 270). -/
def PaintingInDisc.cells (P : PaintingInDisc S) : Set (Set S) :=
  Surface.componentsIn (P.U \ P.N)

/-- A painting `P = (U, N)` in a disc `S` has tree-width `≤ w` (GM VIII Section 10, page 271):
there is a hypertree `(N, T, ℱ)` with `|X_t| ≤ w + 1` for each `t ∈ V(T)` such that for each
cell `e` of `P`, `closure e \ e ⊆ X_t` for some `t ∈ V(T)`. -/
def PaintingTreeWidthLE (P : PaintingInDisc S) (w : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (X : ι → Set S),
    IsHypertree P.N T X ∧ HypertreeWidthLE X w ∧
      ∀ e ∈ P.cells, ∃ t : ι, closure e \ e ⊆ X t

/-- The tree-width of a painting `P = (U, N)` in a disc `S` (GM VIII Section 10, page 271). -/
noncomputable def paintingTreeWidth (P : PaintingInDisc S) : ℕ :=
  sInf {w : ℕ | PaintingTreeWidthLE P w}

/-- A `Q`-*portrait* `(U, N, α, μ, φ)` in a disc `S` (GM VIII Section 10, page 271), where
`(U, N)` is a painting in `S`, `α` is an ordering of `U ∩ bd S`, `μ_e` is an ordering of
`closure e \ e` for each cell `e` of `(U, N)`, and `φ` maps cells of `(U, N)` into `Q`. -/
structure QPortrait (Q : Type w) (S : Type u) [TopologicalSpace S] where
  /-- The underlying painting `(U, N)` in `S`. -/
  painting : PaintingInDisc S
  /-- Ordering `α` of `U ∩ bd S`. -/
  α : List S
  /-- `α` has no duplicate entries. -/
  α_nodup : α.Nodup
  /-- `α` enumerates `U ∩ bd S`. -/
  α_set : {x : S | x ∈ α} = painting.U ∩ Surface.bd S
  /-- Ordering `μ e` of `closure e \ e` for each cell `e`. -/
  μ : Set S → List S
  /-- Each `μ e` has no duplicate entries. -/
  μ_nodup : ∀ e ∈ painting.cells, (μ e).Nodup
  /-- Each `μ e` enumerates `closure e \ e`. -/
  μ_set : ∀ e ∈ painting.cells, {x : S | x ∈ μ e} = closure e \ e
  /-- Cell label function `φ` into `Q`. -/
  φ : Set S → Q

/-- The *index* `|U ∩ bd S|` of a `Q`-portrait (GM VIII Section 10, page 271). -/
noncomputable def QPortrait.index {Q : Type w} (P : QPortrait Q S) : ℕ :=
  (P.painting.U ∩ Surface.bd S).ncard

/-- A `Q`-portrait `P` has tree-width `≤ w` if its underlying painting has tree-width `≤ w`
(GM VIII Section 10, page 271: "The *tree-width* of a $\mathbf{Q}$-portrait $(U, N, \alpha, \mu,
\phi)$ equals the tree-width of $(U, N)$."). -/
def PortraitTreeWidthLE {Q : Type w} (P : QPortrait Q S) (w : ℕ) : Prop :=
  PaintingTreeWidthLE P.painting w

/-- The *tree-width* of a `Q`-portrait (GM VIII Section 10, page 271). -/
noncomputable def portraitTreeWidth {Q : Type w} (P : QPortrait Q S) : ℕ :=
  paintingTreeWidth P.painting

/-- A *simulation* `(Ξ, σv, σe)` of a `Q`-portrait `P` in a `Q`-portrait `P'` in a disc `S`
with respect to a quasi-order `le` on `Q`, satisfying conditions `(i)`–`(viii)` of
GM VIII Section 10 (page 271). -/
def IsPortraitSimulation {Q : Type w} (le : Q → Q → Prop)
    (P P' : QPortrait Q S) (Ξ : Surface.Drawing S)
    (σv : S → Graph S (Set S)) (σe : Set S → Set S) : Prop :=
  Ξ.V = P'.painting.N ∧
  Surface.IsGraphForest Ξ.toGraph ∧
  (∀ v ∈ P.painting.N, GM06.IsGraphComponent (σv v) Ξ.toGraph) ∧
  Set.MapsTo σe P.painting.cells P'.painting.cells ∧
  (∀ f ∈ Ξ.E, ∃ e' ∈ P'.painting.cells, f ⊆ e') ∧
  (∀ v₁ ∈ P.painting.N, ∀ v₂ ∈ P.painting.N, v₁ ≠ v₂ → σv v₁ ≠ σv v₂) ∧
  Set.InjOn σe P.painting.cells ∧
  (∀ v ∈ P.painting.N, ∀ e ∈ P.painting.cells, ∀ f ∈ Graph.edgeSet (σv v), Disjoint f (σe e)) ∧
  (∀ e ∈ P.painting.cells, (closure e \ e).ncard = (closure (σe e) \ σe e).ncard) ∧
  (∀ e ∈ P.painting.cells, ∀ (n : ℕ) (hn : n < (P.μ e).length)
    (hn' : n < (P'.μ (σe e)).length),
    (P'.μ (σe e))[n] ∈ Graph.vertexSet (σv (P.μ e)[n])) ∧
  (P.index = P'.index ∧ ∀ (n : ℕ) (hn : n < P.α.length) (hn' : n < P'.α.length),
    P'.α[n] ∈ Graph.vertexSet (σv P.α[n])) ∧
  (∀ e ∈ P.painting.cells, le (P.φ e) (P'.φ (σe e)))

/-- A `Q`-portrait `P` is *simulated in* `P'` if there is a simulation of `P` in `P'`
(GM VIII Section 10, page 271). -/
def IsPortraitSimulatedIn {Q : Type w} (le : Q → Q → Prop) (P P' : QPortrait Q S) : Prop :=
  ∃ (Ξ : Surface.Drawing S) (σv : S → Graph S (Set S)) (σe : Set S → Set S),
    IsPortraitSimulation le P P' Ξ σv σe

/-!
## Section 11: Paintings from Foundations (pages 271–273)
-/

/-- The class `𝒜(k)` of all rooted graphs `(G, τ)` with index `≤ k` whose underlying grafts have
drawings in `S` and where all terms in `τ` are distinct (GM VIII Section 11, pages 271–272).
Taking `k : ℤ` gives `𝒜(-1) = ∅` when `k_nat = 0` and `k = k_nat - 1`. -/
def discRootedClassA {α : Type u'} {β : Type v'} (S : Type u) [TopologicalSpace S] (k : ℤ) :
    Set (RootedGraph α β) :=
  {X : RootedGraph α β | (X.index : ℤ) ≤ k ∧ EmbedsGraft S X.toGraft ∧ X.τ.Nodup}

/-- Carrier type `𝒜(k) ∪ {*}` of the quasi-order `Q_k` (`none` represents `*`, `some X` represents
`X ∈ 𝒜(k)`) from GM VIII Section 11 (page 272). -/
def QKElem (α : Type u') (β : Type v') (S : Type u) [TopologicalSpace S] (k : ℤ) :
    Type (max u' v') :=
  Option (discRootedClassA (α := α) (β := β) S k)

/-- The quasi-order relation `≤` of `Q_k = (𝒜(k) ∪ {*}, ≤)` (GM VIII Section 11, page 272). -/
def qkLE {α : Type u'} {β : Type v'} (S : Type u) [TopologicalSpace S] (k : ℤ) :
    QKElem α β S k → QKElem α β S k → Prop
  | some X₁, some X₂ => IsRootedGraphSimulatedIn X₁.1 X₂.1
  | none, none => True
  | _, _ => False

/-- A drawing `D` in a disc `S` is *cellular* if each loop bounds an open-disc region of `D`
(GM VIII Section 10, page 270: "Let us say that a drawing is *cellular* if each loop bounds a
region."). -/
def IsCellularDrawing (D : Surface.Drawing S) : Prop :=
  ∀ e : Set S, D.IsLoop e →
    ∃ D_e : Set S, Surface.IsInsideDisc Set.univ (closure e) D_e ∧ Surface.discInt D_e ∈ D.R

/-- `P` is a `Q_{k - 1}`-*portrait derived from* `(G, τ)` via a cellular graft drawing `gd` and
foundation `F : Fin t → Set S` in a disc `S` (GM VIII Section 11, page 272:
"We call it a $\mathbf{Q}_{k - 1}$-*portrait derived from* $(G, \tau)$ (via $\Gamma$)."). -/
def IsDerivedPortraitVia {α : Type u'} {β : Type v'} {k : ℕ}
    (X : RootedGraph α β) (gd : Surface.GraftDrawing X.G X.toGraft.T S)
    {t : ℕ} (F : Fin t → Set S)
    (P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S) : Prop :=
  let Γ := gd.drawing
  let discAt : Fin t → Set S := fun i => F i ∪ {x : S | InsideOArc Set.univ (F i) x}
  let N₀ : Set S := {v ∈ Γ.V | ∀ i : Fin t, ¬ InsideOArc Set.univ (F i) v}
  let E₀ : Set (Set S) := {e ∈ Γ.E | ∀ i : Fin t, ¬ SetInsideOArc Set.univ (F i) e}
  X ∈ discRootedClassA S k ∧
  X.index = k ∧
  IsCellularDrawing Γ ∧
  IsFoundation Γ Set.univ F ∧
  P.α.length = X.τ.length ∧
  (∀ (n : ℕ) (hn : n < X.τ.length) (hn' : n < P.α.length),
    (gd.iso.vertexEquiv ⟨X.τ[n], X.τ_subset _ (List.getElem_mem _)⟩).1 = P.α[n]) ∧
  ∃ (α_ring : Fin t → List S) (G_sub : Fin t → RootedGraph α β)
      (hG_sub : ∀ i, G_sub i ∈ discRootedClassA S ((k : ℤ) - 1))
      (D_edge : Set S → Set S),
    (∀ i : Fin t,
      (α_ring i).Nodup ∧
      {x : S | x ∈ α_ring i} = Γ.V ∩ F i ∧
      (G_sub i).G ≤ X.G ∧
      Graph.vertexSet (G_sub i).G =
        {v : α | ∃ hv : v ∈ Graph.vertexSet X.G,
          (gd.iso.vertexEquiv ⟨v, hv⟩).1 ∈ Γ.V ∩ discAt i} ∧
      Graph.edgeSet (G_sub i).G =
        {e : β | ∃ he : e ∈ Graph.edgeSet X.G,
          (gd.iso.edgeEquiv ⟨e, he⟩).1 ∈ edgesInsideOArc Γ Set.univ (F i)} ∧
      (G_sub i).τ.length = (α_ring i).length ∧
      (∀ (n : ℕ) (hn : n < (G_sub i).τ.length) (hn' : n < (α_ring i).length),
        ∃ hv : (G_sub i).τ[n] ∈ Graph.vertexSet X.G,
          (gd.iso.vertexEquiv ⟨(G_sub i).τ[n], hv⟩).1 = (α_ring i)[n])) ∧
    (∀ e ∈ E₀,
      Surface.IsClosedDisc (D_edge e) ∧
      e ⊆ D_edge e ∧
      D_edge e ∩ Γ.U = closure e ∧
      (∀ i : Fin t, D_edge e ∩ discAt i ⊆ closure e) ∧
      (∀ e' ∈ E₀, e ≠ e' → D_edge e ∩ D_edge e' ⊆ closure e ∩ closure e')) ∧
    P.painting.N = N₀ ∧
    P.painting.U = N₀ ∪ (⋃ i : Fin t, discAt i) ∪ (⋃ e ∈ E₀, D_edge e) ∧
    P.painting.cells =
      (Set.range fun i : Fin t => discAt i \ N₀) ∪ ((fun e => D_edge e \ N₀) '' E₀) ∧
    (∀ i : Fin t,
      closure (discAt i \ N₀) = discAt i ∧
      P.μ (discAt i \ N₀) = α_ring i ∧
      P.φ (discAt i \ N₀) = some ⟨G_sub i, hG_sub i⟩) ∧
    (∀ e ∈ E₀,
      closure (D_edge e \ N₀) = D_edge e ∧
      P.φ (D_edge e \ N₀) = none)

/-- `P` is a `Q_{k - 1}`-*portrait derived from* `(G, τ)` in a disc `S` if it is derived via some
cellular drawing `Γ` of `(G, T)` and foundation `F` (GM VIII Section 11, page 272). -/
def IsDerivedPortrait {α : Type u'} {β : Type v'} {k : ℕ}
    (X : RootedGraph α β) (P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S) : Prop :=
  ∃ (gd : Surface.GraftDrawing X.G X.toGraft.T S) (t : ℕ) (F : Fin t → Set S),
    IsDerivedPortraitVia X gd F P

end GM08
end GraphMinor
