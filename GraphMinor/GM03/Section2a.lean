module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section3a
public import GraphMinor.GM07.RegionNest
public import GraphMinor.GM11.SplitEdge
public import GraphMinor.GM11.RegionWalk
public import GraphMinor.GM12.Section3OneDiscComplement
public import GraphMinor.GM14.PieceFacts

/-!
# Graph Minors III, Section 2 Helper Lemmas

This file provides helper constructions and lemmas for Section 2 of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64:
- Edge subdivision (`SplitData`) preserving planarity and drawing radius while producing a
  simple graph with `G` as a minor (for `(2.1)`).
- Rooted parent trees (`parentTree`) and the explicit width-`(3d + 1)` tree-decomposition of
  `N(d, λ)` (`graphN d lam`) via binary heap intervals (`heapSpan`, for `(2.5)`).
- Correspondence between `GM07.regLayer` and `IsRegionChain`, producing a nested sequence of
  `d` circuits when the drawing radius is `≥ d` (for `(2.8)`), and conversely showing that a
  nested sequence of `d + 1` circuits forces the drawing radius to be `> d` (for `(2.3)`).
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22 GraphMinor.Thomas

universe u v w

/-! ## Part 1: Edge Subdivision for (2.1) -/

section SplitEdgeRadius

theorem pair_eq_pair_iff {α : Type*} {a b c d : α} :
    ({a, b} : Set α) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a ∈ ({c, d} : Set α) := h ▸ mem_insert a {b}
    have hb : b ∈ ({c, d} : Set α) := h ▸ mem_insert_of_mem a rfl
    have hc : c ∈ ({a, b} : Set α) := h.symm ▸ mem_insert c {d}
    have hd : d ∈ ({a, b} : Set α) := h.symm ▸ mem_insert_of_mem c rfl
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rcases hd with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · rcases hc with rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact pair_comm _ _

variable {S : Type} [TopologicalSpace S] {D D₂ D₃ : Drawing S}
  {A B A₂ B₂ : Set S → Set S} {m x y m₂ x₂ y₂ : Set S → S}

/-- Projection of vertices of `D₂` onto `D.V` by mapping each midpoint `m e` (`e ∈ D.E`) to `y e`
and fixing all other points. -/
noncomputable def splitVertexProj (D : Drawing S) (m y : Set S → S) (u : S) : S :=
  if h : ∃ e ∈ D.E, u = m e then y h.choose else u

theorem splitVertexProj_of_mem_V (hd : SplitData D D₂ A B m x y) {u : S} (hu : u ∈ D.V) :
    splitVertexProj D m y u = u := by
  unfold splitVertexProj
  split_ifs with h
  · obtain ⟨e, he, rfl⟩ := h
    exact (hd.mid_notMem he hu).elim
  · rfl

theorem splitVertexProj_mid (hd : SplitData D D₂ A B m x y) {e : Set S} (he : e ∈ D.E) :
    splitVertexProj D m y (m e) = y e := by
  unfold splitVertexProj
  split_ifs with h
  · obtain ⟨he', hme⟩ := h.choose_spec
    exact congrArg y (hd.mid_inj he' he hme.symm)
  · exact (h ⟨e, he, rfl⟩).elim

theorem splitVertexProj_mem_V (hd : SplitData D D₂ A B m x y) {u : S} (hu : u ∈ D₂.V) :
    splitVertexProj D m y u ∈ D.V := by
  rw [hd.V_eq] at hu
  rcases hu with huV | ⟨e, he, rfl⟩
  · rw [splitVertexProj_of_mem_V hd huV]; exact huV
  · rw [splitVertexProj_mid hd he]; exact hd.y_mem e he

/-- If `hd : SplitData D D₂ A B m x y`, then `D.toGraph` is isomorphic to the contraction of
`D₂.toGraph` along `B '' D.E`. -/
noncomputable def isoContractOfSplitData (hd : SplitData D D₂ A B m x y) :
    Iso D.toGraph (contract D₂.toGraph (B '' D.E)) := by
  let C : Set (Set S) := B '' D.E
  let rel := fun u v : S => ∃ g ∈ C, D₂.toGraph.IsLink g u v
  let compOf : S → Set S := fun u => {w | Relation.ReflTransGen rel u w}
  have hB_link : ∀ e ∈ D.E, D₂.toGraph.IsLink (B e) (m e) (y e) := by
    intro e he
    refine ⟨hd.B_mem e he, hd.mid_V₂ he, hd.V_sub (hd.y_mem e he), ?_⟩
    rw [hd.cap_B e he]
  have hA_link : ∀ e ∈ D.E, D₂.toGraph.IsLink (A e) (x e) (m e) := by
    intro e he
    refine ⟨hd.A_mem e he, hd.V_sub (hd.x_mem e he), hd.mid_V₂ he, ?_⟩
    rw [hd.cap_A e he]
  have hrel_proj : ∀ u w : S, rel u w →
      splitVertexProj D m y u = splitVertexProj D m y w := by
    rintro u w ⟨g, ⟨e, he, rfl⟩, _, _, _, hcap⟩
    rw [hd.cap_B e he] at hcap
    have hu : u ∈ ({m e, y e} : Set S) := hcap ▸ mem_insert u {w}
    have hw : w ∈ ({m e, y e} : Set S) := hcap ▸ mem_insert_of_mem u rfl
    have hyV : y e ∈ D.V := hd.y_mem e he
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
    · rfl
    · rw [splitVertexProj_mid hd he, splitVertexProj_of_mem_V hd hyV]
    · rw [splitVertexProj_of_mem_V hd hyV, splitVertexProj_mid hd he]
    · rfl
  have hpath_proj : ∀ u w : S, Relation.ReflTransGen rel u w →
      splitVertexProj D m y u = splitVertexProj D m y w := by
    intro u w hpath
    induction hpath with
    | refl => rfl
    | @tail b c _ hbc ih => exact ih.trans (hrel_proj b c hbc)
  have hto_proj : ∀ u ∈ D₂.V, Relation.ReflTransGen rel u (splitVertexProj D m y u) := by
    intro u hu
    rw [hd.V_eq] at hu
    rcases hu with huV | ⟨e, he, rfl⟩
    · rw [splitVertexProj_of_mem_V hd huV]
    · rw [splitVertexProj_mid hd he]
      exact Relation.ReflTransGen.single ⟨B e, ⟨e, he, rfl⟩, hB_link e he⟩
  have hpath_symm : ∀ {u w : S}, Relation.ReflTransGen rel u w → Relation.ReflTransGen rel w u := by
    intro u w hpath
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c _ hbc ih =>
      obtain ⟨g, hg, hl⟩ := hbc
      exact (Relation.ReflTransGen.single ⟨g, hg, hl.symm⟩).trans ih
  have hcomp_eq_proj : ∀ u ∈ D₂.V, compOf u = compOf (splitVertexProj D m y u) := by
    intro u hu
    ext z
    simp only [compOf, mem_ofPred_eq]
    exact ⟨fun huz => (hpath_symm (hto_proj u hu)).trans huz,
      fun hprojz => (hto_proj u hu).trans hprojz⟩
  have hcomp_inj_V : InjOn compOf D.V := by
    intro u hu v hv huv
    have huv_rel : Relation.ReflTransGen rel u v := by
      have : v ∈ compOf v := Relation.ReflTransGen.refl
      rwa [← huv] at this
    have hproj := hpath_proj u v huv_rel
    rwa [splitVertexProj_of_mem_V hd hu, splitVertexProj_of_mem_V hd hv] at hproj
  have hV_contract : V(contract D₂.toGraph C) = compOf '' D.V := by
    change compOf '' D₂.V = compOf '' D.V
    apply Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hcomp_eq_proj u hu]
      exact ⟨splitVertexProj D m y u, splitVertexProj_mem_V hd hu, rfl⟩
    · exact image_mono fun u hu => hd.V_sub hu
  have hinj_A : InjOn A D.E := fun e₁ he₁ e₂ he₂ h =>
    hd.edge_of_piece he₁ he₂ (Or.inl h)
  have hE_contract : E(contract D₂.toGraph C) = A '' D.E := by
    change D₂.E \ (B '' D.E) = A '' D.E
    ext g
    simp only [mem_sdiff, mem_image]
    constructor
    · rintro ⟨hg, hnotB⟩
      obtain ⟨e, he, rfl | rfl⟩ := hd.all g hg
      · exact ⟨e, he, rfl⟩
      · exact (hnotB ⟨e, he, rfl⟩).elim
    · rintro ⟨e, he, rfl⟩
      refine ⟨hd.A_mem e he, ?_⟩
      rintro ⟨e', he', hBe⟩
      have heq : e' = e := hd.edge_of_piece he' he (Or.inr (Or.inr (Or.inl hBe)))
      subst heq
      exact hd.ne_AB he hBe.symm
  refine
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn compOf D.V hcomp_inj_V).trans
          (Equiv.subtypeEquivRight fun _ => hV_contract.symm ▸ Iff.rfl)
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn A D.E hinj_A).trans
          (Equiv.subtypeEquivRight fun _ => hE_contract.symm ▸ Iff.rfl)
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩
  change D.toGraph.IsLink e u v ↔ (contract D₂.toGraph C).IsLink (A e) (compOf u) (compOf v)
  simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
  have hAe_not_C : A e ∉ C := by
    rintro ⟨e', he', hBe⟩
    have heq : e' = e := hd.edge_of_piece he' he (Or.inr (Or.inr (Or.inl hBe)))
    subst heq
    exact hd.ne_AB he hBe.symm
  have hcomp_m : compOf (m e) = compOf (y e) := by
    rw [hcomp_eq_proj (m e) (hd.mid_V₂ he), splitVertexProj_mid hd he]
  constructor
  · rintro ⟨_, _, _, hcap⟩
    rw [hd.cap e he] at hcap
    refine ⟨?_, hAe_not_C⟩
    rcases pair_eq_pair_iff.mp hcap with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
    · exact ⟨x e, m e, hA_link e he, hxu ▸ rfl, hcomp_m.trans (hyv ▸ rfl)⟩
    · exact ⟨m e, x e, (hA_link e he).symm, hcomp_m.trans (hyu ▸ rfl), hxv ▸ rfl⟩
  · rintro ⟨⟨a, b, ⟨_, _, _, hcapA⟩, ha_u, hb_v⟩, _⟩
    rw [hd.cap_A e he] at hcapA
    refine ⟨he, hu, hv, ?_⟩
    rw [hd.cap e he]
    rcases pair_eq_pair_iff.mp hcapA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hxu : x e = u := hcomp_inj_V (hd.x_mem e he) hu ha_u
      have hyv : y e = v := hcomp_inj_V (hd.y_mem e he) hv (hcomp_m.symm.trans hb_v)
      rw [hxu, hyv]
    · have hxv : x e = v := hcomp_inj_V (hd.x_mem e he) hv hb_v
      have hyu : y e = u := hcomp_inj_V (hd.y_mem e he) hu (hcomp_m.symm.trans ha_u)
      rw [hxv, hyu, pair_comm]

/-- If `hd : SplitData D D₂ A B m x y`, then `D.toGraph` is isomorphic to a minor of
`D₂.toGraph`. -/
theorem isIsoMinor_of_splitData (hd : SplitData D D₂ A B m x y) :
    IsIsoMinor D.toGraph D₂.toGraph := by
  refine ⟨D₂.toGraph, le_rfl, B '' D.E, ?_, ⟨isoContractOfSplitData hd⟩⟩
  rintro _ ⟨e, he, rfl⟩
  exact hd.B_mem e he

/-- Splitting a drawing twice produces a simple graph (`D₃.toGraph.Simple`). -/
theorem simple_of_double_splitData
    (hd₁ : SplitData D D₂ A B m x y)
    (hd₂ : SplitData D₂ D₃ A₂ B₂ m₂ x₂ y₂) :
    D₃.toGraph.Simple where
  not_isLoopAt h z hloop := by
    obtain ⟨hh, _, _, hcap⟩ := hloop
    obtain ⟨a, b, hab, hcap'⟩ := hd₂.noLoop h hh
    have hpair : ({z, z} : Set S) = {a, b} := hcap.symm.trans hcap'
    rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hab rfl
  eq_of_isLink h₁ h₂ u v hl₁ hl₂ := by
    obtain ⟨hh₁, _, _, hcap₁⟩ := hl₁
    obtain ⟨hh₂, _, _, hcap₂⟩ := hl₂
    have hpair : closure h₁ ∩ D₃.V = closure h₂ ∩ D₃.V := hcap₁.trans hcap₂.symm
    obtain ⟨g₁, hg₁, rfl | rfl⟩ := hd₂.all h₁ hh₁ <;>
      obtain ⟨g₂, hg₂, rfl | rfl⟩ := hd₂.all h₂ hh₂
    · rw [hd₂.cap_A g₁ hg₁, hd₂.cap_A g₂ hg₂] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨_, hm⟩ | ⟨hxm, _⟩
      · rw [hd₂.mid_inj hg₁ hg₂ hm]
      · exact (hd₂.mid_notMem hg₂ (hxm ▸ hd₂.x_mem g₁ hg₁)).elim
    · rw [hd₂.cap_A g₁ hg₁, hd₂.cap_B g₂ hg₂] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hxm, _⟩ | ⟨hxy, hm⟩
      · exact (hd₂.mid_notMem hg₂ (hxm ▸ hd₂.x_mem g₁ hg₁)).elim
      · have hg_eq : g₁ = g₂ := hd₂.mid_inj hg₁ hg₂ hm
        subst hg_eq
        exfalso
        obtain ⟨a, b, hab, hcap_g₁⟩ := hd₁.noLoop g₁ hg₁
        have hp : ({x₂ g₁, y₂ g₁} : Set S) = {a, b} := (hd₂.cap g₁ hg₁).symm.trans hcap_g₁
        rw [hxy] at hp
        rcases pair_eq_pair_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hab rfl
    · rw [hd₂.cap_B g₁ hg₁, hd₂.cap_A g₂ hg₂] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hmx, _⟩ | ⟨hm, hyx⟩
      · exact (hd₂.mid_notMem hg₁ (hmx.symm ▸ hd₂.x_mem g₂ hg₂)).elim
      · have hg_eq : g₁ = g₂ := hd₂.mid_inj hg₁ hg₂ hm
        subst hg_eq
        exfalso
        obtain ⟨a, b, hab, hcap_g₁⟩ := hd₁.noLoop g₁ hg₁
        have hp : ({x₂ g₁, y₂ g₁} : Set S) = {a, b} := (hd₂.cap g₁ hg₁).symm.trans hcap_g₁
        rw [hyx] at hp
        rcases pair_eq_pair_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hab rfl
    · rw [hd₂.cap_B g₁ hg₁, hd₂.cap_B g₂ hg₂] at hpair
      rcases pair_eq_pair_iff.mp hpair with ⟨hm, _⟩ | ⟨hmy, _⟩
      · rw [hd₂.mid_inj hg₁ hg₂ hm]
      · exact (hd₂.mid_notMem hg₁ (hmy.symm ▸ hd₂.y_mem g₂ hg₂)).elim

/-- Canonical `GraphDrawing` for `D.toGraph` on `S`. -/
def graphDrawingOfDrawing (D : Drawing S) : GraphDrawing D.toGraph S where
  drawing := D
  iso := Iso.refl D.toGraph

/-- Given `M : PlanarDrawing G` and `D' : Drawing M.S` with `D'.U = M.drawing.U`, the induced
`PlanarDrawing D'.toGraph` with the same infinite region. -/
def planarDrawingOfUEq {α : Type u} {β : Type v} {G : Graph α β} (M : PlanarDrawing G)
    (D' : Drawing M.S) (hU : D'.U = M.drawing.U) : PlanarDrawing D'.toGraph where
  S := M.S
  topSpace := M.topSpace
  isClosedSurface := M.isClosedSurface
  isSphere := M.isSphere
  graphDrawing := graphDrawingOfDrawing D'
  infRegion := M.infRegion
  infRegion_mem := by
    change M.infRegion ∈ componentsIn (univ \ D'.U)
    rw [hU]
    exact M.infRegion_mem

theorem hasDrawingRadiusLE_of_UEq_VSub {α : Type u} {β : Type v} {G : Graph α β}
    (M : PlanarDrawing G) (D' : Drawing M.S) (hU : D'.U = M.drawing.U)
    (hV : M.drawing.V ⊆ D'.V) {d : ℕ} (hrad : HasDrawingRadiusLE M d) :
    HasDrawingRadiusLE (planarDrawingOfUEq M D' hU) d := by
  have hR_eq : D'.R = M.drawing.R := by
    change componentsIn (univ \ D'.U) = componentsIn (univ \ M.drawing.U)
    rw [hU]
  intro R hR
  obtain ⟨k, hkd, R_seq, hR_mem, hR0, hRk, hstep⟩ := hrad R (hR_eq ▸ hR)
  refine ⟨k, hkd, R_seq, fun j => hR_eq.symm ▸ hR_mem j, hR0, hRk, fun j => ?_⟩
  obtain ⟨v, hvV, hv1, hv2⟩ := hstep j
  exact ⟨v, hV hvV, hv1, hv2⟩

theorem splitData_of_exists_split_spec {D D₂ : Drawing S} {A B : Set S → Set S} {m x y : Set S → S}
    (hU : D₂.U = D.U) (hV : D₂.V = D.V ∪ m '' D.E)
    (hE : ∀ e ∈ D.E, A e ∈ D₂.E ∧ B e ∈ D₂.E ∧ m e ∈ e ∧ m e ∉ A e ∧ m e ∉ B e ∧
      Disjoint (A e) (B e) ∧ e = A e ∪ {m e} ∪ B e ∧ x e ∈ D.V ∧ y e ∈ D.V ∧
      closure e ∩ D.V = {x e, y e} ∧ closure (A e) ∩ D₂.V = {x e, m e} ∧
      closure (B e) ∩ D₂.V = {m e, y e})
    (hall : ∀ g ∈ D₂.E, ∃ e ∈ D.E, g = A e ∨ g = B e) :
    SplitData D D₂ A B m x y where
  U_eq := hU
  V_eq := hV
  A_mem e he := (hE e he).1
  B_mem e he := (hE e he).2.1
  mid e he := (hE e he).2.2.1
  mid_A e he := (hE e he).2.2.2.1
  mid_B e he := (hE e he).2.2.2.2.1
  disj e he := (hE e he).2.2.2.2.2.1
  union e he := (hE e he).2.2.2.2.2.2.1
  x_mem e he := (hE e he).2.2.2.2.2.2.2.1
  y_mem e he := (hE e he).2.2.2.2.2.2.2.2.1
  cap e he := (hE e he).2.2.2.2.2.2.2.2.2.1
  cap_A e he := (hE e he).2.2.2.2.2.2.2.2.2.2.1
  cap_B e he := (hE e he).2.2.2.2.2.2.2.2.2.2.2
  all := hall

end SplitEdgeRadius

/-! ## Part 2: Rooted Parent Trees and Tree-Width of `N(d, λ)` for (2.5) -/

section ParentTreeAndGraphN

variable {ι : Type w}

/-- The undirected graph on `ι` in which every vertex `x ≠ r` is adjacent to its parent `p x`. -/
def parentTree (p : ι → ι) (r : ι) : SimpleGraph ι where
  Adj x y := x ≠ y ∧ ((x ≠ r ∧ y = p x) ∨ (y ≠ r ∧ x = p y))
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem parentTree_adj_of_ne_root {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) {x : ι} (hx : x ≠ r) :
    (parentTree p r).Adj x (p x) := by
  refine ⟨?_, Or.inl ⟨hx, rfl⟩⟩
  intro hxp
  have hlt := hμ x hx
  rw [← hxp] at hlt
  exact Nat.lt_irrefl _ hlt

theorem parentTree_reachable_root {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) (x : ι) :
    (parentTree p r).Reachable x r := by
  suffices ∀ n : ℕ, ∀ y : ι, μ y = n → (parentTree p r).Reachable y r from
    this (μ x) x rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy
    by_cases hyr : y = r
    · subst hyr; exact Reachable.refl y
    · have hlt : μ (p y) < n := hy ▸ hμ y hyr
      have hadj : (parentTree p r).Adj y (p y) := parentTree_adj_of_ne_root hμ hyr
      exact hadj.reachable.trans (ih (μ (p y)) hlt (p y) rfl)

theorem parentTree_connected {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) :
    (parentTree p r).Connected where
  preconnected x y := (parentTree_reachable_root hμ x).trans (parentTree_reachable_root hμ y).symm
  nonempty := ⟨r⟩

/-- Bijection between `{x : ι // x ≠ r}` and `(parentTree p r).edgeSet`. -/
noncomputable def parentTreeEdgeEquiv {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) :
    {x : ι // x ≠ r} ≃ (parentTree p r).edgeSet := by
  refine Equiv.ofBijective
    (fun x => ⟨s(x.1, p x.1), by
      rw [mem_edgeSet]
      exact parentTree_adj_of_ne_root hμ x.2⟩)
    ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ heq
    have hsym : (s(x, p x) : Sym2 ι) = s(y, p y) := Subtype.ext_iff.mp heq
    rw [Sym2.eq_iff] at hsym
    rcases hsym with ⟨rfl, _⟩ | ⟨hxy, hyx⟩
    · rfl
    · exfalso
      have h1 : μ (p x) < μ x := hμ x hx
      have h2 : μ (p y) < μ y := hμ y hy
      have h1' : μ (p x) = μ y := congrArg μ hyx
      have h2' : μ x = μ (p y) := congrArg μ hxy
      omega
  · rintro ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet] at he
      rcases he.2 with ⟨hu, rfl⟩ | ⟨hv, rfl⟩
      · exact ⟨⟨u, hu⟩, rfl⟩
      · refine ⟨⟨v, hv⟩, Subtype.ext ?_⟩
        exact Sym2.eq_swap

theorem parentTree_isTree [Fintype ι] {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) :
    (parentTree p r).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨parentTree_connected hμ, ?_⟩
  rw [Nat.card_congr (parentTreeEdgeEquiv hμ).symm]
  have hcard_compl : Nat.card {x : ι // x = r} = 1 := by
    have : Unique {x : ι // x = r} :=
      { default := ⟨r, rfl⟩
        uniq := fun ⟨x, hx⟩ => Subtype.ext hx }
    exact Nat.card_unique
  have hsum := Nat.card_congr (Equiv.sumCompl (fun x : ι => x ≠ r))
  rw [Nat.card_sum] at hsum
  have heq : {x : ι // ¬ x ≠ r} ≃ {x : ι // x = r} :=
    Equiv.subtypeEquivRight fun _ => not_not
  rw [Nat.card_congr heq, hcard_compl] at hsum
  exact hsum

/-- If `S : Set ι` has a local root `x₀ ∈ S` such that every `x ∈ S \ {x₀}` satisfies `x ≠ r` and
`p x ∈ S`, then `S` is convex along paths in `parentTree p r`. -/
theorem onTreePath_mem_of_local_root {p : ι → ι} {r : ι} {μ : ι → ℕ}
    (hμ : ∀ x ≠ r, μ (p x) < μ x) {S : Set ι} {x₀ : ι} (hx₀ : x₀ ∈ S)
    (hparent : ∀ x ∈ S, x ≠ x₀ → x ≠ r ∧ p x ∈ S)
    {t t' t'' : ι} (hpath : OnTreePath (parentTree p r) t t'' t')
    (ht : t ∈ S) (ht'' : t'' ∈ S) :
    t' ∈ S := by
  let T := parentTree p r
  have hwalk : ∀ n : ℕ, ∀ x ∈ S, μ x = n →
      ∃ w : T.Walk x x₀, ∀ z ∈ w.support, z ∈ S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hxS hxn
      by_cases hxx₀ : x = x₀
      · subst hxx₀
        refine ⟨SimpleGraph.Walk.nil, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
        exact hz ▸ hx₀
      · obtain ⟨hxr, hpxS⟩ := hparent x hxS hxx₀
        have hlt : μ (p x) < n := hxn ▸ hμ x hxr
        obtain ⟨w, hw⟩ := ih (μ (p x)) hlt (p x) hpxS rfl
        have hadj : T.Adj x (p x) := parentTree_adj_of_ne_root hμ hxr
        refine ⟨SimpleGraph.Walk.cons hadj w, ?_⟩
        intro z hz
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
        rcases hz with rfl | hz'
        · exact hxS
        · exact hw z hz'
  obtain ⟨wt, hwt⟩ := hwalk (μ t) t ht rfl
  obtain ⟨wt'', hwt''⟩ := hwalk (μ t'') t'' ht'' rfl
  let w : T.Walk t t'' := wt.append wt''.reverse
  have ht'_mem : t' ∈ w.support :=
    onTreePath_iff_forall_walk.mp hpath w
  rw [SimpleGraph.Walk.support_append] at ht'_mem
  rcases List.mem_append.mp ht'_mem with h1 | h2
  · exact hwt t' h1
  · have h2' : t' ∈ wt''.reverse.support := List.mem_of_mem_tail h2
    rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h2'
    exact hwt'' t' h2'

/-! ### Case `d = 0`: `N(0, λ) = Y_λ` has tree-width `≤ 1` -/

/-- Parent map on `GraphNVertex 0 lam` sending every vertex towards `Sum.inl none`. -/
def graphN0Parent (lam : ℕ) : GraphNVertex 0 lam → GraphNVertex 0 lam
  | Sum.inl t => Sum.inl (treeYInternalParent t)
  | Sum.inr (i, _) => Sum.inl (treeYLeafParent lam i)

/-- Depth measure on `GraphNVertex 0 lam` strictly decreasing under `graphN0Parent`. -/
def graphN0Measure (lam : ℕ) : GraphNVertex 0 lam → ℕ
  | Sum.inl none => 0
  | Sum.inl (some (_, m)) => m.1 + 1
  | Sum.inr _ => 2 ^ (lam - 1) + 1

theorem graphN0Measure_parent_lt (lam : ℕ) (x : GraphNVertex 0 lam)
    (hx : x ≠ Sum.inl none) :
    graphN0Measure lam (graphN0Parent lam x) < graphN0Measure lam x := by
  rcases x with (_ | ⟨b, m⟩) | ⟨i, j⟩
  · exact (hx rfl).elim
  · simp only [graphN0Parent, treeYInternalParent]
    split_ifs with h0
    · simp [graphN0Measure]
    · simp only [graphN0Measure]
      omega
  · simp only [graphN0Parent]
    rcases h : treeYLeafParent lam i with _ | ⟨b, m⟩
    · simp [graphN0Measure]
    · simp only [graphN0Measure]
      have hm := m.2
      omega

theorem treeWidthLE_graphN_zero {d : ℕ} (hd : d = 0) (lam : ℕ) :
    TreeWidthLE (graphN d lam) (3 * d + 1) := by
  subst hd
  let r0 : GraphNVertex 0 lam := Sum.inl none
  let p0 := graphN0Parent lam
  let T := parentTree p0 r0
  let X : GraphNVertex 0 lam → Set (GraphNVertex 0 lam) := fun t => {t, p0 t}
  have hT : T.IsTree := parentTree_isTree (graphN0Measure_parent_lt lam)
  have hTD : IsTreeDecomposition (graphN 0 lam) T X := by
    refine ⟨hT, fun _ => subset_univ _, ?_, ?_, ?_⟩
    · apply Subset.antisymm (subset_univ _)
      intro v _
      exact mem_iUnion.mpr ⟨v, mem_insert v _⟩
    · rintro e u v hl
      rcases e with (t | i) | (p | p)
      · rcases hl with ⟨ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨Sum.inl t, mem_insert _ _, mem_insert_of_mem _ rfl⟩
        · exact ⟨Sum.inl t, mem_insert_of_mem _ rfl, mem_insert _ _⟩
      · let leaf : GraphNVertex 0 lam := Sum.inr (i, ⟨0, zero_lt_one⟩)
        rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨leaf, mem_insert_of_mem _ rfl, mem_insert _ _⟩
        · exact ⟨leaf, mem_insert _ _, mem_insert_of_mem _ rfl⟩
      · exact (Nat.lt_irrefl 0 hl.1).elim
      · exact (Nat.lt_irrefl 0 hl.1).elim
    · intro t t' t'' hpath v ⟨hvt, hvt''⟩
      let S : Set (GraphNVertex 0 lam) := {s | v ∈ X s}
      have hvS : v ∈ S := mem_insert v _
      have hparent : ∀ s ∈ S, s ≠ v → s ≠ r0 ∧ p0 s ∈ S := by
        intro s hsS hsv
        rcases hsS with rfl | hps
        · exact (hsv rfl).elim
        · refine ⟨?_, hps.symm ▸ hvS⟩
          rintro rfl
          have hr0 : p0 r0 = r0 := rfl
          exact hsv (hr0.symm.trans hps.symm)
      exact onTreePath_mem_of_local_root (graphN0Measure_parent_lt lam) hvS hparent hpath hvt hvt''
  have hW : TreeDecompHasWidthLE X (3 * 0 + 1) := by
    intro t
    exact (ncard_insert_le t {p0 t}).trans (by simp)
  exact (treeWidthLE_iff_exists_isTreeDecomposition _ _).mpr ⟨_, inferInstance, T, X, hTD, hW⟩

/-! ### Case `d > 0`: Binary Heap Spans and `N(d, λ)` Tree-Decomposition -/

/-- Depth measure on `TreeYInternal lam` strictly decreasing under `treeYInternalParent`. -/
def treeYMeasure {lam : ℕ} : TreeYInternal lam → ℕ
  | none => 0
  | some (_, m) => m.1 + 1

theorem treeYMeasure_parent_lt (lam : ℕ) (t : TreeYInternal lam) (ht : t ≠ none) :
    treeYMeasure (treeYInternalParent t) < treeYMeasure t := by
  rcases t with _ | ⟨b, m⟩
  · exact (ht rfl).elim
  · simp only [treeYInternalParent]
    split_ifs with h0
    · simp [treeYMeasure]
    · simp only [treeYMeasure]
      omega

/-- Binary heap interval `(a, c)` of `[0, L]` associated with heap index `k ≥ 1`. -/
def heapSpan (L : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, L)
  | 1 => (0, L)
  | k + 2 =>
    let p := heapSpan L ((k + 2) / 2)
    let mid := (p.1 + p.2) / 2
    if (k + 2) % 2 = 0 then (p.1, mid) else (mid, p.2)

/-- The three points `{a, (a + c) / 2, c}` of `heapSpan L k`. -/
def heapPoints (L k : ℕ) : Set ℕ :=
  let p := heapSpan L k
  {p.1, (p.1 + p.2) / 2, p.2}

theorem heapSpan_endpoints_mem_parent (L : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    (heapSpan L k).1 ∈ heapPoints L (k / 2) ∧
    (heapSpan L k).2 ∈ heapPoints L (k / 2) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
  simp only [heapSpan, heapPoints]
  split_ifs
  · exact ⟨mem_insert _ _, mem_insert_of_mem _ (mem_insert _ _)⟩
  · exact ⟨mem_insert_of_mem _ (mem_insert _ _),
      mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))⟩

theorem heapSpan_pow_formula (h : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k < 2 ^ h →
      ∃ l < h, ∃ r < 2 ^ l,
        k = 2 ^ l + r ∧
        heapSpan (2 ^ h) k = (r * 2 ^ (h - l), (r + 1) * 2 ^ (h - l)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk1 hkh
    rcases eq_or_lt_of_le hk1 with rfl | hk2
    · have hh_pos : 0 < h := by
        by_contra h0
        have : h = 0 := by omega
        subst this
        omega
      refine ⟨0, hh_pos, 0, zero_lt_one, rfl, ?_⟩
      simp [heapSpan]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      have hdiv_lt : (k' + 2) / 2 < k' + 2 := by omega
      have hdiv_ge : 1 ≤ (k' + 2) / 2 := by omega
      have hdiv_pow : (k' + 2) / 2 < 2 ^ h := lt_trans hdiv_lt hkh
      obtain ⟨l', hl'h, r', hr'l, hdiv_eq, hspan_div⟩ :=
        ih ((k' + 2) / 2) hdiv_lt hdiv_ge hdiv_pow
      have hl'_succ : l' + 1 < h := by
        by_contra hge
        have hle : h ≤ l' + 1 := by omega
        have hpow_le : 2 ^ h ≤ 2 ^ (l' + 1) := Nat.pow_le_pow_right (by omega) hle
        have hpow_succ : 2 ^ (l' + 1) = 2 * 2 ^ l' := by rw [pow_succ']
        omega
      let l := l' + 1
      let r := 2 * r' + (k' + 2) % 2
      have hrl : r < 2 ^ l := by
        have hpow_succ : 2 ^ l = 2 * 2 ^ l' := by rw [pow_succ']
        omega
      have hk_eq : k' + 2 = 2 ^ l + r := by
        have hpow_succ : 2 ^ l = 2 * 2 ^ l' := by rw [pow_succ']
        have hdiv_mod : 2 * ((k' + 2) / 2) + (k' + 2) % 2 = k' + 2 := Nat.div_add_mod (k' + 2) 2
        omega
      refine ⟨l, hl'_succ, r, hrl, hk_eq, ?_⟩
      simp only [heapSpan, hspan_div]
      have hpow_split : 2 ^ (h - l') = 2 * 2 ^ (h - l) := by
        have hsub : h - l' = (h - l) + 1 := by omega
        rw [hsub, pow_succ']
      have hmid_eq :
          (r' * 2 ^ (h - l') + (r' + 1) * 2 ^ (h - l')) / 2 =
            (2 * r' + 1) * 2 ^ (h - l) := by
        rw [hpow_split]
        have hsum :
            r' * (2 * 2 ^ (h - l)) + (r' + 1) * (2 * 2 ^ (h - l)) =
              2 * ((2 * r' + 1) * 2 ^ (h - l)) := by ring
        rw [hsum, Nat.mul_div_right _ (by omega)]
      rw [hmid_eq]
      split_ifs with hmod
      · have hr_even : r = 2 * r' := by omega
        ext
        · dsimp
          rw [hpow_split, hr_even]
          ring
        · dsimp
          rw [hr_even]
      · have hr_odd : r = 2 * r' + 1 := by omega
        ext
        · dsimp
          rw [hr_odd]
        · dsimp
          rw [hpow_split, hr_odd]
          ring

/-- Midpoint of `heapSpan (2 ^ h) k` for `1 ≤ k < 2 ^ h`. -/
def heapMid (h k : ℕ) : ℕ :=
  let p := heapSpan (2 ^ h) k
  (p.1 + p.2) / 2

theorem heapSpan_lt_and_mid_bounds {h k : ℕ} (hk1 : 1 ≤ k) (hkh : k < 2 ^ h) :
    (heapSpan (2 ^ h) k).1 < heapMid h k ∧
    heapMid h k < (heapSpan (2 ^ h) k).2 ∧
    (heapSpan (2 ^ h) k).2 ≤ 2 ^ h := by
  obtain ⟨l, hlh, r, hrl, _, hspan⟩ := heapSpan_pow_formula h k hk1 hkh
  unfold heapMid
  rw [hspan]
  dsimp
  have hpow_split : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
    rw [← pow_succ', show h - l - 1 + 1 = h - l by omega]
  have hmid :
      (r * 2 ^ (h - l) + (r + 1) * 2 ^ (h - l)) / 2 =
        (2 * r + 1) * 2 ^ (h - l - 1) := by
    rw [hpow_split]
    have hsum :
        r * (2 * 2 ^ (h - l - 1)) + (r + 1) * (2 * 2 ^ (h - l - 1)) =
          2 * ((2 * r + 1) * 2 ^ (h - l - 1)) := by ring
    rw [hsum, Nat.mul_div_right _ (by omega)]
  rw [hmid, hpow_split]
  have hpos : 0 < 2 ^ (h - l - 1) := by positivity
  refine ⟨by nlinarith, by nlinarith, ?_⟩
  have hpow_total : 2 ^ h = 2 ^ l * (2 * 2 ^ (h - l - 1)) := by
    rw [← hpow_split, ← pow_add, show l + (h - l) = h by omega]
  rw [hpow_total]
  exact Nat.mul_le_mul_right _ (by omega)

theorem odd_mul_two_pow_inj {h l₁ l₂ r₁ r₂ : ℕ} (hl₁ : l₁ < h) (hl₂ : l₂ < h)
    (heq : (2 * r₁ + 1) * 2 ^ (h - l₁ - 1) = (2 * r₂ + 1) * 2 ^ (h - l₂ - 1)) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have hl_eq : l₁ = l₂ := by
    rcases lt_trichotomy l₁ l₂ with hlt | rfl | hgt
    · exfalso
      have hsub : h - l₁ - 1 = (l₂ - l₁) + (h - l₂ - 1) := by omega
      rw [hsub, pow_add, ← mul_assoc] at heq
      have hpos : 0 < 2 ^ (h - l₂ - 1) := by positivity
      have hmul_eq : (2 * r₁ + 1) * 2 ^ (l₂ - l₁) = 2 * r₂ + 1 :=
        Nat.eq_of_mul_eq_mul_right hpos heq
      have hpow_even : 2 ^ (l₂ - l₁) = 2 * 2 ^ (l₂ - l₁ - 1) := by
        rw [← pow_succ', show l₂ - l₁ - 1 + 1 = l₂ - l₁ by omega]
      rw [hpow_even, ← mul_assoc, mul_comm (2 * r₁ + 1) 2, mul_assoc] at hmul_eq
      omega
    · rfl
    · exfalso
      have hsub : h - l₂ - 1 = (l₁ - l₂) + (h - l₁ - 1) := by omega
      rw [hsub, pow_add, ← mul_assoc] at heq
      have hpos : 0 < 2 ^ (h - l₁ - 1) := by positivity
      have hmul_eq : 2 * r₁ + 1 = (2 * r₂ + 1) * 2 ^ (l₁ - l₂) :=
        Nat.eq_of_mul_eq_mul_right hpos heq
      have hpow_even : 2 ^ (l₁ - l₂) = 2 * 2 ^ (l₁ - l₂ - 1) := by
        rw [← pow_succ', show l₁ - l₂ - 1 + 1 = l₁ - l₂ by omega]
      rw [hpow_even, ← mul_assoc, mul_comm (2 * r₂ + 1) 2, mul_assoc] at hmul_eq
      omega
  subst hl_eq
  have hpos : 0 < 2 ^ (h - l₁ - 1) := by positivity
  have hmul_eq : 2 * r₁ + 1 = 2 * r₂ + 1 := Nat.eq_of_mul_eq_mul_right hpos heq
  exact ⟨rfl, by omega⟩

theorem heapMid_inj {h k₁ k₂ : ℕ} (hk₁ : 1 ≤ k₁) (hkh₁ : k₁ < 2 ^ h)
    (hk₂ : 1 ≤ k₂) (hkh₂ : k₂ < 2 ^ h) (heq : heapMid h k₁ = heapMid h k₂) :
    k₁ = k₂ := by
  obtain ⟨l₁, hl₁, r₁, _, rfl, hspan₁⟩ := heapSpan_pow_formula h k₁ hk₁ hkh₁
  obtain ⟨l₂, hl₂, r₂, _, rfl, hspan₂⟩ := heapSpan_pow_formula h k₂ hk₂ hkh₂
  have hmid : ∀ l < h, ∀ r : ℕ,
      (r * 2 ^ (h - l) + (r + 1) * 2 ^ (h - l)) / 2 = (2 * r + 1) * 2 ^ (h - l - 1) := by
    intro l hl r
    have hpow_split : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
      rw [← pow_succ', show h - l - 1 + 1 = h - l by omega]
    rw [hpow_split]
    have hsum :
        r * (2 * 2 ^ (h - l - 1)) + (r + 1) * (2 * 2 ^ (h - l - 1)) =
          2 * ((2 * r + 1) * 2 ^ (h - l - 1)) := by ring
    rw [hsum, Nat.mul_div_right _ (by omega)]
  unfold heapMid at heq
  rw [hspan₁, hspan₂] at heq
  dsimp at heq
  rw [hmid l₁ hl₁ r₁, hmid l₂ hl₂ r₂] at heq
  obtain ⟨rfl, rfl⟩ := odd_mul_two_pow_inj hl₁ hl₂ heq
  rfl

/-- The 3 natural spoke indices associated with an internal vertex `t : TreeYInternal lam`. -/
def spokeNatSet (lam : ℕ) : TreeYInternal lam → Set ℕ
  | none => {0, 2 ^ (lam - 1), 2 * 2 ^ (lam - 1)}
  | some (b, m) =>
    let L := 2 ^ (lam - 1)
    let p := heapSpan L (m.1 + 1)
    let mid := (p.1 + p.2) / 2
    {b.1 * L + p.1, b.1 * L + mid, (b.1 * L + p.2) % (3 * L)}

/-- The middle spoke index `b.1 * 2 ^ (lam - 1) + mid` of `some (b, m)`. -/
def branchMidSpoke (lam : ℕ) (b : Fin 3) (m : Fin (2 ^ (lam - 1) - 1)) : ℕ :=
  b.1 * 2 ^ (lam - 1) + heapMid (lam - 1) (m.1 + 1)

theorem branchMidSpoke_not_mem_none (lam : ℕ) (b : Fin 3) (m : Fin (2 ^ (lam - 1) - 1)) :
    branchMidSpoke lam b m ∉ spokeNatSet lam none := by
  have hm_lt : m.1 + 1 < 2 ^ (lam - 1) := by omega
  obtain ⟨h1, h2, h3⟩ := heapSpan_lt_and_mid_bounds (by omega) hm_lt
  have hb3 := b.2
  unfold branchMidSpoke spokeNatSet
  rcases (show b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 by omega) with hb | hb | hb <;>
    rw [hb] <;> rintro (h | h | h) <;>
    (try rw [mem_singleton_iff] at h) <;> omega

theorem branchMidSpoke_inj (lam : ℕ) {b₁ b₂ : Fin 3} {m₁ m₂ : Fin (2 ^ (lam - 1) - 1)}
    (heq : branchMidSpoke lam b₁ m₁ = branchMidSpoke lam b₂ m₂) :
    b₁ = b₂ ∧ m₁ = m₂ := by
  have hm₁_lt : m₁.1 + 1 < 2 ^ (lam - 1) := by omega
  have hm₂_lt : m₂.1 + 1 < 2 ^ (lam - 1) := by omega
  obtain ⟨h1₁, hmid₁, h3₁⟩ := heapSpan_lt_and_mid_bounds (by omega) hm₁_lt
  obtain ⟨h1₂, hmid₂, h3₂⟩ := heapSpan_lt_and_mid_bounds (by omega) hm₂_lt
  unfold branchMidSpoke at heq
  have hb_eq : b₁.1 = b₂.1 := by nlinarith
  rw [hb_eq] at heq
  have hmid_eq : heapMid (lam - 1) (m₁.1 + 1) = heapMid (lam - 1) (m₂.1 + 1) :=
    add_left_cancel heq
  have hk_eq := heapMid_inj (by omega) hm₁_lt (by omega) hm₂_lt hmid_eq
  exact ⟨Fin.ext hb_eq, Fin.ext (by omega)⟩

theorem spokeNatSet_mem_parent_of_ne_mid (lam : ℕ) (b : Fin 3) (m : Fin (2 ^ (lam - 1) - 1))
    {x : ℕ} (hx : x ∈ spokeNatSet lam (some (b, m))) (hne : x ≠ branchMidSpoke lam b m) :
    x ∈ spokeNatSet lam (treeYInternalParent (some (b, m))) := by
  have hm_lt : m.1 + 1 < 2 ^ (lam - 1) := by omega
  simp only [spokeNatSet] at hx
  have hmid_eq : ((heapSpan (2 ^ (lam - 1)) (m.1 + 1)).1 +
      (heapSpan (2 ^ (lam - 1)) (m.1 + 1)).2) / 2 =
      heapMid (lam - 1) (m.1 + 1) := rfl
  rw [hmid_eq] at hx
  rcases hx with rfl | hmid | rfl
  · simp only [treeYInternalParent]
    split_ifs with h0
    · have hp1 : (heapSpan (2 ^ (lam - 1)) (m.1 + 1)).1 = 0 := by
        rw [h0]; simp [heapSpan]
      rw [hp1, add_zero]
      simp only [spokeNatSet]
      have hb3 := b.2
      rcases (show b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 by omega) with hb | hb | hb
      · rw [hb, zero_mul]; exact mem_insert _ _
      · rw [hb, one_mul]; exact mem_insert_of_mem _ (mem_insert _ _)
      · rw [hb]; exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))
    · have hk2 : 2 ≤ m.1 + 1 := by omega
      have hparent_k : (m.1 + 1) / 2 - 1 + 1 = (m.1 + 1) / 2 := by omega
      have hp_mem := (heapSpan_endpoints_mem_parent (2 ^ (lam - 1)) hk2).1
      simp only [spokeNatSet, hparent_k]
      rcases hp_mem with hp_eq | hp_eq | hp_eq
      · rw [hp_eq]; exact mem_insert _ _
      · rw [hp_eq]; exact mem_insert_of_mem _ (mem_insert _ _)
      · exfalso
        rw [mem_singleton_iff] at hp_eq
        have hdiv_lt : (m.1 + 1) / 2 < 2 ^ (lam - 1) := by omega
        obtain ⟨h1, h2, _⟩ := heapSpan_lt_and_mid_bounds (by omega) hdiv_lt
        obtain ⟨k', hk'⟩ : ∃ k', m.1 + 1 = k' + 2 := ⟨m.1 - 1, by omega⟩
        have hstep : (heapSpan (2 ^ (lam - 1)) (m.1 + 1)).1 ≤
            heapMid (lam - 1) ((m.1 + 1) / 2) := by
          rw [hk']
          simp only [heapSpan, heapMid]
          split_ifs
          · exact le_of_lt (by rwa [← hk'])
          · exact le_rfl
        dsimp [heapMid] at h1 h2 hstep
        omega
  · exact (hne hmid).elim
  · simp only [treeYInternalParent]
    split_ifs with h0
    · have hp2 : (heapSpan (2 ^ (lam - 1)) (m.1 + 1)).2 = 2 ^ (lam - 1) := by
        rw [h0]; simp [heapSpan]
      rw [hp2]
      simp only [spokeNatSet]
      have hL_pos : 0 < 2 ^ (lam - 1) := by positivity
      have hb3 := b.2
      rcases (show b.1 = 0 ∨ b.1 = 1 ∨ b.1 = 2 by omega) with hb | hb | hb
      · rw [hb, zero_mul, zero_add, Nat.mod_eq_of_lt (by omega)]
        exact mem_insert_of_mem _ (mem_insert _ _)
      · rw [hb, one_mul, show 2 ^ (lam - 1) + 2 ^ (lam - 1) = 2 * 2 ^ (lam - 1) by ring,
          Nat.mod_eq_of_lt (by omega)]
        exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))
      · rw [hb, show 2 * 2 ^ (lam - 1) + 2 ^ (lam - 1) = 3 * 2 ^ (lam - 1) by ring, Nat.mod_self]
        exact mem_insert _ _
    · have hk2 : 2 ≤ m.1 + 1 := by omega
      have hparent_k : (m.1 + 1) / 2 - 1 + 1 = (m.1 + 1) / 2 := by omega
      have hp_mem := (heapSpan_endpoints_mem_parent (2 ^ (lam - 1)) hk2).2
      simp only [spokeNatSet, hparent_k]
      have hdiv_lt : (m.1 + 1) / 2 < 2 ^ (lam - 1) := by omega
      obtain ⟨h1, h2, h3⟩ := heapSpan_lt_and_mid_bounds (by omega) hdiv_lt
      rcases hp_mem with hp_eq | hp_eq | hp_eq
      · exfalso
        obtain ⟨k', hk'⟩ : ∃ k', m.1 + 1 = k' + 2 := ⟨m.1 - 1, by omega⟩
        have hstep : heapMid (lam - 1) ((m.1 + 1) / 2) ≤
            (heapSpan (2 ^ (lam - 1)) (m.1 + 1)).2 := by
          rw [hk']
          simp only [heapSpan, heapMid]
          split_ifs
          · exact le_rfl
          · exact le_of_lt (by rwa [← hk'])
        dsimp [heapMid] at h1 h2 hstep
        omega
      · rw [hp_eq]
        have hlt_3L : b.1 * 2 ^ (lam - 1) +
            ((heapSpan (2 ^ (lam - 1)) ((m.1 + 1) / 2)).1 +
              (heapSpan (2 ^ (lam - 1)) ((m.1 + 1) / 2)).2) / 2 < 3 * 2 ^ (lam - 1) := by
          have hb3 := b.2
          have : ((heapSpan (2 ^ (lam - 1)) ((m.1 + 1) / 2)).1 +
              (heapSpan (2 ^ (lam - 1)) ((m.1 + 1) / 2)).2) / 2 < 2 ^ (lam - 1) :=
            lt_of_lt_of_le h2 h3
          nlinarith
        rw [Nat.mod_eq_of_lt hlt_3L]
        exact mem_insert_of_mem _ (mem_insert _ _)
      · rw [hp_eq]
        exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))

theorem heapSpan_pow_add (h : ℕ) :
    ∀ l < h, ∀ r < 2 ^ l,
      heapSpan (2 ^ h) (2 ^ l + r) = (r * 2 ^ (h - l), (r + 1) * 2 ^ (h - l)) := by
  intro l
  induction l with
  | zero =>
    intro _ r hr
    have hr0 : r = 0 := by omega
    subst hr0
    simp [heapSpan]
  | succ l ih =>
    intro hl r hr
    have hpow_l : 1 ≤ 2 ^ l := Nat.one_le_two_pow
    have hpow_succ : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ']
    obtain ⟨k', hk'⟩ : ∃ k', 2 ^ (l + 1) + r = k' + 2 := ⟨2 ^ (l + 1) + r - 2, by omega⟩
    rw [hk', heapSpan]
    simp only [← hk']
    have hdiv : (2 ^ (l + 1) + r) / 2 = 2 ^ l + r / 2 := by omega
    have hmod : (2 ^ (l + 1) + r) % 2 = r % 2 := by omega
    rw [hdiv, hmod, ih (by omega) (r / 2) (by omega)]
    have hpow_split : 2 ^ (h - l) = 2 * 2 ^ (h - (l + 1)) := by
      have hsub : h - l = (h - (l + 1)) + 1 := by omega
      rw [hsub, pow_succ']
    have hmid :
        (r / 2 * 2 ^ (h - l) + (r / 2 + 1) * 2 ^ (h - l)) / 2 =
          (2 * (r / 2) + 1) * 2 ^ (h - (l + 1)) := by
      rw [hpow_split]
      have hsum :
          r / 2 * (2 * 2 ^ (h - (l + 1))) + (r / 2 + 1) * (2 * 2 ^ (h - (l + 1))) =
            2 * ((2 * (r / 2) + 1) * 2 ^ (h - (l + 1))) := by ring
      rw [hsum, Nat.mul_div_right _ (by omega)]
    rw [hmid]
    split_ifs with hrmod
    · have hr_eq : 2 * (r / 2) = r := by omega
      ext
      · dsimp; rw [hpow_split, ← mul_assoc, mul_comm (r / 2) 2, hr_eq]
      · dsimp; rw [hr_eq]
    · have hr_eq1 : 2 * (r / 2) + 1 = r := by omega
      have hr_eq2 : (r / 2 + 1) * 2 = r + 1 := by omega
      ext
      · dsimp; rw [hr_eq1]
      · dsimp; rw [hpow_split, ← mul_assoc, hr_eq2]

theorem spoke_and_nextSpoke_mem_leafParent (lam : ℕ) (i : Fin (3 * 2 ^ (lam - 1))) :
    i.1 ∈ spokeNatSet lam (treeYLeafParent lam i) ∧
    (nextSpoke i).1 ∈ spokeNatSet lam (treeYLeafParent lam i) := by
  simp only [treeYLeafParent, nextSpoke]
  split_ifs with hlam1
  · have hL1 : 2 ^ (lam - 1) = 1 := by
      have : lam - 1 = 0 := by omega
      simp [this]
    have hi3 : i.1 < 3 := by
      have := i.2
      omega
    simp only [spokeNatSet, hL1, mul_one]
    rcases (show i.1 = 0 ∨ i.1 = 1 ∨ i.1 = 2 by omega) with hi | hi | hi <;>
      simp [hi]
  · have hpow_split : 2 ^ (lam - 1) = 2 * 2 ^ (lam - 2) := by
      rw [← pow_succ', show lam - 2 + 1 = lam - 1 by omega]
    let b : Fin 3 := ⟨i.1 / 2 ^ (lam - 1), Nat.div_lt_of_lt_mul (by linarith [i.2])⟩
    obtain ⟨q, hq_def⟩ : ∃ q, i.1 % 2 ^ (lam - 1) = q := ⟨_, rfl⟩
    obtain ⟨r, hr_def⟩ : ∃ r, q / 2 = r := ⟨_, rfl⟩
    have hq_lt : q < 2 ^ (lam - 1) := hq_def ▸ Nat.mod_lt _ (by positivity)
    have hi_eq : i.1 = b.1 * 2 ^ (lam - 1) + q := by
      have := Nat.div_add_mod i.1 (2 ^ (lam - 1))
      dsimp [b]
      linarith
    have hl_lt : lam - 2 < lam - 1 := by omega
    have hr_lt : r < 2 ^ (lam - 2) := by omega
    have hk_eq : 2 ^ (lam - 2) + (i.1 % 2 ^ (lam - 1)) / 2 - 1 + 1 = 2 ^ (lam - 2) + r := by
      have : 1 ≤ 2 ^ (lam - 2) := Nat.one_le_two_pow
      rw [hq_def, hr_def]
      omega
    have hspan : heapSpan (2 ^ (lam - 1)) (2 ^ (lam - 2) + r) =
        (2 * r, 2 * r + 2) := by
      have hsp := heapSpan_pow_add (lam - 1) (lam - 2) hl_lt r hr_lt
      have hsub : lam - 1 - (lam - 2) = 1 := by omega
      rw [hsub, pow_one] at hsp
      exact hsp.trans (by ext <;> dsimp <;> ring)
    simp only [spokeNatSet]
    rw [hk_eq, hspan]
    dsimp
    have hmid : (2 * r + (2 * r + 2)) / 2 = 2 * r + 1 := by omega
    rw [hmid]
    change i.1 ∈ {b.1 * 2 ^ (lam - 1) + 2 * r,
        b.1 * 2 ^ (lam - 1) + (2 * r + 1),
        (b.1 * 2 ^ (lam - 1) + (2 * r + 2)) % (3 * 2 ^ (lam - 1))} ∧
      (i.1 + 1) % (3 * 2 ^ (lam - 1)) ∈
        {b.1 * 2 ^ (lam - 1) + 2 * r,
          b.1 * 2 ^ (lam - 1) + (2 * r + 1),
          (b.1 * 2 ^ (lam - 1) + (2 * r + 2)) % (3 * 2 ^ (lam - 1))}
    have hq_or : q = 2 * r ∨ q = 2 * r + 1 := by omega
    refine ⟨?_, ?_⟩
    · rw [hi_eq]
      rcases hq_or with hq | hq
      · rw [hq]; exact mem_insert _ _
      · rw [hq]; exact mem_insert_of_mem _ (mem_insert _ _)
    · rw [hi_eq]
      rcases hq_or with hq | hq
      · rw [hq]
        have hlt : b.1 * 2 ^ (lam - 1) + 2 * r + 1 < 3 * 2 ^ (lam - 1) := by
          have hb3 := b.2
          have : 2 * r + 1 < 2 ^ (lam - 1) := by omega
          nlinarith
        rw [Nat.mod_eq_of_lt hlt,
          show b.1 * 2 ^ (lam - 1) + 2 * r + 1 =
            b.1 * 2 ^ (lam - 1) + (2 * r + 1) by ring]
        exact mem_insert_of_mem _ (mem_insert _ _)
      · rw [hq, show b.1 * 2 ^ (lam - 1) + (2 * r + 1) + 1 =
            b.1 * 2 ^ (lam - 1) + (2 * r + 2) by ring]
        exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _))

theorem spokeNatSet_local_root (lam : ℕ) {x : ℕ} {s : TreeYInternal lam}
    (hs : x ∈ spokeNatSet lam s) :
    x ∈ spokeNatSet lam none ∨
      ∃ b₀ m₀, x ∈ spokeNatSet lam (some (b₀, m₀)) ∧ x = branchMidSpoke lam b₀ m₀ := by
  induction hmeas : treeYMeasure s using Nat.strong_induction_on generalizing s with
  | h k ih =>
    rcases s with _ | ⟨b, m⟩
    · exact Or.inl hs
    · by_cases hmid : x = branchMidSpoke lam b m
      · exact Or.inr ⟨b, m, hs, hmid⟩
      · have hparent := spokeNatSet_mem_parent_of_ne_mid lam b m hs hmid
        have hlt : treeYMeasure (treeYInternalParent (some (b, m))) < k := by
          rw [← hmeas]
          exact treeYMeasure_parent_lt lam (some (b, m)) (by simp)
        exact ih _ hlt hparent rfl

/-- The bag $X_t \subseteq V(N(d, \lambda))$ at $t \in V(Y_\lambda)$ in the proof of (2.5). -/
def graphNBag (d lam : ℕ) (t : TreeYInternal lam) : Set (GraphNVertex d lam) :=
  {Sum.inl t, Sum.inl (treeYInternalParent t)} ∪
    {v | ∃ p : Fin (3 * 2 ^ (lam - 1)) × Fin (max d 1),
      p.1.1 ∈ spokeNatSet lam t ∧ v = Sum.inr p}

theorem graphNBag_ncard_le {d : ℕ} (hd : 0 < d) (lam : ℕ) (t : TreeYInternal lam) :
    (graphNBag d lam t).ncard ≤ 3 * d + 2 := by
  obtain ⟨x₁, x₂, x₃, hx⟩ : ∃ x₁ x₂ x₃ : ℕ, spokeNatSet lam t = {x₁, x₂, x₃} := by
    rcases t with _ | ⟨b, m⟩
    · exact ⟨0, 2 ^ (lam - 1), 2 * 2 ^ (lam - 1), rfl⟩
    · exact ⟨_, _, _, rfl⟩
  let ray (x : ℕ) : Set (GraphNVertex d lam) :=
    (fun j : Fin (max d 1) =>
      if h : x < 3 * 2 ^ (lam - 1) then Sum.inr (⟨x, h⟩, j) else Sum.inl t) '' univ
  have hray_ncard : ∀ x : ℕ, (ray x).ncard ≤ d := by
    intro x
    have h1 : (ray x).ncard ≤ (univ : Set (Fin (max d 1))).ncard := ncard_image_le
    have h2 : (univ : Set (Fin (max d 1))).ncard = max d 1 := by
      rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    have h3 : max d 1 = d := Nat.max_eq_left hd
    omega
  have hsub : graphNBag d lam t ⊆
      insert (Sum.inl t) (insert (Sum.inl (treeYInternalParent t))
        (ray x₁ ∪ (ray x₂ ∪ ray x₃))) := by
    rintro v ((rfl | rfl) | ⟨⟨i, j⟩, hi_mem, rfl⟩)
    · exact mem_insert _ _
    · exact mem_insert_of_mem _ (mem_insert _ _)
    · rw [hx] at hi_mem
      apply mem_insert_of_mem _ (mem_insert_of_mem _ ?_)
      have hmem_ray : ∀ x : ℕ, i.1 = x → Sum.inr (i, j) ∈ ray x := by
        intro x hix
        subst hix
        refine ⟨j, mem_univ j, ?_⟩
        simp [i.2]
      rcases hi_mem with rfl | rfl | rfl
      · exact Or.inl (hmem_ray i.1 rfl)
      · exact Or.inr (Or.inl (hmem_ray i.1 rfl))
      · exact Or.inr (Or.inr (hmem_ray i.1 rfl))
  have hle1 := ncard_le_ncard hsub
  have hle2 := ncard_insert_le (Sum.inl t)
    (insert (Sum.inl (treeYInternalParent t)) (ray x₁ ∪ (ray x₂ ∪ ray x₃)))
  have hle3 := ncard_insert_le (Sum.inl (treeYInternalParent t)) (ray x₁ ∪ (ray x₂ ∪ ray x₃))
  have hle4 := ncard_union_le (ray x₁) (ray x₂ ∪ ray x₃)
  have hle5 := ncard_union_le (ray x₂) (ray x₃)
  have hr1 := hray_ncard x₁
  have hr2 := hray_ncard x₂
  have hr3 := hray_ncard x₃
  omega

theorem treeWidthLE_graphN_pos {d : ℕ} (hd : 0 < d) (lam : ℕ) :
    TreeWidthLE (graphN d lam) (3 * d + 1) := by
  let p0 : TreeYInternal lam → TreeYInternal lam := @treeYInternalParent lam
  let T := parentTree p0 none
  let X := graphNBag d lam
  have hT : T.IsTree := parentTree_isTree (treeYMeasure_parent_lt lam)
  have hTD : IsTreeDecomposition (graphN d lam) T X := by
    refine ⟨hT, fun _ => subset_univ _, ?_, ?_, ?_⟩
    · apply Subset.antisymm (subset_univ _)
      rintro (t | ⟨i, j⟩) _
      · exact mem_iUnion.mpr ⟨t, Or.inl (mem_insert _ _)⟩
      · exact mem_iUnion.mpr ⟨treeYLeafParent lam i,
          Or.inr ⟨(i, j), (spoke_and_nextSpoke_mem_leafParent lam i).1, rfl⟩⟩
    · rintro e u v hl
      rcases e with (t | i) | (p | p)
      · rcases hl with ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨t, Or.inl (mem_insert _ _), Or.inl (mem_insert_of_mem _ rfl)⟩
        · exact ⟨t, Or.inl (mem_insert_of_mem _ rfl), Or.inl (mem_insert _ _)⟩
      · let tl := treeYLeafParent lam i
        have hi := (spoke_and_nextSpoke_mem_leafParent lam i).1
        rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨tl, Or.inl (mem_insert _ _), Or.inr ⟨_, hi, rfl⟩⟩
        · exact ⟨tl, Or.inr ⟨_, hi, rfl⟩, Or.inl (mem_insert _ _)⟩
      · let tl := treeYLeafParent lam p.1
        obtain ⟨hi1, hi2⟩ := spoke_and_nextSpoke_mem_leafParent lam p.1
        rcases hl with ⟨_, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨tl, Or.inr ⟨p, hi1, rfl⟩, Or.inr ⟨(nextSpoke p.1, p.2), hi2, rfl⟩⟩
        · exact ⟨tl, Or.inr ⟨(nextSpoke p.1, p.2), hi2, rfl⟩, Or.inr ⟨p, hi1, rfl⟩⟩
      · let tl := treeYLeafParent lam p.1
        have hi1 := (spoke_and_nextSpoke_mem_leafParent lam p.1).1
        rcases hl with ⟨_, hs, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact ⟨tl, Or.inr ⟨p, hi1, rfl⟩, Or.inr ⟨(p.1, ⟨p.2.1 + 1, hs⟩), hi1, rfl⟩⟩
        · exact ⟨tl, Or.inr ⟨(p.1, ⟨p.2.1 + 1, hs⟩), hi1, rfl⟩, Or.inr ⟨p, hi1, rfl⟩⟩
    · intro t t' t'' hpath v ⟨hvt, hvt''⟩
      rcases v with t₀ | ⟨i, j⟩
      · let S : Set (TreeYInternal lam) := {s | Sum.inl t₀ ∈ X s}
        have hmem_iff : ∀ s, s ∈ S ↔ t₀ = s ∨ t₀ = p0 s := by
          intro s
          simp [S, X, graphNBag, p0]
        have ht₀S : t₀ ∈ S := (hmem_iff t₀).mpr (Or.inl rfl)
        have hparent : ∀ s ∈ S, s ≠ t₀ → s ≠ none ∧ p0 s ∈ S := by
          intro s hsS hst₀
          rcases (hmem_iff s).mp hsS with rfl | hps
          · exact (hst₀ rfl).elim
          · refine ⟨?_, hps ▸ ht₀S⟩
            rintro rfl
            exact hst₀ hps.symm
        exact onTreePath_mem_of_local_root (treeYMeasure_parent_lt lam) ht₀S hparent hpath hvt hvt''
      · let S : Set (TreeYInternal lam) := {s | Sum.inr (i, j) ∈ X s}
        have hmem_iff : ∀ s, s ∈ S ↔ i.1 ∈ spokeNatSet lam s := by
          intro s
          simp [S, X, graphNBag]
        have hroot_or := spokeNatSet_local_root lam ((hmem_iff t).mp hvt)
        rcases hroot_or with hnone | ⟨b₀, m₀, hm₀, hmid₀⟩
        · have hnoneS : (none : TreeYInternal lam) ∈ S := (hmem_iff none).mpr hnone
          have hparent : ∀ s ∈ S, s ≠ none → s ≠ none ∧ p0 s ∈ S := by
            intro s hsS hsnone
            rcases s with _ | ⟨b, m⟩
            · exact (hsnone rfl).elim
            · refine ⟨hsnone, (hmem_iff _).mpr ?_⟩
              apply spokeNatSet_mem_parent_of_ne_mid lam b m ((hmem_iff _).mp hsS)
              intro hmid
              exact branchMidSpoke_not_mem_none lam b m (hmid ▸ hnone)
          exact onTreePath_mem_of_local_root (treeYMeasure_parent_lt lam)
            hnoneS hparent hpath hvt hvt''
        · let x₀ : TreeYInternal lam := some (b₀, m₀)
          have hx₀S : x₀ ∈ S := (hmem_iff x₀).mpr hm₀
          have hparent : ∀ s ∈ S, s ≠ x₀ → s ≠ none ∧ p0 s ∈ S := by
            intro s hsS hsx₀
            rcases s with _ | ⟨b, m⟩
            · exfalso
              exact branchMidSpoke_not_mem_none lam b₀ m₀ (hmid₀ ▸ (hmem_iff none).mp hsS)
            · refine ⟨by simp, (hmem_iff _).mpr ?_⟩
              apply spokeNatSet_mem_parent_of_ne_mid lam b m ((hmem_iff _).mp hsS)
              intro hmid
              obtain ⟨rfl, rfl⟩ := branchMidSpoke_inj lam (hmid.symm.trans hmid₀)
              exact hsx₀ rfl
          exact onTreePath_mem_of_local_root (treeYMeasure_parent_lt lam)
            hx₀S hparent hpath hvt hvt''
  have hW : TreeDecompHasWidthLE X (3 * d + 1) := by
    intro t
    exact graphNBag_ncard_le hd lam t
  exact (treeWidthLE_iff_exists_isTreeDecomposition _ _).mpr ⟨_, inferInstance, T, X, hTD, hW⟩

/-- For all $d \ge 0$, $\lambda \ge 1$, the graph $N(d, \lambda)$ has tree-width $\le 3d + 1$. -/
theorem treeWidthLE_graphN (d lam : ℕ) : TreeWidthLE (graphN d lam) (3 * d + 1) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact treeWidthLE_graphN_zero rfl lam
  · exact treeWidthLE_graphN_pos hd lam

end ParentTreeAndGraphN

/-! ## Part 3: Region Layers and Nested Circuits for (2.8) -/

section NestedCircuitsAndRegionLayers

variable {α : Type u} {β : Type v} {G : Graph α β}

/-- A region $R \in M.\text{drawing}.R$ belongs to `GM07.regLayer M.drawing M.infRegion d` if and
only if there is a region chain of length $k \le d$ from $M.\text{infRegion}$ to $R$. -/
theorem regLayer_iff_isRegionChain (M : PlanarDrawing G) (d : ℕ) {R : Set M.S}
    (hR : R ∈ M.drawing.R) :
    R ∈ GM07.regLayer M.drawing M.infRegion d ↔ ∃ k ≤ d, IsRegionChain M R k := by
  induction d generalizing R with
  | zero =>
    simp only [GM07.regLayer, mem_singleton_iff]
    constructor
    · rintro rfl
      refine ⟨0, le_rfl, fun _ => M.infRegion, fun _ => M.infRegion_mem, rfl, rfl, fun j => ?_⟩
      exact Fin.elim0 j
    · rintro ⟨k, hk0, R_seq, _, h0, hk, _⟩
      have hk_eq : k = 0 := by omega
      subst hk_eq
      exact hk.symm.trans h0
  | succ d ih =>
    simp only [GM07.regLayer, mem_union, mem_ofPred_eq]
    constructor
    · rintro (hd | ⟨_, R', hR'_layer, v, hvV, hvR, hvR'⟩)
      · obtain ⟨k, hkd, hchain⟩ := (ih hR).mp hd
        exact ⟨k, by omega, hchain⟩
      · have hR' : R' ∈ M.drawing.R := GM07.regLayer_subset M.infRegion_mem d hR'_layer
        obtain ⟨k, hkd, R_seq, hseq_mem, hseq_0, hseq_k, hseq_step⟩ := (ih hR').mp hR'_layer
        let R_seq' : Fin (k + 2) → Set M.S := fun j =>
          if hj : j.1 < k + 1 then R_seq ⟨j.1, hj⟩ else R
        refine ⟨k + 1, by omega, R_seq', ?_, ?_, ?_, ?_⟩
        · intro j
          dsimp [R_seq']
          split_ifs with hj
          · exact hseq_mem ⟨j.1, hj⟩
          · exact hR
        · simp only [R_seq', Nat.zero_lt_succ, ↓reduceDIte]
          exact hseq_0
        · simp [R_seq']
        · intro j
          by_cases hj : j.1 < k
          · obtain ⟨w, hwV, hw1, hw2⟩ := hseq_step ⟨j.1, hj⟩
            refine ⟨w, hwV, ?_, ?_⟩
            · simp only [R_seq', j.2, ↓reduceDIte]
              exact hw1
            · have hj1 : j.1 + 1 < k + 1 := by omega
              simp only [R_seq', hj1, ↓reduceDIte]
              exact hw2
          · have hjk : j.1 = k := by omega
            refine ⟨v, hvV, ?_, ?_⟩
            · simp only [R_seq', j.2, ↓reduceDIte]
              have hfin : j = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hjk
              rw [hfin, hseq_k]
              exact hvR'
            · have hj1 : ¬ j.1 + 1 < k + 1 := by omega
              simp only [R_seq', hj1, ↓reduceDIte]
              exact hvR
    · rintro ⟨k, hk_le, hchain⟩
      rcases lt_or_eq_of_le hk_le with hlt | rfl
      · exact Or.inl ((ih hR).mpr ⟨k, by omega, hchain⟩)
      · obtain ⟨R_seq, hseq_mem, hseq_0, hseq_k, hseq_step⟩ := hchain
        let R' := R_seq ⟨d, by omega⟩
        have hR' : R' ∈ M.drawing.R := hseq_mem ⟨d, by omega⟩
        have hchain' : IsRegionChain M R' d := by
          refine ⟨fun j => R_seq ⟨j.1, by omega⟩, fun j => hseq_mem ⟨j.1, by omega⟩,
            hseq_0, rfl, fun j => ?_⟩
          exact hseq_step ⟨j.1, by omega⟩
        have hR'_layer : R' ∈ GM07.regLayer M.drawing M.infRegion d :=
          (ih hR').mpr ⟨d, le_rfl, hchain'⟩
        obtain ⟨v, hvV, hv1, hv2⟩ := hseq_step ⟨d, Nat.lt_succ_self d⟩
        exact Or.inr ⟨hR, R', hR'_layer, v, hvV, hseq_k ▸ hv2, hv1⟩

/-- If $R \subseteq M.S$ is a circuit subdrawing of $M.\text{drawing}$, then $V(G)$ and $E(G)$ are
nonempty, so $\alpha$ and $\beta$ are nonempty. -/
theorem nonempty_of_circuit_subdrawing (M : PlanarDrawing G) {R : Drawing M.S}
    (hC : R.IsCircuit) (hsub : R.IsSubdrawing M.drawing) : Nonempty α ∧ Nonempty β := by
  obtain ⟨u, W, _, hlen, _, _⟩ := hC
  rcases W with _ | @⟨_, _, _, e, hl, _⟩
  · simp at hlen
  · have huV : u ∈ M.drawing.V := hsub.1 hl.left_mem
    have heE : e ∈ M.drawing.E := hsub.2 hl.edge_mem
    exact ⟨⟨(M.graphDrawing.iso.vertexEquiv.symm ⟨u, huV⟩).1⟩,
      ⟨(M.graphDrawing.iso.edgeEquiv.symm ⟨e, heE⟩).1⟩⟩

/-- Inverse vertex map from $M.\text{drawing}.V$ to $V(G)$. -/
noncomputable def drawingInvV [Nonempty α] (M : PlanarDrawing G) (x : M.S) : α :=
  if hx : x ∈ V(M.graphDrawing.drawing.toGraph) then
    (M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx⟩).1
  else Classical.arbitrary α

/-- Inverse edge map from $M.\text{drawing}.E$ to $E(G)$. -/
noncomputable def drawingInvE [Nonempty β] (M : PlanarDrawing G) (e : Set M.S) : β :=
  if he : e ∈ E(M.graphDrawing.drawing.toGraph) then
    (M.graphDrawing.iso.edgeEquiv.symm ⟨e, he⟩).1
  else Classical.arbitrary β

theorem gmap_of_planarDrawing [Nonempty α] [Nonempty β] (M : PlanarDrawing G) :
    GM14.GMap M.drawing.toGraph G (drawingInvV M) (drawingInvE M) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    have hx' : x ∈ V(M.graphDrawing.drawing.toGraph) := hx
    simp only [drawingInvV, hx', ↓reduceDIte]
    exact (M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx'⟩).2
  · intro x hx y hy hxy
    have hx' : x ∈ V(M.graphDrawing.drawing.toGraph) := hx
    have hy' : y ∈ V(M.graphDrawing.drawing.toGraph) := hy
    simp only [drawingInvV, hx', hy', ↓reduceDIte] at hxy
    have hsub_eq : M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx'⟩ =
        M.graphDrawing.iso.vertexEquiv.symm ⟨y, hy'⟩ := Subtype.ext hxy
    exact Subtype.ext_iff.mp (M.graphDrawing.iso.vertexEquiv.symm.injective hsub_eq)
  · intro v hv
    let x := M.graphDrawing.iso.vertexEquiv ⟨v, hv⟩
    refine ⟨x.1, x.2, ?_⟩
    simp only [drawingInvV, x.2, ↓reduceDIte]
    exact congrArg Subtype.val (M.graphDrawing.iso.vertexEquiv.symm_apply_apply ⟨v, hv⟩)
  · intro e he
    have he' : e ∈ E(M.graphDrawing.drawing.toGraph) := he
    simp only [drawingInvE, he', ↓reduceDIte]
    exact (M.graphDrawing.iso.edgeEquiv.symm ⟨e, he'⟩).2
  · intro e₁ he₁ e₂ he₂ heq
    have he₁' : e₁ ∈ E(M.graphDrawing.drawing.toGraph) := he₁
    have he₂' : e₂ ∈ E(M.graphDrawing.drawing.toGraph) := he₂
    simp only [drawingInvE, he₁', he₂', ↓reduceDIte] at heq
    have hsub_eq : M.graphDrawing.iso.edgeEquiv.symm ⟨e₁, he₁'⟩ =
        M.graphDrawing.iso.edgeEquiv.symm ⟨e₂, he₂'⟩ := Subtype.ext heq
    exact Subtype.ext_iff.mp (M.graphDrawing.iso.edgeEquiv.symm.injective hsub_eq)
  · intro e he
    let s := M.graphDrawing.iso.edgeEquiv ⟨e, he⟩
    refine ⟨s.1, s.2, ?_⟩
    simp only [drawingInvE, s.2, ↓reduceDIte]
    exact congrArg Subtype.val (M.graphDrawing.iso.edgeEquiv.symm_apply_apply ⟨e, he⟩)
  · intro e x y he hx hy
    have he' : e ∈ E(M.graphDrawing.drawing.toGraph) := he
    have hx' : x ∈ V(M.graphDrawing.drawing.toGraph) := hx
    have hy' : y ∈ V(M.graphDrawing.drawing.toGraph) := hy
    simp only [drawingInvV, drawingInvE, he', hx', hy', ↓reduceDIte]
    have hiff := (M.graphDrawing.iso.isLink_iff
      (M.graphDrawing.iso.edgeEquiv.symm ⟨e, he'⟩)
      (M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx'⟩)
      (M.graphDrawing.iso.vertexEquiv.symm ⟨y, hy'⟩)).symm
    rw [M.graphDrawing.iso.edgeEquiv.apply_symm_apply,
      M.graphDrawing.iso.vertexEquiv.apply_symm_apply,
      M.graphDrawing.iso.vertexEquiv.apply_symm_apply] at hiff
    exact hiff

theorem graphDrawingSubgraphU_gmap_sub [Nonempty α] [Nonempty β] (M : PlanarDrawing G)
    {R : Drawing M.S} (hsub : R.IsSubdrawing M.drawing)
    (hRG : R.toGraph ≤ M.drawing.toGraph) :
    graphDrawingSubgraphU M.graphDrawing ((gmap_of_planarDrawing M).sub R.toGraph) = R.U := by
  let m := gmap_of_planarDrawing M
  have hV_apply : ∀ x (hx : x ∈ M.drawing.V),
      graphDrawingVertexSet M.graphDrawing (drawingInvV M x) = {x} := by
    intro x hx
    have hx' : x ∈ V(M.graphDrawing.drawing.toGraph) := hx
    have hmem : drawingInvV M x ∈ V(G) := m.bijV.mapsTo hx
    have h1 : (⟨drawingInvV M x, hmem⟩ : V(G)) =
        M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx'⟩ := by
      ext
      simp [drawingInvV, hx']
    ext y
    simp only [graphDrawingVertexSet, mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨_, rfl⟩
      rw [h1, M.graphDrawing.iso.vertexEquiv.apply_symm_apply]
    · rintro rfl
      refine ⟨hmem, ?_⟩
      rw [h1, M.graphDrawing.iso.vertexEquiv.apply_symm_apply]
  have hE_apply : ∀ e (he : e ∈ M.drawing.E),
      graphDrawingEdgeSet M.graphDrawing (drawingInvE M e) = e := by
    intro e he
    have he' : e ∈ E(M.graphDrawing.drawing.toGraph) := he
    have hmem : drawingInvE M e ∈ E(G) := m.bijE.mapsTo he
    have h1 : (⟨drawingInvE M e, hmem⟩ : E(G)) =
        M.graphDrawing.iso.edgeEquiv.symm ⟨e, he'⟩ := by
      ext
      simp [drawingInvE, he']
    ext y
    simp only [graphDrawingEdgeSet, mem_iUnion]
    constructor
    · rintro ⟨he', hy⟩
      have hsub_eq : (⟨drawingInvE M e, he'⟩ : E(G)) = ⟨drawingInvE M e, hmem⟩ := rfl
      rw [hsub_eq, h1, M.graphDrawing.iso.edgeEquiv.apply_symm_apply] at hy
      exact hy
    · intro hy
      refine ⟨hmem, ?_⟩
      rw [h1, M.graphDrawing.iso.edgeEquiv.apply_symm_apply]
      exact hy
  rw [R.U_eq]
  refine Subset.antisymm (union_subset (iUnion₂_subset ?_) (iUnion₂_subset ?_))
    (union_subset ?_ (iUnion₂_subset ?_))
  · rintro _ ⟨x, hx, rfl⟩
    rw [hV_apply x (hsub.1 hx)]
    exact singleton_subset_iff.mpr (Or.inl hx)
  · intro a ha
    rw [m.edgeSet_sub hRG] at ha
    obtain ⟨e, he, rfl⟩ := ha
    rw [hE_apply e (hsub.2 he)]
    exact subset_biUnion_of_mem (u := fun e => closure e) he |>.trans subset_union_right
  · intro x hx
    refine Or.inl (mem_iUnion₂.mpr ⟨drawingInvV M x, mem_image_of_mem _ hx, ?_⟩)
    rw [hV_apply x (hsub.1 hx)]
    rfl
  · intro e he
    have hmem : drawingInvE M e ∈ E(m.sub R.toGraph) := by
      rw [m.edgeSet_sub hRG]
      exact mem_image_of_mem _ he
    refine Subset.trans ?_ (subset_union_right (s := _))
    refine subset_biUnion_of_mem (u := fun a => closure (graphDrawingEdgeSet M.graphDrawing a))
      hmem |>.trans' ?_
    rw [hE_apply e (hsub.2 he)]

/-- If $M$ does not have drawing radius $\le d - 1$ (when $d > 0$), then $M$ has a nested sequence
$C_1, \dots, C_d$ of circuits (`IsNestedCircuitSeq M d C`). -/
theorem exists_nestedCircuitSeq_of_not_hasDrawingRadiusLE (M : PlanarDrawing G) (d : ℕ)
    (hnot : ∀ _ : 0 < d, ¬ HasDrawingRadiusLE M (d - 1)) :
    ∃ C : Fin d → Graph α β, IsNestedCircuitSeq M d C := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact ⟨Fin.elim0, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  · have hnot' := hnot hd
    unfold HasDrawingRadiusLE at hnot'
    push Not at hnot'
    obtain ⟨r₂, hr₂, hno_chain⟩ := hnot'
    have hfar : ∀ t < d, r₂ ∉ GM07.regLayer M.drawing M.infRegion t := by
      intro t htd hmem
      obtain ⟨k, hkt, hchain⟩ := (regLayer_iff_isRegionChain M t hr₂).mp hmem
      exact hno_chain k (by omega) hchain
    have hS : IsClosedSurface M.S := M.isClosedSurface
    have : T2Space M.S := hS.2.1
    have : ConnectedSpace M.S := (GM11.IsSphere.isClosedSurface M.isSphere).2
    obtain ⟨p, hp⟩ := region_nonempty M.infRegion_mem
    obtain ⟨a, ha⟩ := region_nonempty hr₂
    obtain ⟨C_draw, D, hCD, hnest⟩ :=
      GM07.exists_region_nest hS M.isSphere M.infRegion_mem hr₂ hp ha hfar
    obtain ⟨hα, hβ⟩ := nonempty_of_circuit_subdrawing M
      (hCD ⟨0, hd⟩).1 (hCD ⟨0, hd⟩).2.1
    let m := gmap_of_planarDrawing M
    let C : Fin d → Graph α β := fun t => m.sub (C_draw t).toGraph
    let Δ : Fin d → Set M.S := fun t => closure (univ \ D t)
    have hC_circuit : ∀ t : Fin d, IsGraphCircuit G (C t) := fun t =>
      m.circuit (GM14.isGraphCircuit_of_isCircuit (hCD t).1 (hCD t).2.1)
    have hC_U : ∀ t : Fin d, graphDrawingSubgraphU M.graphDrawing (C t) = (C_draw t).U := fun t =>
      graphDrawingSubgraphU_gmap_sub M (hCD t).2.1
        (GM14.isGraphCircuit_of_isCircuit (hCD t).1 (hCD t).2.1).1
    have hΔ_inside : ∀ t : Fin d, IsInsideDisc M (C t) (Δ t) := by
      intro t
      obtain ⟨hCt_circ, hCt_sub, hDt_disc, hDt_bd, hp_Dt, _⟩ := hCD t
      obtain ⟨hΔt_disc, hΔt_bd⟩ :=
        GM12.isClosedDisc_closure_compl_of_sphere hS M.isSphere hDt_disc
      refine ⟨hΔt_disc, hΔt_bd.trans (hDt_bd.trans (hC_U t).symm), ?_⟩
      have hfr : frontier (D t) = (C_draw t).U := by
        rw [GM11.IsClosedDisc.frontier_eq_discBd hS hDt_disc, hDt_bd]
      have hinf_off_U : Disjoint M.infRegion (frontier (D t)) := by
        rw [hfr]
        refine disjoint_left.mpr fun x hxinf hxU => ?_
        obtain ⟨z, -, hz_eq⟩ := (mem_R_iff M.drawing).mp M.infRegion_mem
        rw [hz_eq] at hxinf
        exact (connectedComponentIn_subset _ _ hxinf).2 (hCt_sub.U_subset hxU)
      have hinf_int : M.infRegion ⊆ interior (D t) := by
        rcases inside_or_outside (region_isPreconnected M.infRegion_mem)
            hDt_disc.isClosed hinf_off_U with h | h
        · exact h
        · exact (h hp hp_Dt).elim
      refine disjoint_left.mpr fun x hxΔ hxinf => ?_
      have hx_int : x ∈ interior (D t) := hinf_int hxinf
      have hdisj_open : Disjoint (interior (D t)) (univ \ D t) :=
        disjoint_left.mpr fun y hy1 hy2 => hy2.2 (interior_subset hy1)
      exact disjoint_left.mp (hdisj_open.closure_right isOpen_interior) hx_int hxΔ
    refine ⟨C, hC_circuit, fun t t' htt' => ⟨?_, ?_⟩⟩
    · obtain ⟨hdisjV, _⟩ := hnest t t' htt'
      refine disjoint_left.mpr fun v hv1 hv2 => ?_
      obtain ⟨x₁, hx₁, rfl⟩ := hv1
      obtain ⟨x₂, hx₂, hfeq⟩ := hv2
      have hx₁M : x₁ ∈ M.drawing.V := (hCD t).2.1.1 hx₁
      have hx₂M : x₂ ∈ M.drawing.V := (hCD t').2.1.1 hx₂
      have hxeq : x₁ = x₂ := m.bijV.injOn hx₁M hx₂M hfeq.symm
      exact disjoint_left.mp hdisjV hx₁ (hxeq ▸ hx₂)
    · obtain ⟨_, hsubD⟩ := hnest t t' htt'
      refine ⟨Δ t', Δ t, hΔ_inside t', hΔ_inside t, ?_⟩
      exact closure_mono (sdiff_subset_sdiff_right hsubD)

end NestedCircuitsAndRegionLayers

end GraphMinor.GM03
