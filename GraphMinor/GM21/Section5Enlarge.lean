module

public import GraphMinor.GM21.Section2
public import GraphMinor.GM21.Section5One
public import GraphMinor.Surface.RemoveDiscs
public import GraphMinor.Surface.DiscArcs
public import GraphMinor.Surface.Cap
public import GraphMinor.GM19.OrientOfHomeos
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Graph Minors XXI, Section 5: Enlarging a Surface at a Boundary Vertex (Claim (12) of `(5.2)`)

This file formalizes:
1. General hypergraph-isomorphism transport (`mapHypergraph` and `comapHypergraph`) for `IsGraph`,
   `IsComponentOf`, `IsPathGraph`, `IsLinkage`, `terminals`, `linkagePattern`, `IsVitalLinkage`,
   and `IsTangle`.
2. Half-plane truncation of the closed unit disc in `ℂ` (`exists_truncated_closedUnitDisc`) and
   pushforward to any closed disc `E` via a chart (`exists_subdisc_avoiding_bd_point`).
3. Enlarging a capped surface `S` inside `Shat` across a boundary vertex `v ∈ Γ.V ∩ bd S` by
   shrinking the cuff disc at `v`'s cuff (`exists_enlarged_surface_avoiding_cuff_vertex`), and
   proving **Claim (12)** of Graph Minors XXI, `(5.2)` (`claim_5_2_12`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM19

universe u v w

/-! ## 1. Transporting linkages and tangles along injective hypergraph maps -/

section MapHypergraph

variable {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*}

/-- Forward image of a hypergraph `A : Hypergraph α₁ β₁` under vertex and edge maps
`fV : α₁ → α₂` and `fE : β₁ → β₂`. -/
def mapHypergraph (fV : α₁ → α₂) (fE : β₁ → β₂)
    (A : Hypergraph α₁ β₁) : Hypergraph α₂ β₂ where
  vertexSet := fV '' A.vertexSet
  edgeSet := fE '' A.edgeSet
  Inc e v := ∃ e₀ v₀, A.Inc e₀ v₀ ∧ fE e₀ = e ∧ fV v₀ = v
  vertex_mem_of_inc _ _ := fun ⟨_, v₀, h, _, hv⟩ ↦ ⟨v₀, A.vertex_mem_of_inc h, hv⟩
  edge_mem_of_inc _ _ := fun ⟨e₀, _, h, he, _⟩ ↦ ⟨e₀, A.edge_mem_of_inc h, he⟩
  vertexSet_finite := A.vertexSet_finite.image fV
  edgeSet_finite := A.edgeSet_finite.image fE

/-- Pullback of a hypergraph `A' : Hypergraph α₂ β₂` into a subhypergraph of `G : Hypergraph α₁ β₁`
along `fV : α₁ → α₂` and `fE : β₁ → β₂`. -/
def comapHypergraph (fV : α₁ → α₂) (fE : β₁ → β₂)
    (G : Hypergraph α₁ β₁) (A' : Hypergraph α₂ β₂) : Hypergraph α₁ β₁ where
  vertexSet := {v ∈ G.vertexSet | fV v ∈ A'.vertexSet}
  edgeSet := {e ∈ G.edgeSet | fE e ∈ A'.edgeSet}
  Inc e v := G.Inc e v ∧ fE e ∈ A'.edgeSet ∧ fV v ∈ A'.vertexSet
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, h.2.2⟩
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2.1⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

theorem mapSubH_eq_mapHypergraph {S Z : Type} (ι : S → Z) (A : Hypergraph S (Set S)) :
    mapSubH ι A = mapHypergraph ι (image ι) A := rfl

theorem comapSubH_eq_comapHypergraph {S Z : Type} (ι : S → Z)
    (G : Hypergraph S (Set S)) (A' : Hypergraph Z (Set Z)) :
    comapSubH ι G A' = comapHypergraph ι (image ι) G A' := rfl

theorem comapHypergraph_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    comapHypergraph fV fE G (mapHypergraph fV fE A) = A := by
  apply Hypergraph.ext
  · ext v
    simp only [comapHypergraph, mapHypergraph, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun hvA ↦ ⟨hA.vertexSet_subset hvA, v, hvA, rfl⟩⟩
    rintro ⟨hvG, w, hwA, hwv⟩
    exact hinjV (hA.vertexSet_subset hwA) hvG hwv ▸ hwA
  · ext e
    simp only [comapHypergraph, mapHypergraph, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun heA ↦ ⟨hA.edgeSet_subset heA, e, heA, rfl⟩⟩
    rintro ⟨heG, f, hfA, hfe⟩
    exact hinjE (hA.edgeSet_subset hfA) heG hfe ▸ hfA
  · funext e v
    apply propext
    simp only [comapHypergraph, mapHypergraph, mem_image]
    constructor
    · rintro ⟨hincG, ⟨f, hfA, hfe⟩, _⟩
      have he_eq : f = e := hinjE (hA.edgeSet_subset hfA) (G.edge_mem_of_inc hincG) hfe
      subst he_eq
      exact (GM10.inc_iff_of_le hA hfA).mpr hincG
    · intro hincA
      have heA := A.edge_mem_of_inc hincA
      have hvA := A.vertex_mem_of_inc hincA
      exact ⟨GM10.inc_of_le hA hincA, ⟨e, heA, rfl⟩, ⟨v, hvA, rfl⟩⟩

theorem mapHypergraph_comapHypergraph {G : Hypergraph α₁ β₁} {A' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ mapHypergraph fV fE G) :
    mapHypergraph fV fE (comapHypergraph fV fE G A') = A' := by
  apply Hypergraph.ext
  · ext v'
    simp only [mapHypergraph, comapHypergraph, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨_, hv'⟩, rfl⟩
      exact hv'
    · intro hv'
      obtain ⟨v, hvG, rfl⟩ := hA'.vertexSet_subset hv'
      exact ⟨v, ⟨hvG, hv'⟩, rfl⟩
  · ext e'
    simp only [mapHypergraph, comapHypergraph, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨e, ⟨_, he'⟩, rfl⟩
      exact he'
    · intro he'
      obtain ⟨e, heG, rfl⟩ := hA'.edgeSet_subset he'
      exact ⟨e, ⟨heG, he'⟩, rfl⟩
  · funext e' v'
    apply propext
    simp only [mapHypergraph, comapHypergraph]
    constructor
    · rintro ⟨e₀, v₀, ⟨hincG, he₀', _⟩, rfl, rfl⟩
      have hinc_map : (mapHypergraph fV fE G).Inc (fE e₀) (fV v₀) := ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact (GM10.inc_iff_of_le hA' he₀').mpr hinc_map
    · intro hincA'
      have he' := A'.edge_mem_of_inc hincA'
      have hv' := A'.vertex_mem_of_inc hincA'
      have hinc_map : (mapHypergraph fV fE G).Inc e' v' := GM10.inc_of_le hA' hincA'
      rcases hinc_map with ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact ⟨e₀, v₀, ⟨hincG, he', hv'⟩, rfl, rfl⟩

theorem mapHypergraph_le {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hB : B ≤ G) (hinjE : InjOn fE G.edgeSet)
    (hle : A ≤ B) : mapHypergraph fV fE A ≤ mapHypergraph fV fE B where
  vertexSet_subset := image_mono hle.vertexSet_subset
  edgeSet_subset := image_mono hle.edgeSet_subset
  ends_eq e' he' := by
    obtain ⟨f, hfA, rfl⟩ := he'
    ext v'
    simp only [Hypergraph.ends, mapHypergraph, mem_ofPred_eq]
    constructor
    · rintro ⟨e₀, v₀, hincB, he₀, rfl⟩
      have he₀_eq : e₀ = f :=
        hinjE (hB.edgeSet_subset (B.edge_mem_of_inc hincB)) (hA.edgeSet_subset hfA) he₀
      subst he₀_eq
      exact ⟨e₀, v₀, (GM10.inc_iff_of_le hle hfA).mpr hincB, rfl, rfl⟩
    · rintro ⟨e₀, v₀, hincA, he₀, rfl⟩
      exact ⟨e₀, v₀, GM10.inc_of_le hle hincA, he₀, rfl⟩

theorem comapHypergraph_le_self {G : Hypergraph α₁ β₁} {A' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ mapHypergraph fV fE G) : comapHypergraph fV fE G A' ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, comapHypergraph, mem_ofPred_eq]
    refine ⟨fun hincG ↦ ⟨hincG, he.2, ?_⟩, fun h ↦ h.1⟩
    have hinc_map : (mapHypergraph fV fE G).Inc (fE e) (fV v) := ⟨e, v, hincG, rfl, rfl⟩
    exact A'.vertex_mem_of_inc ((GM10.inc_iff_of_le hA' he.2).mpr hinc_map)

theorem comapHypergraph_le {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ mapHypergraph fV fE G) (hB' : B' ≤ mapHypergraph fV fE G)
    (hle : A' ≤ B') :
    comapHypergraph fV fE G A' ≤ comapHypergraph fV fE G B' := by
  rw [GM10.le_iff_of_le (comapHypergraph_le_self hA') (comapHypergraph_le_self hB')]
  exact ⟨fun _ h ↦ ⟨h.1, hle.vertexSet_subset h.2⟩,
    fun _ h ↦ ⟨h.1, hle.edgeSet_subset h.2⟩⟩

theorem ends_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjE : InjOn fE G.edgeSet) {e : β₁} (he : e ∈ A.edgeSet) :
    (mapHypergraph fV fE A).ends (fE e) = fV '' (A.ends e) := by
  ext v'
  simp only [Hypergraph.ends, mapHypergraph, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨e₀, v₀, hinc, he₀, rfl⟩
    have he₀_eq : e₀ = e :=
      hinjE (hA.edgeSet_subset (A.edge_mem_of_inc hinc)) (hA.edgeSet_subset he) he₀
    subst he₀_eq
    exact ⟨v₀, hinc, rfl⟩
  · rintro ⟨v₀, hinc, rfl⟩
    exact ⟨e, v₀, hinc, rfl, rfl⟩

theorem ends_mapHypergraph_ncard {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {e : β₁} (he : e ∈ A.edgeSet) :
    ((mapHypergraph fV fE A).ends (fE e)).ncard = (A.ends e).ncard := by
  rw [ends_mapHypergraph hA hinjE he]
  refine (hinjV.mono ?_).ncard_image
  intro v hv
  exact hA.vertexSet_subset (A.vertex_mem_of_inc hv)

theorem isGraph_mapHypergraph_iff {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    (mapHypergraph fV fE A).IsGraph ↔ A.IsGraph := by
  constructor
  · intro hG' e he
    have he' : fE e ∈ (mapHypergraph fV fE A).edgeSet := mem_image_of_mem fE he
    obtain ⟨hne', hle2'⟩ := hG' (fE e) he'
    rw [ends_mapHypergraph_ncard hA hinjV hinjE he] at hle2'
    rw [ends_mapHypergraph hA hinjE he] at hne'
    exact ⟨hne'.of_image, hle2'⟩
  · intro hG e' he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨hne, hle2⟩ := hG e he
    rw [ends_mapHypergraph_ncard hA hinjV hinjE he]
    rw [ends_mapHypergraph hA hinjE he]
    exact ⟨hne.image fV, hle2⟩

theorem incidentEdges_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) {v : α₁} (hv : v ∈ A.vertexSet) :
    incidentEdges (mapHypergraph fV fE A) (fV v) = fE '' (incidentEdges A v) := by
  ext e'
  simp only [incidentEdges, mapHypergraph, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨_, e₀, v₀, hinc, rfl, hv₀⟩
    have hv₀_eq : v₀ = v :=
      hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hinc)) (hA.vertexSet_subset hv) hv₀
    subst hv₀_eq
    exact ⟨e₀, ⟨A.edge_mem_of_inc hinc, hinc⟩, rfl⟩
  · rintro ⟨e₀, ⟨he₀, hinc⟩, rfl⟩
    exact ⟨⟨e₀, he₀, rfl⟩, e₀, v, hinc, rfl, rfl⟩

theorem incidentEdges_mapHypergraph_ncard {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {v : α₁} (hv : v ∈ A.vertexSet) :
    (incidentEdges (mapHypergraph fV fE A) (fV v)).ncard = (incidentEdges A v).ncard := by
  rw [incidentEdges_mapHypergraph hA hinjV hv]
  exact (hinjE.mono (fun _ h ↦ hA.edgeSet_subset h.1)).ncard_image

theorem vertexDegree_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {v : α₁} (hv : v ∈ A.vertexSet) :
    vertexDegree (mapHypergraph fV fE A) (fV v) = vertexDegree A v := by
  unfold vertexDegree
  rw [incidentEdges_mapHypergraph_ncard hA hinjV hinjE hv]
  congr 1
  have hloop_eq :
      {e' ∈ incidentEdges (mapHypergraph fV fE A) (fV v) |
        ((mapHypergraph fV fE A).ends e').Subsingleton} =
      fE '' {e ∈ incidentEdges A v | (A.ends e).Subsingleton} := by
    rw [incidentEdges_mapHypergraph hA hinjV hv]
    ext e'
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hsub'⟩
      refine ⟨e, ⟨he, ?_⟩, rfl⟩
      rw [ends_mapHypergraph hA hinjE he.1] at hsub'
      intro x hx y hy
      exact hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hx))
        (hA.vertexSet_subset (A.vertex_mem_of_inc hy))
        (hsub' (mem_image_of_mem fV hx) (mem_image_of_mem fV hy))
    · rintro ⟨e, ⟨he, hsub⟩, rfl⟩
      refine ⟨⟨e, he, rfl⟩, ?_⟩
      rw [ends_mapHypergraph hA hinjE he.1]
      exact hsub.image fV
  rw [hloop_eq]
  exact (hinjE.mono (fun _ h ↦ hA.edgeSet_subset h.1.1)).ncard_image

theorem skeleton_adj_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x y : α₁} (hx : x ∈ A.vertexSet) (hy : y ∈ A.vertexSet) :
    (mapHypergraph fV fE A).skeleton.Adj (fV x) (fV y) ↔ A.skeleton.Adj x y := by
  constructor
  · rintro ⟨hne', _, ⟨e₁, x₁, hx₁, rfl, hfx₁⟩, ⟨e₂, y₂, hy₂, he₂₁, hfy₂⟩⟩
    have hx₁_eq : x₁ = x :=
      hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hx₁)) (hA.vertexSet_subset hx) hfx₁
    have hy₂_eq : y₂ = y :=
      hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hy₂)) (hA.vertexSet_subset hy) hfy₂
    have he₁_eq : e₁ = e₂ :=
      (hinjE (hA.edgeSet_subset (A.edge_mem_of_inc hy₂))
        (hA.edgeSet_subset (A.edge_mem_of_inc hx₁)) he₂₁).symm
    subst hx₁_eq hy₂_eq he₁_eq
    exact ⟨fun hxy ↦ hne' (hxy ▸ rfl), e₁, hx₁, hy₂⟩
  · rintro ⟨hne, e, hxe, hye⟩
    refine ⟨fun h ↦ hne (hinjV (hA.vertexSet_subset hx) (hA.vertexSet_subset hy) h),
      fE e, ⟨e, x, hxe, rfl, rfl⟩, ⟨e, y, hye, rfl, rfl⟩⟩

private theorem skeleton_reachable_of_mapHypergraph {G A : Hypergraph α₁ β₁}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x' y' : α₂} (W' : (mapHypergraph fV fE A).skeleton.Walk x' y')
    {x y : α₁} (hx : x ∈ A.vertexSet) (hy : y ∈ A.vertexSet)
    (hfx : fV x = x') (hfy : fV y = y') :
    A.skeleton.Reachable x y := by
  induction W' generalizing x y with
  | nil =>
    have hxy : x = y := hinjV (hA.vertexSet_subset hx) (hA.vertexSet_subset hy) (hfx.trans hfy.symm)
    subst hxy
    exact SimpleGraph.Reachable.refl x
  | @cons u' v' w' hadj' W₁' ih =>
    rcases hadj' with ⟨hne', _, hinc_u', ⟨e₀, z₀, hinc_z₀, rfl, rfl⟩⟩
    have hz₀ : z₀ ∈ A.vertexSet := A.vertex_mem_of_inc hinc_z₀
    subst hfx
    have hadj' : (mapHypergraph fV fE A).skeleton.Adj (fV x) (fV z₀) :=
      ⟨hne', fE e₀, hinc_u', ⟨e₀, z₀, hinc_z₀, rfl, rfl⟩⟩
    have hadj : A.skeleton.Adj x z₀ :=
      (skeleton_adj_mapHypergraph hA hinjV hinjE hx hz₀).mp hadj'
    exact hadj.reachable.trans (ih hz₀ hy rfl hfy)

theorem skeleton_reachable_mapHypergraph {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x y : α₁} (hx : x ∈ A.vertexSet) (hy : y ∈ A.vertexSet) :
    (mapHypergraph fV fE A).skeleton.Reachable (fV x) (fV y) ↔ A.skeleton.Reachable x y := by
  constructor
  · rintro ⟨W'⟩
    exact skeleton_reachable_of_mapHypergraph hA hinjV hinjE W' hx hy rfl rfl
  · rintro ⟨W⟩
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj W₁ ih =>
      have hv : v ∈ A.vertexSet := by
        rcases hadj with ⟨_, e, _, hv_inc⟩
        exact A.vertex_mem_of_inc hv_inc
      have hadj' : (mapHypergraph fV fE A).skeleton.Adj (fV u) (fV v) :=
        (skeleton_adj_mapHypergraph hA hinjV hinjE hx hv).mpr hadj
      exact hadj'.reachable.trans (ih hv hy)

theorem isComponentOf_mapHypergraph {G A C : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hC : C ≤ A) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsComponentOf (mapHypergraph fV fE A) (mapHypergraph fV fE C) ↔ IsComponentOf A C := by
  have hCG : C ≤ G := hC.trans hA
  constructor
  · rintro ⟨_, hne', hconn', hmax'⟩
    refine ⟨hC, hne'.of_image, ?_, ?_⟩
    · intro x hx y hy
      exact (skeleton_reachable_mapHypergraph hCG hinjV hinjE hx hy).mp
        (hconn' (fV x) (mem_image_of_mem fV hx) (fV y) (mem_image_of_mem fV hy))
    · intro C₁ hC₁A hC₁_ne hC₁_conn hCC₁
      have hC₁G : C₁ ≤ G := hC₁A.trans hA
      have hmap_eq : mapHypergraph fV fE C₁ = mapHypergraph fV fE C := by
        refine hmax' (mapHypergraph fV fE C₁) (mapHypergraph_le hC₁G hA hinjE hC₁A)
          (hC₁_ne.image fV) ?_ (mapHypergraph_le hCG hC₁G hinjE hCC₁)
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact (skeleton_reachable_mapHypergraph hC₁G hinjV hinjE hx hy).mpr (hC₁_conn x hx y hy)
      have h := congrArg (comapHypergraph fV fE G) hmap_eq
      rwa [comapHypergraph_mapHypergraph hC₁G hinjV hinjE,
        comapHypergraph_mapHypergraph hCG hinjV hinjE] at h
  · rintro ⟨_, hne, hconn, hmax⟩
    refine ⟨mapHypergraph_le hCG hA hinjE hC, hne.image fV, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (skeleton_reachable_mapHypergraph hCG hinjV hinjE hx hy).mpr (hconn x hx y hy)
    · intro C' hC'A' hC'_ne hC'_conn hCC'
      have hC'G' : C' ≤ mapHypergraph fV fE G :=
        hC'A'.trans (mapHypergraph_le hA le_rfl hinjE hA)
      let C₁ := comapHypergraph fV fE G C'
      have hC₁G : C₁ ≤ G := comapHypergraph_le_self hC'G'
      have hmapC₁ : mapHypergraph fV fE C₁ = C' := mapHypergraph_comapHypergraph hC'G'
      have hC₁A : C₁ ≤ A := by
        rw [← comapHypergraph_mapHypergraph hA hinjV hinjE]
        exact comapHypergraph_le hC'G' (mapHypergraph_le hA le_rfl hinjE hA) hC'A'
      have hCC₁ : C ≤ C₁ := by
        rw [← comapHypergraph_mapHypergraph hCG hinjV hinjE]
        exact comapHypergraph_le (mapHypergraph_le hCG le_rfl hinjE hCG) hC'G' hCC'
      have hC₁_ne : C₁.vertexSet.Nonempty := by
        rw [← hmapC₁] at hC'_ne
        exact hC'_ne.of_image
      have hC₁_conn : ∀ x ∈ C₁.vertexSet, ∀ y ∈ C₁.vertexSet, C₁.skeleton.Reachable x y := by
        intro x hx y hy
        rw [← skeleton_reachable_mapHypergraph hC₁G hinjV hinjE hx hy, hmapC₁]
        exact hC'_conn (fV x) (hmapC₁ ▸ mem_image_of_mem fV hx)
          (fV y) (hmapC₁ ▸ mem_image_of_mem fV hy)
      have hC₁_eq : C₁ = C := hmax C₁ hC₁A hC₁_ne hC₁_conn hCC₁
      rw [← hmapC₁, hC₁_eq]

theorem isPathGraph_mapHypergraph {G P : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hP : P ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsPathGraph (mapHypergraph fV fE P) ↔ IsPathGraph P := by
  constructor
  · rintro ⟨hG', hne', hconn', hends2', hpar', hdeg2', hacyc'⟩
    refine ⟨(isGraph_mapHypergraph_iff hP hinjV hinjE).mp hG', hne'.of_image, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact (skeleton_reachable_mapHypergraph hP hinjV hinjE hx hy).mp
        (hconn' (fV x) (mem_image_of_mem fV hx) (fV y) (mem_image_of_mem fV hy))
    · intro e he
      have h := hends2' (fE e) (mem_image_of_mem fE he)
      rwa [ends_mapHypergraph_ncard hP hinjV hinjE he] at h
    · intro e₁ he₁ e₂ he₂ hends_eq
      have h_eq' : fE e₁ = fE e₂ := by
        refine hpar' (fE e₁) (mem_image_of_mem fE he₁) (fE e₂) (mem_image_of_mem fE he₂) ?_
        rw [ends_mapHypergraph hP hinjE he₁, ends_mapHypergraph hP hinjE he₂, hends_eq]
      exact hinjE (hP.edgeSet_subset he₁) (hP.edgeSet_subset he₂) h_eq'
    · intro x hx
      have h := hdeg2' (fV x) (mem_image_of_mem fV hx)
      rwa [incidentEdges_mapHypergraph_ncard hP hinjV hinjE hx] at h
    · intro H hHP hH_ne
      have hHG : H ≤ G := hHP.trans hP
      obtain ⟨_, ⟨x, hxH, rfl⟩, hdeg1⟩ :=
        hacyc' (mapHypergraph fV fE H) (mapHypergraph_le hHG hP hinjE hHP) (hH_ne.image fE)
      rw [incidentEdges_mapHypergraph_ncard hHG hinjV hinjE hxH] at hdeg1
      exact ⟨x, hxH, hdeg1⟩
  · rintro ⟨hG, hne, hconn, hends2, hpar, hdeg2, hacyc⟩
    refine ⟨(isGraph_mapHypergraph_iff hP hinjV hinjE).mpr hG, hne.image fV, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (skeleton_reachable_mapHypergraph hP hinjV hinjE hx hy).mpr (hconn x hx y hy)
    · rintro _ ⟨e, he, rfl⟩
      rw [ends_mapHypergraph_ncard hP hinjV hinjE he]
      exact hends2 e he
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hends_eq'
      rw [ends_mapHypergraph hP hinjE he₁, ends_mapHypergraph hP hinjE he₂] at hends_eq'
      have hends_eq : P.ends e₁ = P.ends e₂ := by
        ext v
        constructor
        · intro hv₁
          have : fV v ∈ fV '' P.ends e₂ := hends_eq' ▸ mem_image_of_mem fV hv₁
          obtain ⟨w, hw₂, hwv⟩ := this
          exact hinjV (hP.vertexSet_subset (P.vertex_mem_of_inc hw₂))
            (hP.vertexSet_subset (P.vertex_mem_of_inc hv₁)) hwv ▸ hw₂
        · intro hv₂
          have : fV v ∈ fV '' P.ends e₁ := hends_eq'.symm ▸ mem_image_of_mem fV hv₂
          obtain ⟨w, hw₁, hwv⟩ := this
          exact hinjV (hP.vertexSet_subset (P.vertex_mem_of_inc hw₁))
            (hP.vertexSet_subset (P.vertex_mem_of_inc hv₂)) hwv ▸ hw₁
      rw [hpar e₁ he₁ e₂ he₂ hends_eq]
    · rintro _ ⟨x, hx, rfl⟩
      rw [incidentEdges_mapHypergraph_ncard hP hinjV hinjE hx]
      exact hdeg2 x hx
    · intro H' hH'P' hH'_ne
      have hH'G' : H' ≤ mapHypergraph fV fE G :=
        hH'P'.trans (mapHypergraph_le hP le_rfl hinjE hP)
      let H := comapHypergraph fV fE G H'
      have hHG : H ≤ G := comapHypergraph_le_self hH'G'
      have hmapH : mapHypergraph fV fE H = H' := mapHypergraph_comapHypergraph hH'G'
      have hHP : H ≤ P := by
        rw [← comapHypergraph_mapHypergraph hP hinjV hinjE]
        exact comapHypergraph_le hH'G' (mapHypergraph_le hP le_rfl hinjE hP) hH'P'
      have hH_ne : H.edgeSet.Nonempty := by
        rw [← hmapH] at hH'_ne
        exact hH'_ne.of_image
      obtain ⟨x, hxH, hdeg1⟩ := hacyc H hHP hH_ne
      refine ⟨fV x, hmapH ▸ mem_image_of_mem fV hxH, ?_⟩
      rw [← hmapH, incidentEdges_mapHypergraph_ncard hHG hinjV hinjE hxH]
      exact hdeg1

theorem isLinkage_mapHypergraph {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsLinkage (mapHypergraph fV fE G) (mapHypergraph fV fE L) ↔ IsLinkage G L := by
  constructor
  · rintro ⟨_, hG', hcomp'⟩
    refine ⟨hL, (isGraph_mapHypergraph_iff hL hinjV hinjE).mp hG', ?_⟩
    intro C hC
    have hCG : C ≤ G := hC.1.trans hL
    have hC' : IsComponentOf (mapHypergraph fV fE L) (mapHypergraph fV fE C) :=
      (isComponentOf_mapHypergraph hL hC.1 hinjV hinjE).mpr hC
    exact (isPathGraph_mapHypergraph hCG hinjV hinjE).mp (hcomp' _ hC')
  · rintro ⟨_, hG, hcomp⟩
    refine ⟨mapHypergraph_le hL le_rfl hinjE hL,
      (isGraph_mapHypergraph_iff hL hinjV hinjE).mpr hG, ?_⟩
    intro C' hC'
    have hC'G' : C' ≤ mapHypergraph fV fE G :=
      hC'.1.trans (mapHypergraph_le hL le_rfl hinjE hL)
    let C := comapHypergraph fV fE G C'
    have hCG : C ≤ G := comapHypergraph_le_self hC'G'
    have hmapC : mapHypergraph fV fE C = C' := mapHypergraph_comapHypergraph hC'G'
    have hCL : C ≤ L := by
      rw [← comapHypergraph_mapHypergraph hL hinjV hinjE]
      exact comapHypergraph_le hC'G' (mapHypergraph_le hL le_rfl hinjE hL) hC'.1
    have hC : IsComponentOf L C := by
      rw [← isComponentOf_mapHypergraph hL hCL hinjV hinjE, hmapC]
      exact hC'
    rw [← hmapC]
    exact (isPathGraph_mapHypergraph hCG hinjV hinjE).mpr (hcomp C hC)

theorem terminals_mapHypergraph {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    terminals (mapHypergraph fV fE L) = fV '' terminals L := by
  ext v'
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨v, hvL, rfl⟩, hdeg'⟩
    rw [vertexDegree_mapHypergraph hL hinjV hinjE hvL] at hdeg'
    exact ⟨v, ⟨hvL, hdeg'⟩, rfl⟩
  · rintro ⟨v, ⟨hvL, hdeg⟩, rfl⟩
    refine ⟨mem_image_of_mem fV hvL, ?_⟩
    rw [vertexDegree_mapHypergraph hL hinjV hinjE hvL]
    exact hdeg

theorem linkagePattern_mapHypergraph {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    linkagePattern (mapHypergraph fV fE L) = (image fV) '' linkagePattern L := by
  ext B'
  simp only [linkagePattern, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨C', hC', rfl⟩
    have hC'G' : C' ≤ mapHypergraph fV fE G :=
      hC'.1.trans (mapHypergraph_le hL le_rfl hinjE hL)
    let C := comapHypergraph fV fE G C'
    have hmapC : mapHypergraph fV fE C = C' := mapHypergraph_comapHypergraph hC'G'
    have hCL : C ≤ L := by
      rw [← comapHypergraph_mapHypergraph hL hinjV hinjE]
      exact comapHypergraph_le hC'G' (mapHypergraph_le hL le_rfl hinjE hL) hC'.1
    have hC : IsComponentOf L C := by
      rw [← isComponentOf_mapHypergraph hL hCL hinjV hinjE, hmapC]
      exact hC'
    refine ⟨terminals L ∩ C.vertexSet, ⟨C, hC, rfl⟩, ?_⟩
    rw [← hmapC, terminals_mapHypergraph hL hinjV hinjE]
    change fV '' (terminals L ∩ C.vertexSet) = fV '' terminals L ∩ fV '' C.vertexSet
    ext v'
    simp only [mem_image, mem_inter_iff]
    constructor
    · rintro ⟨v, ⟨hvT, hvC⟩, rfl⟩
      exact ⟨⟨v, hvT, rfl⟩, ⟨v, hvC, rfl⟩⟩
    · rintro ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂₁⟩⟩
      have hv_eq : v₂ = v₁ :=
        hinjV (hL.vertexSet_subset (hCL.vertexSet_subset hv₂))
          (hL.vertexSet_subset hv₁.1) hv₂₁
      exact ⟨v₁, ⟨hv₁, hv_eq ▸ hv₂⟩, rfl⟩
  · rintro ⟨_, ⟨C, hC, rfl⟩, rfl⟩
    refine ⟨mapHypergraph fV fE C,
      (isComponentOf_mapHypergraph hL hC.1 hinjV hinjE).mpr hC, ?_⟩
    rw [terminals_mapHypergraph hL hinjV hinjE]
    change fV '' (terminals L ∩ C.vertexSet) = fV '' terminals L ∩ fV '' C.vertexSet
    ext v'
    simp only [mem_image, mem_inter_iff]
    constructor
    · rintro ⟨v, ⟨hvT, hvC⟩, rfl⟩
      exact ⟨⟨v, hvT, rfl⟩, ⟨v, hvC, rfl⟩⟩
    · rintro ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂₁⟩⟩
      have hv_eq : v₂ = v₁ :=
        hinjV (hL.vertexSet_subset (hC.1.vertexSet_subset hv₂))
          (hL.vertexSet_subset hv₁.1) hv₂₁
      exact ⟨v₁, ⟨hv₁, hv_eq ▸ hv₂⟩, rfl⟩

theorem isVitalLinkage_mapHypergraph {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsVitalLinkage (mapHypergraph fV fE G) (mapHypergraph fV fE L) ↔ IsVitalLinkage G L := by
  constructor
  · rintro ⟨hlink', hV', huniq'⟩
    refine ⟨(isLinkage_mapHypergraph hL hinjV hinjE).mp hlink', ?_, ?_⟩
    · apply Subset.antisymm hL.vertexSet_subset
      intro v hvG
      have : fV v ∈ (mapHypergraph fV fE L).vertexSet := hV'.symm ▸ mem_image_of_mem fV hvG
      obtain ⟨w, hwL, hwv⟩ := this
      exact hinjV (hL.vertexSet_subset hwL) hvG hwv ▸ hwL
    · intro L₁ hL₁ hpat₁
      have hmap_link : IsLinkage (mapHypergraph fV fE G) (mapHypergraph fV fE L₁) :=
        (isLinkage_mapHypergraph hL₁.1 hinjV hinjE).mpr hL₁
      have hmap_pat : linkagePattern (mapHypergraph fV fE L₁) =
          linkagePattern (mapHypergraph fV fE L) := by
        rw [linkagePattern_mapHypergraph hL₁.1 hinjV hinjE,
          linkagePattern_mapHypergraph hL hinjV hinjE, hpat₁]
      have hmap_eq := huniq' (mapHypergraph fV fE L₁) hmap_link hmap_pat
      have h := congrArg (comapHypergraph fV fE G) hmap_eq
      rwa [comapHypergraph_mapHypergraph hL₁.1 hinjV hinjE,
        comapHypergraph_mapHypergraph hL hinjV hinjE] at h
  · rintro ⟨hlink, hV, huniq⟩
    refine ⟨(isLinkage_mapHypergraph hL hinjV hinjE).mpr hlink,
      congrArg (image fV) hV, ?_⟩
    intro L' hL' hpat'
    let L₁ := comapHypergraph fV fE G L'
    have hL₁G : L₁ ≤ G := comapHypergraph_le_self hL'.1
    have hmapL₁ : mapHypergraph fV fE L₁ = L' := mapHypergraph_comapHypergraph hL'.1
    have hL₁_link : IsLinkage G L₁ := by
      rw [← isLinkage_mapHypergraph hL₁G hinjV hinjE, hmapL₁]
      exact hL'
    have hpat₁ : linkagePattern L₁ = linkagePattern L := by
      rw [← hmapL₁, linkagePattern_mapHypergraph hL₁G hinjV hinjE,
        linkagePattern_mapHypergraph hL hinjV hinjE] at hpat'
      ext B
      constructor
      · intro hB
        have hB_sub : B ⊆ G.vertexSet := by
          rcases hB with ⟨C, hC, rfl⟩
          intro v hv
          exact hL₁G.vertexSet_subset hv.1.1
        have : fV '' B ∈ (image fV) '' linkagePattern L := hpat' ▸ mem_image_of_mem (image fV) hB
        obtain ⟨B₂, hB₂, hB₂_eq⟩ := this
        have hB₂_sub : B₂ ⊆ G.vertexSet := by
          rcases hB₂ with ⟨C, hC, rfl⟩
          intro v hv
          exact hL.vertexSet_subset hv.1.1
        have h_eq : B₂ = B := by
          ext v
          constructor
          · intro hv₂
            have : fV v ∈ fV '' B := hB₂_eq ▸ mem_image_of_mem fV hv₂
            obtain ⟨w, hw, hwv⟩ := this
            exact hinjV (hB_sub hw) (hB₂_sub hv₂) hwv ▸ hw
          · intro hv
            have : fV v ∈ fV '' B₂ := hB₂_eq.symm ▸ mem_image_of_mem fV hv
            obtain ⟨w, hw₂, hwv⟩ := this
            exact hinjV (hB₂_sub hw₂) (hB_sub hv) hwv ▸ hw₂
        exact h_eq ▸ hB₂
      · intro hB
        have hB_sub : B ⊆ G.vertexSet := by
          rcases hB with ⟨C, hC, rfl⟩
          intro v hv
          exact hL.vertexSet_subset hv.1.1
        have : fV '' B ∈ (image fV) '' linkagePattern L₁ :=
          hpat'.symm ▸ mem_image_of_mem (image fV) hB
        obtain ⟨B₁, hB₁, hB₁_eq⟩ := this
        have hB₁_sub : B₁ ⊆ G.vertexSet := by
          rcases hB₁ with ⟨C, hC, rfl⟩
          intro v hv
          exact hL₁G.vertexSet_subset hv.1.1
        have h_eq : B₁ = B := by
          ext v
          constructor
          · intro hv₁
            have : fV v ∈ fV '' B := hB₁_eq ▸ mem_image_of_mem fV hv₁
            obtain ⟨w, hw, hwv⟩ := this
            exact hinjV (hB_sub hw) (hB₁_sub hv₁) hwv ▸ hw
          · intro hv
            have : fV v ∈ fV '' B₁ := hB₁_eq.symm ▸ mem_image_of_mem fV hv
            obtain ⟨w, hw₁, hwv⟩ := this
            exact hinjV (hB₁_sub hw₁) (hB_sub hv) hwv ▸ hw₁
        exact h_eq ▸ hB₁
    have hL₁_eq : L₁ = L := huniq L₁ hL₁_link hpat₁
    rw [← hmapL₁, hL₁_eq]

theorem isVitalPLinkage_mapHypergraph {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    {p : ℕ} (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsVitalPLinkage (mapHypergraph fV fE G) (mapHypergraph fV fE L) p ↔ IsVitalPLinkage G L p := by
  unfold IsVitalPLinkage IsPLinkage
  rw [isVitalLinkage_mapHypergraph hL hinjV hinjE,
    isLinkage_mapHypergraph hL hinjV hinjE,
    terminals_mapHypergraph hL hinjV hinjE,
    (hinjV.mono (fun _ h ↦ hL.vertexSet_subset h.1)).ncard_image]

theorem hasVitalPLinkage_mapHypergraph {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    {p : ℕ} (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    HasVitalPLinkage (mapHypergraph fV fE G) p ↔ HasVitalPLinkage G p := by
  constructor
  · rintro ⟨L', hL'⟩
    let L := comapHypergraph fV fE G L'
    have hLG : L ≤ G := comapHypergraph_le_self hL'.1.1.1
    have hmapL : mapHypergraph fV fE L = L' := mapHypergraph_comapHypergraph hL'.1.1.1
    rw [← hmapL, isVitalPLinkage_mapHypergraph hLG hinjV hinjE] at hL'
    exact ⟨L, hL'⟩
  · rintro ⟨L, hL⟩
    exact ⟨mapHypergraph fV fE L, (isVitalPLinkage_mapHypergraph hL.1.1.1 hinjV hinjE).mpr hL⟩

theorem mapHypergraph_union {A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂} :
    mapHypergraph fV fE (A ∪ B) = mapHypergraph fV fE A ∪ mapHypergraph fV fE B := by
  apply Hypergraph.ext
  · exact image_union fV A.vertexSet B.vertexSet
  · exact image_union fE A.edgeSet B.edgeSet
  · funext e v
    apply propext
    change (∃ e₀ v₀, (A.Inc e₀ v₀ ∨ B.Inc e₀ v₀) ∧ fE e₀ = e ∧ fV v₀ = v) ↔
      (∃ e₀ v₀, A.Inc e₀ v₀ ∧ fE e₀ = e ∧ fV v₀ = v) ∨
      (∃ e₀ v₀, B.Inc e₀ v₀ ∧ fE e₀ = e ∧ fV v₀ = v)
    constructor
    · rintro ⟨e₀, v₀, h | h, he, hv⟩
      · exact Or.inl ⟨e₀, v₀, h, he, hv⟩
      · exact Or.inr ⟨e₀, v₀, h, he, hv⟩
    · rintro (⟨e₀, v₀, h, he, hv⟩ | ⟨e₀, v₀, h, he, hv⟩)
      · exact ⟨e₀, v₀, Or.inl h, he, hv⟩
      · exact ⟨e₀, v₀, Or.inr h, he, hv⟩

theorem isSeparation_mapHypergraph {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjE : InjOn fE G.edgeSet) (hsep : G.IsSeparation A B) :
    (mapHypergraph fV fE G).IsSeparation (mapHypergraph fV fE A) (mapHypergraph fV fE B) := by
  have hleA := mapHypergraph_le (fV := fV) hsep.left_le le_rfl hinjE hsep.left_le
  have hleB := mapHypergraph_le (fV := fV) hsep.right_le le_rfl hinjE hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · change fV '' A.vertexSet ∪ fV '' B.vertexSet = fV '' G.vertexSet
    rw [← image_union, hsep.vertexSet_union]
  · change fE '' A.edgeSet ∪ fE '' B.edgeSet = fE '' G.edgeSet
    rw [← image_union, hsep.edgeSet_union]
  · ext e'
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨⟨e₁, he₁, rfl⟩, ⟨e₂, he₂, he₂₁⟩⟩
    have he_eq : e₂ = e₁ :=
      hinjE (hsep.right_le.edgeSet_subset he₂) (hsep.left_le.edgeSet_subset he₁) he₂₁
    subst he_eq
    exact hsep.notMem_edgeSet_right he₁ he₂

theorem isSeparation_comapHypergraph {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hsep : (mapHypergraph fV fE G).IsSeparation A' B') :
    G.IsSeparation (comapHypergraph fV fE G A') (comapHypergraph fV fE G B') := by
  have hleA := comapHypergraph_le_self hsep.left_le
  have hleB := comapHypergraph_le_self hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [comapHypergraph, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hvG
      have hfv : fV v ∈ A'.vertexSet ∪ B'.vertexSet :=
        hsep.vertexSet_union.symm ▸ mem_image_of_mem fV hvG
      exact hfv.imp (fun h ↦ ⟨hvG, h⟩) (fun h ↦ ⟨hvG, h⟩)
  · ext e
    simp only [comapHypergraph, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro heG
      have hfe : fE e ∈ A'.edgeSet ∪ B'.edgeSet :=
        hsep.edgeSet_union.symm ▸ mem_image_of_mem fE heG
      exact hfe.imp (fun h ↦ ⟨heG, h⟩) (fun h ↦ ⟨heG, h⟩)
  · ext e
    simp only [comapHypergraph, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heA'⟩, ⟨_, heB'⟩⟩
    exact hsep.notMem_edgeSet_right heA' heB'

theorem separationOrder_mapHypergraph {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hB : B ≤ G) (hinjV : InjOn fV G.vertexSet) :
    separationOrder (mapHypergraph fV fE A) (mapHypergraph fV fE B) = separationOrder A B := by
  unfold separationOrder
  have h_eq : ((mapHypergraph fV fE A) ∩ (mapHypergraph fV fE B)).vertexSet =
      fV '' (A ∩ B).vertexSet := by
    ext v'
    simp only [GM10.inter_vertexSet, mapHypergraph, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂₁⟩⟩
      have hv_eq : v₂ = v₁ := hinjV (hB.vertexSet_subset hv₂) (hA.vertexSet_subset hv₁) hv₂₁
      exact ⟨v₁, ⟨hv₁, hv_eq ▸ hv₂⟩, rfl⟩
    · rintro ⟨v, ⟨hvA, hvB⟩, rfl⟩
      exact ⟨⟨v, hvA, rfl⟩, ⟨v, hvB, rfl⟩⟩
  rw [h_eq]
  exact (hinjV.mono ((GM10.inter_le hA hB).vertexSet_subset)).ncard_image

theorem separationOrder_comapHypergraph {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ mapHypergraph fV fE G) (hB' : B' ≤ mapHypergraph fV fE G)
    (hinjV : InjOn fV G.vertexSet) :
    separationOrder (comapHypergraph fV fE G A') (comapHypergraph fV fE G B') =
      separationOrder A' B' := by
  rw [← separationOrder_mapHypergraph (fE := fE)
      (comapHypergraph_le_self hA') (comapHypergraph_le_self hB') hinjV,
    mapHypergraph_comapHypergraph hA', mapHypergraph_comapHypergraph hB']

/-- Transport a tangle `𝒯` on `G` forward along `fV` and `fE`. -/
def mapTangle (fV : α₁ → α₂) (fE : β₁ → β₂)
    (𝒯 : Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁)) :
    Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂) :=
  (fun p ↦ (mapHypergraph fV fE p.1, mapHypergraph fV fE p.2)) '' 𝒯

/-- Pull back a tangle `𝒯'` on `mapHypergraph fV fE G` to `G`. -/
def comapTangle (fV : α₁ → α₂) (fE : β₁ → β₂) (G : Hypergraph α₁ β₁)
    (𝒯' : Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂)) :
    Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁) :=
  (fun p ↦ (comapHypergraph fV fE G p.1, comapHypergraph fV fE G p.2)) '' 𝒯'

theorem isTangle_mapHypergraph {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) {θ : ℕ}
    {𝒯 : Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁)}
    (h𝒯 : IsTangle G θ 𝒯) :
    IsTangle (mapHypergraph fV fE G) θ (mapTangle fV fE 𝒯) := by
  refine ⟨h𝒯.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_mapHypergraph hinjE (h𝒯.isSeparation hAB)
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep := h𝒯.isSeparation hAB
    rw [separationOrder_mapHypergraph hsep.left_le hsep.right_le hinjV]
    exact h𝒯.order_lt hAB
  · intro A' B' hsep' hord'
    have hsep := isSeparation_comapHypergraph hsep'
    have hord : separationOrder (comapHypergraph fV fE G A') (comapHypergraph fV fE G B') < θ := by
      rw [separationOrder_comapHypergraph hsep'.left_le hsep'.right_le hinjV]
      exact hord'
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · refine Or.inl ⟨(comapHypergraph fV fE G A', comapHypergraph fV fE G B'), hm, ?_⟩
      simp [mapHypergraph_comapHypergraph hsep'.left_le,
        mapHypergraph_comapHypergraph hsep'.right_le]
    · refine Or.inr ⟨(comapHypergraph fV fE G B', comapHypergraph fV fE G A'), hm, ?_⟩
      simp [mapHypergraph_comapHypergraph hsep'.left_le,
        mapHypergraph_comapHypergraph hsep'.right_le]
  · rintro _ _ _ _ _ _ ⟨⟨A₁, B₁⟩, h₁, heq₁⟩ ⟨⟨A₂, B₂⟩, h₂, heq₂⟩ ⟨⟨A₃, B₃⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯.isSeparation h₁).left_le
    have hle₂ := (h𝒯.isSeparation h₂).left_le
    have hle₃ := (h𝒯.isSeparation h₃).left_le
    have hleU : A₁ ∪ A₂ ∪ A₃ ≤ G := GM10.union_le (GM10.union_le hle₁ hle₂) hle₃
    have h := congrArg (comapHypergraph fV fE G) hU
    simp only [← mapHypergraph_union] at h
    rw [comapHypergraph_mapHypergraph hleU hinjV hinjE,
      comapHypergraph_mapHypergraph le_rfl hinjV hinjE] at h
    exact h
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩ hVA'
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯.axiom3 hAB
    have hleA := (h𝒯.isSeparation hAB).left_le
    apply Subset.antisymm hleA.vertexSet_subset
    intro v hvG
    have hfv : fV v ∈ (mapHypergraph fV fE A).vertexSet := hVA'.symm ▸ mem_image_of_mem fV hvG
    obtain ⟨w, hwA, hwv⟩ := hfv
    exact hinjV (hleA.vertexSet_subset hwA) hvG hwv ▸ hwA

theorem isTangle_comapHypergraph {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) {θ : ℕ}
    {𝒯' : Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂)}
    (h𝒯' : IsTangle (mapHypergraph fV fE G) θ 𝒯') :
    IsTangle G θ (comapTangle fV fE G 𝒯') := by
  refine ⟨h𝒯'.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_comapHypergraph (h𝒯'.isSeparation hAB')
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep' := h𝒯'.isSeparation hAB'
    rw [separationOrder_comapHypergraph hsep'.left_le hsep'.right_le hinjV]
    exact h𝒯'.order_lt hAB'
  · intro A B hsep hord
    have hsep' := isSeparation_mapHypergraph (fV := fV) hinjE hsep
    have hord' : separationOrder (mapHypergraph fV fE A) (mapHypergraph fV fE B) < θ := by
      rw [separationOrder_mapHypergraph hsep.left_le hsep.right_le hinjV]
      exact hord
    rcases h𝒯'.axiom1 hsep' hord' with hm | hm
    · refine Or.inl ⟨(mapHypergraph fV fE A, mapHypergraph fV fE B), hm, ?_⟩
      simp [comapHypergraph_mapHypergraph hsep.left_le hinjV hinjE,
        comapHypergraph_mapHypergraph hsep.right_le hinjV hinjE]
    · refine Or.inr ⟨(mapHypergraph fV fE B, mapHypergraph fV fE A), hm, ?_⟩
      simp [comapHypergraph_mapHypergraph hsep.left_le hinjV hinjE,
        comapHypergraph_mapHypergraph hsep.right_le hinjV hinjE]
  · rintro _ _ _ _ _ _ ⟨⟨A₁', B₁'⟩, h₁, heq₁⟩ ⟨⟨A₂', B₂'⟩, h₂, heq₂⟩ ⟨⟨A₃', B₃'⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯'.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯'.isSeparation h₁).left_le
    have hle₂ := (h𝒯'.isSeparation h₂).left_le
    have hle₃ := (h𝒯'.isSeparation h₃).left_le
    have h := congrArg (mapHypergraph fV fE) hU
    simp only [mapHypergraph_union, mapHypergraph_comapHypergraph hle₁,
      mapHypergraph_comapHypergraph hle₂, mapHypergraph_comapHypergraph hle₃] at h
    exact h
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩ hVA
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯'.axiom3 hAB'
    have hleA' := (h𝒯'.isSeparation hAB').left_le
    apply Subset.antisymm hleA'.vertexSet_subset
    rintro _ ⟨v, hvG, rfl⟩
    have hv_in : v ∈ (comapHypergraph fV fE G A').vertexSet := hVA.symm ▸ hvG
    exact hv_in.2

end MapHypergraph

/-! ## 2. Specialization of `mapHypergraph` to `mapDrawingInjOn` -/

section MapDrawingLinkage

variable {S Z : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TopologicalSpace Z] [T2Space Z]

omit [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
theorem drawing_injOn_V_and_E (D : Surface.Drawing S) {ι : S → Z} (hinj : InjOn ι D.U) :
    InjOn ι D.toHypergraph.vertexSet ∧ InjOn (image ι) D.toHypergraph.edgeSet := by
  refine ⟨hinj.mono D.V_subset_U, ?_⟩
  intro A₁ hA₁ A₂ hA₂ heq
  have h₁ : A₁ ⊆ D.U := hA₁.2.1.trans sdiff_subset
  have h₂ : A₂ ⊆ D.U := hA₂.2.1.trans sdiff_subset
  ext x
  constructor
  · intro hx₁
    have : ι x ∈ ι '' A₂ := heq ▸ mem_image_of_mem ι hx₁
    obtain ⟨y, hy₂, hyx⟩ := this
    exact hinj (h₂ hy₂) (h₁ hx₁) hyx ▸ hy₂
  · intro hx₂
    have : ι x ∈ ι '' A₁ := heq.symm ▸ mem_image_of_mem ι hx₂
    obtain ⟨y, hy₁, hyx⟩ := this
    exact hinj (h₁ hy₁) (h₂ hx₂) hyx ▸ hy₁

omit [T2Space S] in
theorem isVitalLinkage_mapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U)
    {L : Hypergraph S (Set S)} (hL : IsVitalLinkage D.toHypergraph L) :
    IsVitalLinkage (mapDrawingInjOn D ι hcont hinj).toHypergraph (mapSubH ι L) ∧
      terminals (mapSubH ι L) = ι '' terminals L := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj,
    mapSubH_eq_mapHypergraph, mapSubH_eq_mapHypergraph]
  obtain ⟨hinjV, hinjE⟩ := drawing_injOn_V_and_E D hinj
  exact ⟨(isVitalLinkage_mapHypergraph hL.1.1 hinjV hinjE).mpr hL,
    terminals_mapHypergraph hL.1.1 hinjV hinjE⟩

omit [T2Space S] in
theorem isVitalPLinkage_mapDrawingInjOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U)
    {L : Hypergraph S (Set S)} {p : ℕ} (hL : IsVitalPLinkage D.toHypergraph L p) :
    IsVitalPLinkage (mapDrawingInjOn D ι hcont hinj).toHypergraph (mapSubH ι L) p ∧
      terminals (mapSubH ι L) = ι '' terminals L := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj,
    mapSubH_eq_mapHypergraph, mapSubH_eq_mapHypergraph]
  obtain ⟨hinjV, hinjE⟩ := drawing_injOn_V_and_E D hinj
  exact ⟨(isVitalPLinkage_mapHypergraph hL.1.1.1 hinjV hinjE).mpr hL,
    terminals_mapHypergraph hL.1.1.1 hinjV hinjE⟩

end MapDrawingLinkage

/-! ## 3. Half-plane truncation of the closed unit disc and chart pushforward -/

/-- For a point `w₀ ∈ sphere 0 1` in `ℂ` and a finite subset `F ⊆ sphere 0 1 \ {w₀}`, there is a
real number `r ∈ (0, 1)` such that `z.re * w₀.re + z.im * w₀.im ≤ r` for all `z ∈ F`. -/
private lemma exists_radius_truncating_sphere_points {w₀ : ℂ}
    (hw₀ : w₀ ∈ Metric.sphere (0 : ℂ) 1) {F : Set ℂ} (hF_fin : F.Finite)
    (hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1 \ {w₀}) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ z ∈ F, z.re * w₀.re + z.im * w₀.im ≤ r := by
  have hw₀_sq : w₀.re * w₀.re + w₀.im * w₀.im = 1 := by
    have hnorm : ‖w₀‖ = 1 := by simpa using hw₀
    have hsq := Complex.normSq_eq_norm_sq w₀
    rw [hnorm, one_pow, Complex.normSq_apply] at hsq
    exact hsq
  have hlt_one : ∀ z ∈ F, z.re * w₀.re + z.im * w₀.im < 1 := by
    intro z hzF
    obtain ⟨hz_sph, hz_ne⟩ := hF_sub hzF
    have hz_sq : z.re * z.re + z.im * z.im = 1 := by
      have hnorm : ‖z‖ = 1 := by simpa using hz_sph
      have hsq := Complex.normSq_eq_norm_sq z
      rw [hnorm, one_pow, Complex.normSq_apply] at hsq
      exact hsq
    have hdiff_pos : 0 < (z.re - w₀.re) * (z.re - w₀.re) + (z.im - w₀.im) * (z.im - w₀.im) := by
      have hpos : 0 < ‖z - w₀‖ ^ 2 := sq_pos_of_pos (norm_sub_pos_iff.mpr hz_ne)
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hpos
      simpa using hpos
    linarith
  induction F, hF_fin using Set.Finite.induction_on with
  | empty =>
    exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨r₀, hr₀_pos, hr₀_lt, hr₀_le⟩ := ih (subset_insert a s |>.trans hF_sub)
      (fun z hz ↦ hlt_one z (mem_insert_of_mem a hz))
    have ha_lt : a.re * w₀.re + a.im * w₀.im < 1 := hlt_one a (mem_insert a s)
    let r := max r₀ ((a.re * w₀.re + a.im * w₀.im + 1) / 2)
    refine ⟨r, lt_of_lt_of_le hr₀_pos (le_max_left _ _),
      max_lt hr₀_lt (by linarith), ?_⟩
    rintro z (rfl | hzs)
    · exact le_trans (by linarith) (le_max_right _ _)
    · exact le_trans (hr₀_le z hzs) (le_max_left _ _)

/-- Half-plane truncation of the closed unit disc in `ℂ`: given `w₀ ∈ sphere 0 1` and a finite
subset `F ⊆ sphere 0 1 \ {w₀}`, there exists a closed disc `K ⊆ closedBall 0 1` with
`discInt K ⊆ ball 0 1`, `w₀ ∉ K`, and `F ⊆ discBd K`. -/
theorem exists_truncated_closedUnitDisc {w₀ : ℂ}
    (hw₀ : w₀ ∈ Metric.sphere (0 : ℂ) 1) {F : Set ℂ} (hF_fin : F.Finite)
    (hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1 \ {w₀}) :
    ∃ K : Set ℂ,
      K ⊆ Metric.closedBall (0 : ℂ) 1 ∧
      IsClosedDisc K ∧
      discInt K ⊆ Metric.ball (0 : ℂ) 1 ∧
      w₀ ∉ K ∧
      F ⊆ discBd K := by
  obtain ⟨r, hr_pos, hr_lt, hF_le⟩ := exists_radius_truncating_sphere_points hw₀ hF_fin hF_sub
  let L : ℂ → ℝ := fun z ↦ z.re * w₀.re + z.im * w₀.im
  have hL_cont : Continuous L := by fun_prop
  let H : Set ℂ := {z : ℂ | L z ≤ r}
  let K : Set ℂ := Metric.closedBall (0 : ℂ) 1 ∩ H
  have hH_closed : IsClosed H := isClosed_le hL_cont continuous_const
  have hK_compact : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).inter_right hH_closed
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hH_convex : Convex ℝ H := by
    intro x hx y hy a b ha hb hab
    change L (a • x + b • y) ≤ r
    have hlin : L (a • x + b • y) = a * L x + b * L y := by
      simp [L]
      ring
    rw [hlin]
    have hx' : L x ≤ r := hx
    have hy' : L y ≤ r := hy
    nlinarith
  have hK_convex : Convex ℝ K := (convex_closedBall (0 : ℂ) 1).inter hH_convex
  have hK_int_ne : (interior K).Nonempty := by
    let U : Set ℂ := Metric.ball (0 : ℂ) 1 ∩ {z : ℂ | L z < r}
    have hU_open : IsOpen U := Metric.isOpen_ball.inter (isOpen_lt hL_cont continuous_const)
    have hU_sub : U ⊆ K :=
      inter_subset_inter Metric.ball_subset_closedBall (fun _ hz ↦ show L _ ≤ r from le_of_lt hz)
    have h0_mem : (0 : ℂ) ∈ U := by
      refine ⟨by simp, ?_⟩
      change L 0 < r
      simp [L, hr_pos]
    exact ⟨0, interior_maximal hU_sub hU_open h0_mem⟩
  obtain ⟨hK_disc, hK_bd⟩ :=
    Surface.isClosedDisc_of_convex hK_convex hK_int_ne hK_compact.isBounded hK_closed
  refine ⟨K, inter_subset_left, hK_disc, ?_, ?_, ?_⟩
  · intro z hz
    rw [Surface.discInt, hK_bd, frontier, hK_closed.closure_eq] at hz
    have hz_int : z ∈ interior K := by
      by_contra hz_not_int
      exact hz.2 ⟨hz.1, hz_not_int⟩
    have hz_int_ball : z ∈ interior (Metric.closedBall (0 : ℂ) 1) :=
      interior_mono inter_subset_left hz_int
    rwa [interior_closedBall' (0 : ℂ) 1] at hz_int_ball
  · intro hw₀_K
    have hw₀_le : L w₀ ≤ r := hw₀_K.2
    have hw₀_eq : L w₀ = 1 := by
      have hnorm : ‖w₀‖ = 1 := by simpa using hw₀
      have hsq := Complex.normSq_eq_norm_sq w₀
      rw [hnorm, one_pow, Complex.normSq_apply] at hsq
      exact hsq
    linarith
  · intro z hzF
    rw [hK_bd, frontier, hK_closed.closure_eq]
    obtain ⟨hz_sph, -⟩ := hF_sub hzF
    have hz_norm : ‖z‖ = 1 := by simpa using hz_sph
    have hz_K : z ∈ K := ⟨by simp [hz_norm], hF_le z hzF⟩
    refine ⟨hz_K, fun hz_int ↦ ?_⟩
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := by
      rw [← interior_closedBall' (0 : ℂ) 1]
      exact interior_mono inter_subset_left hz_int
    simp [hz_norm] at hz_ball

/-- Given a closed disc `E` in a Hausdorff space `Z`, a boundary point `v₀ ∈ discBd E`, and a
finite subset `A ⊆ discBd E \ {v₀}`, there is a closed subdisc `D ⊆ E` such that
`discInt D ⊆ discInt E`, `v₀ ∉ D`, and `A ⊆ discBd D`. -/
theorem exists_subdisc_avoiding_bd_point {Z : Type*} [TopologicalSpace Z]
    {E : Set Z} (hE : IsClosedDisc E) {v₀ : Z} (hv₀ : v₀ ∈ discBd E)
    {A : Set Z} (hA_fin : A.Finite) (hA_sub : A ⊆ discBd E \ {v₀}) :
    ∃ D : Set Z,
      D ⊆ E ∧
      IsClosedDisc D ∧
      discInt D ⊆ discInt E ∧
      v₀ ∉ D ∧
      A ⊆ discBd D := by
  obtain ⟨h, g, c⟩ := hE.exists_isChart
  let w₀ : ℂ := h v₀
  have hw₀ : w₀ ∈ Metric.sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hv₀
  let F : Set ℂ := h '' A
  have hF_fin : F.Finite := hA_fin.image h
  have hF_sub : F ⊆ Metric.sphere (0 : ℂ) 1 \ {w₀} := by
    rintro _ ⟨u, huA, rfl⟩
    obtain ⟨hu_bd, hu_ne⟩ := hA_sub huA
    refine ⟨c.bd ▸ mem_image_of_mem h hu_bd, fun h_eq ↦ hu_ne ?_⟩
    have huE : u ∈ E := Surface.discBd_subset E hu_bd
    have hv₀E : v₀ ∈ E := Surface.discBd_subset E hv₀
    calc u = g (h u) := (c.gh huE).symm
      _ = g (h v₀) := congrArg g h_eq
      _ = v₀ := c.gh hv₀E
  obtain ⟨K, hK_sub, hK_disc, hK_int, hw₀_not_K, hF_bd⟩ :=
    exists_truncated_closedUnitDisc hw₀ hF_fin hF_sub
  obtain ⟨hD_disc, hD_bd⟩ := c.disc_g hK_sub hK_disc
  refine ⟨g '' K, c.g_subset hK_sub, hD_disc, ?_, ?_, ?_⟩
  · have hD_int : discInt (g '' K) = g '' discInt K := by
      rw [Surface.discInt, hD_bd, ← c.g_sdiff hK_sub ( (Surface.discBd_subset K).trans hK_sub)]
      rfl
    rw [hD_int]
    rintro _ ⟨z, hz, rfl⟩
    have hz_ball : z ∈ Metric.ball (0 : ℂ) 1 := hK_int hz
    have hz_cb : z ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hz_ball
    have hz_not_sph : z ∉ Metric.sphere (0 : ℂ) 1 := by
      intro hz_sph
      have hnorm : ‖z‖ = 1 := by simpa using hz_sph
      simp [hnorm] at hz_ball
    have hz_sdiff : z ∈ Metric.closedBall (0 : ℂ) 1 \ Metric.sphere (0 : ℂ) 1 :=
      ⟨hz_cb, hz_not_sph⟩
    have h_img := mem_image_of_mem g hz_sdiff
    rw [c.g_sdiff Subset.rfl Metric.sphere_subset_closedBall, c.g_closedBall, c.g_sphere] at h_img
    exact h_img
  · rintro ⟨z, hzK, hgz⟩
    apply hw₀_not_K
    have hv₀_eq : w₀ = z := by
      calc w₀ = h v₀ := rfl
        _ = h (g z) := congrArg h hgz.symm
        _ = z := c.hg (hK_sub hzK)
    exact hv₀_eq ▸ hzK
  · rw [hD_bd]
    intro u huA
    have huE : u ∈ E := Surface.discBd_subset E (hA_sub huA).1
    have hhu_bd : h u ∈ discBd K := hF_bd (mem_image_of_mem h huA)
    exact ⟨h u, hhu_bd, c.gh huE⟩

/-! ## 4. Enlarging a capped surface across a boundary vertex and Claim (12) of `(5.2)` -/

/-- Enlarging a connected surface `S` inside its capped surface `Shat` across a boundary vertex
`v ∈ Γ.V ∩ bd S` of a proper drawing `Γ`:
replacing the cuff disc at `v`'s cuff by the smaller closed disc of `exists_subdisc_avoiding_bd_point`
yields a subsurface `X ⊆ Shat` with `IsSurface ↥X`, `ConnectedSpace ↥X`,
`(cuffs ↥X).ncard = (cuffs S).ncard`, `IsCappedSurface ↥X Shat`, `range cap.emb ⊆ X`, and such that
for `u ∈ Γ.U`, `⟨cap.emb u, ...⟩ ∈ bd ↥X ↔ u ∈ (Γ.V ∩ bd S) \ {v}`. -/
theorem exists_enlarged_surface_avoiding_cuff_vertex
    {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S Shat)
    {Γ : Surface.Drawing S} (hΓ : Γ.IsProper)
    {v : S} (hv : v ∈ Γ.V ∩ bd S) :
    ∃ (X : Set Shat) (_ : IsSurface ↥X) (_ : ConnectedSpace ↥X)
      (_ : GM19.IsCappedSurface ↥X Shat)
      (h_range : range cap.emb ⊆ X),
      (cuffs ↥X).ncard = (cuffs S).ncard ∧
      ∀ u ∈ Γ.U,
        (⟨cap.emb u, h_range (mem_range_self u)⟩ : ↥X) ∈ bd ↥X ↔
          u ∈ (Γ.V ∩ bd S) \ {v} := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hShat : IsSurface Shat := cap.isSurface
  have hcl_Shat : IsClosedSurface Shat := cap.isClosedSurface
  have : ConnectedSpace Shat := cap.connected
  have : T2Space Shat := hShat.2.1
  have hv_bd : v ∈ bd S := hv.2
  rw [← sUnion_cuffs] at hv_bd
  obtain ⟨C, hC, hvC⟩ := hv_bd
  let E : Set Shat := closure (cap.cuffDisc C)
  have hE_disc : IsClosedDisc E := cap.cuffDisc_closedDisc C hC
  have hE_bd : discBd E = cap.emb '' C := cap.cuffDisc_bd C hC
  have hE_int : discInt E = cap.cuffDisc C := (cap.cuffDisc_eq_discInt hS hC).symm
  have hv_hat_bd : cap.emb v ∈ discBd E := hE_bd ▸ mem_image_of_mem cap.emb hvC
  let A : Set Shat := cap.emb '' ((C ∩ Γ.V) \ {v})
  have hA_fin : A.Finite := ((Γ.finite_V.subset inter_subset_right).sdiff).image cap.emb
  have hA_sub : A ⊆ discBd E \ {cap.emb v} := by
    rintro _ ⟨u, ⟨⟨huC, _⟩, huv⟩, rfl⟩
    refine ⟨hE_bd ▸ mem_image_of_mem cap.emb huC, fun h_eq ↦ huv ?_⟩
    exact cap.isEmbedding.injective h_eq
  obtain ⟨D, hD_sub_E, hD_disc, hD_int_sub, hv_not_D, hA_sub_bdD⟩ :=
    exists_subdisc_avoiding_bd_point hE_disc hv_hat_bd hA_fin hA_sub
  classical
  have hcuffs_fin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have : Finite (cuffs S) := hcuffs_fin.to_subtype
  let P : cuffs S → Set Shat := fun i ↦
    if i.1 = C then D else closure (cap.cuffDisc i.1)
  have hP_disc : ∀ i : cuffs S, IsClosedDisc (P i) := by
    intro i
    dsimp only [P]
    split_ifs with hi
    · exact hD_disc
    · exact cap.cuffDisc_closedDisc i.1 i.2
  have hP_sub_closure : ∀ i : cuffs S, P i ⊆ closure (cap.cuffDisc i.1) := by
    intro i
    dsimp only [P]
    split_ifs with hi
    · exact hi ▸ hD_sub_E
    · exact Subset.rfl
  have hP_int_sub : ∀ i : cuffs S, discInt (P i) ⊆ cap.cuffDisc i.1 := by
    intro i
    dsimp only [P]
    split_ifs with hi
    · subst hi
      exact hD_int_sub.trans hE_int.subset
    · exact (cap.cuffDisc_eq_discInt hS i.2).symm.subset
  have hP_disj : Pairwise fun i j : cuffs S ↦ Disjoint (P i) (P j) := by
    intro i j hij
    have hne : i.1 ≠ j.1 := fun h ↦ hij (Subtype.ext h)
    exact (cap.cuffDisc_disjoint i.1 i.2 j.1 j.2 hne).mono
      (hP_sub_closure i) (hP_sub_closure j)
  obtain ⟨_, hX_surf, hX_bd, hX_conn, hX_cuffs⟩ :=
    Surface.remove_discs hShat hcl_Shat.2.2 hP_disc hP_disj
  obtain ⟨capX⟩ := GM19.nonempty_capped_of_removal hcl_Shat hP_disc hP_disj
  let X : Set Shat := (⋃ i : cuffs S, discInt (P i))ᶜ
  have hbW : ∀ i : cuffs S, ∀ x ∈ discBd (P i), x ∈ X := fun i x hx hu ↦ by
    obtain ⟨j, hj⟩ := mem_iUnion.mp hu
    by_cases hij : i = j
    · subst hij
      exact hj.2 hx
    · exact Set.disjoint_left.mp (hP_disj hij) (Surface.discBd_subset _ hx) hj.1
  have hinj_cuff : Function.Injective
      (fun i : cuffs S ↦ (Subtype.val ⁻¹' discBd (P i) : Set ↥X)) := by
    intro i j he
    by_contra hij
    obtain ⟨y, hy⟩ := (IsOArc.isConnected' (hP_disc i).isOArc_discBd).nonempty
    have h1 : (⟨y, hbW i y hy⟩ : ↥X) ∈ (Subtype.val ⁻¹' discBd (P j) : Set ↥X) := by
      dsimp only at he
      have hmem : (⟨y, hbW i y hy⟩ : ↥X) ∈ (Subtype.val ⁻¹' discBd (P i) : Set ↥X) := hy
      rwa [he] at hmem
    exact Set.disjoint_left.mp (hP_disj hij)
      (Surface.discBd_subset _ hy) (Surface.discBd_subset _ h1)
  have hcuffs_eq : (cuffs ↥X).ncard = (cuffs S).ncard := by
    rw [hX_cuffs, ← image_univ, Set.ncard_image_of_injective univ hinj_cuff,
      ncard_univ, Nat.card_coe_set_eq]
  have h_range : range cap.emb ⊆ X := by
    rintro _ ⟨s, rfl⟩
    change cap.emb s ∉ ⋃ i : cuffs S, discInt (P i)
    rw [mem_iUnion]
    rintro ⟨i, hs_int⟩
    have hs_disc : cap.emb s ∈ cap.cuffDisc i.1 := hP_int_sub i hs_int
    have hs_compl : cap.emb s ∈ (range cap.emb)ᶜ := by
      rw [cap.compl_eq]
      exact mem_iUnion₂.mpr ⟨i.1, i.2, hs_disc⟩
    exact hs_compl (mem_range_self s)
  refine ⟨X, hX_surf, hX_conn, capX, h_range, hcuffs_eq, ?_⟩
  intro u huU
  rw [hX_bd, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨i, hu_bdPi⟩
    have hu_Pi : cap.emb u ∈ P i := Surface.discBd_subset (P i) hu_bdPi
    have hu_cl : cap.emb u ∈ closure (cap.cuffDisc i.1) := hP_sub_closure i hu_Pi
    rw [cap.closure_cuffDisc hS i.2] at hu_cl
    have hu_i : u ∈ i.1 := by
      rcases hu_cl with hu_open | ⟨w, hw, hwu⟩
      · exfalso
        have : cap.emb u ∈ (range cap.emb)ᶜ := by
          rw [cap.compl_eq]
          exact mem_iUnion₂.mpr ⟨i.1, i.2, hu_open⟩
        exact this (mem_range_self u)
      · exact cap.isEmbedding.injective hwu ▸ hw
    have hi_bd : i.1 ⊆ bd S := by
      rcases i.2 with ⟨x, _, hxi⟩
      rw [← hxi]
      exact connectedComponentIn_subset (bd S) x
    have hu_bdS : u ∈ bd S := hi_bd hu_i
    have hu_V : u ∈ Γ.V := hΓ ⟨hu_bdS, huU⟩
    refine ⟨⟨hu_V, hu_bdS⟩, ?_⟩
    rintro rfl
    by_cases hiC : i.1 = C
    · have hPi_eq : P i = D := by simp [P, hiC]
      exact hv_not_D (hPi_eq ▸ hu_Pi)
    · have hdisj_C := cap.cuffDisc_disjoint i.1 i.2 C hC hiC
      exact disjoint_left.mp hdisj_C (hP_sub_closure i hu_Pi)
        (Surface.discBd_subset E hv_hat_bd)
  · rintro ⟨⟨hu_V, hu_bdS⟩, huv⟩
    rw [← sUnion_cuffs] at hu_bdS
    obtain ⟨C', hC', hu_C'⟩ := hu_bdS
    refine ⟨⟨C', hC'⟩, ?_⟩
    dsimp only [P]
    split_ifs with hC'_eq
    · subst hC'_eq
      exact hA_sub_bdD ⟨u, ⟨⟨hu_C', hu_V⟩, huv⟩, rfl⟩
    · rw [cap.cuffDisc_bd C' hC']
      exact mem_image_of_mem cap.emb hu_C'

/-- Two connected surfaces with homeomorphic cappings and the same number of cuffs are
homeomorphic. -/
private theorem homeo_of_same_cap_and_cuffs_ncard_eq
    {S Shat S' : Type}
    [TopologicalSpace S] [TopologicalSpace Shat] [TopologicalSpace S']
    (hS : IsSurface S) [ConnectedSpace S]
    (hS' : IsSurface S') [ConnectedSpace S']
    (cap : GM19.IsCappedSurface S Shat) (cap' : GM19.IsCappedSurface S' Shat)
    (hcuffs : (cuffs S').ncard = (cuffs S).ncard) :
    Nonempty (S' ≃ₜ S) := by
  obtain ⟨a, b, c, ⟨eS⟩⟩ := classification S hS inferInstance
  obtain ⟨a', b', c', ⟨eS'⟩⟩ := classification S' hS' inferInstance
  obtain ⟨e_SM⟩ := GM19.capModel a b c Shat (GM19.IsCappedSurface.ofHomeo eS.symm cap)
  obtain ⟨e_S'M⟩ := GM19.capModel a' b' c' Shat (GM19.IsCappedSurface.ofHomeo eS'.symm cap')
  have hM0 : Nonempty (SurfaceModel a' b' 0 ≃ₜ SurfaceModel a b 0) :=
    ⟨e_S'M.symm.trans e_SM⟩
  obtain ⟨-, hab, hb0⟩ := (modelCriterion.2 a' b' 0 a b 0).mp hM0
  have hcS : (cuffs S).ncard = c := by
    have h := GM19.numCuffs_eq eS
    rw [numCuffs_model] at h
    exact h
  have hcS' : (cuffs S').ncard = c' := by
    have h := GM19.numCuffs_eq eS'
    rw [numCuffs_model] at h
    exact h
  have hcc' : c' = c := by omega
  obtain ⟨e_M⟩ := (modelCriterion.2 a' b' c' a b c).mpr ⟨hcc', hab, hb0⟩
  exact ⟨eS'.trans (e_M.trans eS.symm)⟩

/-- **Graph Minors XXI, (5.2), Claim (12)** (page 21 of the preprint):
"(12) *Every vertex in* $V(\Gamma) \cap bd(\Sigma)$ *is a terminal of* $L$."

Proved by enlarging `S` across `v` via `exists_enlarged_surface_avoiding_cuff_vertex`, transporting
`Γ`, `𝒯`, and `L` into `S` along the resulting homeomorphism `e : ↥X ≃ₜ S`, and applying inductive
hypothesis (3). -/
theorem claim_5_2_12
    {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]
    (hS : IsSurface S) [ConnectedSpace S]
    (cap : GM19.IsCappedSurface S Shat)
    {Γ : Surface.Drawing S} (hΓ : Γ.IsProper)
    {p θ θ₃ : ℕ} (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (hθ₃_pos : 1 ≤ θ₃) (hθ_ge : θ₃ ≤ θ)
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    {L : Hypergraph S (Set S)}
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    -- Inductive hypothesis (3):
    (h_ind3 : ∀ (Γ' : Surface.Drawing S),
      Γ'.IsProper →
      (Γ'.V ∩ bd S).ncard < p →
      ∀ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (L' : Hypergraph S (Set S)),
        IsTangle Γ'.toHypergraph θ₃ T' →
        IsVitalLinkage Γ'.toHypergraph L' →
        ¬ (terminals L' ⊆ bd S)) :
    Γ.V ∩ bd S ⊆ terminals L := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  intro v hv
  by_contra hv_not_term
  obtain ⟨X, hX_surf, hX_conn, capX, h_range, hcuffs_eq, hbd_iff⟩ :=
    exists_enlarged_surface_avoiding_cuff_vertex hS cap hΓ hv
  obtain ⟨e⟩ := homeo_of_same_cap_and_cuffs_ncard_eq hS hX_surf cap capX hcuffs_eq
  let ι : S → ↥X := fun s ↦ ⟨cap.emb s, h_range (mem_range_self s)⟩
  let φ : S → S := e ∘ ι
  have hcont_ι : Continuous ι := cap.isEmbedding.continuous.subtype_mk _
  have hinj_ι : Function.Injective ι :=
    fun x y h ↦ cap.isEmbedding.injective (congrArg Subtype.val h)
  have hcont_φ : Continuous φ := e.continuous.comp hcont_ι
  have hinj_φ : Function.Injective φ := e.injective.comp hinj_ι
  let Γ' : Surface.Drawing S := mapDrawingInjOn Γ φ hcont_φ.continuousOn hinj_φ.injOn
  have he_bd : ∀ y : ↥X, e y ∈ bd S ↔ y ∈ bd ↥X := by
    intro y
    change ¬ IsInteriorPoint (e y) ↔ ¬ IsInteriorPoint y
    rw [isInteriorPoint_homeomorph_iff e y]
  have hφ_bd_iff : ∀ u ∈ Γ.U, φ u ∈ bd S ↔ u ∈ (Γ.V ∩ bd S) \ {v} := by
    intro u huU
    change e (ι u) ∈ bd S ↔ u ∈ (Γ.V ∩ bd S) \ {v}
    rw [he_bd, hbd_iff u huU]
  have hΓ'_prop : Γ'.IsProper := by
    rintro z ⟨hz_bd, ⟨u, huU, rfl⟩⟩
    have hu_mem : u ∈ (Γ.V ∩ bd S) \ {v} := (hφ_bd_iff u huU).mp hz_bd
    exact mem_image_of_mem φ hu_mem.1.1
  have hΓ'_bd_eq : Γ'.V ∩ bd S = φ '' ((Γ.V ∩ bd S) \ {v}) := by
    ext z
    change (z ∈ φ '' Γ.V ∧ z ∈ bd S) ↔ z ∈ φ '' ((Γ.V ∩ bd S) \ {v})
    simp only [mem_image]
    constructor
    · rintro ⟨⟨u, huV, rfl⟩, hφu_bd⟩
      exact ⟨u, (hφ_bd_iff u (Γ.V_subset_U huV)).mp hφu_bd, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu.1.1, rfl⟩, (hφ_bd_iff u (Γ.V_subset_U hu.1.1)).mpr hu⟩
  have hΓ'_bd_lt : (Γ'.V ∩ bd S).ncard < p := by
    rw [hΓ'_bd_eq, hinj_φ.injOn.ncard_image]
    have hfin : (Γ.V ∩ bd S).Finite := Γ.finite_V.subset inter_subset_left
    have hlt : ((Γ.V ∩ bd S) \ {v}).ncard < (Γ.V ∩ bd S).ncard :=
      ncard_lt_ncard (sdiff_singleton_ssubset.mpr hv) hfin
    omega
  have h𝒯_θ₃ : IsTangle Γ.toHypergraph θ₃ (truncation 𝒯 θ₃) :=
    h𝒯.truncation hθ₃_pos hθ_ge
  have h𝒯' : IsTangle Γ'.toHypergraph θ₃ (mapTangleInjOn φ (truncation 𝒯 θ₃)) :=
    isTangle_mapDrawingInjOn Γ φ hcont_φ.continuousOn hinj_φ.injOn h𝒯_θ₃
  obtain ⟨hL'_vital, hL'_term⟩ :=
    isVitalLinkage_mapDrawingInjOn Γ φ hcont_φ.continuousOn hinj_φ.injOn hL
  have hL'_bd : terminals (mapSubH φ L) ⊆ bd S := by
    rw [hL'_term]
    rintro _ ⟨u, hu_term, rfl⟩
    have huV : u ∈ Γ.V := hL.1.1.vertexSet_subset hu_term.1
    have hu_bd : u ∈ bd S := hL_bd hu_term
    have huv : u ≠ v := fun h ↦ hv_not_term (h ▸ hu_term)
    exact (hφ_bd_iff u (Γ.V_subset_U huV)).mpr ⟨⟨huV, hu_bd⟩, huv⟩
  exact h_ind3 Γ' hΓ'_prop hΓ'_bd_lt (mapTangleInjOn φ (truncation 𝒯 θ₃)) (mapSubH φ L)
    h𝒯' hL'_vital hL'_bd

end GM21
end GraphMinor
