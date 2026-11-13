module

public import GraphMinor.GM21.Section4Tangle

/-!
# Transporting linkages and tangles along injective hypergraph maps

A hypergraph `G : Hypergraph α₁ β₁` and maps `fV : α₁ → α₂`, `fE : β₁ → β₂` that are injective on
`V(G)` and `E(G)` give an isomorphic copy `isoImage fV fE G`. This file proves that the copy has
the same paths, components, linkages, terminals, patterns, vital linkages, separations and
tangles, read through the maps. Every subhypergraph `A'` of the copy is the image of the
subhypergraph `isoPreimage fV fE G A'` of `G`, so a statement about all subhypergraphs (such as
"no other linkage has the same pattern") transfers as well.

The last section specializes this to the image `mapDrawingInjOn D ι` of a drawing under a map that
is injective on `U(D)`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12

section MapHypergraph

variable {α₁ : Type*} {β₁ : Type*} {α₂ : Type*} {β₂ : Type*}

/-- Forward image of a hypergraph `A : Hypergraph α₁ β₁` under vertex and edge maps
`fV : α₁ → α₂` and `fE : β₁ → β₂`. -/
def isoImage (fV : α₁ → α₂) (fE : β₁ → β₂)
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
def isoPreimage (fV : α₁ → α₂) (fE : β₁ → β₂)
    (G : Hypergraph α₁ β₁) (A' : Hypergraph α₂ β₂) : Hypergraph α₁ β₁ where
  vertexSet := {v ∈ G.vertexSet | fV v ∈ A'.vertexSet}
  edgeSet := {e ∈ G.edgeSet | fE e ∈ A'.edgeSet}
  Inc e v := G.Inc e v ∧ fE e ∈ A'.edgeSet ∧ fV v ∈ A'.vertexSet
  vertex_mem_of_inc _ _ h := ⟨G.vertex_mem_of_inc h.1, h.2.2⟩
  edge_mem_of_inc _ _ h := ⟨G.edge_mem_of_inc h.1, h.2.1⟩
  vertexSet_finite := G.vertexSet_finite.subset fun _ h ↦ h.1
  edgeSet_finite := G.edgeSet_finite.subset fun _ h ↦ h.1

theorem mapSubH_eq_isoImage {S Z : Type} (ι : S → Z) (A : Hypergraph S (Set S)) :
    mapSubH ι A = isoImage ι (image ι) A := rfl

theorem comapSubH_eq_isoPreimage {S Z : Type} (ι : S → Z)
    (G : Hypergraph S (Set S)) (A' : Hypergraph Z (Set Z)) :
    comapSubH ι G A' = isoPreimage ι (image ι) G A' := rfl

theorem isoPreimage_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    isoPreimage fV fE G (isoImage fV fE A) = A := by
  apply Hypergraph.ext
  · ext v
    simp only [isoPreimage, isoImage, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun hvA ↦ ⟨hA.vertexSet_subset hvA, v, hvA, rfl⟩⟩
    rintro ⟨hvG, w, hwA, hwv⟩
    exact hinjV (hA.vertexSet_subset hwA) hvG hwv ▸ hwA
  · ext e
    simp only [isoPreimage, isoImage, mem_ofPred_eq, mem_image]
    refine ⟨?_, fun heA ↦ ⟨hA.edgeSet_subset heA, e, heA, rfl⟩⟩
    rintro ⟨heG, f, hfA, hfe⟩
    exact hinjE (hA.edgeSet_subset hfA) heG hfe ▸ hfA
  · funext e v
    apply propext
    simp only [isoPreimage, isoImage, mem_image]
    constructor
    · rintro ⟨hincG, ⟨f, hfA, hfe⟩, _⟩
      have he_eq : f = e := hinjE (hA.edgeSet_subset hfA) (G.edge_mem_of_inc hincG) hfe
      subst he_eq
      exact (GM10.inc_iff_of_le hA hfA).mpr hincG
    · intro hincA
      have heA := A.edge_mem_of_inc hincA
      have hvA := A.vertex_mem_of_inc hincA
      exact ⟨GM10.inc_of_le hA hincA, ⟨e, heA, rfl⟩, ⟨v, hvA, rfl⟩⟩

theorem isoImage_isoPreimage {G : Hypergraph α₁ β₁} {A' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ isoImage fV fE G) :
    isoImage fV fE (isoPreimage fV fE G A') = A' := by
  apply Hypergraph.ext
  · ext v'
    simp only [isoImage, isoPreimage, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨v, ⟨_, hv'⟩, rfl⟩
      exact hv'
    · intro hv'
      obtain ⟨v, hvG, rfl⟩ := hA'.vertexSet_subset hv'
      exact ⟨v, ⟨hvG, hv'⟩, rfl⟩
  · ext e'
    simp only [isoImage, isoPreimage, mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨e, ⟨_, he'⟩, rfl⟩
      exact he'
    · intro he'
      obtain ⟨e, heG, rfl⟩ := hA'.edgeSet_subset he'
      exact ⟨e, ⟨heG, he'⟩, rfl⟩
  · funext e' v'
    apply propext
    simp only [isoImage, isoPreimage]
    constructor
    · rintro ⟨e₀, v₀, ⟨hincG, he₀', _⟩, rfl, rfl⟩
      have hinc_map : (isoImage fV fE G).Inc (fE e₀) (fV v₀) := ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact (GM10.inc_iff_of_le hA' he₀').mpr hinc_map
    · intro hincA'
      have he' := A'.edge_mem_of_inc hincA'
      have hv' := A'.vertex_mem_of_inc hincA'
      have hinc_map : (isoImage fV fE G).Inc e' v' := GM10.inc_of_le hA' hincA'
      rcases hinc_map with ⟨e₀, v₀, hincG, rfl, rfl⟩
      exact ⟨e₀, v₀, ⟨hincG, he', hv'⟩, rfl, rfl⟩

theorem isoImage_le {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hB : B ≤ G) (hinjE : InjOn fE G.edgeSet)
    (hle : A ≤ B) : isoImage fV fE A ≤ isoImage fV fE B where
  vertexSet_subset := image_mono hle.vertexSet_subset
  edgeSet_subset := image_mono hle.edgeSet_subset
  ends_eq e' he' := by
    obtain ⟨f, hfA, rfl⟩ := he'
    ext v'
    simp only [Hypergraph.ends, isoImage, mem_ofPred_eq]
    constructor
    · rintro ⟨e₀, v₀, hincB, he₀, rfl⟩
      have he₀_eq : e₀ = f :=
        hinjE (hB.edgeSet_subset (B.edge_mem_of_inc hincB)) (hA.edgeSet_subset hfA) he₀
      subst he₀_eq
      exact ⟨e₀, v₀, (GM10.inc_iff_of_le hle hfA).mpr hincB, rfl, rfl⟩
    · rintro ⟨e₀, v₀, hincA, he₀, rfl⟩
      exact ⟨e₀, v₀, GM10.inc_of_le hle hincA, he₀, rfl⟩

theorem isoPreimage_le_self {G : Hypergraph α₁ β₁} {A' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ isoImage fV fE G) : isoPreimage fV fE G A' ≤ G where
  vertexSet_subset _ h := h.1
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, isoPreimage, mem_ofPred_eq]
    refine ⟨fun hincG ↦ ⟨hincG, he.2, ?_⟩, fun h ↦ h.1⟩
    have hinc_map : (isoImage fV fE G).Inc (fE e) (fV v) := ⟨e, v, hincG, rfl, rfl⟩
    exact A'.vertex_mem_of_inc ((GM10.inc_iff_of_le hA' he.2).mpr hinc_map)

theorem isoPreimage_le {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ isoImage fV fE G) (hB' : B' ≤ isoImage fV fE G)
    (hle : A' ≤ B') :
    isoPreimage fV fE G A' ≤ isoPreimage fV fE G B' := by
  rw [GM10.le_iff_of_le (isoPreimage_le_self hA') (isoPreimage_le_self hB')]
  exact ⟨fun _ h ↦ ⟨h.1, hle.vertexSet_subset h.2⟩,
    fun _ h ↦ ⟨h.1, hle.edgeSet_subset h.2⟩⟩

theorem ends_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjE : InjOn fE G.edgeSet) {e : β₁} (he : e ∈ A.edgeSet) :
    (isoImage fV fE A).ends (fE e) = fV '' (A.ends e) := by
  ext v'
  simp only [Hypergraph.ends, isoImage, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨e₀, v₀, hinc, he₀, rfl⟩
    have he₀_eq : e₀ = e :=
      hinjE (hA.edgeSet_subset (A.edge_mem_of_inc hinc)) (hA.edgeSet_subset he) he₀
    subst he₀_eq
    exact ⟨v₀, hinc, rfl⟩
  · rintro ⟨v₀, hinc, rfl⟩
    exact ⟨e, v₀, hinc, rfl, rfl⟩

theorem ends_isoImage_ncard {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {e : β₁} (he : e ∈ A.edgeSet) :
    ((isoImage fV fE A).ends (fE e)).ncard = (A.ends e).ncard := by
  rw [ends_isoImage hA hinjE he]
  refine (hinjV.mono ?_).ncard_image
  intro v hv
  exact hA.vertexSet_subset (A.vertex_mem_of_inc hv)

theorem isGraph_isoImage_iff {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    (isoImage fV fE A).IsGraph ↔ A.IsGraph := by
  constructor
  · intro hG' e he
    have he' : fE e ∈ (isoImage fV fE A).edgeSet := mem_image_of_mem fE he
    obtain ⟨hne', hle2'⟩ := hG' (fE e) he'
    rw [ends_isoImage_ncard hA hinjV hinjE he] at hle2'
    rw [ends_isoImage hA hinjE he] at hne'
    exact ⟨hne'.of_image, hle2'⟩
  · intro hG e' he'
    obtain ⟨e, he, rfl⟩ := he'
    obtain ⟨hne, hle2⟩ := hG e he
    rw [ends_isoImage_ncard hA hinjV hinjE he]
    rw [ends_isoImage hA hinjE he]
    exact ⟨hne.image fV, hle2⟩

theorem incidentEdges_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) {v : α₁} (hv : v ∈ A.vertexSet) :
    incidentEdges (isoImage fV fE A) (fV v) = fE '' (incidentEdges A v) := by
  ext e'
  simp only [incidentEdges, isoImage, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨_, e₀, v₀, hinc, rfl, hv₀⟩
    have hv₀_eq : v₀ = v :=
      hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hinc)) (hA.vertexSet_subset hv) hv₀
    subst hv₀_eq
    exact ⟨e₀, ⟨A.edge_mem_of_inc hinc, hinc⟩, rfl⟩
  · rintro ⟨e₀, ⟨he₀, hinc⟩, rfl⟩
    exact ⟨⟨e₀, he₀, rfl⟩, e₀, v, hinc, rfl, rfl⟩

theorem incidentEdges_isoImage_ncard {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {v : α₁} (hv : v ∈ A.vertexSet) :
    (incidentEdges (isoImage fV fE A) (fV v)).ncard = (incidentEdges A v).ncard := by
  rw [incidentEdges_isoImage hA hinjV hv]
  exact (hinjE.mono (fun _ h ↦ hA.edgeSet_subset h.1)).ncard_image

theorem vertexDegree_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {v : α₁} (hv : v ∈ A.vertexSet) :
    vertexDegree (isoImage fV fE A) (fV v) = vertexDegree A v := by
  unfold vertexDegree
  rw [incidentEdges_isoImage_ncard hA hinjV hinjE hv]
  congr 1
  have hloop_eq :
      {e' ∈ incidentEdges (isoImage fV fE A) (fV v) |
        ((isoImage fV fE A).ends e').Subsingleton} =
      fE '' {e ∈ incidentEdges A v | (A.ends e).Subsingleton} := by
    rw [incidentEdges_isoImage hA hinjV hv]
    ext e'
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨⟨e, he, rfl⟩, hsub'⟩
      refine ⟨e, ⟨he, ?_⟩, rfl⟩
      rw [ends_isoImage hA hinjE he.1] at hsub'
      intro x hx y hy
      exact hinjV (hA.vertexSet_subset (A.vertex_mem_of_inc hx))
        (hA.vertexSet_subset (A.vertex_mem_of_inc hy))
        (hsub' (mem_image_of_mem fV hx) (mem_image_of_mem fV hy))
    · rintro ⟨e, ⟨he, hsub⟩, rfl⟩
      refine ⟨⟨e, he, rfl⟩, ?_⟩
      rw [ends_isoImage hA hinjE he.1]
      exact hsub.image fV
  rw [hloop_eq]
  exact (hinjE.mono (fun _ h ↦ hA.edgeSet_subset h.1.1)).ncard_image

theorem skeleton_adj_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x y : α₁} (hx : x ∈ A.vertexSet) (hy : y ∈ A.vertexSet) :
    (isoImage fV fE A).skeleton.Adj (fV x) (fV y) ↔ A.skeleton.Adj x y := by
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

private theorem skeleton_reachable_of_isoImage {G A : Hypergraph α₁ β₁}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x' y' : α₂} (W' : (isoImage fV fE A).skeleton.Walk x' y')
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
    have hadj' : (isoImage fV fE A).skeleton.Adj (fV x) (fV z₀) :=
      ⟨hne', fE e₀, hinc_u', ⟨e₀, z₀, hinc_z₀, rfl, rfl⟩⟩
    have hadj : A.skeleton.Adj x z₀ :=
      (skeleton_adj_isoImage hA hinjV hinjE hx hz₀).mp hadj'
    exact hadj.reachable.trans (ih hz₀ hy rfl hfy)

theorem skeleton_reachable_isoImage {G A : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet)
    {x y : α₁} (hx : x ∈ A.vertexSet) (hy : y ∈ A.vertexSet) :
    (isoImage fV fE A).skeleton.Reachable (fV x) (fV y) ↔ A.skeleton.Reachable x y := by
  constructor
  · rintro ⟨W'⟩
    exact skeleton_reachable_of_isoImage hA hinjV hinjE W' hx hy rfl rfl
  · rintro ⟨W⟩
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v w hadj W₁ ih =>
      have hv : v ∈ A.vertexSet := by
        rcases hadj with ⟨_, e, _, hv_inc⟩
        exact A.vertex_mem_of_inc hv_inc
      have hadj' : (isoImage fV fE A).skeleton.Adj (fV u) (fV v) :=
        (skeleton_adj_isoImage hA hinjV hinjE hx hv).mpr hadj
      exact hadj'.reachable.trans (ih hv hy)

theorem isComponentOf_isoImage {G A C : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hC : C ≤ A) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsComponentOf (isoImage fV fE A) (isoImage fV fE C) ↔ IsComponentOf A C := by
  have hCG : C ≤ G := hC.trans hA
  constructor
  · rintro ⟨_, hne', hconn', hmax'⟩
    refine ⟨hC, hne'.of_image, ?_, ?_⟩
    · intro x hx y hy
      exact (skeleton_reachable_isoImage hCG hinjV hinjE hx hy).mp
        (hconn' (fV x) (mem_image_of_mem fV hx) (fV y) (mem_image_of_mem fV hy))
    · intro C₁ hC₁A hC₁_ne hC₁_conn hCC₁
      have hC₁G : C₁ ≤ G := hC₁A.trans hA
      have hmap_eq : isoImage fV fE C₁ = isoImage fV fE C := by
        refine hmax' (isoImage fV fE C₁) (isoImage_le hC₁G hA hinjE hC₁A)
          (hC₁_ne.image fV) ?_ (isoImage_le hCG hC₁G hinjE hCC₁)
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact (skeleton_reachable_isoImage hC₁G hinjV hinjE hx hy).mpr (hC₁_conn x hx y hy)
      have h := congrArg (isoPreimage fV fE G) hmap_eq
      rwa [isoPreimage_isoImage hC₁G hinjV hinjE,
        isoPreimage_isoImage hCG hinjV hinjE] at h
  · rintro ⟨_, hne, hconn, hmax⟩
    refine ⟨isoImage_le hCG hA hinjE hC, hne.image fV, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (skeleton_reachable_isoImage hCG hinjV hinjE hx hy).mpr (hconn x hx y hy)
    · intro C' hC'A' hC'_ne hC'_conn hCC'
      have hC'G' : C' ≤ isoImage fV fE G :=
        hC'A'.trans (isoImage_le hA le_rfl hinjE hA)
      let C₁ := isoPreimage fV fE G C'
      have hC₁G : C₁ ≤ G := isoPreimage_le_self hC'G'
      have hmapC₁ : isoImage fV fE C₁ = C' := isoImage_isoPreimage hC'G'
      have hC₁A : C₁ ≤ A := by
        rw [← isoPreimage_isoImage hA hinjV hinjE]
        exact isoPreimage_le hC'G' (isoImage_le hA le_rfl hinjE hA) hC'A'
      have hCC₁ : C ≤ C₁ := by
        rw [← isoPreimage_isoImage hCG hinjV hinjE]
        exact isoPreimage_le (isoImage_le hCG le_rfl hinjE hCG) hC'G' hCC'
      have hC₁_ne : C₁.vertexSet.Nonempty := by
        rw [← hmapC₁] at hC'_ne
        exact hC'_ne.of_image
      have hC₁_conn : ∀ x ∈ C₁.vertexSet, ∀ y ∈ C₁.vertexSet, C₁.skeleton.Reachable x y := by
        intro x hx y hy
        rw [← skeleton_reachable_isoImage hC₁G hinjV hinjE hx hy, hmapC₁]
        exact hC'_conn (fV x) (hmapC₁ ▸ mem_image_of_mem fV hx)
          (fV y) (hmapC₁ ▸ mem_image_of_mem fV hy)
      have hC₁_eq : C₁ = C := hmax C₁ hC₁A hC₁_ne hC₁_conn hCC₁
      rw [← hmapC₁, hC₁_eq]

theorem isPathGraph_isoImage {G P : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hP : P ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsPathGraph (isoImage fV fE P) ↔ IsPathGraph P := by
  constructor
  · rintro ⟨hG', hne', hconn', hends2', hpar', hdeg2', hacyc'⟩
    refine ⟨(isGraph_isoImage_iff hP hinjV hinjE).mp hG', hne'.of_image, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx y hy
      exact (skeleton_reachable_isoImage hP hinjV hinjE hx hy).mp
        (hconn' (fV x) (mem_image_of_mem fV hx) (fV y) (mem_image_of_mem fV hy))
    · intro e he
      have h := hends2' (fE e) (mem_image_of_mem fE he)
      rwa [ends_isoImage_ncard hP hinjV hinjE he] at h
    · intro e₁ he₁ e₂ he₂ hends_eq
      have h_eq' : fE e₁ = fE e₂ := by
        refine hpar' (fE e₁) (mem_image_of_mem fE he₁) (fE e₂) (mem_image_of_mem fE he₂) ?_
        rw [ends_isoImage hP hinjE he₁, ends_isoImage hP hinjE he₂, hends_eq]
      exact hinjE (hP.edgeSet_subset he₁) (hP.edgeSet_subset he₂) h_eq'
    · intro x hx
      have h := hdeg2' (fV x) (mem_image_of_mem fV hx)
      rwa [incidentEdges_isoImage_ncard hP hinjV hinjE hx] at h
    · intro H hHP hH_ne
      have hHG : H ≤ G := hHP.trans hP
      obtain ⟨_, ⟨x, hxH, rfl⟩, hdeg1⟩ :=
        hacyc' (isoImage fV fE H) (isoImage_le hHG hP hinjE hHP) (hH_ne.image fE)
      rw [incidentEdges_isoImage_ncard hHG hinjV hinjE hxH] at hdeg1
      exact ⟨x, hxH, hdeg1⟩
  · rintro ⟨hG, hne, hconn, hends2, hpar, hdeg2, hacyc⟩
    refine ⟨(isGraph_isoImage_iff hP hinjV hinjE).mpr hG, hne.image fV, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (skeleton_reachable_isoImage hP hinjV hinjE hx hy).mpr (hconn x hx y hy)
    · rintro _ ⟨e, he, rfl⟩
      rw [ends_isoImage_ncard hP hinjV hinjE he]
      exact hends2 e he
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ hends_eq'
      rw [ends_isoImage hP hinjE he₁, ends_isoImage hP hinjE he₂] at hends_eq'
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
      rw [incidentEdges_isoImage_ncard hP hinjV hinjE hx]
      exact hdeg2 x hx
    · intro H' hH'P' hH'_ne
      have hH'G' : H' ≤ isoImage fV fE G :=
        hH'P'.trans (isoImage_le hP le_rfl hinjE hP)
      let H := isoPreimage fV fE G H'
      have hHG : H ≤ G := isoPreimage_le_self hH'G'
      have hmapH : isoImage fV fE H = H' := isoImage_isoPreimage hH'G'
      have hHP : H ≤ P := by
        rw [← isoPreimage_isoImage hP hinjV hinjE]
        exact isoPreimage_le hH'G' (isoImage_le hP le_rfl hinjE hP) hH'P'
      have hH_ne : H.edgeSet.Nonempty := by
        rw [← hmapH] at hH'_ne
        exact hH'_ne.of_image
      obtain ⟨x, hxH, hdeg1⟩ := hacyc H hHP hH_ne
      refine ⟨fV x, hmapH ▸ mem_image_of_mem fV hxH, ?_⟩
      rw [← hmapH, incidentEdges_isoImage_ncard hHG hinjV hinjE hxH]
      exact hdeg1

theorem isLinkage_isoImage {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsLinkage (isoImage fV fE G) (isoImage fV fE L) ↔ IsLinkage G L := by
  constructor
  · rintro ⟨_, hG', hcomp'⟩
    refine ⟨hL, (isGraph_isoImage_iff hL hinjV hinjE).mp hG', ?_⟩
    intro C hC
    have hCG : C ≤ G := hC.1.trans hL
    have hC' : IsComponentOf (isoImage fV fE L) (isoImage fV fE C) :=
      (isComponentOf_isoImage hL hC.1 hinjV hinjE).mpr hC
    exact (isPathGraph_isoImage hCG hinjV hinjE).mp (hcomp' _ hC')
  · rintro ⟨_, hG, hcomp⟩
    refine ⟨isoImage_le hL le_rfl hinjE hL,
      (isGraph_isoImage_iff hL hinjV hinjE).mpr hG, ?_⟩
    intro C' hC'
    have hC'G' : C' ≤ isoImage fV fE G :=
      hC'.1.trans (isoImage_le hL le_rfl hinjE hL)
    let C := isoPreimage fV fE G C'
    have hCG : C ≤ G := isoPreimage_le_self hC'G'
    have hmapC : isoImage fV fE C = C' := isoImage_isoPreimage hC'G'
    have hCL : C ≤ L := by
      rw [← isoPreimage_isoImage hL hinjV hinjE]
      exact isoPreimage_le hC'G' (isoImage_le hL le_rfl hinjE hL) hC'.1
    have hC : IsComponentOf L C := by
      rw [← isComponentOf_isoImage hL hCL hinjV hinjE, hmapC]
      exact hC'
    rw [← hmapC]
    exact (isPathGraph_isoImage hCG hinjV hinjE).mpr (hcomp C hC)

theorem terminals_isoImage {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    terminals (isoImage fV fE L) = fV '' terminals L := by
  ext v'
  simp only [terminals, IsTerminal, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨⟨v, hvL, rfl⟩, hdeg'⟩
    rw [vertexDegree_isoImage hL hinjV hinjE hvL] at hdeg'
    exact ⟨v, ⟨hvL, hdeg'⟩, rfl⟩
  · rintro ⟨v, ⟨hvL, hdeg⟩, rfl⟩
    refine ⟨mem_image_of_mem fV hvL, ?_⟩
    rw [vertexDegree_isoImage hL hinjV hinjE hvL]
    exact hdeg

theorem linkagePattern_isoImage {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    linkagePattern (isoImage fV fE L) = (image fV) '' linkagePattern L := by
  ext B'
  simp only [linkagePattern, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨C', hC', rfl⟩
    have hC'G' : C' ≤ isoImage fV fE G :=
      hC'.1.trans (isoImage_le hL le_rfl hinjE hL)
    let C := isoPreimage fV fE G C'
    have hmapC : isoImage fV fE C = C' := isoImage_isoPreimage hC'G'
    have hCL : C ≤ L := by
      rw [← isoPreimage_isoImage hL hinjV hinjE]
      exact isoPreimage_le hC'G' (isoImage_le hL le_rfl hinjE hL) hC'.1
    have hC : IsComponentOf L C := by
      rw [← isComponentOf_isoImage hL hCL hinjV hinjE, hmapC]
      exact hC'
    refine ⟨terminals L ∩ C.vertexSet, ⟨C, hC, rfl⟩, ?_⟩
    rw [← hmapC, terminals_isoImage hL hinjV hinjE]
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
    refine ⟨isoImage fV fE C,
      (isComponentOf_isoImage hL hC.1 hinjV hinjE).mpr hC, ?_⟩
    rw [terminals_isoImage hL hinjV hinjE]
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

theorem isVitalLinkage_isoImage {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsVitalLinkage (isoImage fV fE G) (isoImage fV fE L) ↔ IsVitalLinkage G L := by
  constructor
  · rintro ⟨hlink', hV', huniq'⟩
    refine ⟨(isLinkage_isoImage hL hinjV hinjE).mp hlink', ?_, ?_⟩
    · apply Subset.antisymm hL.vertexSet_subset
      intro v hvG
      have : fV v ∈ (isoImage fV fE L).vertexSet := hV'.symm ▸ mem_image_of_mem fV hvG
      obtain ⟨w, hwL, hwv⟩ := this
      exact hinjV (hL.vertexSet_subset hwL) hvG hwv ▸ hwL
    · intro L₁ hL₁ hpat₁
      have hmap_link : IsLinkage (isoImage fV fE G) (isoImage fV fE L₁) :=
        (isLinkage_isoImage hL₁.1 hinjV hinjE).mpr hL₁
      have hmap_pat : linkagePattern (isoImage fV fE L₁) =
          linkagePattern (isoImage fV fE L) := by
        rw [linkagePattern_isoImage hL₁.1 hinjV hinjE,
          linkagePattern_isoImage hL hinjV hinjE, hpat₁]
      have hmap_eq := huniq' (isoImage fV fE L₁) hmap_link hmap_pat
      have h := congrArg (isoPreimage fV fE G) hmap_eq
      rwa [isoPreimage_isoImage hL₁.1 hinjV hinjE,
        isoPreimage_isoImage hL hinjV hinjE] at h
  · rintro ⟨hlink, hV, huniq⟩
    refine ⟨(isLinkage_isoImage hL hinjV hinjE).mpr hlink,
      congrArg (image fV) hV, ?_⟩
    intro L' hL' hpat'
    let L₁ := isoPreimage fV fE G L'
    have hL₁G : L₁ ≤ G := isoPreimage_le_self hL'.1
    have hmapL₁ : isoImage fV fE L₁ = L' := isoImage_isoPreimage hL'.1
    have hL₁_link : IsLinkage G L₁ := by
      rw [← isLinkage_isoImage hL₁G hinjV hinjE, hmapL₁]
      exact hL'
    have hpat₁ : linkagePattern L₁ = linkagePattern L := by
      rw [← hmapL₁, linkagePattern_isoImage hL₁G hinjV hinjE,
        linkagePattern_isoImage hL hinjV hinjE] at hpat'
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

theorem isVitalPLinkage_isoImage {G L : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    {p : ℕ} (hL : L ≤ G) (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    IsVitalPLinkage (isoImage fV fE G) (isoImage fV fE L) p ↔ IsVitalPLinkage G L p := by
  unfold IsVitalPLinkage IsPLinkage
  rw [isVitalLinkage_isoImage hL hinjV hinjE,
    isLinkage_isoImage hL hinjV hinjE,
    terminals_isoImage hL hinjV hinjE,
    (hinjV.mono (fun _ h ↦ hL.vertexSet_subset h.1)).ncard_image]

theorem hasVitalPLinkage_isoImage {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    {p : ℕ} (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) :
    HasVitalPLinkage (isoImage fV fE G) p ↔ HasVitalPLinkage G p := by
  constructor
  · rintro ⟨L', hL'⟩
    let L := isoPreimage fV fE G L'
    have hLG : L ≤ G := isoPreimage_le_self hL'.1.1.1
    have hmapL : isoImage fV fE L = L' := isoImage_isoPreimage hL'.1.1.1
    rw [← hmapL, isVitalPLinkage_isoImage hLG hinjV hinjE] at hL'
    exact ⟨L, hL'⟩
  · rintro ⟨L, hL⟩
    exact ⟨isoImage fV fE L, (isVitalPLinkage_isoImage hL.1.1.1 hinjV hinjE).mpr hL⟩

theorem isoImage_union {A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂} :
    isoImage fV fE (A ∪ B) = isoImage fV fE A ∪ isoImage fV fE B := by
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

theorem isSeparation_isoImage {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjE : InjOn fE G.edgeSet) (hsep : G.IsSeparation A B) :
    (isoImage fV fE G).IsSeparation (isoImage fV fE A) (isoImage fV fE B) := by
  have hleA := isoImage_le (fV := fV) hsep.left_le le_rfl hinjE hsep.left_le
  have hleB := isoImage_le (fV := fV) hsep.right_le le_rfl hinjE hsep.right_le
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

theorem isSeparation_isoPreimage {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hsep : (isoImage fV fE G).IsSeparation A' B') :
    G.IsSeparation (isoPreimage fV fE G A') (isoPreimage fV fE G B') := by
  have hleA := isoPreimage_le_self hsep.left_le
  have hleB := isoPreimage_le_self hsep.right_le
  rw [GM10.isSeparation_iff_of_le hleA hleB]
  refine ⟨?_, ?_, ?_⟩
  · ext v
    simp only [isoPreimage, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hvG
      have hfv : fV v ∈ A'.vertexSet ∪ B'.vertexSet :=
        hsep.vertexSet_union.symm ▸ mem_image_of_mem fV hvG
      exact hfv.imp (fun h ↦ ⟨hvG, h⟩) (fun h ↦ ⟨hvG, h⟩)
  · ext e
    simp only [isoPreimage, mem_union, mem_ofPred_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro heG
      have hfe : fE e ∈ A'.edgeSet ∪ B'.edgeSet :=
        hsep.edgeSet_union.symm ▸ mem_image_of_mem fE heG
      exact hfe.imp (fun h ↦ ⟨heG, h⟩) (fun h ↦ ⟨heG, h⟩)
  · ext e
    simp only [isoPreimage, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
    rintro ⟨⟨_, heA'⟩, ⟨_, heB'⟩⟩
    exact hsep.notMem_edgeSet_right heA' heB'

theorem separationOrder_isoImage {G A B : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA : A ≤ G) (hB : B ≤ G) (hinjV : InjOn fV G.vertexSet) :
    separationOrder (isoImage fV fE A) (isoImage fV fE B) = separationOrder A B := by
  unfold separationOrder
  have h_eq : ((isoImage fV fE A) ∩ (isoImage fV fE B)).vertexSet =
      fV '' (A ∩ B).vertexSet := by
    ext v'
    simp only [GM10.inter_vertexSet, isoImage, mem_inter_iff, mem_image]
    constructor
    · rintro ⟨⟨v₁, hv₁, rfl⟩, ⟨v₂, hv₂, hv₂₁⟩⟩
      have hv_eq : v₂ = v₁ := hinjV (hB.vertexSet_subset hv₂) (hA.vertexSet_subset hv₁) hv₂₁
      exact ⟨v₁, ⟨hv₁, hv_eq ▸ hv₂⟩, rfl⟩
    · rintro ⟨v, ⟨hvA, hvB⟩, rfl⟩
      exact ⟨⟨v, hvA, rfl⟩, ⟨v, hvB, rfl⟩⟩
  rw [h_eq]
  exact (hinjV.mono ((GM10.inter_le hA hB).vertexSet_subset)).ncard_image

theorem separationOrder_isoPreimage {G : Hypergraph α₁ β₁} {A' B' : Hypergraph α₂ β₂}
    {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hA' : A' ≤ isoImage fV fE G) (hB' : B' ≤ isoImage fV fE G)
    (hinjV : InjOn fV G.vertexSet) :
    separationOrder (isoPreimage fV fE G A') (isoPreimage fV fE G B') =
      separationOrder A' B' := by
  rw [← separationOrder_isoImage (fE := fE)
      (isoPreimage_le_self hA') (isoPreimage_le_self hB') hinjV,
    isoImage_isoPreimage hA', isoImage_isoPreimage hB']

/-- Transport a tangle `𝒯` on `G` forward along `fV` and `fE`. -/
def isoImageTangle (fV : α₁ → α₂) (fE : β₁ → β₂)
    (𝒯 : Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁)) :
    Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂) :=
  (fun p ↦ (isoImage fV fE p.1, isoImage fV fE p.2)) '' 𝒯

/-- Pull back a tangle `𝒯'` on `isoImage fV fE G` to `G`. -/
def isoPreimageTangle (fV : α₁ → α₂) (fE : β₁ → β₂) (G : Hypergraph α₁ β₁)
    (𝒯' : Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂)) :
    Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁) :=
  (fun p ↦ (isoPreimage fV fE G p.1, isoPreimage fV fE G p.2)) '' 𝒯'

theorem isTangle_isoImage {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) {θ : ℕ}
    {𝒯 : Set (Hypergraph α₁ β₁ × Hypergraph α₁ β₁)}
    (h𝒯 : IsTangle G θ 𝒯) :
    IsTangle (isoImage fV fE G) θ (isoImageTangle fV fE 𝒯) := by
  refine ⟨h𝒯.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_isoImage hinjE (h𝒯.isSeparation hAB)
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep := h𝒯.isSeparation hAB
    rw [separationOrder_isoImage hsep.left_le hsep.right_le hinjV]
    exact h𝒯.order_lt hAB
  · intro A' B' hsep' hord'
    have hsep := isSeparation_isoPreimage hsep'
    have hord : separationOrder (isoPreimage fV fE G A') (isoPreimage fV fE G B') < θ := by
      rw [separationOrder_isoPreimage hsep'.left_le hsep'.right_le hinjV]
      exact hord'
    rcases h𝒯.axiom1 hsep hord with hm | hm
    · refine Or.inl ⟨(isoPreimage fV fE G A', isoPreimage fV fE G B'), hm, ?_⟩
      simp [isoImage_isoPreimage hsep'.left_le,
        isoImage_isoPreimage hsep'.right_le]
    · refine Or.inr ⟨(isoPreimage fV fE G B', isoPreimage fV fE G A'), hm, ?_⟩
      simp [isoImage_isoPreimage hsep'.left_le,
        isoImage_isoPreimage hsep'.right_le]
  · rintro _ _ _ _ _ _ ⟨⟨A₁, B₁⟩, h₁, heq₁⟩ ⟨⟨A₂, B₂⟩, h₂, heq₂⟩ ⟨⟨A₃, B₃⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯.isSeparation h₁).left_le
    have hle₂ := (h𝒯.isSeparation h₂).left_le
    have hle₃ := (h𝒯.isSeparation h₃).left_le
    have hleU : A₁ ∪ A₂ ∪ A₃ ≤ G := GM10.union_le (GM10.union_le hle₁ hle₂) hle₃
    have h := congrArg (isoPreimage fV fE G) hU
    simp only [← isoImage_union] at h
    rw [isoPreimage_isoImage hleU hinjV hinjE,
      isoPreimage_isoImage le_rfl hinjV hinjE] at h
    exact h
  · rintro _ _ ⟨⟨A, B⟩, hAB, heq⟩ hVA'
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯.axiom3 hAB
    have hleA := (h𝒯.isSeparation hAB).left_le
    apply Subset.antisymm hleA.vertexSet_subset
    intro v hvG
    have hfv : fV v ∈ (isoImage fV fE A).vertexSet := hVA'.symm ▸ mem_image_of_mem fV hvG
    obtain ⟨w, hwA, hwv⟩ := hfv
    exact hinjV (hleA.vertexSet_subset hwA) hvG hwv ▸ hwA

theorem isTangle_isoPreimage {G : Hypergraph α₁ β₁} {fV : α₁ → α₂} {fE : β₁ → β₂}
    (hinjV : InjOn fV G.vertexSet) (hinjE : InjOn fE G.edgeSet) {θ : ℕ}
    {𝒯' : Set (Hypergraph α₂ β₂ × Hypergraph α₂ β₂)}
    (h𝒯' : IsTangle (isoImage fV fE G) θ 𝒯') :
    IsTangle G θ (isoPreimageTangle fV fE G 𝒯') := by
  refine ⟨h𝒯'.one_le, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    exact isSeparation_isoPreimage (h𝒯'.isSeparation hAB')
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp heq
    have hsep' := h𝒯'.isSeparation hAB'
    rw [separationOrder_isoPreimage hsep'.left_le hsep'.right_le hinjV]
    exact h𝒯'.order_lt hAB'
  · intro A B hsep hord
    have hsep' := isSeparation_isoImage (fV := fV) hinjE hsep
    have hord' : separationOrder (isoImage fV fE A) (isoImage fV fE B) < θ := by
      rw [separationOrder_isoImage hsep.left_le hsep.right_le hinjV]
      exact hord
    rcases h𝒯'.axiom1 hsep' hord' with hm | hm
    · refine Or.inl ⟨(isoImage fV fE A, isoImage fV fE B), hm, ?_⟩
      simp [isoPreimage_isoImage hsep.left_le hinjV hinjE,
        isoPreimage_isoImage hsep.right_le hinjV hinjE]
    · refine Or.inr ⟨(isoImage fV fE B, isoImage fV fE A), hm, ?_⟩
      simp [isoPreimage_isoImage hsep.left_le hinjV hinjE,
        isoPreimage_isoImage hsep.right_le hinjV hinjE]
  · rintro _ _ _ _ _ _ ⟨⟨A₁', B₁'⟩, h₁, heq₁⟩ ⟨⟨A₂', B₂'⟩, h₂, heq₂⟩ ⟨⟨A₃', B₃'⟩, h₃, heq₃⟩ hU
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₁
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₂
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq₃
    apply h𝒯'.axiom2 h₁ h₂ h₃
    have hle₁ := (h𝒯'.isSeparation h₁).left_le
    have hle₂ := (h𝒯'.isSeparation h₂).left_le
    have hle₃ := (h𝒯'.isSeparation h₃).left_le
    have h := congrArg (isoImage fV fE) hU
    simp only [isoImage_union, isoImage_isoPreimage hle₁,
      isoImage_isoPreimage hle₂, isoImage_isoPreimage hle₃] at h
    exact h
  · rintro _ _ ⟨⟨A', B'⟩, hAB', heq⟩ hVA
    obtain ⟨rfl, -⟩ := Prod.ext_iff.mp heq
    apply h𝒯'.axiom3 hAB'
    have hleA' := (h𝒯'.isSeparation hAB').left_le
    apply Subset.antisymm hleA'.vertexSet_subset
    rintro _ ⟨v, hvG, rfl⟩
    have hv_in : v ∈ (isoPreimage fV fE G A').vertexSet := hVA.symm ▸ hvG
    exact hv_in.2

end MapHypergraph

/-! ## 2. Specialization of `isoImage` to `mapDrawingInjOn` -/

section MapDrawingLinkage

variable {S Z : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TopologicalSpace Z] [T2Space Z]

omit [CompactSpace S] [T2Space S] [TopologicalSpace Z] [T2Space Z] in
theorem drawing_injOn_V_and_E_of_injOn (D : Surface.Drawing S) {ι : S → Z} (hinj : InjOn ι D.U) :
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
theorem isVitalLinkage_mapDrawingInjOn_of_injOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U)
    {L : Hypergraph S (Set S)} (hL : IsVitalLinkage D.toHypergraph L) :
    IsVitalLinkage (mapDrawingInjOn D ι hcont hinj).toHypergraph (mapSubH ι L) ∧
      terminals (mapSubH ι L) = ι '' terminals L := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj,
    mapSubH_eq_isoImage, mapSubH_eq_isoImage]
  obtain ⟨hinjV, hinjE⟩ := drawing_injOn_V_and_E_of_injOn D hinj
  exact ⟨(isVitalLinkage_isoImage hL.1.1 hinjV hinjE).mpr hL,
    terminals_isoImage hL.1.1 hinjV hinjE⟩

omit [T2Space S] in
theorem isVitalPLinkage_mapDrawingInjOn_of_injOn (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U)
    {L : Hypergraph S (Set S)} {p : ℕ} (hL : IsVitalPLinkage D.toHypergraph L p) :
    IsVitalPLinkage (mapDrawingInjOn D ι hcont hinj).toHypergraph (mapSubH ι L) p ∧
      terminals (mapSubH ι L) = ι '' terminals L := by
  rw [toHypergraph_mapDrawingInjOn D ι hcont hinj,
    mapSubH_eq_isoImage, mapSubH_eq_isoImage]
  obtain ⟨hinjV, hinjE⟩ := drawing_injOn_V_and_E_of_injOn D hinj
  exact ⟨(isVitalPLinkage_isoImage hL.1.1.1 hinjV hinjE).mpr hL,
    terminals_isoImage hL.1.1.1 hinjV hinjE⟩

end MapDrawingLinkage

end GM21
end GraphMinor
