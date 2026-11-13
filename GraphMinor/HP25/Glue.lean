module

public import GraphMinor.HP25.GlueTools
public import GraphMinor.HP25.Rib
import GraphMinor.HP25.EdgeFaces
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.Schoenflies
import GraphMinor.Surface.SurfaceGraph

/-!
# Gluing two rib embeddings along a path

This is the drawing step of Proposition 3.1 of Humeau and Pous (arXiv:2505.16431v2, page 8):
"Consider plane embeddings of $R_G$ and $R_H$ for which the outer faces are sent onto two polygons
whose intersection is precisely $P$ and $P'$. As $P$ and $P'$ are induced, there are no parallel
edges in the union of the plane embeddings of $R_G$ and $R_H$. Hence, this union is a plane
embedding of $R$."

Instead of polygons we use the two halves of the closed unit disc cut by the diameter from `-1` to
`1`. Let `φ₁`, `φ₂` be rib embeddings of `G` on `R₁` and `R₂` with frames `C₁` and `C₂`, and let `l`
be an induced path with `R₁ ∩ R₂ = l`. We assume homeomorphisms `ψ₁` and `ψ₂` of the closed inner
domains of the frame images onto the two half discs, which send the image of `l` onto the diameter
and agree on the points and lines of `l` (`Glue`). Then we draw a vertex of `R₁` by `ψ₁` and the
other vertices by `ψ₂`, and the same for the edges (`Glue.emb`). The faces of this drawing are the
outside of the unit disc and the images of the inner faces of `φ₁` and `φ₂`
(`Glue.faces_cases`), so it has the faces of a rib (`Glue.isRibEmbedding`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface Metric

local notation "𝕀" => unitInterval

variable {V : Type*} {G : SimpleGraph V}

/-! ### One side -/

namespace PlaneEmbedding

variable {R : Set V} (φ : PlaneEmbedding G R) {C : List V}

/-- In an embedding with the faces of a rib, the drawing lies in the closed inner domain of the
image of the frame. -/
theorem U_subset_closedInner (h : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) : φ.U ⊆ closedInner (φ.cycleImage C) := by
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  intro z hz
  by_cases hzF : z ∈ φ.cycleImage C
  · exact Or.inr hzF
  · have : z ∈ (φ.cycleImage C)ᶜ := hzF
    rw [← J.union_eq] at this
    rcases this with h1 | h1
    · exact Or.inl h1
    · exact absurd h1 (Set.disjoint_left.mp (h.disjoint_outer hC hR) hz)

/-- In an embedding with the faces of a rib, a bounded face lies in the inner domain of the image of
the frame. -/
theorem subset_inner_of_bounded (h : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {r : Set ℂ} (hr : r ∈ φ.faces) (hb : Bornology.IsBounded r) :
    r ⊆ inner (φ.cycleImage C) := by
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
  have hFU := φ.cycleImage_subset_U hC hR
  have hrF : Disjoint r (φ.cycleImage C) :=
    Set.disjoint_left.mpr fun z hz hzF => hrU hz (hFU hzF)
  obtain ⟨z, hz⟩ := hrc.nonempty
  have hz' : z ∈ (φ.cycleImage C)ᶜ := fun h' => Set.disjoint_left.mp hrF hz h'
  rw [← J.union_eq] at hz'
  rcases hz' with hzi | hzo
  · exact J.subset_inner hrc.isPreconnected hrF ⟨z, hz, hzi⟩
  · have hout : outer (φ.cycleImage C) ⊆ φ.Uᶜ := fun w hw hwU =>
      Set.disjoint_left.mp (h.disjoint_outer hC hR) hwU hw
    have := φ.subset_face hr J.isConnected_outer.isPreconnected hout hzo hz
    exact absurd (hb.subset this) J.not_isBounded_outer

/-- In an embedding with the faces of a rib, every undrawn point of the closed inner domain of the
frame image lies in a bounded face. -/
theorem exists_bounded_face (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {z : ℂ} (hz : z ∈ closedInner (φ.cycleImage C)) (hzU : z ∉ φ.U) :
    ∃ r ∈ φ.faces, Bornology.IsBounded r ∧ z ∈ r := by
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  obtain ⟨hf, hzf⟩ := φ.mem_faces_of_notMem hzU
  refine ⟨_, hf, ?_, hzf⟩
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hf
  have hFU := φ.cycleImage_subset_U hC hR
  have hzi : z ∈ inner (φ.cycleImage C) :=
    hz.resolve_right fun h' => hzU (hFU h')
  refine J.isBounded_inner.subset (J.subset_inner hrc.isPreconnected ?_ ⟨z, hzf, hzi⟩)
  exact Set.disjoint_left.mpr fun w hw hwF => hrU hw (hFU hwF)

/-- **Moving a bounded face.** Let `ψ` be a homeomorphism of the closed inner domain of the frame
image onto the closed inner domain of an `O`-arc `F'`, sending the frame image onto `F'`. Then `ψ`
sends a bounded face to an open connected subset of the inner domain of `F'`, with frontier the
image of the frontier of the face, and missing the image of the drawing. -/
theorem image_face (h : φ.IsRibEmbedding C) (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    {F' : Set ℂ} (J' : IsJordanParts F') {ψ χ : ℂ → ℂ}
    (m : BdMatch (closedInner (φ.cycleImage C)) (closedInner F') ψ χ)
    (hbd : ψ '' φ.cycleImage C = F') {r : Set ℂ} (hr : r ∈ φ.faces) (hb : Bornology.IsBounded r) :
    IsOpen (ψ '' r) ∧ IsConnected (ψ '' r) ∧ ψ '' r ⊆ inner F' ∧
      frontier (ψ '' r) = ψ '' frontier r ∧ Disjoint (ψ '' r) (ψ '' φ.U) := by
  set F := φ.cycleImage C
  have J := isJordanParts (φ.isOArc_cycleImage hC hR).some
  obtain ⟨hro, hrc, hrU⟩ := φ.isOpen_of_mem_faces hr
  have hri := φ.subset_inner_of_bounded h hC hR hr hb
  have hFD : F ⊆ closedInner F := subset_union_right
  have hiD : inner F ⊆ closedInner F := subset_union_left
  have hinj : InjOn ψ (closedInner F) := m.2.2.1.injOn
  have hcont : ContinuousOn ψ (closedInner F) := m.2.2.2.2.1
  -- the image of the inner domain
  have himg : ψ '' inner F = inner F' := by
    have h1 : inner F = closedInner F \ F := by
      ext z
      constructor
      · intro hz
        exact ⟨Or.inl hz, hz.1⟩
      · rintro ⟨hz | hz, hn⟩
        · exact hz
        · exact absurd hz hn
    rw [h1, hinj.image_sdiff_subset hFD, m.image_eq, hbd]
    ext z
    constructor
    · rintro ⟨hz | hz, hn⟩
      · exact hz
      · exact absurd hz hn
    · intro hz
      exact ⟨Or.inl hz, hz.1⟩
  have hrin : ψ '' r ⊆ inner F' := himg ▸ image_mono hri
  -- openness, through the inverse map
  have hopen : IsOpen (ψ '' r) := by
    have he : ψ '' r = inner F' ∩ χ ⁻¹' r := by
      ext w
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨hrin ⟨z, hz, rfl⟩, by rw [mem_preimage, m.2.2.1 (hiD (hri hz))]; exact hz⟩
      · rintro ⟨hw, hwr⟩
        exact ⟨χ w, hwr, m.2.2.2.1 (subset_union_left hw)⟩
    rw [he]
    exact (m.2.2.2.2.2.mono subset_union_left).isOpen_inter_preimage J'.isOpen_inner hro
  -- the closure of the image is the image of the closure
  have hcl : closure r ⊆ closedInner F := by
    refine (closure_mono hri).trans ?_
    rw [J.closure_inner]
    rfl
  have hcomp : IsCompact (closure r) :=
    J.isCompact_closure_inner.of_isClosed_subset isClosed_closure hcl
  have hclim : closure (ψ '' r) = ψ '' closure r := by
    refine Subset.antisymm ?_ ((hcont.mono hcl).image_closure)
    exact closure_minimal (image_mono subset_closure)
      ((hcomp.image_of_continuousOn (hcont.mono hcl)).isClosed)
  refine ⟨hopen, hrc.image ψ (hcont.mono (hri.trans hiD)), hrin, ?_, ?_⟩
  · rw [hopen.frontier_eq, hro.frontier_eq, hclim,
      (hinj.mono hcl).image_sdiff_subset subset_closure]
  · exact Disjoint.image (Set.disjoint_left.mpr fun z hz hzU => hrU hz hzU) hinj
      (hri.trans hiD) (φ.U_subset_closedInner h hC hR)

end PlaneEmbedding

/-! ### The glued drawing -/

variable {R₁ R₂ : Set V}

/-- The situation of the gluing: two rib embeddings `φ₁`, `φ₂` with frames `C₁`, `C₂`, an induced
path `l` with `R₁ ∩ R₂ = l` along which they are glued, the cut of the unit circle by the diameter
`e` into the arcs `a₁` and `a₂`, and homeomorphisms `ψ₁`, `ψ₂` (with inverses `χ₁`, `χ₂`) of the
closed inner domains of the frame images onto the two closed half discs. They send the frame
images onto the boundaries of the half discs and the image of `l` onto the diameter, and they agree
on the points and on the lines of `l`. -/
structure Glue (φ₁ : PlaneEmbedding G R₁) (φ₂ : PlaneEmbedding G R₂) (C₁ C₂ l : List V)
    (a₁ a₂ e : 𝕀 → ℂ) (ψ₁ χ₁ ψ₂ χ₂ : ℂ → ℂ) : Prop where
  rib₁ : φ₁.IsRibEmbedding C₁
  rib₂ : φ₂.IsRibEmbedding C₂
  cyc₁ : IsCycleList G C₁
  cyc₂ : IsCycleList G C₂
  sub₁ : ∀ x ∈ C₁, x ∈ R₁
  sub₂ : ∀ x ∈ C₂, x ∈ R₂
  inter : R₁ ∩ R₂ = {v | v ∈ l}
  path₁ : IsPathList G R₁ l
  path₂ : IsPathList G R₂ l
  ind : ∀ u ∈ l, ∀ v ∈ l, G.Adj u v → IsListEdge l u v
  edge : ∀ u ∈ R₁ ∪ R₂, ∀ v ∈ R₁ ∪ R₂, G.Adj u v → (u ∈ R₁ ∧ v ∈ R₁) ∨ (u ∈ R₂ ∧ v ∈ R₂)
  cut : IsCut (sphere (0 : ℂ) 1) a₁ a₂ e
  m₁ : BdMatch (closedInner (φ₁.cycleImage C₁)) (closedInner (side a₁ e)) ψ₁ χ₁
  m₂ : BdMatch (closedInner (φ₂.cycleImage C₂)) (closedInner (side a₂ e)) ψ₂ χ₂
  bd₁ : ψ₁ '' φ₁.cycleImage C₁ = side a₁ e
  bd₂ : ψ₂ '' φ₂.cycleImage C₂ = side a₂ e
  pe₁ : ψ₁ '' φ₁.pathImage l = range e
  pe₂ : ψ₂ '' φ₂.pathImage l = range e
  agree_pt : ∀ x ∈ l, ψ₁ (φ₁.pt x) = ψ₂ (φ₂.pt x)
  agree_line : ∀ u v, IsListEdge l u v → ψ₁ '' φ₁.line u v = ψ₂ '' φ₂.line u v

/-- The point of a vertex in the glued drawing. -/
noncomputable def gluePt (φ₁ : PlaneEmbedding G R₁) (φ₂ : PlaneEmbedding G R₂) (ψ₁ ψ₂ : ℂ → ℂ)
    (v : V) : ℂ :=
  open Classical in if v ∈ R₁ then ψ₁ (φ₁.pt v) else ψ₂ (φ₂.pt v)

/-- The line of a pair of vertices in the glued drawing. -/
noncomputable def glueLine (φ₁ : PlaneEmbedding G R₁) (φ₂ : PlaneEmbedding G R₂) (ψ₁ ψ₂ : ℂ → ℂ)
    (u v : V) : Set ℂ :=
  open Classical in if u ∈ R₁ ∧ v ∈ R₁ then ψ₁ '' φ₁.line u v else ψ₂ '' φ₂.line u v

namespace Glue

variable {φ₁ : PlaneEmbedding G R₁} {φ₂ : PlaneEmbedding G R₂} {C₁ C₂ l : List V}
  {a₁ a₂ e : 𝕀 → ℂ} {ψ₁ χ₁ ψ₂ χ₂ : ℂ → ℂ}
  (g : Glue φ₁ φ₂ C₁ C₂ l a₁ a₂ e ψ₁ χ₁ ψ₂ χ₂)

include g

theorem jordan₁ : IsJordanParts (side a₁ e) := isJordanParts g.cut.oArc_side.some

theorem jordan₂ : IsJordanParts (side a₂ e) := isJordanParts g.cut.symm.oArc_side.some

omit g in
theorem jordan_sphere : IsJordanParts (sphere (0 : ℂ) 1) := isJordanParts oArc_sphere.some

theorem half_union :
    closedInner (side a₁ e) ∪ closedInner (side a₂ e) = closedInner (sphere (0 : ℂ) 1) :=
  (g.cut.closedInner_facts jordan_sphere).1

theorem half_inter : closedInner (side a₁ e) ∩ closedInner (side a₂ e) ⊆ range e :=
  (g.cut.closedInner_facts jordan_sphere).2.2.2.1

theorem isBounded_half₁ : Bornology.IsBounded (closedInner (side a₁ e)) :=
  g.jordan₁.isBounded_inner.union g.jordan₁.isCompact.isBounded

theorem isBounded_half₂ : Bornology.IsBounded (closedInner (side a₂ e)) :=
  g.jordan₂.isBounded_inner.union g.jordan₂.isCompact.isBounded

theorem U₁_sub : φ₁.U ⊆ closedInner (φ₁.cycleImage C₁) :=
  φ₁.U_subset_closedInner g.rib₁ g.cyc₁ g.sub₁

theorem U₂_sub : φ₂.U ⊆ closedInner (φ₂.cycleImage C₂) :=
  φ₂.U_subset_closedInner g.rib₂ g.cyc₂ g.sub₂

theorem inj₁ : InjOn ψ₁ (closedInner (φ₁.cycleImage C₁)) := g.m₁.2.2.1.injOn

theorem inj₂ : InjOn ψ₂ (closedInner (φ₂.cycleImage C₂)) := g.m₂.2.2.1.injOn

theorem pt₁_mem {v : V} (hv : v ∈ R₁) : φ₁.pt v ∈ closedInner (φ₁.cycleImage C₁) :=
  g.U₁_sub (φ₁.pt_mem_U hv)

theorem pt₂_mem {v : V} (hv : v ∈ R₂) : φ₂.pt v ∈ closedInner (φ₂.cycleImage C₂) :=
  g.U₂_sub (φ₂.pt_mem_U hv)

theorem line₁_sub {u v : V} (hu : u ∈ R₁) (hv : v ∈ R₁) (huv : G.Adj u v) :
    φ₁.line u v ⊆ closedInner (φ₁.cycleImage C₁) :=
  (φ₁.line_subset_U hu hv huv).trans g.U₁_sub

theorem line₂_sub {u v : V} (hu : u ∈ R₂) (hv : v ∈ R₂) (huv : G.Adj u v) :
    φ₂.line u v ⊆ closedInner (φ₂.cycleImage C₂) :=
  (φ₂.line_subset_U hu hv huv).trans g.U₂_sub

theorem mem_l₁ {v : V} (hv : v ∈ R₁) (h : ψ₁ (φ₁.pt v) ∈ closedInner (side a₂ e)) : v ∈ l := by
  have hz : ψ₁ (φ₁.pt v) ∈ range e := g.half_inter ⟨g.m₁.1 (g.pt₁_mem hv), h⟩
  rw [← g.pe₁] at hz
  obtain ⟨y, hy, he⟩ := hz
  have hsub := (φ₁.pathImage_subset_U g.path₁).trans g.U₁_sub
  rw [g.inj₁ (hsub hy) (g.pt₁_mem hv) he] at hy
  exact φ₁.mem_of_pt_mem_pathImage g.path₁ hv hy

theorem mem_l₂ {v : V} (hv : v ∈ R₂) (h : ψ₂ (φ₂.pt v) ∈ closedInner (side a₁ e)) : v ∈ l := by
  have hz : ψ₂ (φ₂.pt v) ∈ range e := g.half_inter ⟨h, g.m₂.1 (g.pt₂_mem hv)⟩
  rw [← g.pe₂] at hz
  obtain ⟨y, hy, he⟩ := hz
  have hsub := (φ₂.pathImage_subset_U g.path₂).trans g.U₂_sub
  rw [g.inj₂ (hsub hy) (g.pt₂_mem hv) he] at hy
  exact φ₂.mem_of_pt_mem_pathImage g.path₂ hv hy

theorem l_R₁ {v : V} (hv : v ∈ l) : v ∈ R₁ := by
  have : v ∈ R₁ ∩ R₂ := g.inter ▸ hv
  exact this.1

theorem l_R₂ {v : V} (hv : v ∈ l) : v ∈ R₂ := by
  have : v ∈ R₁ ∩ R₂ := g.inter ▸ hv
  exact this.2

theorem mem_l {v : V} (h₁ : v ∈ R₁) (h₂ : v ∈ R₂) : v ∈ l := by
  have : v ∈ R₁ ∩ R₂ := ⟨h₁, h₂⟩
  rwa [g.inter] at this

omit g in
theorem pt_eq₁ {v : V} (hv : v ∈ R₁) : gluePt φ₁ φ₂ ψ₁ ψ₂ v = ψ₁ (φ₁.pt v) := by
  simp [gluePt, hv]

theorem pt_eq₂ {v : V} (hv : v ∈ R₂) : gluePt φ₁ φ₂ ψ₁ ψ₂ v = ψ₂ (φ₂.pt v) := by
  by_cases h : v ∈ R₁
  · rw [pt_eq₁ h]
    exact g.agree_pt v (g.mem_l h hv)
  · simp [gluePt, h]

omit g in
theorem line_eq₁ {u v : V} (hu : u ∈ R₁) (hv : v ∈ R₁) :
    glueLine φ₁ φ₂ ψ₁ ψ₂ u v = ψ₁ '' φ₁.line u v := by
  simp [glueLine, hu, hv]

theorem line_eq₂ {u v : V} (hu : u ∈ R₂) (hv : v ∈ R₂) (huv : G.Adj u v) :
    glueLine φ₁ φ₂ ψ₁ ψ₂ u v = ψ₂ '' φ₂.line u v := by
  by_cases h : u ∈ R₁ ∧ v ∈ R₁
  · rw [line_eq₁ h.1 h.2]
    exact g.agree_line u v (g.ind u (g.mem_l h.1 hu) v (g.mem_l h.2 hv) huv)
  · simp only [glueLine, h, ↓reduceIte]

theorem pt_injOn : InjOn (gluePt φ₁ φ₂ ψ₁ ψ₂) (R₁ ∪ R₂) := by
  have c1 : ∀ {u v}, u ∈ R₁ → v ∈ R₁ → gluePt φ₁ φ₂ ψ₁ ψ₂ u = gluePt φ₁ φ₂ ψ₁ ψ₂ v → u = v := by
    intro u v hu hv he
    rw [pt_eq₁ hu, pt_eq₁ hv] at he
    exact φ₁.injOn hu hv (g.inj₁ (g.pt₁_mem hu) (g.pt₁_mem hv) he)
  have c2 : ∀ {u v}, u ∈ R₂ → v ∈ R₂ → gluePt φ₁ φ₂ ψ₁ ψ₂ u = gluePt φ₁ φ₂ ψ₁ ψ₂ v → u = v := by
    intro u v hu hv he
    rw [g.pt_eq₂ hu, g.pt_eq₂ hv] at he
    exact φ₂.injOn hu hv (g.inj₂ (g.pt₂_mem hu) (g.pt₂_mem hv) he)
  have c3 : ∀ {u v}, u ∈ R₁ → v ∈ R₂ → gluePt φ₁ φ₂ ψ₁ ψ₂ u = gluePt φ₁ φ₂ ψ₁ ψ₂ v → v ∈ R₁ := by
    intro u v hu hv he
    rw [pt_eq₁ hu, g.pt_eq₂ hv] at he
    refine g.l_R₁ (g.mem_l₂ hv ?_)
    rw [← he]
    exact g.m₁.1 (g.pt₁_mem hu)
  rintro u (hu | hu) v (hv | hv) he
  · exact c1 hu hv he
  · exact c1 hu (c3 hu hv he) he
  · exact (c1 hv (c3 hv hu he.symm) he.symm).symm
  · exact c2 hu hv he

theorem isLine (u : V) (hu : u ∈ R₁ ∪ R₂) (v : V) (hv : v ∈ R₁ ∪ R₂) (huv : G.Adj u v) :
    IsLineWithEnds (glueLine φ₁ φ₂ ψ₁ ψ₂ u v) (gluePt φ₁ φ₂ ψ₁ ψ₂ u) (gluePt φ₁ φ₂ ψ₁ ψ₂ v) := by
  rcases g.edge u hu v hv huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [line_eq₁ hu hv, pt_eq₁ hu, pt_eq₁ hv]
    exact isLineWithEnds_image (φ₁.isLine u hu v hv huv)
      (g.m₁.2.2.2.2.1.mono (g.line₁_sub hu hv huv)) (g.inj₁.mono (g.line₁_sub hu hv huv))
  · rw [g.line_eq₂ hu hv huv, g.pt_eq₂ hu, g.pt_eq₂ hv]
    exact isLineWithEnds_image (φ₂.isLine u hu v hv huv)
      (g.m₂.2.2.2.2.1.mono (g.line₂_sub hu hv huv)) (g.inj₂.mono (g.line₂_sub hu hv huv))

/-- A line drawn on the first side meets a line drawn on the second side, not on the first, only at
points of common ends. -/
theorem inter_mixed {u v u' v' : V} (hu : u ∈ R₁) (hv : v ∈ R₁) (huv : G.Adj u v) (hu' : u' ∈ R₂)
    (hv' : v' ∈ R₂) (huv' : G.Adj u' v') (hn : ¬ (u' ∈ R₁ ∧ v' ∈ R₁)) :
    ψ₁ '' φ₁.line u v ∩ ψ₂ '' φ₂.line u' v' ⊆ gluePt φ₁ φ₂ ψ₁ ψ₂ '' ({u, v} ∩ {u', v'}) := by
  rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
  have hz : ψ₁ x ∈ range e :=
    g.half_inter ⟨g.m₁.1 (g.line₁_sub hu hv huv hx), hxy ▸ g.m₂.1 (g.line₂_sub hu' hv' huv' hy)⟩
  rw [← g.pe₂] at hz
  obtain ⟨y', hy', he⟩ := hz
  have hsub := (φ₂.pathImage_subset_U g.path₂).trans g.U₂_sub
  have hyy : y' = y := g.inj₂ (hsub hy') (g.line₂_sub hu' hv' huv' hy) (he.trans hxy.symm)
  subst hyy
  -- `u'v'` is not an edge of `l`, so its line meets the image of `l` only at points of `l`
  have hne : ∀ p ∈ l.zip l.tail, s(u', v') ≠ s(p.1, p.2) := by
    intro p hp hs
    have hp1 : p.1 ∈ l := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ l := List.mem_of_mem_tail (List.of_mem_zip hp).2
    rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn ⟨g.l_R₁ hp1, g.l_R₁ hp2⟩
    · exact hn ⟨g.l_R₁ hp2, g.l_R₁ hp1⟩
  obtain ⟨w, ⟨hw1, hw2⟩, hw⟩ := φ₂.line_inter_pathImage_sub hu' hv' huv' g.path₂ hne ⟨hy, hy'⟩
  subst hw
  have hwR₁ : w ∈ R₁ := g.l_R₁ hw2
  -- the point of `w` on the first side
  have hxw : x = φ₁.pt w := by
    refine g.inj₁ (g.line₁_sub hu hv huv hx) (g.pt₁_mem hwR₁) ?_
    rw [← he]
    exact (g.agree_pt w hw2).symm
  rw [hxw] at hx
  have hwuv := φ₁.avoid u hu v hv huv w hwR₁ hx
  refine ⟨w, ⟨hwuv, hw1⟩, ?_⟩
  rw [pt_eq₁ hwR₁, hxw]

theorem inter_line (u : V) (hu : u ∈ R₁ ∪ R₂) (v : V) (hv : v ∈ R₁ ∪ R₂) (u' : V) (hu' : u' ∈ R₁ ∪ R₂)
    (v' : V) (hv' : v' ∈ R₁ ∪ R₂) (huv : G.Adj u v) (huv' : G.Adj u' v')
    (hne : s(u, v) ≠ s(u', v')) :
    glueLine φ₁ φ₂ ψ₁ ψ₂ u v ∩ glueLine φ₁ φ₂ ψ₁ ψ₂ u' v' ⊆
      gluePt φ₁ φ₂ ψ₁ ψ₂ '' ({u, v} ∩ {u', v'}) := by
  have c1 : ∀ {u v u' v'}, u ∈ R₁ → v ∈ R₁ → u' ∈ R₁ → v' ∈ R₁ → G.Adj u v → G.Adj u' v' →
      s(u, v) ≠ s(u', v') → ψ₁ '' φ₁.line u v ∩ ψ₁ '' φ₁.line u' v' ⊆
        gluePt φ₁ φ₂ ψ₁ ψ₂ '' ({u, v} ∩ {u', v'}) := by
    intro u v u' v' hu hv hu' hv' huv huv' hne
    rw [← g.inj₁.image_inter (g.line₁_sub hu hv huv) (g.line₁_sub hu' hv' huv')]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := φ₁.inter u hu v hv u' hu' v' hv' huv huv' hne hx
    have hwR : w ∈ R₁ := by rcases hw.1 with rfl | rfl <;> assumption
    exact ⟨w, hw, pt_eq₁ hwR⟩
  have c2 : ∀ {u v u' v'}, u ∈ R₂ → v ∈ R₂ → u' ∈ R₂ → v' ∈ R₂ → G.Adj u v → G.Adj u' v' →
      s(u, v) ≠ s(u', v') → ψ₂ '' φ₂.line u v ∩ ψ₂ '' φ₂.line u' v' ⊆
        gluePt φ₁ φ₂ ψ₁ ψ₂ '' ({u, v} ∩ {u', v'}) := by
    intro u v u' v' hu hv hu' hv' huv huv' hne
    rw [← g.inj₂.image_inter (g.line₂_sub hu hv huv) (g.line₂_sub hu' hv' huv')]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨w, hw, rfl⟩ := φ₂.inter u hu v hv u' hu' v' hv' huv huv' hne hx
    have hwR : w ∈ R₂ := by rcases hw.1 with rfl | rfl <;> assumption
    exact ⟨w, hw, g.pt_eq₂ hwR⟩
  rcases g.edge u hu v hv huv with ⟨hu1, hv1⟩ | ⟨hu2, hv2⟩ <;>
    rcases g.edge u' hu' v' hv' huv' with ⟨hu1', hv1'⟩ | ⟨hu2', hv2'⟩
  · rw [line_eq₁ hu1 hv1, line_eq₁ hu1' hv1']
    exact c1 hu1 hv1 hu1' hv1' huv huv' hne
  · by_cases h : u' ∈ R₁ ∧ v' ∈ R₁
    · rw [line_eq₁ hu1 hv1, line_eq₁ h.1 h.2]
      exact c1 hu1 hv1 h.1 h.2 huv huv' hne
    · rw [line_eq₁ hu1 hv1, g.line_eq₂ hu2' hv2' huv']
      exact g.inter_mixed hu1 hv1 huv hu2' hv2' huv' h
  · by_cases h : u ∈ R₁ ∧ v ∈ R₁
    · rw [line_eq₁ h.1 h.2, line_eq₁ hu1' hv1']
      exact c1 h.1 h.2 hu1' hv1' huv huv' hne
    · rw [g.line_eq₂ hu2 hv2 huv, line_eq₁ hu1' hv1', inter_comm, inter_comm {u, v}]
      exact g.inter_mixed hu1' hv1' huv' hu2 hv2 huv h
  · rw [g.line_eq₂ hu2 hv2 huv, g.line_eq₂ hu2' hv2' huv']
    exact c2 hu2 hv2 hu2' hv2' huv huv' hne

theorem avoid (u : V) (hu : u ∈ R₁ ∪ R₂) (v : V) (hv : v ∈ R₁ ∪ R₂) (huv : G.Adj u v) (w : V)
    (hw : w ∈ R₁ ∪ R₂) (hwl : gluePt φ₁ φ₂ ψ₁ ψ₂ w ∈ glueLine φ₁ φ₂ ψ₁ ψ₂ u v) : w = u ∨ w = v := by
  rcases g.edge u hu v hv huv with ⟨hu1, hv1⟩ | ⟨hu2, hv2⟩
  · rw [line_eq₁ hu1 hv1] at hwl
    have hw1 : w ∈ R₁ := by
      rcases hw with hw | hw
      · exact hw
      · refine g.l_R₁ (g.mem_l₂ hw ?_)
        rw [← g.pt_eq₂ hw]
        exact image_subset_iff.mpr (g.m₁.1.mono_left (g.line₁_sub hu1 hv1 huv)) hwl
    rw [pt_eq₁ hw1] at hwl
    obtain ⟨x, hx, he⟩ := hwl
    rw [g.inj₁ (g.line₁_sub hu1 hv1 huv hx) (g.pt₁_mem hw1) he] at hx
    exact φ₁.avoid u hu1 v hv1 huv w hw1 hx
  · rw [g.line_eq₂ hu2 hv2 huv] at hwl
    have hw2 : w ∈ R₂ := by
      rcases hw with hw | hw
      · refine g.l_R₂ (g.mem_l₁ hw ?_)
        rw [← pt_eq₁ (φ₁ := φ₁) (φ₂ := φ₂) (ψ₁ := ψ₁) (ψ₂ := ψ₂) hw]
        exact image_subset_iff.mpr (g.m₂.1.mono_left (g.line₂_sub hu2 hv2 huv)) hwl
      · exact hw
    rw [g.pt_eq₂ hw2] at hwl
    obtain ⟨x, hx, he⟩ := hwl
    rw [g.inj₂ (g.line₂_sub hu2 hv2 huv hx) (g.pt₂_mem hw2) he] at hx
    exact φ₂.avoid u hu2 v hv2 huv w hw2 hx

omit g in
theorem line_comm (u v : V) : glueLine φ₁ φ₂ ψ₁ ψ₂ u v = glueLine φ₁ φ₂ ψ₁ ψ₂ v u := by
  simp only [glueLine, φ₁.line_comm u v, φ₂.line_comm u v]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · rfl

/-- **The glued drawing**: vertices of `R₁` and edges inside `R₁` are drawn by `ψ₁ ∘ φ₁`, the others
by `ψ₂ ∘ φ₂`. -/
@[expose] noncomputable def emb : PlaneEmbedding G (R₁ ∪ R₂) where
  pt := gluePt φ₁ φ₂ ψ₁ ψ₂
  line := glueLine φ₁ φ₂ ψ₁ ψ₂
  finite := φ₁.finite.union φ₂.finite
  injOn := g.pt_injOn
  line_comm := line_comm
  isLine := g.isLine
  inter := g.inter_line
  avoid := g.avoid

/-! ### The faces of the glued drawing -/

theorem emb_pt : g.emb.pt = gluePt φ₁ φ₂ ψ₁ ψ₂ := rfl

theorem emb_line : g.emb.line = glueLine φ₁ φ₂ ψ₁ ψ₂ := rfl

/-- The glued drawing is the union of the images of the two drawings. -/
theorem U_eq : g.emb.U = ψ₁ '' φ₁.U ∪ ψ₂ '' φ₂.U := by
  ext z
  constructor
  · rintro (⟨v, hv, rfl⟩ | hz)
    · rw [g.emb_pt]
      rcases hv with hv | hv
      · exact Or.inl ⟨φ₁.pt v, φ₁.pt_mem_U hv, (pt_eq₁ hv).symm⟩
      · exact Or.inr ⟨φ₂.pt v, φ₂.pt_mem_U hv, (g.pt_eq₂ hv).symm⟩
    · simp only [mem_iUnion] at hz
      obtain ⟨u, hu, v, hv, huv, hz⟩ := hz
      rw [g.emb_line] at hz
      rcases g.edge u hu v hv huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [line_eq₁ hu hv] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact Or.inl ⟨x, φ₁.line_subset_U hu hv huv hx, rfl⟩
      · rw [g.line_eq₂ hu hv huv] at hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact Or.inr ⟨x, φ₂.line_subset_U hu hv huv hx, rfl⟩
  · rintro (⟨x, hx | hx, rfl⟩ | ⟨x, hx | hx, rfl⟩)
    · obtain ⟨v, hv, rfl⟩ := hx
      exact Or.inl ⟨v, Or.inl hv, pt_eq₁ hv⟩
    · simp only [mem_iUnion] at hx
      obtain ⟨u, hu, v, hv, huv, hx⟩ := hx
      refine Or.inr ?_
      simp only [mem_iUnion]
      refine ⟨u, Or.inl hu, v, Or.inl hv, huv, ?_⟩
      rw [g.emb_line, line_eq₁ hu hv]
      exact mem_image_of_mem _ hx
    · obtain ⟨v, hv, rfl⟩ := hx
      exact Or.inl ⟨v, Or.inr hv, g.pt_eq₂ hv⟩
    · simp only [mem_iUnion] at hx
      obtain ⟨u, hu, v, hv, huv, hx⟩ := hx
      refine Or.inr ?_
      simp only [mem_iUnion]
      refine ⟨u, Or.inr hu, v, Or.inr hv, huv, ?_⟩
      rw [g.emb_line, g.line_eq₂ hu hv huv]
      exact mem_image_of_mem _ hx

theorem U_sub : g.emb.U ⊆ closedInner (sphere (0 : ℂ) 1) := by
  rw [g.U_eq, ← g.half_union]
  rintro z (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
  · exact Or.inl (g.m₁.1 (g.U₁_sub hx))
  · exact Or.inr (g.m₂.1 (g.U₂_sub hx))

/-- The image of a cyclic list of vertices of `R₁`. -/
theorem cycleImage_eq₁ {T : List V} (hT : ∀ x ∈ T, x ∈ R₁) :
    g.emb.cycleImage T = ψ₁ '' φ₁.cycleImage T := by
  simp only [PlaneEmbedding.cycleImage, image_iUnion₂, g.emb_line]
  refine iUnion₂_congr fun p hp => line_eq₁ (hT _ (List.of_mem_zip hp).1)
    (hT _ (List.mem_rotate.mp (List.of_mem_zip hp).2))

/-- The image of a cycle of `G` on `R₂`. -/
theorem cycleImage_eq₂ {T : List V} (hT : IsCycleList G T) (hTR : ∀ x ∈ T, x ∈ R₂) :
    g.emb.cycleImage T = ψ₂ '' φ₂.cycleImage T := by
  simp only [PlaneEmbedding.cycleImage, image_iUnion₂, g.emb_line]
  refine iUnion₂_congr fun p hp => g.line_eq₂ (hTR _ (List.of_mem_zip hp).1)
    (hTR _ (List.mem_rotate.mp (List.of_mem_zip hp).2)) (hT.2.2 p hp)

/-- The image of a list of vertices of `R₁`. -/
theorem pathImage_eq₁ {T : List V} (hT : ∀ x ∈ T, x ∈ R₁) :
    g.emb.pathImage T = ψ₁ '' φ₁.pathImage T := by
  simp only [PlaneEmbedding.pathImage, image_iUnion₂, g.emb_line]
  refine iUnion₂_congr fun p hp => line_eq₁ (hT _ (List.of_mem_zip hp).1)
    (hT _ (List.mem_of_mem_tail (List.of_mem_zip hp).2))

/-- The image of a path list of `G` on `R₂`. -/
theorem pathImage_eq₂ {T : List V} (hT : IsPathList G R₂ T) :
    g.emb.pathImage T = ψ₂ '' φ₂.pathImage T := by
  simp only [PlaneEmbedding.pathImage, image_iUnion₂, g.emb_line]
  refine iUnion₂_congr fun p hp => g.line_eq₂ (hT.2.2 _ (List.of_mem_zip hp).1)
    (hT.2.2 _ (List.mem_of_mem_tail (List.of_mem_zip hp).2)) (isChain_iff_zip.mp hT.2.1 _ hp)

/-- A bounded face of `φ₁` is sent to a bounded face of the glued drawing. -/
theorem face₁ {r : Set ℂ} (hr : r ∈ φ₁.faces) (hb : Bornology.IsBounded r) :
    ψ₁ '' r ∈ g.emb.faces ∧ frontier (ψ₁ '' r) = ψ₁ '' frontier r ∧
      Bornology.IsBounded (ψ₁ '' r) := by
  obtain ⟨ho, hc, hin, hfr, hdis⟩ :=
    φ₁.image_face g.rib₁ g.cyc₁ g.sub₁ g.jordan₁ g.m₁ g.bd₁ hr hb
  refine ⟨g.emb.mem_faces_of_frontier ho hc ?_ ?_, hfr, g.jordan₁.isBounded_inner.subset hin⟩
  · intro z hz hzU
    rw [g.U_eq] at hzU
    rcases hzU with h | ⟨x, hx, rfl⟩
    · exact Set.disjoint_left.mp hdis hz h
    · have hz2 := g.m₂.1 (g.U₂_sub hx)
      exact (hin hz).1 (Or.inr (g.half_inter ⟨Or.inl (hin hz), hz2⟩))
  · rw [hfr, g.U_eq]
    obtain ⟨a, b, c, hT, hfr'⟩ := g.rib₁.2.1 r hr hb
    rw [hfr']
    exact (image_mono (φ₁.cycleImage_subset_U hT.isCycleList hT.mem)).trans subset_union_left

/-- A bounded face of `φ₂` is sent to a bounded face of the glued drawing. -/
theorem face₂ {r : Set ℂ} (hr : r ∈ φ₂.faces) (hb : Bornology.IsBounded r) :
    ψ₂ '' r ∈ g.emb.faces ∧ frontier (ψ₂ '' r) = ψ₂ '' frontier r ∧
      Bornology.IsBounded (ψ₂ '' r) := by
  obtain ⟨ho, hc, hin, hfr, hdis⟩ :=
    φ₂.image_face g.rib₂ g.cyc₂ g.sub₂ g.jordan₂ g.m₂ g.bd₂ hr hb
  refine ⟨g.emb.mem_faces_of_frontier ho hc ?_ ?_, hfr, g.jordan₂.isBounded_inner.subset hin⟩
  · intro z hz hzU
    rw [g.U_eq] at hzU
    rcases hzU with ⟨x, hx, rfl⟩ | h
    · have hz1 := g.m₁.1 (g.U₁_sub hx)
      exact (hin hz).1 (Or.inr (g.half_inter ⟨hz1, Or.inl (hin hz)⟩))
    · exact Set.disjoint_left.mp hdis hz h
  · rw [hfr, g.U_eq]
    obtain ⟨a, b, c, hT, hfr'⟩ := g.rib₂.2.1 r hr hb
    rw [hfr']
    exact (image_mono (φ₂.cycleImage_subset_U hT.isCycleList hT.mem)).trans subset_union_right

/-- The outside of the unit disc is a face of the glued drawing. -/
theorem outer_face : outer (sphere (0 : ℂ) 1) ∈ g.emb.faces := by
  have J := jordan_sphere
  refine g.emb.mem_faces_of_frontier J.isOpen_outer J.isConnected_outer ?_ ?_
  · intro z hz hzU
    rcases g.U_sub hzU with h | h
    · exact Set.disjoint_left.mp J.disjoint h hz
    · exact hz.1 h
  · rw [J.frontier_outer, ← g.cut.union, g.U_eq]
    have h1 : range a₁ ⊆ ψ₁ '' φ₁.U := by
      refine (subset_union_left.trans g.bd₁.symm.subset).trans (image_mono ?_)
      exact φ₁.cycleImage_subset_U g.cyc₁ g.sub₁
    have h2 : range a₂ ⊆ ψ₂ '' φ₂.U := by
      refine (subset_union_left.trans g.bd₂.symm.subset).trans (image_mono ?_)
      exact φ₂.cycleImage_subset_U g.cyc₂ g.sub₂
    exact union_subset_union h1 h2

/-- Every face of the glued drawing is the outside of the unit disc or the image of a bounded face
of `φ₁` or of `φ₂`. -/
theorem faces_cases {f : Set ℂ} (hf : f ∈ g.emb.faces) :
    f = outer (sphere (0 : ℂ) 1) ∨ (∃ r ∈ φ₁.faces, Bornology.IsBounded r ∧ f = ψ₁ '' r) ∨
      ∃ r ∈ φ₂.faces, Bornology.IsBounded r ∧ f = ψ₂ '' r := by
  obtain ⟨z, hz, rfl⟩ := hf
  have same : ∀ f' ∈ g.emb.faces, z ∈ f' → connectedComponentIn (univ \ g.emb.U) z = f' := by
    rintro _ ⟨w, -, rfl⟩ hzw
    exact (connectedComponentIn_eq hzw).symm
  by_cases hzD : z ∈ closedInner (sphere (0 : ℂ) 1)
  · rw [← g.half_union] at hzD
    rcases hzD with h1 | h2
    · have hy := g.m₁.2.1 h1
      have hyz : ψ₁ (χ₁ z) = z := g.m₁.2.2.2.1 h1
      have hyU : χ₁ z ∉ φ₁.U := fun h => hz.2 (g.U_eq ▸ Or.inl ⟨χ₁ z, h, hyz⟩)
      obtain ⟨r, hr, hb, hyr⟩ := φ₁.exists_bounded_face g.cyc₁ g.sub₁ hy hyU
      exact Or.inr (Or.inl ⟨r, hr, hb, same _ (g.face₁ hr hb).1 ⟨χ₁ z, hyr, hyz⟩⟩)
    · have hy := g.m₂.2.1 h2
      have hyz : ψ₂ (χ₂ z) = z := g.m₂.2.2.2.1 h2
      have hyU : χ₂ z ∉ φ₂.U := fun h => hz.2 (g.U_eq ▸ Or.inr ⟨χ₂ z, h, hyz⟩)
      obtain ⟨r, hr, hb, hyr⟩ := φ₂.exists_bounded_face g.cyc₂ g.sub₂ hy hyU
      exact Or.inr (Or.inr ⟨r, hr, hb, same _ (g.face₂ hr hb).1 ⟨χ₂ z, hyr, hyz⟩⟩)
  · left
    have J := jordan_sphere
    have hzs : z ∈ (sphere (0 : ℂ) 1)ᶜ := fun h => hzD (Or.inr h)
    rw [← J.union_eq] at hzs
    have hzo : z ∈ outer (sphere (0 : ℂ) 1) := hzs.resolve_left fun h => hzD (Or.inl h)
    exact same _ g.outer_face hzo

/-- **The glued drawing has the faces of a rib**, with any frame drawn on the unit circle. -/
theorem isRibEmbedding {C : List V} (hC : g.emb.cycleImage C = sphere (0 : ℂ) 1) :
    g.emb.IsRibEmbedding C := by
  refine ⟨fun r hr hb => ?_, fun r hr hb => ?_, fun a b c hT => ?_⟩
  · rcases g.faces_cases hr with rfl | ⟨r', hr', hb', rfl⟩ | ⟨r', hr', hb', rfl⟩
    · rw [jordan_sphere.frontier_outer, hC]
    · exact absurd (g.face₁ hr' hb').2.2 hb
    · exact absurd (g.face₂ hr' hb').2.2 hb
  · rcases g.faces_cases hr with rfl | ⟨r', hr', hb', rfl⟩ | ⟨r', hr', hb', rfl⟩
    · exact absurd hb jordan_sphere.not_isBounded_outer
    · obtain ⟨a, b, c, hT, hfr⟩ := g.rib₁.2.1 r' hr' hb'
      refine ⟨a, b, c, ⟨Or.inl hT.1, Or.inl hT.2.1, Or.inl hT.2.2.1, hT.2.2.2⟩, ?_⟩
      rw [(g.face₁ hr' hb').2.1, hfr, g.cycleImage_eq₁ hT.mem]
    · obtain ⟨a, b, c, hT, hfr⟩ := g.rib₂.2.1 r' hr' hb'
      refine ⟨a, b, c, ⟨Or.inr hT.1, Or.inr hT.2.1, Or.inr hT.2.2.1, hT.2.2.2⟩, ?_⟩
      rw [(g.face₂ hr' hb').2.1, hfr, g.cycleImage_eq₂ hT.isCycleList hT.mem]
  · obtain ⟨ha, hb, hc, hab, hbc, hac⟩ := hT
    by_cases h : a ∈ R₁ ∧ b ∈ R₁ ∧ c ∈ R₁
    · have T₁ : IsTriangleOn G R₁ a b c := ⟨h.1, h.2.1, h.2.2, hab, hbc, hac⟩
      obtain ⟨r, hr, hb, hfr⟩ := g.rib₁.2.2 a b c T₁
      obtain ⟨hf, hfr', hb'⟩ := g.face₁ hr hb
      exact ⟨_, hf, hb', by rw [hfr', hfr, g.cycleImage_eq₁ T₁.mem]⟩
    · have key : ∀ x y, x ∈ R₁ ∪ R₂ → x ∉ R₁ → y ∈ R₁ ∪ R₂ → G.Adj x y → x ∈ R₂ ∧ y ∈ R₂ := by
        intro x y hx hx1 hy hxy
        rcases g.edge x hx y hy hxy with h' | h'
        · exact absurd h'.1 hx1
        · exact h'
      have T₂ : a ∈ R₂ ∧ b ∈ R₂ ∧ c ∈ R₂ := by
        by_cases ha1 : a ∈ R₁
        · by_cases hb1 : b ∈ R₁
          · have hc1 : c ∉ R₁ := fun hc1 => h ⟨ha1, hb1, hc1⟩
            exact ⟨(key c a hc hc1 ha hac.symm).2, (key c b hc hc1 hb hbc.symm).2,
              (key c a hc hc1 ha hac.symm).1⟩
          · exact ⟨(key b a hb hb1 ha hab.symm).2, (key b a hb hb1 ha hab.symm).1,
              (key b c hb hb1 hc hbc).2⟩
        · exact ⟨(key a b ha ha1 hb hab).1, (key a b ha ha1 hb hab).2, (key a c ha ha1 hc hac).2⟩
      have T₂' : IsTriangleOn G R₂ a b c := ⟨T₂.1, T₂.2.1, T₂.2.2, hab, hbc, hac⟩
      obtain ⟨r, hr, hb, hfr⟩ := g.rib₂.2.2 a b c T₂'
      obtain ⟨hf, hfr', hb'⟩ := g.face₂ hr hb
      exact ⟨_, hf, hb', by rw [hfr', hfr, g.cycleImage_eq₂ T₂'.isCycleList T₂'.mem]⟩

end Glue

end GraphMinor.HP25
