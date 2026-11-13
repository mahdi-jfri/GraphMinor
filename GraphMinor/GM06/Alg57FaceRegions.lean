module

public import GraphMinor.GM06.Alg57DartRotation
public import GraphMinor.GM11.Rotation
import GraphMinor.GM06.Alg57SphereEuler
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Walks

/-!
# Face orbits and regions, given the corners

Lemma 3 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) says that the orbits of
`φ = σ⁻¹ τ` on the darts of a connected graph in the sphere are the regions, with the incidence
rules (3) and (4). This file proves the counting half of that lemma.

The darts of a drawing are its edges with a chosen end (`DrawingDart`). A rotation on them is
read in the drawing through a label `ρ d`, the region in the corner after `d` at its vertex
(`IsCornerLabel`). The corner facts at one vertex are those of `GM11.IsCorners`. The one fact that
links two vertices is `coherent`: the corner after `d` and the corner before `rev d` at the other
end are the same region, `ρ (φ d) = ρ d`. This is Step 1 of the proof of Lemma 3.

Given these, the face orbits map onto the regions: every region meets the drawing in its
closure, at a vertex or along an edge. Euler's lower bound for the regions and
`DartRotation.card_faces_add_card_vertices_le` then show that the map is one-to-one, and (3)
and (4) follow from the corner facts.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 Equiv unitInterval

universe u

namespace DartRotation

variable {D : Type u} [Finite D]

/-- A function that does not change along a permutation is constant on each of its cycles. -/
theorem eq_of_sameCycle {β : Type*} {p : Perm D} {g : D → β} (hg : ∀ d, g (p d) = g d)
    {a b : D} (h : p.SameCycle a b) : g a = g b := by
  obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
  have hpow : ∀ n : ℕ, g ((p ^ n) a) = g a := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', Perm.mul_apply, hg, ih]
  rw [← hi, hpow]

variable (R : DartRotation D)

/-- The label of a face orbit, for a dart label that does not change along `face`. -/
def faceLabel {β : Type*} (ρ : D → β) (hρ : ∀ d, ρ (R.face d) = ρ d) : R.Faces → β :=
  Quotient.lift ρ fun _ _ h => eq_of_sameCycle hρ h

theorem faceLabel_faceOf {β : Type*} (ρ : D → β) (hρ : ∀ d, ρ (R.face d) = ρ d) (d : D) :
    R.faceLabel ρ hρ (R.faceOf d) = ρ d := rfl

end DartRotation

variable {S : Type u} [TopologicalSpace S]

/-- The darts of a drawing: an edge together with one of its two ends. A loop has two darts. -/
abbrev DrawingDart (Γ : Drawing S) : Type u := {x : Set S × Bool // x.1 ∈ Γ.E}

instance (Γ : Drawing S) : Finite (DrawingDart Γ) := by
  have h : {x : Set S × Bool | x.1 ∈ Γ.E} = Γ.E ×ˢ univ := by ext x; simp
  have hf : {x : Set S × Bool | x.1 ∈ Γ.E}.Finite := by
    rw [h]; exact Γ.finite_edges.prod finite_univ
  exact hf.to_subtype

/-- Reversal of a dart: the same edge with its other end. -/
def dartFlip (Γ : Drawing S) : Perm (DrawingDart Γ) where
  toFun d := ⟨(d.1.1, !d.1.2), d.2⟩
  invFun d := ⟨(d.1.1, !d.1.2), d.2⟩
  left_inv d := by simp
  right_inv d := by simp

@[simp]
theorem dartFlip_apply (Γ : Drawing S) (d : DrawingDart Γ) :
    dartFlip Γ d = ⟨(d.1.1, !d.1.2), d.2⟩ := rfl

/-- The vertex at which a dart starts, read through the edge parametrization `γ`. -/
def dartVertex {Γ : Drawing S} (γ : Set S → I → S) (d : DrawingDart Γ) : S :=
  γ d.1.1 (endOf d.1.2)

theorem dartVertex_mem {Γ : Drawing S} {γ : Set S → I → S} (hγ : EdgePar Γ γ)
    (d : DrawingDart Γ) : dartVertex γ d ∈ Γ.V := by
  rcases d with ⟨⟨e, b⟩, he⟩
  cases b
  · simpa [dartVertex, endOf] using hγ.zero e he
  · simpa [dartVertex, endOf] using hγ.one e he

/-- A rotation system on the darts of `Γ` that fits the drawing: reversal swaps the two ends of
an edge, and the rotation stays at the vertex and reaches every dart there. -/
structure IsDrawingRotation (Γ : Drawing S) (γ : Set S → I → S)
    (R : DartRotation (DrawingDart Γ)) : Prop where
  rev_eq : ∀ d, R.rev d = dartFlip Γ d
  vertex_rot : ∀ d, dartVertex γ (R.rot d) = dartVertex γ d
  reach : ∀ d d', dartVertex γ d = dartVertex γ d' → R.rot.SameCycle d d'

/-- `ρ d` is the region in the corner after the dart `d` at its vertex. The first four
conditions are those of `GM11.IsCorners` at one vertex: the corner regions at a vertex are all
regions near it, and the regions along the edge of `d` are the corners just before and just
after `d`. The last condition says that both ends of an edge see the same region on the same
side: the corner after `d` is the corner before `rev d`, which is the corner after `φ d`. -/
structure IsCornerLabel (Γ : Drawing S) (γ : Set S → I → S)
    (R : DartRotation (DrawingDart Γ)) (ρ : DrawingDart Γ → Set S) : Prop where
  region : ∀ d, ρ d ∈ Γ.R
  closure_vertex : ∀ d, dartVertex γ d ∈ closure (ρ d)
  all : ∀ r ∈ Γ.R, ∀ d : DrawingDart Γ, dartVertex γ d ∈ closure r →
    ∃ d' : DrawingDart Γ, dartVertex γ d' = dartVertex γ d ∧ r = ρ d'
  edge : ∀ d, d.1.1 ⊆ closure (ρ d)
  sides : ∀ d, ∀ r ∈ Γ.R, d.1.1 ⊆ closure r → r = ρ (R.rot.symm d) ∨ r = ρ d
  coherent : ∀ d, ρ (R.face d) = ρ d

variable {Γ : Drawing S} {γ : Set S → I → S} {R : DartRotation (DrawingDart Γ)}

namespace IsDrawingRotation

/-- The rotation orbits are the vertices, when every vertex has a dart. -/
theorem card_vertices (hR : IsDrawingRotation Γ γ R) (hγ : EdgePar Γ γ)
    (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v) : Nat.card R.Vertices = Γ.V.ncard := by
  let f : R.Vertices → Γ.V :=
    Quotient.lift (fun d => ⟨dartVertex γ d, dartVertex_mem hγ d⟩) fun _ _ h =>
      DartRotation.eq_of_sameCycle (g := fun d => (⟨dartVertex γ d, dartVertex_mem hγ d⟩ : Γ.V))
        (fun d => Subtype.ext (hR.vertex_rot d)) h
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun v => ?_⟩
    · induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (hR.reach _ _ (congrArg Subtype.val hab))
    · obtain ⟨d, hd⟩ := hV v.1 v.2
      exact ⟨R.vertexOf d, Subtype.ext hd⟩
  rw [Nat.card_eq_of_bijective f hf, Nat.card_coe_set_eq]

/-- The reversal orbits are the edges. -/
theorem card_edges (hR : IsDrawingRotation Γ γ R) : Nat.card R.Edges = Γ.E.ncard := by
  let f : R.Edges → Γ.E :=
    Quotient.lift (fun d => ⟨d.1.1, d.2⟩) fun _ _ h =>
      DartRotation.eq_of_sameCycle (g := fun d => (⟨d.1.1, d.2⟩ : Γ.E))
        (fun d => by rw [hR.rev_eq]; rfl) h
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun e => ⟨R.edgeOf ⟨(e.1, false), e.2⟩, rfl⟩⟩
    induction a using Quotient.inductionOn with | h a => ?_
    induction b using Quotient.inductionOn with | h b => ?_
    have hab' : a.1.1 = b.1.1 := congrArg Subtype.val hab
    change R.edgeOf a = R.edgeOf b
    rw [R.edgeOf_eq_iff, hR.rev_eq]
    rcases a with ⟨⟨e, x⟩, he⟩
    rcases b with ⟨⟨e', y⟩, he'⟩
    simp only at hab'
    subst hab'
    cases x <;> cases y <;> simp
  rw [Nat.card_eq_of_bijective f hf, Nat.card_coe_set_eq]

end IsDrawingRotation

/-- In a connected surface, the closure of a region meets a nonempty drawing. -/
theorem closure_region_inter_nonempty [ConnectedSpace S] [LocallyConnectedSpace S]
    (hU : Γ.U.Nonempty) {r : Set S} (hr : r ∈ Γ.R) : (closure r ∩ Γ.U).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hcl : closure r ⊆ r := fun y hy =>
    (closure_region_subset hr hy).resolve_right fun hyU => h.subset ⟨hy, hyU⟩
  have hclo : IsClopen r := ⟨closure_subset_iff_isClosed.mp hcl, region_isOpen hr⟩
  rcases isClopen_iff.mp hclo with h0 | hu
  · exact (region_nonempty hr).ne_empty h0
  · obtain ⟨x, hx⟩ := hU
    exact region_subset hr (hu ▸ mem_univ x) hx

namespace IsCornerLabel

variable {ρ : DrawingDart Γ → Set S}

/-- The region of a face orbit: the corner region of any of its darts. -/
def label (hρ : IsCornerLabel Γ γ R ρ) : R.Faces → Γ.R :=
  R.faceLabel (fun d => ⟨ρ d, hρ.region d⟩) fun d => Subtype.ext (hρ.coherent d)

theorem label_faceOf (hρ : IsCornerLabel Γ γ R ρ) (d : DrawingDart Γ) :
    (hρ.label (R.faceOf d)).1 = ρ d := rfl

/-- The corner after `rot⁻¹ d` is the corner after `rev d`. -/
theorem rot_symm (hρ : IsCornerLabel Γ γ R ρ) (d : DrawingDart Γ) : ρ (R.rot.symm d) = ρ (R.rev d) := by
  have h := hρ.coherent (R.rev d)
  rw [DartRotation.face_apply, R.rev_rev] at h
  exact h

/-- Every region is the region of a face orbit. -/
theorem label_surjective [ConnectedSpace S] (hS : IsClosedSurface S) (hγ : EdgePar Γ γ)
    (hρ : IsCornerLabel Γ γ R ρ) (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v)
    (hne : Γ.E.Nonempty) : Function.Surjective hρ.label := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rintro ⟨r, hr⟩
  have hU : Γ.U.Nonempty := by
    obtain ⟨e, he⟩ := hne
    have hhalf : (⟨1 / 2, by norm_num, by norm_num⟩ : I) ∈ Ioo 0 1 := by
      constructor
      · change (0 : ℝ) < 1 / 2; norm_num
      · change (1 / 2 : ℝ) < 1; norm_num
    have hx := mem_image_of_mem (γ e) hhalf
    rw [hγ.image e he] at hx
    exact ⟨_, Γ.closure_subset_U he (subset_closure hx)⟩
  obtain ⟨x, hxr, hxU⟩ := closure_region_inter_nonempty hU hr
  by_cases hxV : x ∈ Γ.V
  · obtain ⟨d, rfl⟩ := hV x hxV
    obtain ⟨d', -, hd'⟩ := hρ.all r hr d hxr
    exact ⟨R.faceOf d', Subtype.ext hd'.symm⟩
  · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
    have hsub : e ⊆ closure r := edge_subset_closure_of_incident hS he hr ⟨x, hxe, hxr⟩
    let d : DrawingDart Γ := ⟨(e, false), he⟩
    rcases hρ.sides d r hr hsub with h | h
    · exact ⟨R.faceOf (R.rot.symm d), Subtype.ext h.symm⟩
    · exact ⟨R.faceOf d, Subtype.ext h.symm⟩

/-- **Face orbits are regions** (the bijection of Lemma 3 of the proof of VI (5.7)), for a
connected rotation whose corner regions are given by `ρ` and a drawing with Euler's lower
bound on its regions. -/
theorem label_bijective [ConnectedSpace S] (hS : IsClosedSurface S) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) (hρ : IsCornerLabel Γ γ R ρ) (hc : R.Connected)
    (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v) (hne : Γ.E.Nonempty)
    (hcount : Γ.E.ncard + 2 ≤ Γ.V.ncard + Γ.R.ncard) : Function.Bijective hρ.label := by
  classical
  have : Fintype (DrawingDart Γ) := Fintype.ofFinite _
  refine (hρ.label_surjective hS hγ hV hne).bijective_of_nat_card_le ?_
  have h := R.card_faces_add_card_vertices_le hc
  rw [hR.card_vertices hγ hV, hR.card_edges] at h
  rw [Nat.card_coe_set_eq]
  omega

/-- **Incidence (3).** An edge lies in the closure of the region of a face orbit exactly when one
of its two darts is in the orbit. -/
theorem edge_subset_closure_iff [ConnectedSpace S] (hS : IsClosedSurface S) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) (hρ : IsCornerLabel Γ γ R ρ) (hc : R.Connected)
    (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v) (hne : Γ.E.Nonempty)
    (hcount : Γ.E.ncard + 2 ≤ Γ.V.ncard + Γ.R.ncard) (O : R.Faces) (d : DrawingDart Γ) :
    d.1.1 ⊆ closure (hρ.label O).1 ↔ R.faceOf d = O ∨ R.faceOf (R.rev d) = O := by
  have hinj := (hρ.label_bijective hS hγ hR hc hV hne hcount).1
  constructor
  · intro h
    rcases hρ.sides d _ (hρ.label O).2 h with h' | h'
    · rw [hρ.rot_symm] at h'
      exact Or.inr (hinj (Subtype.ext h').symm)
    · exact Or.inl (hinj (Subtype.ext h').symm)
  · rintro (rfl | rfl)
    · exact hρ.edge d
    · have h := hρ.edge (R.rev d)
      change (R.rev d).1.1 ⊆ closure (ρ (R.rev d)) at h
      change d.1.1 ⊆ closure (ρ (R.rev d))
      rw [hR.rev_eq] at h ⊢
      exact h

/-- **Incidence (4).** A vertex lies in the closure of the region of a face orbit exactly when it
is the vertex of a dart in the orbit. -/
theorem vertex_mem_closure_iff [ConnectedSpace S] (hS : IsClosedSurface S) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) (hρ : IsCornerLabel Γ γ R ρ) (hc : R.Connected)
    (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v) (hne : Γ.E.Nonempty)
    (hcount : Γ.E.ncard + 2 ≤ Γ.V.ncard + Γ.R.ncard) (O : R.Faces) {v : S} (hv : v ∈ Γ.V) :
    v ∈ closure (hρ.label O).1 ↔ ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ R.faceOf d = O := by
  have hinj := (hρ.label_bijective hS hγ hR hc hV hne hcount).1
  constructor
  · intro h
    obtain ⟨d, rfl⟩ := hV v hv
    obtain ⟨d', hd', h'⟩ := hρ.all _ (hρ.label O).2 d h
    exact ⟨d', hd', hinj (Subtype.ext h'.symm)⟩
  · rintro ⟨d, rfl, rfl⟩
    exact hρ.closure_vertex d

/-- **Lemma 3 of the proof of VI (5.7), given the corners.** Let `Γ` be a drawing in the sphere
that misses the point at infinity and has an edge, with a connected rotation `R` on its darts
whose corner regions `ρ` fit together along the edges. Then the face orbits correspond one to one
with the regions, and the incidence rules (3) and (4) hold. -/
theorem sphere_faceOrbits {Γ : Drawing (OnePoint EuclideanPlane)} {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} {ρ : DrawingDart Γ → Set (OnePoint EuclideanPlane)}
    (hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ Γ.U) (hγ : EdgePar Γ γ)
    (hR : IsDrawingRotation Γ γ R) (hρ : IsCornerLabel Γ γ R ρ) (hc : R.Connected)
    (hV : ∀ v ∈ Γ.V, ∃ d : DrawingDart Γ, dartVertex γ d = v) (hne : Γ.E.Nonempty) :
    Function.Bijective hρ.label ∧
    (∀ (O : R.Faces) (d : DrawingDart Γ),
      d.1.1 ⊆ closure (hρ.label O).1 ↔ R.faceOf d = O ∨ R.faceOf (R.rev d) = O) ∧
    (∀ (O : R.Faces), ∀ v ∈ Γ.V,
      v ∈ closure (hρ.label O).1 ↔ ∃ d : DrawingDart Γ, dartVertex γ d = v ∧ R.faceOf d = O) := by
  have hsph := GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩
  have : ConnectedSpace (OnePoint EuclideanPlane) := hsph.2
  have hVne : Γ.V.Nonempty := by
    obtain ⟨e, he⟩ := hne
    exact ⟨_, dartVertex_mem hγ (⟨(e, false), he⟩ : DrawingDart Γ)⟩
  have hcount := sphere_euler_lower_bound hinf hVne
  exact ⟨hρ.label_bijective hsph.1 hγ hR hc hV hne hcount,
    fun O d => hρ.edge_subset_closure_iff hsph.1 hγ hR hc hV hne hcount O d,
    fun O v hv => hρ.vertex_mem_closure_iff hsph.1 hγ hR hc hV hne hcount O hv⟩

end IsCornerLabel

end GraphMinor.GM06
