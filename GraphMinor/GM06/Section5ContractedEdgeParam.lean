module

public import GraphMinor.GM06.Section5CollapseBoundaryCrossings
public import GraphMinor.GM11.Rotation
import GraphMinor.GM06.Section3Dual

/-!
# Directed ends of surviving contracted edges

For Lemma 8 of our proof of VI (5.7), page 133 (outlined in
`Alg57Algorithm.lean`),
the surviving edges retain their directions and both ends of a
loop remain distinct. The collapse is injective on each surviving
open edge and on their union. Taking edge images therefore gives
an edge bijection and explicit image parametrizations.

At a fixed vertex away from the collapsed closed edge, every new
directed end comes from exactly one old directed end. Its spoke
is the image of the old spoke. These facts let a retained rotation
use the same directed labels in the two drawings.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- An edge parametrization includes both ends in the closed edge,
and its complete range is exactly that closure. -/
theorem range_eq_closure_of_edgePar {S : Type*} [TopologicalSpace S] [T2Space S]
    {G : Drawing S} {γ : Set S → I → S} (hγ : EdgePar G γ) {f : Set S} (hf : f ∈ G.E) :
    range (γ f) = closure f := by
  have hc : closure (Ioo (0 : I) 1) = univ := by
    rw [closure_Ioo (zero_ne_one : (0 : I) ≠ 1)]
    ext t
    exact iff_true_intro t.property
  calc
    range (γ f) = γ f '' univ := (image_univ (f := γ f)).symm
    _ = γ f '' closure (Ioo (0 : I) 1) := congrArg (image (γ f)) hc.symm
    _ = closure (γ f '' Ioo 0 1) :=
      ((hγ.cont f hf).isClosedMap.closure_image_eq_of_continuous (hγ.cont f hf) _).symm
    _ = closure f := congrArg closure (hγ.image f hf)

/-- Taking the images of all edges other than the contracted edge
is injective, since their open points avoid its closed fibre. -/
theorem image_edges_injective_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] {G : Drawing S}
    {e : Set S} {s v : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hi : InjOn π (closure e)ᶜ) :
    InjOn (image π) (G.E \ {e}) := by
  have hsub : ∀ f ∈ G.E \ {e}, ∀ g ∈ G.E \ {e}, π '' f = π '' g → f ⊆ g := by
    intro f hf g hg heq x hx
    have hfx : x ∉ closure e :=
      disjoint_left.mp (disjoint_open_edge_closed_link hl hvs hf.1 hf.2) hx
    obtain ⟨y, hy, hyx⟩ := heq ▸ mem_image_of_mem π hx
    have hgy : y ∉ closure e :=
      disjoint_left.mp (disjoint_open_edge_closed_link hl hvs hg.1 hg.2) hy
    exact hi hgy hfx hyx ▸ hy
  intro f hf g hg heq
  exact subset_antisymm (hsub f hf g hg heq) (hsub g hg f hf heq.symm)

/-- The exact retained edge-image set gives a bijection, with its
forward map equal to the actual geometric image operation. -/
theorem exists_edge_equiv_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] {G G' : Drawing S}
    {e : Set S} {s v : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hi : InjOn π (closure e)ᶜ)
    (hE : G'.E = (image π) '' (G.E \ {e})) :
    ∃ η : {a : Set S // a ∈ G.E ∧ a ≠ e} ≃ G'.E, ∀ a, (η a).val = π '' a.val := by
  let f : {a : Set S // a ∈ G.E ∧ a ≠ e} → G'.E := fun a => ⟨π '' a.val, hE ▸ mem_image_of_mem (image π) a.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact image_edges_injective_of_closed_edge_collapse hl hvs π hi a.property b.property
      (congrArg Subtype.val hab)
  have hfs : Function.Surjective f := by
    intro a
    have hh : a.val ∈ (image π) '' (G.E \ {e}) := by
      rw [← hE]
      exact a.property
    obtain ⟨b, hb, hba⟩ := hh
    exact ⟨⟨b, hb⟩, Subtype.ext hba⟩
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun _ => rfl⟩

/-- Surviving edges have actual image parametrizations. Their
orientations are inherited from the old directed intervals. -/
theorem exists_edgePar_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] {G G' : Drawing S}
    {e : Set S} {s v : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : C(S, S)) (hi : InjOn π (closure e)ᶜ)
    (hV : G'.V = π '' G.V) (hE : G'.E = (image π) '' (G.E \ {e}))
    {γ : Set S → I → S} (hγ : EdgePar G γ) :
    ∃ γ' : Set S → I → S, EdgePar G' γ' ∧
      ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t) := by
  classical
  obtain ⟨η, hη⟩ := exists_edge_equiv_of_closed_edge_collapse hl hvs π hi hE
  let γ' : Set S → I → S := fun f t => if hf : f ∈ G'.E then
    π (γ (η.symm ⟨f, hf⟩).val t) else π s
  have hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t) := by
    intro f hf hfe t
    let a : {a : Set S // a ∈ G.E ∧ a ≠ e} := ⟨f, hf, hfe⟩
    have hm : π '' f ∈ G'.E := hE ▸ mem_image_of_mem (image π) a.property
    have heq : (⟨π '' f, hm⟩ : G'.E) = η a := Subtype.ext (hη a).symm
    simp only [γ', dite_eq_left hm, heq, η.symm_apply_apply]
    rfl
  refine ⟨γ', ⟨?_, ?_, ?_, ?_, ?_⟩, hpar⟩
  · intro f hf
    let a := η.symm ⟨f, hf⟩
    have he : π '' a.val = f := (hη a).symm.trans
      (congrArg Subtype.val (η.apply_symm_apply ⟨f, hf⟩))
    rw [← he]
    exact (π.continuous.comp (hγ.cont a.val a.property.1)).congr
      (fun t => (hpar a.val a.property.1 a.property.2 t).symm)
  · intro f hf
    let a := η.symm ⟨f, hf⟩
    have he : π '' a.val = f := (hη a).symm.trans
      (congrArg Subtype.val (η.apply_symm_apply ⟨f, hf⟩))
    rw [← he, hpar a.val a.property.1 a.property.2 0, hV]
    exact mem_image_of_mem π (hγ.zero a.val a.property.1)
  · intro f hf
    let a := η.symm ⟨f, hf⟩
    have he : π '' a.val = f := (hη a).symm.trans
      (congrArg Subtype.val (η.apply_symm_apply ⟨f, hf⟩))
    rw [← he, hpar a.val a.property.1 a.property.2 1, hV]
    exact mem_image_of_mem π (hγ.one a.val a.property.1)
  · intro f hf t ht u hu htu
    let a := η.symm ⟨f, hf⟩
    have he : π '' a.val = f := (hη a).symm.trans
      (congrArg Subtype.val (η.apply_symm_apply ⟨f, hf⟩))
    rw [← he, hpar a.val a.property.1 a.property.2 t,
      hpar a.val a.property.1 a.property.2 u] at htu
    have hdis := disjoint_open_edge_closed_link hl hvs a.property.1 a.property.2
    apply hγ.inj a.val a.property.1 ht hu
    apply hi
    · exact disjoint_left.mp hdis ((hγ.image a.val a.property.1).subset (mem_image_of_mem (γ a.val) ht))
    · exact disjoint_left.mp hdis ((hγ.image a.val a.property.1).subset (mem_image_of_mem (γ a.val) hu))
    · exact htu
  · intro f hf
    let a := η.symm ⟨f, hf⟩
    have he : π '' a.val = f := (hη a).symm.trans
      (congrArg Subtype.val (η.apply_symm_apply ⟨f, hf⟩))
    rw [← he]
    have hh : γ' (π '' a.val) = π ∘ γ a.val := funext
      (hpar a.val a.property.1 a.property.2)
    rw [hh]
    calc
      (π ∘ γ a.val) '' Ioo 0 1 = π '' (γ a.val '' Ioo 0 1) :=
        (image_image π (γ a.val) _).symm
      _ = π '' a.val := congrArg (image π) (hγ.image a.val a.property.1)

/-- At a vertex outside the collapsed closed edge, the
actual directed ends before and after contraction correspond one
to one, with unchanged Boolean end indices and exact image spokes. -/
theorem exists_halfedge_equiv_of_closed_edge_collapse_mapped
    {S : Type*} [TopologicalSpace S] [T2Space S] {G G' : Drawing S}
    {e : Set S} {s v w : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hE : G'.E = (image π) '' (G.E \ {e}))
    {γ γ' : Set S → I → S} (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (hw : w ∉ closure e) :
    ∃ η : halfEdges G γ w ≃ halfEdges G' γ' (π w),
      (∀ a, (η a).val = (π '' a.val.1, a.val.2)) ∧
      ∀ a t, spoke γ' (η a).val t = π (spoke γ a.val t) := by
  have hne : ∀ a : halfEdges G γ w, a.val.1 ≠ e := by
    intro a hae
    apply hw
    have hh : w ∈ range (γ e) := ⟨endOf a.val.2, hae ▸ a.property.2⟩
    rwa [range_eq_closure_of_edgePar hγ hl.edge_mem] at hh
  let f : halfEdges G γ w → halfEdges G' γ' (π w) := fun a =>
    ⟨(π '' a.val.1, a.val.2),
      hE ▸ mem_image_of_mem (image π) ⟨a.property.1, hne a⟩,
      (hpar a.val.1 a.property.1 (hne a) _).trans
        (congrArg π a.property.2)⟩
  have hfi : Function.Injective f := by
    intro a b hab
    have he : π '' a.val.1 = π '' b.val.1 := congrArg (fun z => z.val.1) hab
    have hb : a.val.2 = b.val.2 := congrArg (fun z => z.val.2) hab
    have hEdge := image_edges_injective_of_closed_edge_collapse hl hvs π hi
      ⟨a.property.1, hne a⟩ ⟨b.property.1, hne b⟩ he
    exact Subtype.ext (Prod.ext hEdge hb)
  have hfs : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, hab⟩ := hE ▸ b.property.1
    have hpoint : π (γ a (endOf b.val.2)) = π w := by
      rw [← hpar a ha.1 ha.2, hab]
      exact b.property.2
    have hwπ : π w ≠ s := by
      intro he
      exact hw (hfibre ▸ he)
    have hx : γ a (endOf b.val.2) ∉ closure e := by
      intro hx
      have he : π (γ a (endOf b.val.2)) = s :=
        show γ a (endOf b.val.2) ∈ π ⁻¹' {s} from hfibre.symm ▸ hx
      exact hwπ (hpoint.symm.trans he)
    have hend : γ a (endOf b.val.2) = w := hi hx hw hpoint
    let a' : halfEdges G γ w := ⟨(a, b.val.2), ha.1, hend⟩
    exact ⟨a', Subtype.ext (Prod.ext hab rfl)⟩
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun _ => rfl, ?_⟩
  intro a t
  exact hpar a.val.1 a.property.1 (hne a) (halfPar a.val.2 t)

/-- At an unchanged vertex outside the collapsed closed edge, the
actual directed ends before and after contraction correspond one
to one, with unchanged Boolean end indices and exact image spokes. -/
theorem exists_halfedge_equiv_of_closed_edge_collapse
    {S : Type*} [TopologicalSpace S] [T2Space S] {G G' : Drawing S}
    {e : Set S} {s v w : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hE : G'.E = (image π) '' (G.E \ {e}))
    {γ γ' : Set S → I → S} (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t))
    (hw : w ∉ closure e) (hπw : π w = w) :
    ∃ η : halfEdges G γ w ≃ halfEdges G' γ' w,
      (∀ a, (η a).val = (π '' a.val.1, a.val.2)) ∧
      ∀ a t, spoke γ' (η a).val t = π (spoke γ a.val t) := by
  have hex := exists_halfedge_equiv_of_closed_edge_collapse_mapped
    hl hvs π hfibre hi hE hγ hpar hw
  rw [hπw] at hex
  exact hex

/-- At the collapsed vertex, the surviving directed ends are exactly
the old ends at the two endpoints, with the contracted edge's two
ends removed. The equivalence keeps the Boolean end and maps the
spoke by the actual collapse. This is the source-incidence part of
Lemma 8, including loops based at the old neighbour. -/
theorem exists_contracted_source_halfedge_equiv
    {S : Type*} [TopologicalSpace S] [T2Space S] {G G' : Drawing S}
    {e : Set S} {s v : S} (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s)
    (π : S → S) (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hE : G'.E = (image π) '' (G.E \ {e}))
    {γ γ' : Set S → I → S} (hγ : EdgePar G γ)
    (hpar : ∀ f ∈ G.E, f ≠ e → ∀ t, γ' (π '' f) t = π (γ f t)) :
    ∃ η : ({a : halfEdges G γ s // a.val.1 ≠ e} ⊕
        {a : halfEdges G γ v // a.val.1 ≠ e}) ≃ halfEdges G' γ' s,
      (∀ a, (η (.inl a)).val = (π '' a.val.val.1, a.val.val.2)) ∧
      (∀ a, (η (.inr a)).val = (π '' a.val.val.1, a.val.val.2)) ∧
      (∀ a t, spoke γ' (η (.inl a)).val t = π (spoke γ a.val.val t)) ∧
      ∀ a t, spoke γ' (η (.inr a)).val t = π (spoke γ a.val.val t) := by
  have hscl : s ∈ closure e :=
    (show s ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert s {v}).1
  have hvcl : v ∈ closure e :=
    (show v ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem s rfl).1
  have hπs : π s = s := show s ∈ π ⁻¹' {s} from hfibre.symm ▸ hscl
  have hπv : π v = s := show v ∈ π ⁻¹' {s} from hfibre.symm ▸ hvcl
  let A := {a : halfEdges G γ s // a.val.1 ≠ e}
  let B := {a : halfEdges G γ v // a.val.1 ≠ e}
  let endMap : ∀ w, π w = s → {a : halfEdges G γ w // a.val.1 ≠ e} → halfEdges G' γ' s :=
    fun w hw a => ⟨(π '' a.val.val.1, a.val.val.2),
      hE ▸ mem_image_of_mem (image π) ⟨a.val.property.1, a.property⟩,
      (hpar a.val.val.1 a.val.property.1 a.property _).trans
        ((congrArg π a.val.property.2).trans hw)⟩
  let f : A ⊕ B → halfEdges G' γ' s := Sum.elim (endMap s hπs) (endMap v hπv)
  have hpair {x y : S} (a : halfEdges G γ x) (b : halfEdges G γ y)
      (ha : a.val.1 ≠ e) (hb : b.val.1 ≠ e)
      (heq : (π '' a.val.1, a.val.2) = (π '' b.val.1, b.val.2)) : a.val = b.val := by
    have he := congrArg (fun p : Set S × Bool => p.1) heq
    have hb' := congrArg (fun p : Set S × Bool => p.2) heq
    exact Prod.ext (image_edges_injective_of_closed_edge_collapse hl hvs π hi
      ⟨a.property.1, ha⟩ ⟨b.property.1, hb⟩ he) hb'
  have hend {x y : S} (a : halfEdges G γ x) (b : halfEdges G γ y)
      (heq : a.val = b.val) : x = y :=
    a.property.2.symm.trans ((congrArg (fun p : Set S × Bool => γ p.1 (endOf p.2)) heq).trans b.property.2)
  have hfi : Function.Injective f := by
    intro a b hab
    have hdata := congrArg Subtype.val hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        change (π '' a.val.val.1, a.val.val.2) = (π '' b.val.val.1, b.val.val.2) at hdata
        exact congrArg Sum.inl (Subtype.ext (Subtype.ext (hpair a.val b.val a.property b.property hdata)))
      | inr b =>
        change (π '' a.val.val.1, a.val.val.2) = (π '' b.val.val.1, b.val.val.2) at hdata
        exact False.elim (hvs (hend a.val b.val (hpair a.val b.val a.property b.property hdata)).symm)
    | inr a =>
      cases b with
      | inl b =>
        change (π '' a.val.val.1, a.val.val.2) = (π '' b.val.val.1, b.val.val.2) at hdata
        exact False.elim (hvs (hend a.val b.val (hpair a.val b.val a.property b.property hdata)))
      | inr b =>
        change (π '' a.val.val.1, a.val.val.2) = (π '' b.val.val.1, b.val.val.2) at hdata
        exact congrArg Sum.inr (Subtype.ext (Subtype.ext (hpair a.val b.val a.property b.property hdata)))
  have hfs : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, hab⟩ := hE ▸ b.property.1
    let q := γ a (endOf b.val.2)
    have hπq : π q = s := by
      rw [← hpar a ha.1 ha.2, hab]
      exact b.property.2
    have hqcl : q ∈ closure e := hfibre ▸ hπq
    have hqV : q ∈ G.V := by
      cases hb : b.val.2
      · simpa only [q, endOf, hb, Bool.false_eq_true, ite_false] using hγ.zero a ha.1
      · simpa only [q, endOf, hb, ite_true] using hγ.one a ha.1
    have hqends : q ∈ ({s, v} : Set S) := hl.2.2.2 ▸ ⟨hqcl, hqV⟩
    rcases hqends with hqs | hqv
    · let a' : halfEdges G γ s := ⟨(a, b.val.2), ha.1, hqs⟩
      exact ⟨.inl ⟨a', ha.2⟩, Subtype.ext (Prod.ext hab rfl)⟩
    · let a' : halfEdges G γ v := ⟨(a, b.val.2), ha.1, hqv⟩
      exact ⟨.inr ⟨a', ha.2⟩, Subtype.ext (Prod.ext hab rfl)⟩
  refine ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro a t
    exact hpar a.val.val.1 a.val.property.1 a.property (halfPar a.val.val.2 t)
  · intro a t
    exact hpar a.val.val.1 a.val.property.1 a.property (halfPar a.val.val.2 t)

end GraphMinor.GM06
