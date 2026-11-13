module

public import GraphMinor.Surface.Defs
public import GraphMinor.GM05.CopyContractionClasses
import GraphMinor.GM19.Section6Minor
import GraphMinor.GM19.Section6a

/-!
# The vertex classes of drawing contraction

The drawing contraction joins ends of selected edges. The abstract
contraction uses walks along those edges. These relations agree:
a pair of distinct ends is a link, and an equal pair is reflexive.
Thus the point identifications made by the surface construction are
exactly the abstract contraction classes used in GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface Relation

private theorem contraction_reach_symm {α β : Type*} (G : Graph α β) (C : Set β)
    {x y : α} (h : y∈contractionClass G C x) : x∈contractionClass G C y := by
  change ReflTransGen (fun p q ↦ ∃ e∈C,G.IsLink e p q) y x
  change ReflTransGen (fun p q ↦ ∃ e∈C,G.IsLink e p q) x y at h
  induction h with
  | refl => exact .refl
  | tail h hstep ih =>
    obtain ⟨e,he,hl⟩ := hstep
    exact .head ⟨e,he,hl.symm⟩ ih

/-- Two contraction classes agree exactly when the selected edges
join their starting vertices. -/
theorem contractionClass_eq_iff {α β : Type*} (G : Graph α β) (C : Set β) (x y : α) :
    contractionClass G C x=contractionClass G C y ↔ y∈contractionClass G C x := by
  constructor
  · intro he
    rw [he]
    exact mem_contractionClass_self G C y
  · intro h
    ext z
    constructor
    · intro hz
      exact (contraction_reach_symm G C h).trans hz
    · intro hz
      exact h.trans hz

private theorem drawing_link_of_distinct_ends {S : Type*} [TopologicalSpace S] [T1Space S]
    (D : Drawing S) {e : Set S} (he : e∈D.E) {x y : S}
    (hx : x∈tilde e) (hy : y∈tilde e) (hne : x≠y) : D.toGraph.IsLink e x y := by
  have hxV := (GM19.tilde_eq_inter_V D he ▸ hx).2
  have hyV := (GM19.tilde_eq_inter_V D he ▸ hy).2
  refine ⟨he,hxV,hyV,?_⟩
  rcases D.edge_cond e he with ⟨u,v,huv,hcap,-⟩|⟨u,hcap,-⟩
  · rw [GM19.tilde_eq_inter_V D he,hcap] at hx hy
    rcases hx with rfl|hx <;> rcases hy with rfl|hy
    · exact (hne rfl).elim
    · rw [hy]
      exact hcap
    · rw [hx,pair_comm]
      exact hcap
    · exact (hne (hx.trans hy.symm)).elim
  · rw [GM19.tilde_eq_inter_V D he,hcap] at hx hy
    exact (hne (hx.trans hy.symm)).elim

/-- The geometric endpoint equivalence in the drawing construction
is the reachability relation in the abstract contracted graph. -/
theorem drawing_endpoint_equiv_iff_reach {S : Type*} [TopologicalSpace S] [T1Space S]
    (D : Drawing S) {C : Set (Set S)} (hC : C⊆D.E) (x y : S) :
    EqvGen (fun p q ↦ ∃ e∈C,p∈tilde e ∧ q∈tilde e) x y ↔
      y∈contractionClass D.toGraph C x := by
  constructor
  · intro h
    induction h with
    | rel p q hrel =>
      obtain ⟨e,he,hp,hq⟩ := hrel
      by_cases hpq : p=q
      · subst q
        exact .refl
      · exact ReflTransGen.single ⟨e,he,drawing_link_of_distinct_ends D (hC he) hp hq hpq⟩
    | refl p => exact .refl
    | symm p q h ih => exact contraction_reach_symm D.toGraph C ih
    | trans p q r h h' ih ih' => exact ih.trans ih'
  · intro h
    change ReflTransGen (fun p q ↦ ∃ e∈C,D.toGraph.IsLink e p q) x y at h
    induction h with
    | refl => exact .refl _
    | @tail y z h hstep ih =>
      obtain ⟨e,he,hl⟩ := hstep
      have hp : y∈tilde e := by rw [GM19.tilde_eq_inter_V D (hC he),hl.2.2.2]; exact .inl rfl
      have hq : z∈tilde e := by rw [GM19.tilde_eq_inter_V D (hC he),hl.2.2.2]; exact .inr rfl
      exact .trans _ _ _ ih (.rel _ _ ⟨e,he,hp,hq⟩)

end GraphMinor.GM05
