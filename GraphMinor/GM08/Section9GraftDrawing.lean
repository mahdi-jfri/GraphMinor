module

public import GraphMinor.GM08.Defs
public import GraphMinor.Surface.Defs
public import GraphMinor.GM08.Section11Iso
public import GraphMinor.GM07.Defs
import GraphMinor.GM19.Section6a

/-!
# Drawing facts for the graft simulation in VIII (9.3)

The boundary vertices of a graft drawing are exactly the images of its
roots. Hence their number is the graft index. To apply VII (9.4), orient
each drawing edge by choosing its two ends. Forgetting these choices
later recovers the undirected simulation.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u v w

/-- The boundary vertices of a graft drawing are exactly its drawn roots,
as required by the definition of a graft drawing in VIII, Section 5,
page 262. -/
theorem graftDrawing_boundary_eq {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] [Nonempty S] {G : Graph α β} {T : Set α}
    (gd : GraftDrawing G T S) : gd.drawing.V ∩ bd S = gd.iso.fv '' T := by
  ext x
  constructor
  · rintro ⟨hxV, hxbd⟩
    obtain ⟨v, hv, rfl⟩ := gd.iso.exists_fv hxV
    refine ⟨v, ?_, rfl⟩
    exact (gd.mem_bd_iff v hv).mp (by rwa [← gd.iso.fv_of_mem hv])
  · rintro ⟨v, hv, rfl⟩
    have hvG := gd.T_subset_V hv
    refine ⟨gd.iso.fv_mem hvG, ?_⟩
    rw [gd.iso.fv_of_mem hvG]
    exact (gd.mem_bd_iff v hvG).mpr hv

/-- The number of boundary vertices of a graft drawing is its index.
This identifies the parameters of VIII (9.2) and (9.3). -/
theorem graftDrawing_boundary_ncard {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] [Nonempty S] {G : Graph α β} {T : Set α}
    (gd : GraftDrawing G T S) : (gd.drawing.V ∩ bd S).ncard = T.ncard := by
  rw [graftDrawing_boundary_eq gd]
  exact (gd.iso.fv_injOn.mono gd.T_subset_V).ncard_image

/-- Any drawing can be oriented by choosing the two ends of each edge,
as in the definition of a surface digraph in VII, Section 9, page 242.
The choice does not alter the underlying drawing used in VIII (9.3). -/
theorem exists_surfaceDigraph_of_drawing {S : Type u} [TopologicalSpace S]
    [T1Space S] [Nonempty S] (D : Drawing S) :
    ∃ H : GM07.SurfaceDigraph S, H.G = D := by
  classical
  have hex : ∀ e : D.E, ∃ a b, D.toGraph.IsLink e a b := fun e =>
    D.toGraph.exists_isLink_of_mem_edgeSet e.2
  choose a b hab using hex
  let plus : Set S → S := fun e => if he : e ∈ D.E then a ⟨e, he⟩ else Classical.arbitrary S
  let minus : Set S → S := fun e => if he : e ∈ D.E then b ⟨e, he⟩ else Classical.arbitrary S
  have hp : ∀ e (he : e ∈ D.E), plus e = a ⟨e, he⟩ := by
    intro e he
    simp only [plus, dite_eq_left he]
  have hm : ∀ e (he : e ∈ D.E), minus e = b ⟨e, he⟩ := by
    intro e he
    simp only [minus, dite_eq_left he]
  refine ⟨{
    G := D
    plus := plus
    minus := minus
    plus_mem := fun e he => by rw [hp e he]; exact (hab ⟨e, he⟩).left_mem
    minus_mem := fun e he => by rw [hm e he]; exact (hab ⟨e, he⟩).right_mem
    ends_eq := fun e he => ?_ }, rfl⟩
  rw [hp e he, hm e he, GM19.tilde_eq_inter_V D he]
  exact (hab ⟨e, he⟩).2.2.2.symm

end GraphMinor.GM08
