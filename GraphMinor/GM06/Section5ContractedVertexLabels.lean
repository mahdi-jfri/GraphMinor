module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM11.PaintingFacts
import Mathlib.SetTheory.Cardinal.Embedding
import Mathlib.Logic.Equiv.Basic

/-!
# Live vertex labels after an initial-edge contraction

Reduction 3 of VI (5.7), page 133, retains the initial vertex label
and retires its neighbour. The collapse is injective on the old
drawing with the initial vertex deleted. Exchanging the two labels
therefore proves injectivity on the live labels with the neighbour
removed. Extend this finite injection to the unused labels with
fresh points. Those unused points carry no graph data. The new
live labels represent exactly the contracted drawing's vertices.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

private theorem exists_embedding_extending_finite_labels {n : ℕ} {β : Type*} [Infinite β]
    (A : Finset (Fin n)) (f : Fin n → β) (hi : InjOn f (A : Set (Fin n))) :
    ∃ g : Fin n ↪ β, ∀ x ∈ A, g x = f x := by
  classical
  let S := f '' (A : Set (Fin n))
  have hS : S.Finite := A.finite_toSet.image f
  letI : Finite S := hS.to_subtype
  obtain ⟨g, hg⟩ := Fin.Embedding.exists_embedding_disjoint_range_of_add_le_ENat_card
    (n := n) (s := S) (by simp only [ENat.card_eq_top_of_infinite, le_top])
  let h : Fin n → β := fun x => if x ∈ A then f x else g x
  have hhi : Function.Injective h := by
    intro x y hxy
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ A
      · exact hi hx hy (by simpa only [h, hx, hy, ite_true] using hxy)
      · have hxy' : f x = g y := by simpa only [h, hx, hy, ite_true, ite_false] using hxy
        exact False.elim (disjoint_left.mp hg ⟨x, hx, rfl⟩ ⟨y, hxy'.symm⟩)
    · by_cases hy : y ∈ A
      · have hxy' : g x = f y := by simpa only [h, hx, hy, ite_true, ite_false] using hxy
        exact False.elim (disjoint_left.mp hg ⟨y, hy, rfl⟩ ⟨x, hxy'⟩)
      · exact g.injective (by simpa only [h, hx, hy, ite_false] using hxy)
  refine ⟨⟨h, hhi⟩, ?_⟩
  intro x hx
  change h x = f x
  simp only [h, hx, ite_true]

/-- The live labels after a collapse have a full injective vertex
labelling that agrees with the actual collapse on every live label.
Their image is exactly the contracted vertex set and the retained
initial label remains at its fixed cuff point. -/
theorem exists_contracted_live_vertex_labels
    {n k : ℕ} {G G' : Drawing ClosedCylinder} {i : Fin k}
    (vertex : Fin n ↪ ClosedCylinder) (A : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hvertex : ∀ x ∈ A, vertex x ∈ G.V)
    (hcover : ∀ p ∈ G.V, ∃ x ∈ A, vertex x = p)
    (hpoint : vertex a = cylinderM1Point k i)
    {e : Set ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) (vertex b))
    (hvs : vertex b ≠ cylinderM1Point k i)
    (π : C(ClosedCylinder, ClosedCylinder))
    (hfiber : π ⁻¹' {cylinderM1Point k i} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hV : G'.V = π '' G.V) :
    ∃ vertex' : Fin n ↪ ClosedCylinder,
      (∀ x ∈ A.erase b, vertex' x = π (vertex x)) ∧
      G'.V = vertex' '' (A.erase b : Set (Fin n)) ∧
      vertex' a = cylinderM1Point k i := by
  classical
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  have hJV : J.V = G.V \ {cylinderM1Point k i} := induceDrawing_V G sdiff_subset
  have hJi : InjOn π J.U := injOn_deleted_initial_vertex_drawing hval hl hvs hfiber hi
  have hπa : π (vertex a) = cylinderM1Point k i := by
    have hx : vertex a ∈ closure e := hpoint.symm ▸
      (show cylinderM1Point k i ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ _).1
    have hh : vertex a ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hh
  have hπb : π (vertex b) = cylinderM1Point k i := by
    have hx : vertex b ∈ closure e :=
      (show vertex b ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem _ rfl).1
    have hh : vertex b ∈ π ⁻¹' {cylinderM1Point k i} := hfiber.symm ▸ hx
    exact hh
  let sw := Equiv.swap a b
  have hsw : ∀ x ∈ A.erase b, sw x ∈ A ∧ sw x ≠ a := by
    intro x hx
    obtain ⟨hxb, hxA⟩ := Finset.mem_erase.mp hx
    by_cases hxa : x = a
    · subst x
      simpa only [sw, Equiv.swap_apply_left] using And.intro hb hab.symm
    · simpa only [sw, Equiv.swap_apply_of_ne_of_ne hxa hxb] using And.intro hxA hxa
  have hπsw : ∀ x ∈ A.erase b, π (vertex (sw x)) = π (vertex x) := by
    intro x hx
    have hxb := (Finset.mem_erase.mp hx).1
    by_cases hxa : x = a
    · subst x
      simp only [sw, Equiv.swap_apply_left, hπa, hπb]
    · simp only [sw, Equiv.swap_apply_of_ne_of_ne hxa hxb]
  have hswU : ∀ x ∈ A.erase b, vertex (sw x) ∈ J.U := by
    intro x hx
    obtain ⟨hxA, hxa⟩ := hsw x hx
    apply J.V_subset_U
    rw [hJV]
    refine ⟨hvertex _ hxA, ?_⟩
    intro heq
    exact hxa (vertex.injective (heq.trans hpoint.symm))
  have hLiveInj : InjOn (fun x => π (vertex x)) (A.erase b : Set (Fin n)) := by
    intro x hx y hy hxy
    have hsxy : π (vertex (sw x)) = π (vertex (sw y)) :=
      (hπsw x hx).trans (hxy.trans (hπsw y hy).symm)
    exact sw.injective (vertex.injective (hJi (hswU x hx) (hswU y hy) hsxy))
  letI : Infinite ClosedCylinder := Set.infinite_univ_iff.mp
    ((infinite_of_isOArc isOArc_cylinderCuff1).mono (Set.subset_univ _))
  obtain ⟨vertex', hv⟩ := exists_embedding_extending_finite_labels (A.erase b)
    (fun x => π (vertex x)) hLiveInj
  have ha' : a ∈ A.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
  refine ⟨vertex', hv, ?_, (hv a ha').trans hπa⟩
  rw [hV]
  apply subset_antisymm
  · rintro z ⟨p, hp, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hcover p hp
    by_cases hxb : x = b
    · subst x
      exact ⟨a, ha', (hv a ha').trans (hπa.trans hπb.symm)⟩
    · have hx' : x ∈ A.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
      exact ⟨x, hx', hv x hx'⟩
  · rintro z ⟨x, hx, rfl⟩
    rw [hv x hx]
    exact mem_image_of_mem π (hvertex x (Finset.mem_erase.mp hx).2)

end GraphMinor.GM06
