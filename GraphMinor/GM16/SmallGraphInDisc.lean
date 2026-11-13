module

public import GraphMinor.GM16.SmallBoundaryCurves
public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic
import GraphMinor.Surface.ArcTools

/-!
# Drawing a small torso inside its arrangement disc

The last geometric step in the torso assembly of XVI (1.3), page 51,
draws the edges of a society with at most three boundary vertices inside
its disc. We choose the two ends of each edge and apply the finite curve
construction. Injectivity of the prescribed vertex map then verifies
the incidence conditions, including loops and parallel edges.
-/

public section
namespace GraphMinor.GM16
open Set Graph Surface
universe u v w

/-- A finite graph with at most three vertices can be drawn inside a
closed disc with any prescribed distinct boundary positions for its
vertices. Its edge curves meet the disc boundary only at those vertices. -/
theorem exists_small_graph_edges_in_disc
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α : Type u} {β : Type v} (H : Graph α β)
    (hV : V(H).Finite) (hE : E(H).Finite) (hcard : V(H).ncard ≤ 3)
    {D : Set S} (hD : IsClosedDisc D) (ν : α → S) (hν : InjOn ν V(H))
    (hνBd : ∀ x ∈ V(H), ν x ∈ discBd D) :
    ∃ edgeOf : β → Set S,
      (∀ e ∈ E(H), ∀ x y, H.IsLink e x y → x ≠ y →
        IsLineWithEnds (edgeOf e) (ν x) (ν y)) ∧
      (∀ e ∈ E(H), ∀ x, H.IsLoopAt e x → IsOArc (edgeOf e) ∧ ν x ∈ edgeOf e) ∧
      (∀ e ∈ E(H), ∀ f ∈ E(H), e ≠ f → edgeOf e ∩ edgeOf f ⊆ ν '' V(H)) ∧
      (∀ e ∈ E(H), ∀ x ∈ V(H), ν x ∈ edgeOf e → H.Inc e x) ∧
      (∀ e ∈ E(H), edgeOf e ⊆ D) ∧
      (∀ e ∈ E(H), edgeOf e ∩ discBd D ⊆ ν '' V(H)) := by
  classical
  let P : Set S := ν '' V(H)
  have hP : P.Finite := hV.image ν
  have hPcard : P.ncard ≤ 3 := by rw [hν.ncard_image]; exact hcard
  have hPb : P ⊆ discBd D := by rintro _ ⟨x, hx, rfl⟩; exact hνBd x hx
  obtain ⟨φ⟩ := hD
  let z₀ : S := (φ ⟨0, by simp [ClosedUnitDisc]⟩).1
  choose x y hxy using fun e : E(H) => H.exists_isLink_of_mem_edgeSet e.2
  let a : β → S := fun e => if he : e ∈ E(H) then ν (x ⟨e, he⟩) else z₀
  let b : β → S := fun e => if he : e ∈ E(H) then ν (y ⟨e, he⟩) else z₀
  have ha : ∀ e ∈ E(H), a e ∈ P := by
    intro e he
    simp only [a, dite_eq_left he]
    exact mem_image_of_mem ν (hxy ⟨e, he⟩).left_mem
  have hb : ∀ e ∈ E(H), b e ∈ P := by
    intro e he
    simp only [b, dite_eq_left he]
    exact mem_image_of_mem ν (hxy ⟨e, he⟩).right_mem
  have hDisc : IsClosedDisc D := ⟨φ⟩
  obtain ⟨J, hJ, hJJ⟩ := exists_small_boundary_curves hDisc hP hPcard hPb a b E(H) hE
    (fun e he => ⟨ha e he, hb e he⟩)
  have hEnds : ∀ e (he : e ∈ E(H)) u v, H.IsLink e u v →
      (a e = ν u ∧ b e = ν v) ∨ (a e = ν v ∧ b e = ν u) := by
    intro e he u v huv
    simp only [a, b, dite_eq_left he]
    rcases (hxy ⟨e, he⟩).eq_and_eq_or_eq_and_eq huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  refine ⟨J, ?_, ?_, hJJ, ?_, ?_, ?_⟩
  · intro e he u v huv hne
    have hνne : ν u ≠ ν v := fun heq => hne (hν huv.left_mem huv.right_mem heq)
    rcases hEnds e he u v huv with ⟨hae, hbe⟩ | ⟨hae, hbe⟩
    · have hne' : a e ≠ b e := by rw [hae, hbe]; exact hνne
      simpa only [hae, hbe] using (hJ e he).1 hne'
    · have hne' : a e ≠ b e := by rw [hae, hbe]; exact fun heq => hνne heq.symm
      exact (hae ▸ hbe ▸ (hJ e he).1 hne').symm
  · intro e he u huu
    have haeu : a e = ν u := (hEnds e he u u huu).elim And.left And.left
    have hbeu : b e = ν u := (hEnds e he u u huu).elim And.right And.right
    have heq : a e = b e := haeu.trans hbeu.symm
    simpa only [haeu] using (hJ e he).2.1 heq
  · intro e he u hu hmem
    have hpoint : ν u ∈ ({a e, b e} : Set S) :=
      (hJ e he).2.2.2.1 ▸ And.intro hmem (mem_image_of_mem ν hu)
    simp only [a, b, dite_eq_left he] at hpoint
    rcases hpoint with hpoint | hpoint
    · have hueq : u = x ⟨e, he⟩ := hν hu (hxy ⟨e, he⟩).left_mem hpoint
      exact hueq ▸ (hxy ⟨e, he⟩).inc_left
    · have hueq : u = y ⟨e, he⟩ := hν hu (hxy ⟨e, he⟩).right_mem hpoint
      exact hueq ▸ (hxy ⟨e, he⟩).inc_right
  · intro e he
    exact (hJ e he).2.2.1
  · intro e he q hq
    have hEndsQ : q ∈ ({a e, b e} : Set S) := (hJ e he).2.2.2.2 ▸ hq
    rcases hEndsQ with rfl | rfl
    · exact ha e he
    · exact hb e he

end GraphMinor.GM16
