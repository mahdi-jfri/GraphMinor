module

public import GraphMinor.GM02.Valency
public import GraphMinor.GM02.TopologicalContainment

/-!
# Recognizing a suppressible vertex of valency two

If a vertex of valency two has no loop, exactly two distinct edges are
incident with it, and neither is a loop. Those edges give the suppression
data of II, Section 4. A vertex with a loop and valency two cannot reach
any other vertex. Thus connectivity to an attachment rules out that case.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- A vertex of valency two that carries a loop has no other incident edge. -/
theorem incident_eq_of_loop_of_valency_two {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Finite) {x : α} (hval : valency G x = 2)
    {e : β} (he : G.IsLoopAt e x) {f : β} (hf : G.Inc f x) : f = e := by
  by_contra hfe
  have hpair : ({f, e} : Set β) ⊆ incidentEdges G x := by
    rintro a (rfl | rfl)
    · exact hf
    · exact he.inc
  have hloop : ({e} : Set β) ⊆ loopEdges G x := fun _ h => h ▸ he
  have hi := Set.ncard_le_ncard hpair (incidentEdges_finite hE x)
  have hl := Set.ncard_le_ncard hloop (loopEdges_finite hE x)
  rw [Set.ncard_pair hfe] at hi
  rw [Set.ncard_singleton] at hl
  change (incidentEdges G x).ncard + (loopEdges G x).ncard = 2 at hval
  omega

/-- Connectivity to a different vertex rules out a loop at a vertex of
valency two. Otherwise its only incident edge is that loop, and every
walk beginning there stays at that vertex. -/
theorem not_loop_of_valency_two_of_reachable_ne {α : Type u} {β : Type v}
    {G : Graph α β} (hE : E(G).Finite) {x y : α} (hval : valency G x = 2)
    (hreach : Relation.ReflTransGen G.Adj x y) (hne : x ≠ y) :
    ∀ e, ¬ G.IsLoopAt e x := by
  intro e he
  have hall : ∀ z, G.Adj x z → z = x := by
    rintro z ⟨f, hf⟩
    have hfe := incident_eq_of_loop_of_valency_two hE hval he hf.inc_left
    subst f
    exact (he.eq_of_inc hf.inc_right).symm
  have hyx : y = x := by
    clear hne
    induction hreach with
    | refl => rfl
    | @tail b c _ hbc ih =>
      apply hall c
      exact ih ▸ hbc
  exact hne hyx.symm

/-- Without loops, valency is just the number of incident edges. -/
theorem valency_eq_incidentEdges_of_not_loop {α : Type u} {β : Type v}
    {G : Graph α β} {x : α} (hloop : ∀ e, ¬ G.IsLoopAt e x) :
    valency G x = (incidentEdges G x).ncard := by
  have heq : loopEdges G x = ∅ := Set.eq_empty_iff_forall_notMem.2 hloop
  simp only [valency, heq, Set.ncard_empty, Nat.add_zero]

/-- A loopless vertex of valency two has the suppression data specified
in II, Section 4, page 318. One of its erased edge names is reused for the
replacement edge, so no assumption on the ambient edge-label type is needed. -/
theorem exists_suppressionData_of_valency_two {α : Type u} {β : Type v}
    {G : Graph α β} {x : α} (hval : valency G x = 2)
    (hloop : ∀ e, ¬ G.IsLoopAt e x) :
    ∃ d : SuppressionData G, d.vertex = x ∧ d.fresh = d.first := by
  have hc : (incidentEdges G x).ncard = 2 := by
    rwa [valency_eq_incidentEdges_of_not_loop hloop] at hval
  obtain ⟨e, f, hef, hset⟩ := Set.ncard_eq_two.1 hc
  have he : G.Inc e x := by
    change e ∈ incidentEdges G x
    rw [hset]
    exact Or.inl rfl
  have hf : G.Inc f x := by
    change f ∈ incidentEdges G x
    rw [hset]
    exact Or.inr rfl
  obtain ⟨a, hea⟩ := he
  obtain ⟨b, hfb⟩ := hf
  let d : SuppressionData G := {
    vertex := x
    left := a
    right := b
    first := e
    second := f
    fresh := e
    first_ne_second := hef
    first_link := hea
    second_link := hfb
    vertex_ne_left := fun h => hloop e (h ▸ hea)
    vertex_ne_right := fun h => hloop f (h ▸ hfb)
    incident := by
      intro g hg
      change g ∈ incidentEdges G x at hg
      rwa [hset] at hg
    fresh_notMem := fun h => h.2 (Or.inl rfl) }
  exact ⟨d, rfl, rfl⟩

end GraphMinor.GM02
