module

public import GraphMinor.Crossing.DefsReplace
import GraphMinor.Crossing.CutSec2Fan

/-!
# Reachability for the recorded-component search

In a valid replacement, the recorded component has the recorded boundary as its whole
neighbourhood. Each boundary endpoint has a neighbour in that component. Joining those
two neighbours inside the component gives a walk whose inner vertices belong to it.
Thus the search program's reachability condition follows from replacement validity.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

private theorem walk_restrict {V : Type*} {G : SimpleGraph V} (S : Set V) :
    ∀ {u v} (W : G.Walk u v), (∀ x ∈ W.support, x ∈ S) →
      ∃ W' : (HP25.restrict G S).Walk u v, W'.support = W.support := by
  intro u v W
  induction W with
  | nil => intro _; exact ⟨.nil, rfl⟩
  | @cons u x v hux W ih =>
    intro hS
    obtain ⟨W', hW'⟩ := ih (fun y hy => hS y (List.mem_cons_of_mem _ hy))
    have hu : u ∈ S := hS u (Walk.start_mem_support _)
    have hx : x ∈ S := hS x (List.mem_cons_of_mem _ (Walk.start_mem_support W))
    exact ⟨.cons ⟨hux, hu, hx⟩ W', by exact congrArg (List.cons u) hW'⟩

/-- The recorded component joins any two boundary vertices, with only component vertices
in the interior. The search graph is restricted to the component and boundary. -/
theorem liftReplacementReach {V : Type*} {r : ReplRecord V} {D : List V}
    (hvalid : r.IsValid D) {p q : V} (hp : p ∈ r.boundary) (hq : q ∈ r.boundary) :
    ∃ W : (HP25.restrict r.graph (r.rep ∪ (r.boundary : Set V))).Walk p q,
      ∀ x ∈ W.support, x ≠ p → x ≠ q → x ∈ r.rep := by
  have hcomp := hvalid.2.2.2.2.2
  have hnbhd := hvalid.2.2.2.2.1 r.rep hcomp
  have hp' : p ∈ nbhd r.graph r.rep := hnbhd.symm ▸ hp
  have hq' : q ∈ nbhd r.graph r.rep := hnbhd.symm ▸ hq
  obtain ⟨a, ha, hap⟩ := hp'.2
  obtain ⟨b, hb, hbq⟩ := hq'.2
  obtain ⟨W, hW⟩ := hcomp.2.1.2 a ha b hb
  let U : Set V := r.rep ∪ {p, q}
  have hpU : p ∈ U := Or.inr (by simp)
  have hqU : q ∈ U := Or.inr (by simp)
  have hpa : ReachIn r.graph U p a := ReachIn.of_adj hap.symm hpU (Or.inl ha)
  have hab : ReachIn r.graph U a b := ⟨W, fun x hx => Or.inl (hW x hx)⟩
  have hbq' : ReachIn r.graph U b q := ReachIn.of_adj hbq (Or.inl hb) hqU
  obtain ⟨Z, hZ⟩ := (hpa.trans hab).trans hbq'
  have hS : ∀ x ∈ Z.support, x ∈ r.rep ∪ (r.boundary : Set V) := by
    intro x hx
    rcases hZ x hx with h | h
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr (h ▸ hp)
      · exact Or.inr ((Set.mem_singleton_iff.mp h) ▸ hq)
  obtain ⟨Z', hZ'⟩ := walk_restrict _ Z hS
  refine ⟨Z', ?_⟩
  intro x hx hxp hxq
  rw [hZ'] at hx
  rcases hZ x hx with h | h
  · exact h
  · rcases h with h | h
    · exact False.elim (hxp h)
    · exact False.elim (hxq (Set.mem_singleton_iff.mp h))

end GraphMinor.Compute.Crossing
