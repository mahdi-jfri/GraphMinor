module

public import GraphMinor.Compute.CrossingLiftVertexBound
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Searching below an inferred vertex bound

The lift program infers an array size from the recorded labels. A walk whose labels all
lie below that size can be read as a walk on the smaller finite type. Inclusion into the
ambient type preserves its vertex list. This lets the existing finite-graph search run
without a register holding the ambient vertex count.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph

/-- A walk using only labels below `M` is a walk in the graph pulled back to `Fin M`.
Its vertex list is unchanged by the inclusion back into the ambient finite type. -/
theorem liftBoundedWalk {N M : ℕ} (G : SimpleGraph (Fin N)) (hMN : M ≤ N) :
    ∀ {u v : Fin N} (W : G.Walk u v) (u' v' : Fin M),
      Fin.castLE hMN u' = u → Fin.castLE hMN v' = v →
      (∀ x ∈ W.support, x.val < M) →
      ∃ W' : (G.comap (Fin.castLE hMN)).Walk u' v',
        W'.support.map (Fin.castLE hMN) = W.support := by
  intro u v W
  induction W with
  | nil =>
    intro u' v' hu hv _
    have huv : u' = v' := Fin.ext (congrArg (fun x : Fin N => x.val) (hu.trans hv.symm))
    subst v'
    exact ⟨.nil, by simp [hu]⟩
  | @cons u x v hux W ih =>
    intro u' v' hu hv hbound
    have hx : x.val < M := hbound x (List.mem_cons_of_mem _ (Walk.start_mem_support W))
    let x' : Fin M := ⟨x.val, hx⟩
    have hx' : Fin.castLE hMN x' = x := Fin.ext rfl
    obtain ⟨W', hW'⟩ := ih x' v' hx' hv
      (fun y hy => hbound y (List.mem_cons_of_mem _ hy))
    have hadj : (G.comap (Fin.castLE hMN)).Adj u' x' := by
      change G.Adj (Fin.castLE hMN u') (Fin.castLE hMN x')
      rw [hu, hx']
      exact hux
    exact ⟨.cons hadj W', by simp only [Walk.support_cons, List.map_cons, hW', hu]⟩

end GraphMinor.Compute.Crossing
