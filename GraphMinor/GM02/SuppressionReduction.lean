module

public import GraphMinor.GM02.TopologicalContainment

/-!
# Removing suppressions while keeping a graph property

To find the finite topological patterns in II (4.8), one may first suppress
vertices as long as the desired minor remains. The process terminates
because each suppression removes one vertex. This file proves that
termination argument for any graph property, without assuming that a
suppression preserves the property.
-/

public section

namespace GraphMinor.GM02

open Graph Relation

universe u v

/-- Starting with a finite graph satisfying `P`, repeated suppressions that
keep `P` lead to a graph where no further suppression keeps `P`. Each step
removes one vertex, so strong induction on the vertex count suffices. -/
theorem exists_suppression_minimal {α : Type u} {β : Type v}
    (P : Graph α β → Prop) (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hP : P G) :
    ∃ L : Graph α β, ReflTransGen IsSuppression G L ∧
      V(L).Finite ∧ E(L).Finite ∧ P L ∧
      ∀ d : SuppressionData L, ¬ P d.result := by
  classical
  generalize hn : V(G).ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hstep : ∃ d : SuppressionData G, P d.result
    · obtain ⟨d, hd⟩ := hstep
      have hfinite := d.result_finite hV hE
      have hlt : V(d.result).ncard < n := by
        have heq := d.ncard_vertexSet hV
        omega
      obtain ⟨L, hs, hVL, hEL, hPL, hstop⟩ :=
        ih (V(d.result).ncard) hlt d.result hfinite.1 hfinite.2 hd rfl
      exact ⟨L, (ReflTransGen.single ⟨d, rfl⟩).trans hs, hVL, hEL, hPL, hstop⟩
    · exact ⟨G, ReflTransGen.refl, hV, hE, hP,
        fun d hd => hstep ⟨d, hd⟩⟩

end GraphMinor.GM02
