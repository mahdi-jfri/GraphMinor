module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4InitialInterval

/-!
# The minimum interval choice in VI (4.2), claim (2)

Once a component meeting only one cuff exists, the initial interval
construction gives candidates satisfying conditions (i) and (ii) on
page 126. Choose one containing as few vertices of the entire forest
as possible. The minimum is taken over all such components and intervals,
as in the paper.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Graph Minors VI (4.2), claim (2), page 126: choose the initial
component and cuff interval so that `|S ∩ V(H)|` is minimum, among all
choices satisfying conditions (i) and (ii). This theorem makes the
choice. The argument that its interval is a base is a further step. -/
theorem exists_minimum_initial_interval_on_cuff
    {H : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    (hex : ∃ K : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent K H.toGraph ∧ Graph.vertexSet K ∩ bd ClosedCylinder ⊆ C) :
    ∃ K : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent K H.toGraph ∧
      ∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧
        ∃ A ∈ componentsIn (C \ {s, t}),
          Graph.vertexSet K ∩ bd ClosedCylinder ⊆ A ∧
          (∀ a ∈ Graph.vertexSet K ∩ A, ∀ b ∈ Graph.vertexSet K ∩ A, a ≠ b →
            ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
              PathHomotopicToArc P a b (cuffSubArc C A a b)) ∧
          ∀ K' : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent K' H.toGraph →
            ∀ s' ∈ C \ H.V, ∀ t' ∈ C \ H.V, s' ≠ t' →
              ∀ A' ∈ componentsIn (C \ {s', t'}),
                Graph.vertexSet K' ∩ bd ClosedCylinder ⊆ A' →
                (∀ a ∈ Graph.vertexSet K' ∩ A', ∀ b ∈ Graph.vertexSet K' ∩ A', a ≠ b →
                  ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
                    PathHomotopicToArc P a b (cuffSubArc C A' a b)) →
                (A ∩ H.V).ncard ≤ (A' ∩ H.V).ncard := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ K : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent K H.toGraph ∧
      ∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧
        ∃ A ∈ componentsIn (C \ {s, t}),
          Graph.vertexSet K ∩ bd ClosedCylinder ⊆ A ∧
          (∀ a ∈ Graph.vertexSet K ∩ A, ∀ b ∈ Graph.vertexSet K ∩ A, a ≠ b →
            ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
              PathHomotopicToArc P a b (cuffSubArc C A a b)) ∧
          (A ∩ H.V).ncard = n
  have hQ : ∃ n, Q n := by
    obtain ⟨K, hK, hKC⟩ := hex
    obtain ⟨s, hs, t, ht, hst, A, hA, hKA, hpaths⟩ :=
      exists_initial_interval_of_component_on_one_cuff hH hK hC hKC
    exact ⟨(A ∩ H.V).ncard, K, hK, s, hs, t, ht, hst, A, hA, hKA, hpaths, rfl⟩
  obtain ⟨K, hK, s, hs, t, ht, hst, A, hA, hKA, hpaths, hn⟩ := Nat.find_spec hQ
  refine ⟨K, hK, s, hs, t, ht, hst, A, hA, hKA, hpaths, ?_⟩
  intro K' hK' s' hs' t' ht' hst' A' hA' hKA' hpaths'
  rw [hn]
  exact Nat.find_min' hQ
    ⟨K', hK', s', hs', t', ht', hst', A', hA', hKA', hpaths', rfl⟩

end GraphMinor.GM06
