module

public import GraphMinor.GM10.Section7ModelRealization
public import GraphMinor.GM10.Section7
import GraphMinor.GM10.Section7GridTwo
public import GraphMinor.GM10.Section7ModelTangle

/-!
# A grid minor inducing a prescribed tangle truncation

Graph Minors X (7.5) cites Robertson, Seymour and Thomas. We use their proved
grid-set theorem, including the size-two conversion, and realize the model
as a literal minor. The canonical grid tangle is carried along the specified
vertex and edge maps. The inducing formula then agrees with the formula
already proved to be the truncation.
-/

public section

namespace GraphMinor.GM10

open Hypergraph RST94 Set Graph

universe u v

/-- Reading the inducing formula after an injective renaming of a grid uses
exactly the model's edge representatives. The equality itself does not need
injectivity, since both sides quantify over the same canonical separations. -/
theorem inducedTangle_isoImage_grid {α : Type u} {β : Type v}
    (G : Hypergraph α β) (g : ℕ)
    (fV : Fin g × Fin g → Set α) (fE : Sym2 (Fin g × Fin g) → β) :
    inducedTangle G (GM21.isoImage fV fE (gridHypergraph g))
      (GM21.isoImageTangle fV fE (gridTangle g)) g =
      gridModelInducedTangle G g fE := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨hs, ho, p, ⟨q, hq, rfl⟩, he⟩
    exact ⟨hs, ho, q, hq, he⟩
  · rintro ⟨hs, ho, q, hq, he⟩
    exact ⟨hs, ho, _, ⟨q, hq, rfl⟩, he⟩

/-- Graph Minors X, (7.5), page 173:
"For every $\theta \ge 2$ there exists $\phi \ge 0$ such that for every graph
$G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge \phi$, the truncation of
$\mathscr{T}$ to order $\theta$ is the tangle induced by some $\theta$-grid minor of $G$."

The minor is literal and is explicitly isomorphic to the grid. The two maps
identify its canonical tangle with the image of `gridTangle`. The cited grid
result is used with its proof, so no cited hypothesis remains. -/
theorem theorem_7_5_proof (g : ℕ) (hg : 2 ≤ g) :
    ∃ φ : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
      (hV : V(G).Finite) (hE : E(G).Finite)
      (θ : ℕ) (T : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (Hypergraph.ofGraph G hV hE) θ T → φ ≤ θ →
      ∃ (H : Graph (Set α) β) (hVH : V(H).Finite) (hEH : E(H).Finite)
        (fV : Fin g × Fin g → Set α) (fE : Sym2 (Fin g × Fin g) → β),
        IsMinor H G ∧ Nonempty (Iso (GM01.gridGraph g) H) ∧
        InjOn fV (gridHypergraph g).vertexSet ∧
        InjOn fE (gridHypergraph g).edgeSet ∧
        Hypergraph.ofGraph H hVH hEH = GM21.isoImage fV fE (gridHypergraph g) ∧
        IsTangle (Hypergraph.ofGraph H hVH hEH) g
          (GM21.isoImageTangle fV fE (gridTangle g)) ∧
        truncation T g = inducedTangle (Hypergraph.ofGraph G hV hE)
          (Hypergraph.ofGraph H hVH hEH)
          (GM21.isoImageTangle fV fE (gridTangle g)) g := by
  refine ⟨max g (20 ^ ((max g 3) ^ 4 * (2 * max g 3 - 1))), ?_⟩
  intro α β G hV hE θ T hT hθ
  have hgle : g ≤ θ := (le_max_left _ _).trans hθ
  have hbound : 20 ^ ((max g 3) ^ 4 * (2 * max g 3 - 1)) ≤ θ :=
    (le_max_right _ _).trans hθ
  have hgrid : HasGrid (Hypergraph.ofGraph G hV hE) T θ g := by
    by_cases hg2 : g = 2
    · subst g
      apply hasGrid_two_of_three hT
      exact RST94.theorem_5_7 (GM16.isGraph_ofGraph G hV hE) hT (by omega)
        (by simpa only [show max 2 3 = 3 from rfl] using hbound)
    · have hg3 : 3 ≤ g := by omega
      exact RST94.theorem_5_7 (GM16.isGraph_ofGraph G hV hE) hT hg3
        (by simpa only [max_eq_left hg3] using hbound)
  obtain ⟨W, hW⟩ := hgrid
  obtain ⟨ηe, hm, hηe⟩ := RST94.grid_model hW hg
  have heq := truncation_eq_gridModelInducedTangle hT hW hg hgle hm hηe
  obtain ⟨H, hVH, hEH, hminor, hH, hinjV, hiso⟩ :=
    ModelRealization.exists_literal_minor_eq_isoImage hm (Set.toFinite _) (Set.toFinite _)
  change Hypergraph.ofGraph H hVH hEH =
    GM21.isoImage (fun z => W z.1 z.2) ηe (gridHypergraph g) at hH
  refine ⟨H, hVH, hEH, (fun z => W z.1 z.2), ηe, hminor, hiso,
    hinjV, hm.edge_injOn, hH, ?_, ?_⟩
  · rw [hH]
    exact GM21.isTangle_isoImage hinjV hm.edge_injOn (theorem_7_3_proof hg)
  · rw [hH]
    rw [inducedTangle_isoImage_grid]
    exact heq

end GraphMinor.GM10
