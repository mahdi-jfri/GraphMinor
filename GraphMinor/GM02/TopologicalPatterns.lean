module

public import GraphMinor.GM02.SplitExtraction
import GraphMinor.GM02.FiniteGraphPatterns

/-!
# Finite topological patterns for a fixed minor

For II (4.8) the paper says (page 320): "This is elementary. (We 'split'
every vertex of $H$ with valency $\ge 4$ into two adjacent vertices of
valency $\ge 3$, repeatedly, in all possible ways.)"

We use the paper's finite set: one copy of each split of `H`, up to
isomorphism. There are finitely many, since a split of `H` has at most
`|V(H)| + 2|E(H)|` vertices and at most `3|E(H)|` edges
(`IsSplitOf.ncard_le`). A split of `H` has `H` as a minor
(`IsSplitOf.isIsoMinor`), and topological containment implies minor
containment, which gives one direction. For the other direction, a graph
with an `H` minor topologically contains a split of `H`
(`exists_split_topological_pattern`).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Graph Minors II, (4.8), page 320:
"For any graph $H$ there is a finite set $H_1, \dots, H_r$ of graphs such
that for any graph $G$, $G$ has a minor isomorphic to $H$ if and only if $G$
topologically contains a graph isomorphic to one of $H_1, \dots, H_r$."

The finite set is the paper's: its members are splits of `H`, and every
split of `H` is isomorphic to one of them. Graphs use the standard numbered
source types. -/
theorem theorem_4_8_proof {α : Type u} {β : Type v} (H : Graph α β)
    (hVH : V(H).Finite) (hEH : E(H).Finite) :
    ∃ F : Finset (Graph ℕ (ℕ × ℕ × ℕ)),
      (∀ J ∈ F, IsSplitOf H J) ∧
      (∀ J : Graph ℕ (ℕ × ℕ × ℕ), IsSplitOf H J → ∃ J' ∈ F, Nonempty (Iso J J')) ∧
      ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
        (IsIsoMinor H G ↔ ∃ J ∈ F, ∃ L : Graph ℕ (ℕ × ℕ × ℕ),
          TopologicallyContains G L ∧ Nonempty (Iso J L)) := by
  obtain ⟨D, hD⟩ := exists_finset_iso_cover (V(H).ncard + 2 * E(H).ncard) (3 * E(H).ncard)
  -- Replace each member of `D` that is isomorphic to a split by such a split.
  let P : Graph ℕ (ℕ × ℕ × ℕ) → Prop := fun J =>
    ∃ J' : Graph ℕ (ℕ × ℕ × ℕ), IsSplitOf H J' ∧ Nonempty (Iso J J')
  let g : Graph ℕ (ℕ × ℕ × ℕ) → Graph ℕ (ℕ × ℕ × ℕ) := fun J =>
    if h : P J then h.choose else J
  have hg : ∀ J, P J → IsSplitOf H (g J) ∧ Nonempty (Iso J (g J)) := by
    intro J h
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec
  let F := (D.filter P).image g
  have hsplit : ∀ J ∈ F, IsSplitOf H J := by
    intro J hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := Finset.mem_image.1 hJ
    exact (hg J₀ (Finset.mem_filter.1 hJ₀).2).1
  have hcover : ∀ J : Graph ℕ (ℕ × ℕ × ℕ), IsSplitOf H J → ∃ J' ∈ F, Nonempty (Iso J J') := by
    intro J hJ
    obtain ⟨hVJ, hEJ, -⟩ := hJ.isIsoMinor hVH hEH
    obtain ⟨hn, he⟩ := hJ.ncard_le hVH hEH
    obtain ⟨J₀, hJ₀D, ⟨φ⟩⟩ := hD J hVJ hEJ hn he
    have hP : P J₀ := ⟨J, hJ, ⟨φ.symm⟩⟩
    obtain ⟨-, ⟨ψ⟩⟩ := hg J₀ hP
    exact ⟨g J₀, Finset.mem_image.2 ⟨J₀, Finset.mem_filter.2 ⟨hJ₀D, hP⟩, rfl⟩, ⟨φ.trans ψ⟩⟩
  refine ⟨F, hsplit, hcover, ?_⟩
  intro G hVG hEG
  constructor
  · intro hm
    obtain ⟨L, htop, hL⟩ := exists_split_topological_pattern hVG hEG hm
    obtain ⟨J, hJ, ⟨φ⟩⟩ := hcover L hL
    exact ⟨J, hJ, L, htop, ⟨φ.symm⟩⟩
  · rintro ⟨J, hJF, L, htop, ⟨φ⟩⟩
    have hHJ := ((hsplit J hJF).isIsoMinor hVH hEH).2.2
    exact (φ.isIsoMinor_right hHJ).trans (htop.isIsoMinor hVG hEG)

end GraphMinor.GM02
