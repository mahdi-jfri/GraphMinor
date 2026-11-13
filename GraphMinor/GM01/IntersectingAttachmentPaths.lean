module

public import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM16.PathEndSubpath

/-!
# Rerouting intersecting attachment paths

Graph Minors I, (4.13), page 59, reroutes the second attachment through
the first one when the two paths meet. The subpath from their meeting
point to the second boundary cannot contain the original second
attachment as an internal vertex. The subpath from the first
attachment to the meeting point similarly avoids the first boundary
if that boundary is forbidden. Their union therefore gives the
required clean attachment from the first vertex.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The rerouting used in GM01 (4.13), page 59. Each original path
meets the represented subdivision only at its attachment. A meeting
of the paths yields a clean path from the first attachment to the
second boundary with the same avoidance condition. -/
theorem exists_rerouted_clean_attachment {α β : Type*} {G P₁ P₂ : Graph α β}
    {X F : Set α} (hXF : Disjoint X F) {d₁ d₂ w₁ w₂ : α}
    (hd₁ : d₁ ∈ X) (hd₂ : d₂ ∈ X) (hw₂ : w₂ ∈ F) (hne : w₁ ≠ w₂)
    (hP₁ : IsGraphPathWithEnds G P₁ d₁ w₁) (hP₂ : IsGraphPathWithEnds G P₂ d₂ w₂)
    (hP₁X : V(P₁) ∩ X = {d₁}) (hP₂X : V(P₂) ∩ X = {d₂})
    (hP₁F : Disjoint V(P₁) (F \ {w₁})) (hP₂F : Disjoint V(P₂) (F \ {w₂}))
    (hmeet : (V(P₁) ∩ V(P₂)).Nonempty) :
    ∃ Q : Graph α β, IsGraphPathWithEnds G Q d₁ w₂ ∧
      Disjoint V(Q) (F \ {w₂}) ∧ V(Q) ∩ X = {d₁} := by
  by_cases hdd : d₁ = d₂
  · subst d₂
    exact ⟨P₂, hP₂, hP₂F, hP₂X⟩
  obtain ⟨z, hz₁, hz₂⟩ := hmeet
  have hw₂NotP₁ : w₂ ∉ V(P₁) := fun h ↦ Set.disjoint_left.mp hP₁F h ⟨hw₂, Ne.symm hne⟩
  have hzNotF : z ∉ F := by
    intro hzF
    have hzw : z = w₂ := by
      by_contra h
      exact Set.disjoint_left.mp hP₂F hz₂ ⟨hzF, h⟩
    exact hw₂NotP₁ (hzw ▸ hz₁)
  have hzNotX : z ∉ X := by
    intro hzX
    have hzd₁ : z = d₁ := mem_singleton_iff.mp (hP₁X ▸ ⟨hz₁, hzX⟩)
    have hzd₂ : z = d₂ := mem_singleton_iff.mp (hP₂X ▸ ⟨hz₂, hzX⟩)
    exact hdd (hzd₁.symm.trans hzd₂)
  have hw₂NotX : w₂ ∉ X := fun h ↦ Set.disjoint_left.mp hXF h hw₂
  have hd₁NotF : d₁ ∉ F := fun h ↦ Set.disjoint_left.mp hXF hd₁ h
  obtain ⟨Q₁, hQ₁P₁, _, hQ₁⟩ := hP₁.exists_subpath hP₁.left_mem hz₁
  obtain ⟨Q₂, hQ₂P₂, _, hQ₂⟩ := hP₂.exists_subpath hz₂ hP₂.right_mem
  have hQ₁F : Disjoint V(Q₁) F := by
    apply Set.disjoint_left.mpr
    intro x hx hxF
    have hxw : x = w₁ := by
      by_contra h
      exact Set.disjoint_left.mp hP₁F (hQ₁P₁.vertexSet_mono hx) ⟨hxF, h⟩
    have hwQ : w₁ ∈ V(Q₁) := hxw ▸ hx
    rcases GraphMinor.GM16.path_start_mem_subpath_is_end hP₁.symm hQ₁ hQ₁P₁ hwQ with h | h
    · exact hd₁NotF (h ▸ (hxw ▸ hxF))
    · exact hzNotF (h ▸ (hxw ▸ hxF))
  have hQ₂X : Disjoint V(Q₂) X := by
    apply Set.disjoint_left.mpr
    intro x hx hxX
    have hxd : x = d₂ := mem_singleton_iff.mp (hP₂X ▸ ⟨hQ₂P₂.vertexSet_mono hx, hxX⟩)
    have hdQ : d₂ ∈ V(Q₂) := hxd ▸ hx
    rcases GraphMinor.GM16.path_start_mem_subpath_is_end hP₂ hQ₂ hQ₂P₂ hdQ with h | h
    · exact hzNotX (h ▸ hd₂)
    · exact hw₂NotX (h ▸ hd₂)
  let K := subgraphUnion G Q₁ Q₂
  have hKG : K ≤ G := subgraphUnion_le hQ₁.le hQ₂.le
  have hKconn : GraphConnected K := graphConnected_subgraphUnion hQ₁.le hQ₂.le
    (graphConnected_of_isGraphPath hQ₁) (graphConnected_of_isGraphPath hQ₂)
    ⟨z, hQ₁.right_mem, hQ₂.left_mem⟩
  have hdK : d₁ ∈ V(K) := Or.inl hQ₁.left_mem
  have hwK : w₂ ∈ V(K) := Or.inr hQ₂.right_mem
  obtain ⟨Q, hQ⟩ := exists_path_of_adj_reachable hdK (hKconn.2 d₁ hdK w₂ hwK)
  have hKF : Disjoint V(K) (F \ {w₂}) :=
    (hQ₁F.mono_right sdiff_subset).union_left (hP₂F.mono_left hQ₂P₂.vertexSet_mono)
  refine ⟨Q, hQ.mono hKG, hKF.mono_left hQ.le.vertexSet_mono, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rcases hQ.le.vertexSet_mono hx.1 with hx₁ | hx₂
    · exact hP₁X ▸ ⟨hQ₁P₁.vertexSet_mono hx₁, hx.2⟩
    · exact False.elim (Set.disjoint_left.mp hQ₂X hx₂ hx.2)
  · intro x hx
    have hxd : x = d₁ := hx
    subst x
    exact ⟨hQ.left_mem, hd₁⟩

end GraphMinor.GM01
