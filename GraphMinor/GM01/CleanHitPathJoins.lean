module

public import GraphMinor.GM09.Basic

/-!
# Joining a clean first-hit path to a path inside the hit graph

In Graph Minors I, (4.10), page 58, the first boundary path meets `D`
only at its initial vertex. A path inside the first end then reaches
the retained tail. Their union is a path because they share only the
first-hit vertex. It keeps the prescribed single intersection with
the old prefix and with the retained tail.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The clean path concatenation in the contraction for GM01 (4.10),
page 58. The inner path lies in `D`, which is disjoint from the old
piece, and enters the new piece only at its terminal vertex. -/
theorem exists_clean_join_of_first_hit_with_vertex_cover {α β : Type*} {G D N₁ N₂ P Q : Graph α β}
    {d w t : α} (hDG : D ≤ G) (hN₂D : N₂ ≤ D) (hdis : Disjoint V(N₁) V(D))
    (hP : IsGraphPathWithEnds G P d w) (hPD : V(P) ∩ V(D) = {d})
    (hPN₁ : V(P) ∩ V(N₁) = {w}) (hQ : IsGraphPathWithEnds D Q d t)
    (hQN₂ : V(Q) ∩ V(N₂) = {t}) :
    ∃ J : Graph α β, IsGraphPathWithEnds G J w t ∧
      V(J) ∩ V(N₁) = {w} ∧ V(J) ∩ V(N₂) = {t} ∧ V(J) = V(P) ∪ V(Q) := by
  have hPQ : V(P) ∩ V(Q) = {d} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact hPD ▸ ⟨hx.1, hQ.le.vertexSet_mono hx.2⟩
    · intro x hx
      have hxd : x = d := hx
      subst x
      exact ⟨hP.left_mem, hQ.left_mem⟩
  let J := subgraphUnion G P Q
  have hJ : IsGraphPathWithEnds G J w t := hP.symm.subgraphUnion (hQ.mono hDG) hPQ
  refine ⟨J, hJ, ?_, ?_, rfl⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hx.1 with hxP | hxQ
      · exact hPN₁ ▸ ⟨hxP, hx.2⟩
      · exact False.elim (Set.disjoint_left.mp hdis hx.2 (hQ.le.vertexSet_mono hxQ))
    · intro x hx
      have hxw : x = w := hx
      subst x
      have hw : w ∈ V(P) ∩ V(N₁) := hPN₁.symm ▸ (show w ∈ ({w} : Set α) from rfl)
      exact ⟨Or.inl hw.1, hw.2⟩
  · apply Set.Subset.antisymm
    · intro x hx
      rcases hx.1 with hxP | hxQ
      · have hxd : x = d := mem_singleton_iff.mp (hPD ▸ ⟨hxP, hN₂D.vertexSet_mono hx.2⟩)
        exact hQN₂ ▸ ⟨hxd.symm ▸ hQ.left_mem, hx.2⟩
      · exact hQN₂ ▸ ⟨hxQ, hx.2⟩
    · intro x hx
      have hxt : x = t := hx
      subst x
      have ht : t ∈ V(Q) ∩ V(N₂) := hQN₂.symm ▸ (show t ∈ ({t} : Set α) from rfl)
      exact ⟨Or.inr ht.1, ht.2⟩

/-- The clean join in GM01 (4.10), page 58, without the vertex-cover
identity used for the two joins in (4.14). -/
theorem exists_clean_join_of_first_hit {α β : Type*} {G D N₁ N₂ P Q : Graph α β}
    {d w t : α} (hDG : D ≤ G) (hN₂D : N₂ ≤ D) (hdis : Disjoint V(N₁) V(D))
    (hP : IsGraphPathWithEnds G P d w) (hPD : V(P) ∩ V(D) = {d})
    (hPN₁ : V(P) ∩ V(N₁) = {w}) (hQ : IsGraphPathWithEnds D Q d t)
    (hQN₂ : V(Q) ∩ V(N₂) = {t}) :
    ∃ J : Graph α β, IsGraphPathWithEnds G J w t ∧
      V(J) ∩ V(N₁) = {w} ∧ V(J) ∩ V(N₂) = {t} := by
  obtain ⟨J, hJ, hJ₁, hJ₂, _⟩ := exists_clean_join_of_first_hit_with_vertex_cover hDG hN₂D hdis
    hP hPD hPN₁ hQ hQN₂
  exact ⟨J, hJ, hJ₁, hJ₂⟩

end GraphMinor.GM01
