module

public import GraphMinor.GM01.SeparatorLayers
public import GraphMinor.GM01.SeparatedPathPrefixes
import GraphMinor.GM01.SubdivisionConnected

/-!
# Paths from a layer to its preceding separator

Graph Minors I, proof of (4.7), page 58, uses a path within `W_i` to
`Y_i` for a positive layer index. A layer vertex has a path to the
root avoiding the next separator. In the last layer connectivity gives
a path to the root. Stop at its first vertex in the preceding
separator. The prefix stays separated by that separator and avoids
separation by the next one, so it lies in the layer.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09 GraphMinor.Surface

/-- The path within `W_i` to `Y_i` used in GM01 (4.7), page 58,
including the last-layer case. If the initial vertex is already in
that separator, use its one-vertex path. -/
theorem exists_path_in_layer_to_preceding_separator {α β : Type*} {T : ℕ}
    {G : Graph α β} {root : α} (hG : GraphConnected G) (hroot : root ∈ V(G))
    (Y : Fin T → Set α) {i : Fin (T + 1)} (hi : 0 < i.val)
    {x : α} (hx : x ∈ separatorLayer G root Y i) :
    ∃ y ∈ Y ⟨i.val - 1, by omega⟩,
      ∃ Q : Graph α β, IsGraphPathWithEnds G Q x y ∧
        V(Q) ⊆ separatorLayer G root Y i := by
  classical
  let a : Fin T := ⟨i.val - 1, by omega⟩
  have ha : a.val + 1 = i.val := by dsimp [a]; omega
  have hsep : GraphSeparates G (Y a) {x} {root} := hx.2.1 a ha
  by_cases hxY : x ∈ Y a
  · obtain ⟨Q, hQ, hV, _⟩ := exists_isGraphPathWithEnds_of_walk (GraphWalk.nil hx.1)
    refine ⟨x, hxY, Q, hQ, ?_⟩
    intro z hz
    have hzx : z = x := by
      simpa only [Set.mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton] using hV hz
    exact hzx ▸ hx
  have hpath : ∃ P : Graph α β, IsGraphPathWithEnds G P x root ∧
      ∀ b : Fin T, b.val = i.val → Disjoint V(P) (Y b) := by
    by_cases hiT : i.val < T
    · let b : Fin T := ⟨i.val, hiT⟩
      obtain ⟨x', hx', r', hr', P, hP, hAvoid⟩ :=
        not_graphSeparates_iff.mp (hx.2.2 b rfl)
      have hxx : x' = x := hx'
      have hrr : r' = root := hr'
      subst x'
      subst r'
      refine ⟨P, hP, ?_⟩
      intro b' hb'
      have heq : b' = b := Fin.ext hb'
      exact heq ▸ hAvoid
    · obtain ⟨P, hP⟩ := exists_path_of_adj_reachable hx.1 (hG.2 x hx.1 root hroot)
      refine ⟨P, hP, ?_⟩
      intro b hb
      have hbT := b.isLt
      omega
  obtain ⟨P, hP, hAvoid⟩ := hpath
  have hMeet : ¬ Disjoint V(P) (Y a) := by
    intro hAvoidA
    exact ((not_graphSeparates_iff (A := {x}) (B := {root})).mpr
      ⟨x, rfl, root, rfl, P, hP, hAvoidA⟩) hsep
  obtain ⟨y, hyP, hyA⟩ := Set.not_disjoint_iff.mp hMeet
  obtain ⟨P₀, hP₀P, _, hP₀⟩ := hP.exists_subpath hP.left_mem hyP
  obtain ⟨x', hx', y', hy', Q, hQP₀, hQ⟩ :=
    hP₀.exists_isFromToPathWithEnds (X := {x}) (Y := Y a) rfl hyA
  have hQP := hQP₀.trans hP₀P
  have hxx : x' = x := hx'
  subst x'
  have hsepQ := separated_vertices_of_first_hit_path hQ.1 hQ.2.2 hxY hsep
  refine ⟨y', hy', Q, hQ.1, ?_⟩
  intro z hz
  refine ⟨hQ.1.le.vertexSet_mono hz, ?_, ?_⟩
  · intro b hb
    have heq : b = a := Fin.ext (by dsimp [a]; omega)
    subst b
    exact hsepQ z hz
  · intro b hb
    exact not_separated_vertices_of_avoiding_root_path hP (hAvoid b hb) z
      (hQP.vertexSet_mono hz)

end GraphMinor.GM01
