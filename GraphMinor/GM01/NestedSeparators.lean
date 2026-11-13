module

public import GraphMinor.GM01.GraphSeparators

/-!
# Nesting of separators toward a fixed root

Graph Minors I, proof of (1.7), pages 41–42, considers a path to the
root avoiding an earlier separator. If a later separator cuts off its
initial vertex, the path meets that later separator. The remaining
subpath then contradicts the assumed order of the separators. This
proves that separation from the root is monotone in their index.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- The path argument in the uniqueness proof of GM01 (1.7), pages
41–42: if `X` separates `B` from the root and `B` separates `A` from
the root, then `X` separates `A` from the root. -/
theorem GraphSeparates.trans_root {α β : Type*} {G : Graph α β}
    {X A B : Set α} {root : α} (hXB : GraphSeparates G X B {root})
    (hBA : GraphSeparates G B A {root}) : GraphSeparates G X A {root} := by
  classical
  by_contra hno
  obtain ⟨a, ha, b, hb, P, hP, hAvoid⟩ := not_graphSeparates_iff.mp hno
  have hbr : b = root := mem_singleton_iff.mp hb
  subst b
  have hMeet : ¬ Disjoint V(P) B := by
    intro hAvoidB
    exact ((not_graphSeparates_iff (B := {root})).mpr ⟨a, ha, root, rfl, P, hP, hAvoidB⟩) hBA
  obtain ⟨z, hzP, hzB⟩ := Set.not_disjoint_iff.mp hMeet
  obtain ⟨Q, hQP, _, hQ⟩ := hP.exists_subpath hzP hP.right_mem
  exact ((not_graphSeparates_iff (B := {root})).mpr
    ⟨z, hzB, root, rfl, Q, hQ, hAvoid.mono_left hQP.vertexSet_mono⟩) hXB

/-- Separation from the root is monotone for an ordered separator
family, as established in the proof of GM01 (1.7), pages 41–42. -/
theorem ordered_separator_separation_mono {α β : Type*} {T : ℕ}
    {G : Graph α β} {root : α} (Y : Fin T → Set α)
    (horder : ∀ i j, ∀ y ∈ Y j,
      GraphSeparates G (Y i) {y} {root} ↔ i ≤ j)
    {i j : Fin T} (hij : i ≤ j) {A : Set α}
    (hsep : GraphSeparates G (Y j) A {root}) :
    GraphSeparates G (Y i) A {root} := by
  have hY : GraphSeparates G (Y i) (Y j) {root} := by
    intro y hy r hr hyv hrv hyr
    exact ((horder i j y hy).mpr hij) y rfl r hr hyv hrv hyr
  exact hY.trans_root hsep

end GraphMinor.GM01
