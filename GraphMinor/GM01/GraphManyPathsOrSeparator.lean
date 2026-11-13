module

public import GraphMinor.GM01.GraphSeparators
public import GraphMinor.GM01.Defs
public import GraphMinor.GM09.Defs
import GraphMinor.GM01.MengerSeparators
import GraphMinor.GM01.SeparatorGraphBridge
import GraphMinor.GM01.SimplePathLift
import GraphMinor.GM01.Basic

/-!
# The two alternatives of (2.9) for general graphs

For the application on page 60 of Graph Minors I, apply the proved
Section 2 theorem to the underlying simple graph and the induced
vertex supports. Lift each resulting path using original edges.
The exact image vertex sets retain disjointness and the absence of
internal vertices in the selected supports. A separator maps back
under subtype inclusion with its cardinality unchanged.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The general-graph form of GM01 (2.9), used on page 60. Both its
clean paths and its separator are constructed in the original graph. -/
theorem graph_many_paths_or_small_separator {α β : Type*} {θ r n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (G : Graph α β) (hfin : V(G).Finite)
    (hG : ¬ IsIsoMinor (gridGraph θ) G) (S : Set α) (_hS : S ⊆ V(G))
    (D : Fin n → Set α) (hD : ∀ i, D i ⊆ V(G))
    (hDC : ∀ i, GraphConnected (G.induce (D i)))
    (hDD : Pairwise fun i j ↦ Disjoint (D i) (D j)) :
    (∃ (J : Set (Fin n)) (a b : J → α) (P : J → Graph α β), J.ncard = r ∧
      (∀ j, a j ∈ D j.val ∧ b j ∈ S ∧ IsGraphPathWithEnds G (P j) (a j) (b j)) ∧
      (Pairwise fun i j ↦ Disjoint V(P i) V(P j)) ∧
      (∀ j x, x ∈ V(P j) → x ≠ a j → x ≠ b j → x ∉ S ∪ ⋃ i ∈ J, D i)) ∨
    (∃ (X : Set α) (J : Set (Fin n)), X ⊆ V(G) ∧ X.ncard + J.ncard ≤ 2 ^ (r * θ ^ 4) ∧
      ∀ j ∉ J, GraphSeparates G X S (D j)) := by
  classical
  let : Finite V(G) := hfin.to_subtype
  let K := SimpleGraph.toSubgraph G.toSimpleGraph le_top
  let B := fun i ↦ simpleInducedVertices G (D i)
  have hBD : Pairwise fun i j ↦ Disjoint (B i).verts (B j).verts := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact Set.disjoint_left.mp (hDD hij) hx hy
  have hFrom := theorem_2_9_simple (r := r) (V' := Subtype.val ⁻¹' S) hθ heven (G := K) Set.finite_univ
    (simplification_mem_gridFree G hG) (fun _ _ ↦ mem_univ _) B
    (fun i ↦ simpleInducedVertices_le G (D i))
    (fun i ↦ simpleInducedVertices_connected G (D i) (hD i) (hDC i)) hBD
  rcases hFrom with ⟨J,P,hJ,hP,hPP,hInt⟩ | ⟨X,J,_,hSize,hSep⟩
  · left
    have hLift := fun j ↦ exists_graph_path_of_simple_path G (P j) (hP j).1
    choose Q hQ hQV using hLift
    refine ⟨J,(fun j ↦ (P j).first.val),(fun j ↦ (P j).last.val),Q,hJ,?_,?_,?_⟩
    · intro j
      exact ⟨(hP j).2.1,(hP j).2.2,hQ j⟩
    · intro i j hij
      rw [hQV i,hQV j]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv : u = v := Subtype.ext (hux.trans hvx.symm)
      exact Set.disjoint_left.mp (hPP hij) hu (huv.symm ▸ hv)
    · intro j x hx hxa hxb hxTarget
      rw [hQV j] at hx
      obtain ⟨v,hv,rfl⟩ := hx
      have hvInt : v ∈ (P j).internalVerts := by
        refine ⟨hv,?_⟩
        rintro (heq | heq)
        · exact hxa (congrArg Subtype.val heq)
        · exact hxb (congrArg Subtype.val heq)
      have hvTarget : v ∈ (Subtype.val ⁻¹' S) ∪ ⋃ i ∈ J, (B i).verts := by
        rcases hxTarget with hxS | hxD
        · exact Or.inl hxS
        · obtain ⟨i,hi,hvi⟩ := mem_iUnion₂.mp hxD
          exact Or.inr (mem_iUnion₂.mpr ⟨i,hi,hvi⟩)
      exact Set.disjoint_left.mp (hInt j) hvInt hvTarget
  · right
    let X' : Set α := Subtype.val '' X
    have hXcard : X'.ncard = X.ncard := ncard_image_of_injective X Subtype.val_injective
    refine ⟨X',J,?_,?_,?_⟩
    · rintro x ⟨v,_,rfl⟩
      exact v.property
    · rw [hXcard]
      exact hSize
    · intro j hj
      apply (graphSeparates_iff_simple_subgraph G X' S (D j)).mpr
      have hs : Separates K X (Subtype.val ⁻¹' S) (Subtype.val ⁻¹' D j) := hSep j hj
      simpa only [X',preimage_image_eq X Subtype.val_injective] using hs

end GraphMinor.GM01
