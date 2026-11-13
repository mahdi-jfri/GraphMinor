module

public import GraphMinor.GM01.BinaryMinorModels
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.RootedSubcubicSubdivision
import GraphMinor.GM01.RootedModelOfMinor
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.RootedPathAttachment
import GraphMinor.GM01.SubdivisionConnected

/-!
# The rooted binary subdivision in the root set

Graph Minors I, Section 5, page 60, replaces the rooted `H_γ` minor
in `X_0` by a subdivision together with a path from the ambient root.
The degree bounds allow the proved rooted subcubic construction.
Its root centre remains in the ordinary model's root branch.
Root that model at the centre, restore the source labels, and attach
the separate root path. The resulting union retains the rooted minor.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual subdivision and separate root path in `B_0` on page 60
of GM01. The union is connected and retains the rooted `H_γ` model. -/
theorem RootedMinorModel.binaryTree_subdivision {α β : Type*} {γ : ℕ}
    (hγ : 0 < γ) (G : RootedGraph α β) (M : RootedMinorModel (binaryRootedTree γ) G) :
    ∃ (N : Graph α β) (c : (binaryTree γ).verts → α)
      (P : (binaryTree γ).coe.edgeSet → Graph α β) (R : Graph α β),
      N ≤ G.graph ∧ Injective c ∧
      V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : (binaryTree γ).coe.edgeSet, e ≠ f →
        Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
      IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root) ∧
      V(R) ∩ V(N) = {c (binaryRootedTree γ).root} ∧
      GraphConnected N ∧ GraphConnected (subgraphUnion G.graph N R) ∧
      ∃ hroot : G.root.val ∈ V(subgraphUnion G.graph N R),
        HasRootedMinor (binaryRootedTree γ)
          (⟨subgraphUnion G.graph N R, ⟨G.root.val, hroot⟩⟩ : RootedGraph α β) := by
  let : Finite (binaryTree γ).verts := (binaryTree_vertices_finite γ).to_subtype
  let root : (binaryTree γ).verts := ⟨[], binaryTree_root_mem γ⟩
  obtain ⟨ηv, ηe, hModel, hRoot⟩ := M.binaryTree_minor_model hγ G
  obtain ⟨N, c, P, R, hN, hc, _, hV, hE, hPaths, hInter, hR, hMeet,
      ηv', hModel', hcRoot⟩ := exists_rooted_subcubic_subdivision hModel
    (binaryTree_coe_neighborSet_ncard_le_three γ) root
    (binaryTree_root_coe_neighborSet_ncard_le_two γ) (binaryTree_root_coe_neighborSet_nonempty hγ)
    G.root.val hRoot
  have hcentre : c root ∈ V(N) := by
    rw [hV]
    exact Or.inl (mem_range_self root)
  let Nr : RootedGraph α β := ⟨N, ⟨c root, hcentre⟩⟩
  let M₀ := rootedModelOfMinorModel hModel' root Nr.root hcRoot
  let iso := subgraphSimpleGraphIso (binaryTree γ)
  let iso' : GraphMinor.Iso (toGraph (binaryTree γ)) (Graph.ofSimpleGraph (binaryTree γ).coe) :=
    { vertexEquiv := iso.vertexEquiv.symm
      edgeEquiv := iso.edgeEquiv.symm
      isLink_iff := fun e u v ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (iso.isLink_iff (iso.edgeEquiv.symm e) (iso.vertexEquiv.symm u) (iso.vertexEquiv.symm v)).symm }
  let MN : RootedMinorModel (binaryRootedTree γ) Nr := M₀.comapSource iso' rfl
  have hmeet : V(N) ∩ V(R) ⊆ {c root} := by
    rw [Set.inter_comm]
    exact hMeet.subset
  let MR := MN.attachRootPath hN G.root.val hR hmeet
  have hNconn : GraphConnected N := subdivision_connected (binaryTree_connected γ).coe root N c P hV
    (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hHconn := graphConnected_subgraphUnion hN hR.le hNconn
    (graphConnected_of_isGraphPath hR) ⟨c root, hcentre, hR.right_mem⟩
  refine ⟨N, c, P, R, hN, hc, hV, hE, ?_, hInter, hR, hMeet, hNconn, hHconn,
    Or.inr hR.left_mem, ⟨MR⟩⟩
  intro e
  obtain ⟨a, b, he, hab, hP, _, hRange⟩ := hPaths e
  exact ⟨a, b, he, hab, hP, hRange⟩

end GraphMinor.GM01
