module

public import GraphMinor.GM01.CombMinorModels
public import GraphMinor.GM01.RootedSubcubicSubdivision
public import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.RootedCombUnion

/-!
# Subdivisions of rooted combs

Graph Minors I, page 55, replaces a rooted model of a long comb by a
subdivision and a path from the target root. The comb has degree at most
three and its root has degree at most two. Applying the proved rooted
branch construction gives the subdivision with the required intersection
with that path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The subdivision choice on page 55 of Graph Minors I. The map `c`
identifies the comb vertices and `P` gives the replacing edge paths. The
path from the target root meets the subdivision exactly at the first
spine vertex. -/
theorem RootedMinorModel.pathComb_subdivision {γ δ : ℕ} (hδ : 2 ≤ δ)
    {α : Type u} {β : Type v} (G : RootedGraph α β)
    (M : RootedMinorModel (rootedPathComb γ δ (by omega)) G) :
    ∃ (N : Graph α β) (c : (pathComb γ δ).verts → α)
      (P : (pathComb γ δ).coe.edgeSet → Graph α β) (R : Graph α β),
      N ≤ G.graph ∧ Injective c ∧
      V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : (pathComb γ δ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        (pathComb γ δ).coe.Adj a b ∧
        IsGraphPathWithEnds N (P e) (c a) (c b) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : (pathComb γ δ).coe.edgeSet, e ≠ f →
        Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
      IsGraphPathWithEnds G.graph R G.root.val
        (c (rootedPathComb γ δ (by omega)).root) ∧
      V(R) ∩ V(N) = {c (rootedPathComb γ δ (by omega)).root} ∧
      GraphConnected N ∧ GraphConnected (subgraphUnion G.graph N R) ∧
      G.root.val ∈ V(subgraphUnion G.graph N R) ∧
      (∃ hroot : G.root.val ∈ V(subgraphUnion G.graph N R),
        HasRootedMinor (rootedPathComb γ δ (by omega))
          (⟨subgraphUnion G.graph N R, ⟨G.root.val, hroot⟩⟩ : RootedGraph α β)) ∧
      ∃ (ηv : (pathComb γ δ).verts → Set α)
        (ηe : Sym2 (pathComb γ δ).verts → β),
        IsMinorModel (Graph.ofSimpleGraph (pathComb γ δ).coe) N ηv ηe ∧
        c (rootedPathComb γ δ (by omega)).root ∈
          ηv (rootedPathComb γ δ (by omega)).root := by
  let : Finite (pathComb γ δ).verts := (pathComb_vertices_finite γ δ).to_subtype
  obtain ⟨ηv, ηe, hModel, hroot⟩ := M.pathComb_minor_model hδ G
  obtain ⟨N, c, P, R, hN, hc, _, hV, hE, hPaths, hInter, hR, hMeet,
      ηv', hModel', hcRoot⟩ :=
    exists_rooted_subcubic_subdivision hModel
      (pathComb_coe_neighborSet_ncard_le_three γ δ)
      (rootedPathComb γ δ (by omega)).root
      (pathComb_root_coe_neighborSet_ncard_le_two γ δ (by omega))
      (pathComb_root_coe_neighborSet_nonempty γ δ hδ) G.root.val hroot
  have hNconn : GraphConnected N :=
    subdivision_connected (pathComb_connected (γ := γ) (by omega : 0 < δ)).coe
      (rootedPathComb γ δ (by omega)).root N c P hV (fun e ↦ by
        obtain ⟨a, b, he, hab, hP, _, _⟩ := hPaths e
        exact ⟨a, b, he, hab, hP⟩)
  have hrootCentre : c (rootedPathComb γ δ (by omega)).root ∈ V(N) := by
    rw [hV]
    exact Or.inl (mem_range_self _)
  have hHconn := graphConnected_subgraphUnion hN hR.le hNconn
    (graphConnected_of_isGraphPath hR) ⟨_, hrootCentre, hR.right_mem⟩
  have hRootModel := rootedPathComb_minor_in_union (by omega : 0 < δ) G hN hModel'
    (c (rootedPathComb γ δ (by omega)).root) hcRoot hR
    (by rw [Set.inter_comm]; exact hMeet.subset)
  refine ⟨N, c, P, R, hN, hc, hV, hE, ?_, hInter, hR, hMeet,
    hNconn, hHconn, Or.inr hR.left_mem, ⟨Or.inr hR.left_mem, hRootModel⟩, ηv', ηe, hModel', hcRoot⟩
  intro e
  obtain ⟨a, b, he, hab, hP, _, hRange⟩ := hPaths e
  exact ⟨a, b, he, hab, hP, hRange⟩

end GraphMinor.GM01
