module

public import GraphMinor.GM01.CombInteriorRooting
public import GraphMinor.GM01.CombInteriorForkReflection
import GraphMinor.GM01.RootedModelComposition

/-!
# The fork rooted at an interior subdivision attachment

For Graph Minors I, (4.9), page 58, first contract `D` while retaining
its attachment vertex in an interior source branch. Then contract the
source comb to the fork, using the longer side for the comb arm. Model
composition keeps the original attachment as the target root. Thus an
attachment outside both ends supplies the actual forbidden fork model.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The contraction of `D` in GM01 (4.9), page 58: an attachment outside
both ends gives a rooted fork in `D` at that attachment vertex. -/
theorem rootedFork_of_subdivision_attachment_outside_ends {α β : Type*} {γ δ L : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 5 ≤ L) (hlong : 2 * δ ≤ L)
    {D : Graph α β} {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    (P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β)
    (hV : V(D) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (x : V(D))
    (hx : x.val ∉ combFirstEndSupport (by omega) c P ∪ combSecondEndSupport (by omega) c P) :
    HasRootedMinor (rootedForkGraph γ δ hγ hδ) (⟨D, x⟩ : RootedGraph α β) := by
  obtain ⟨v, hv, hv', ⟨M⟩⟩ := rooted_comb_at_interior_vertex_of_subdivision hL hc P hV hPaths hInter x hx
  exact ⟨(rootedForkModelOfCombInterior hγ hδ hlong v hv hv').trans M⟩

end GraphMinor.GM01
