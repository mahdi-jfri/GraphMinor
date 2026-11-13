module

public import GraphMinor.GM01.FullPaths
import GraphMinor.GM01.GridPaths

/-!
# Ordered paths and stars in general graphs

A star has one actual edge from its centre to each other vertex. Its shadow
is a simple star on the same vertices. This transfers the star bound while
keeping all path orders and intersections.
-/

@[expose] public section
namespace GraphMinor.GM01.Full
open Graph Set SimpleGraph GM05
universe u v
variable {α : Type u} {β : Type v}

/-- A star is a tree whose centre is adjacent to every other vertex,
Graph Minors I, Section 2, page 42. Each edge joins the centre to a distinct
vertex, and there is at most one edge for each pair of ends. -/
def IsStarWithCenter (B : Graph α β) (c : α) : Prop :=
  c ∈ V(B) ∧ (∀ x ∈ V(B), x ≠ c → B.Adj c x) ∧
    (∀ e x y, B.IsLink e x y → x ≠ y ∧ (x = c ∨ y = c)) ∧
    (∀ e f x y, B.IsLink e x y → B.IsLink f x y → e = f)

/-- Taking the shadow of a star keeps its centre. -/
theorem IsStarWithCenter.shadow {B : Graph α β} {c : α}
    (h : IsStarWithCenter B c) : GM01.IsStarWithCenter (simpleShadow B) c := by
  refine ⟨h.1, ?_, ?_⟩
  · intro x hx hxc
    exact ⟨hxc.symm, h.2.1 x hx hxc⟩
  · rintro x y ⟨_, e, he⟩
    exact (h.2.2.1 e x y he).2

/-- Graph Minors I, (2.2), page 42, for graphs with loops and multiple edges:
"If $P_1, ..., P_m$ are disjoint paths of $G \in \mathcal{F}_\theta$, and $B_1, ..., B_n$ are
disjoint stars, and each $P_i$ has exactly one vertex in common with each $B_j$, and no $P_i$
contains the centre of any star $B_j$, and each $P_i$ meets $B_1, ..., B_n$ in that order, then
either $m < \theta$ or $n < \theta(\theta - 1)$."
The simple special case is `GM01.theorem_2_2_simple`. -/
theorem theorem_2_2_proof {θ m n : ℕ} (hθ : 3 ≤ θ) {G : Graph α β}
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : ¬ IsIsoMinor (gridGraph θ) G)
    (P : Fin m → Path α β) (B : Fin n → Graph α β) (c : Fin n → α)
    (hP : ∀ i, (P i).IsIn G)
    (hPD : Pairwise fun i j ↦ Disjoint (P i).verts (P j).verts)
    (hB : ∀ j, B j ≤ G) (hstar : ∀ j, IsStarWithCenter (B j) (c j))
    (hBD : Pairwise fun i j ↦ Disjoint V(B i) V(B j))
    (hmeet : ∀ i j, ((P i).verts ∩ V(B j)).ncard = 1)
    (hc : ∀ i j, c j ∉ (P i).verts)
    (hord : ∀ i, (P i).toPath.MeetsInOrder (fun j ↦ simpleShadow (B j))) :
    m < θ ∨ n < θ * (θ - 1) := by
  exact GM01.theorem_2_2_simple hθ hV (shadow_mem_gridFree hV hE hG)
    (fun i ↦ (P i).toPath) (fun j ↦ simpleShadow (B j)) c
    (fun i ↦ Path.isIn_shadow (hP i)) hPD (fun j ↦ simpleShadow_mono (hB j))
    (fun j ↦ (hstar j).shadow) hBD hmeet hc hord

end GraphMinor.GM01.Full
