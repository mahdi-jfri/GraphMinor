module

public import GraphMinor.HP25.Web
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Paths in a web and paths in its rib

Humeau and Pous, arXiv:2505.16431v2, Section 3.4 (page 9): "An immediate yet important observation
is that in a web with rib $R$, the intersection with $R$ of a path with endpoints in $R$ yields an
induced path. Indeed, if such a path $P$ uses a clique vertex $u$, then we can take the longest
subpath $Q$ of $P$ containing $u$, and whose inner vertices are all clique vertices. The endpoints of
$Q$ are on a triangle $T$ of the rib. In particular $Q$ can be replaced in $P$ by an edge of $T$".

We prove the form of this observation that the later proofs use (`IsWebOn.exists_rib_path`): a walk
of a web between two rib vertices can be replaced by a path between the same ends whose vertices are
rib vertices of the walk. We follow the walk and remember the last rib vertex `r` that we have
reached by a path of rib vertices. While the walk runs through the clique of a triangle `T`, the
vertex `r` stays a vertex of `T`. When the walk comes back to the rib at a vertex of `T`, this vertex
is `r` or a neighbour of `r` in `T`. This replaces each run through a clique by at most one edge of
its triangle, as in the paper.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V} {S : Set V} {C : List V}

/-- `Walk.mapLe` keeps the support. -/
theorem support_mapLe {H : SimpleGraph V} {u v : V} (p : G.Walk u v) (h : G ≤ H) :
    (p.mapLe h).support = p.support := by
  simp [Walk.mapLe, Walk.support_map]

/-- The vertices of a walk of `restrict G T` that starts in `T` are in `T`. -/
theorem mem_of_support_restrict {T : Set V} :
    ∀ {u v : V} (w : (restrict G T).Walk u v), u ∈ T → ∀ x ∈ w.support, x ∈ T
  | _, _, .nil, hu, x, hx => by simp at hx; rw [hx]; exact hu
  | _, _, .cons h p, hu, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hu
    · exact mem_of_support_restrict p h.2.2 x hx

/-- The data of a web: rib vertices `R ⊆ S` with a rib structure, and the triangle `tri x` of each
clique vertex `x`. -/
structure WebData (G : SimpleGraph V) (S : Set V) (C : List V) (R : Set V) (tri : V → Set V) :
    Prop where
  supp : IsSupportedOn G S
  sub : R ⊆ S
  rib : IsRibOn G R C
  tri_spec : ∀ x ∈ S \ R, ∃ a b c, IsTriangleOn G R a b c ∧ tri x = {a, b, c}
  adj_iff : ∀ x ∈ S \ R, ∀ y, G.Adj x y ↔ y ∈ tri x ∨ (y ∈ S \ R ∧ y ≠ x ∧ tri y = tri x)

theorem IsWebOn.exists_webData (h : IsWebOn G S C) : ∃ R tri, WebData G S C R tri := by
  obtain ⟨hs, R, tri, hRS, hrib, hcl⟩ := h
  exact ⟨R, tri, hs, hRS, hrib, fun x hx => (hcl x hx).1, fun x hx => (hcl x hx).2⟩

namespace WebData

variable {R : Set V} {tri : V → Set V} (W : WebData G S C R tri)
include W

/-- The vertices of a triangle of the rib are pairwise adjacent. -/
theorem adj_of_mem_tri {x : V} (hx : x ∈ S \ R) {y z : V} (hy : y ∈ tri x) (hz : z ∈ tri x)
    (hyz : y ≠ z) : G.Adj y z := by
  obtain ⟨a, b, c, ⟨-, -, -, hab, hbc, hac⟩, he⟩ := W.tri_spec x hx
  rw [he] at hy hz
  simp only [mem_insert_iff, mem_singleton_iff] at hy hz
  rcases hy with rfl | rfl | rfl <;> rcases hz with rfl | rfl | rfl
  all_goals first
    | exact absurd rfl hyz
    | exact hab | exact hab.symm | exact hbc | exact hbc.symm | exact hac | exact hac.symm

theorem tri_subset {x : V} (hx : x ∈ S \ R) : tri x ⊆ R := by
  obtain ⟨a, b, c, ⟨ha, hb, hc, -⟩, he⟩ := W.tri_spec x hx
  rw [he]
  rintro y (rfl | rfl | rfl) <;> assumption

/-- A walk from a rib vertex `r`, or from a clique vertex `a` with `r` on its triangle, to a rib
vertex `v`: then `r` reaches `v` through rib vertices of the walk. -/
theorem reach (X : Set V) :
    ∀ {a v : V} (p : G.Walk a v), v ∈ R → (∀ x ∈ p.support, x ∈ X) →
      ∀ r, r ∈ X → (r = a ∨ (a ∈ S \ R ∧ r ∈ tri a)) → r ∈ R →
      (restrict G (R ∩ X)).Reachable r v
  | a, _, .nil, hv, _, r, _, hra, _ => by
    rcases hra with rfl | ⟨ha, -⟩
    · rfl
    · exact absurd hv ha.2
  | a, v, .cons (v := a') hadj p, hv, hX, r, hrX, hra, hrR => by
    have hX' : ∀ x ∈ p.support, x ∈ X := fun x hx => hX x (by simp [hx])
    have ha'X : a' ∈ X := hX' a' (Walk.start_mem_support p)
    by_cases ha' : a' ∈ R
    · -- the walk steps to the rib vertex `a'`, which `r` reaches by at most one edge
      have hra' : (restrict G (R ∩ X)).Reachable r a' := by
        rcases hra with rfl | ⟨ha, hrt⟩
        · exact Adj.reachable ⟨hadj, ⟨hrR, hrX⟩, ⟨ha', ha'X⟩⟩
        · have ha't : a' ∈ tri a := by
            rcases (W.adj_iff a ha a').mp hadj with h | ⟨h, -⟩
            · exact h
            · exact absurd ha' h.2
          by_cases he : r = a'
          · rw [he]
          · exact Adj.reachable ⟨W.adj_of_mem_tri ha hrt ha't he, ⟨hrR, hrX⟩, ⟨ha', ha'X⟩⟩
      exact hra'.trans (reach X p hv hX' a' ha'X (Or.inl rfl) ha')
    · -- the walk steps to the clique vertex `a'`; `r` stays on its triangle
      have ha'S : a' ∈ S := W.supp hadj.symm
      have ha'SR : a' ∈ S \ R := ⟨ha'S, ha'⟩
      refine reach X p hv hX' r hrX (Or.inr ⟨ha'SR, ?_⟩) hrR
      rcases hra with rfl | ⟨ha, hrt⟩
      · rcases (W.adj_iff a' ha'SR r).mp hadj.symm with h | ⟨h, -⟩
        · exact h
        · exact absurd hrR h.2
      · rcases (W.adj_iff a ha a').mp hadj with h | ⟨-, -, h⟩
        · exact absurd (W.tri_subset ha h) ha'
        · rw [h]; exact hrt

/-- Section 3.4 (page 9): a walk of a web between two rib vertices gives a path between the same
ends whose vertices are rib vertices of the walk. -/
theorem exists_rib_path {u v : V} (p : G.Walk u v) (hu : u ∈ R) (hv : v ∈ R) :
    ∃ q : G.Walk u v, q.IsPath ∧ ∀ x ∈ q.support, x ∈ R ∧ x ∈ p.support := by
  classical
  have hr := W.reach {x | x ∈ p.support} p hv (fun x hx => hx) u (Walk.start_mem_support p)
    (Or.inl rfl) hu
  obtain ⟨q⟩ := hr
  let q' := q.toPath
  have hle : restrict G (R ∩ {x | x ∈ p.support}) ≤ G := fun _ _ h => h.1
  refine ⟨(q'.1).mapLe hle, q'.2.mapLe hle, fun x hx => ?_⟩
  rw [support_mapLe] at hx
  exact mem_of_support_restrict q (⟨hu, Walk.start_mem_support p⟩) x (Walk.support_bypass_subset_support q hx)

end WebData

end GraphMinor.HP25
