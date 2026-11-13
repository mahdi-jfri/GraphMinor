module

public import GraphMinor.GM09.Basic
public import GraphMinor.Minor.Model
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectivity of the subdivided comb

A subdivision of a connected graph is connected. Follow a source walk
by its replacing paths to join branch centres. Every other vertex lies
on one replacing path, so it can first reach a centre. This supplies the
connectivity of the subdivided comb on page 55 of Graph Minors I, in the
proof needed for (1.1).
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09 GraphMinor.Surface

private theorem graphWalk_reachable {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : Relation.ReflTransGen G.Adj a b := by
  induction W with
  | nil _ => exact .refl
  | cons h W ih => exact (Relation.ReflTransGen.single ⟨_, h⟩).trans ih

/-- A graph path is connected in the reachability sense used for minor
branches. Its subpaths join any two of its vertices. -/
theorem graphConnected_of_isGraphPath {α β : Type*} {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) : GraphConnected P := by
  refine ⟨⟨a, hP.left_mem⟩, ?_⟩
  intro x hx y hy
  obtain ⟨Q, hQP, hQ, _⟩ := hP.exists_subpath hx hy
  obtain ⟨W, _, _, _⟩ := hQ.2
  exact Relation.ReflTransGen.mono
    (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hQP⟩)
    x y (graphWalk_reachable W)

/-- Replacing every source edge by a path preserves connectivity when
all vertices are either centres or vertices on those paths. No
connectivity of the subdivision is assumed. -/
theorem subdivision_connected {α β ν : Type*} {S : SimpleGraph ν}
    (hS : S.Connected) (r : ν) (N : Graph α β) (c : ν → α)
    (P : S.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧ S.Adj a b ∧
      IsGraphPathWithEnds N (P e) (c a) (c b)) : GraphConnected N := by
  have hcentres_mem : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hedge : ∀ {a b}, S.Adj a b → Relation.ReflTransGen N.Adj (c a) (c b) := by
    intro a b hab
    let e : S.edgeSet := ⟨s(a,b), hab⟩
    obtain ⟨a', b', he, _, hPath⟩ := hPaths e
    have hpair : s(a,b) = s(a',b') := he
    have hreach := (graphConnected_of_isGraphPath hPath).2
      (c a') hPath.left_mem (c b') hPath.right_mem
    have hNreach : Relation.ReflTransGen N.Adj (c a') (c b') := Relation.ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨edge, he⟩ := h; exact ⟨edge, he.mono hPath.le⟩)
      (c a') (c b') hreach
    rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hNreach
    · exact Std.Symm.symm _ _ hNreach
  have hcentres : ∀ a b, Relation.ReflTransGen N.Adj (c a) (c b) := by
    intro a b
    obtain ⟨p⟩ := hS a b
    induction p with
    | nil => exact .refl
    | cons hab p ih => exact (hedge hab).trans ih
  have htoRoot : ∀ x ∈ V(N), Relation.ReflTransGen N.Adj x (c r) := by
    intro x hx
    rw [hV] at hx
    rcases hx with ⟨v, rfl⟩ | hx
    · exact hcentres v r
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
      obtain ⟨a, b, _, _, hPath⟩ := hPaths e
      have hr := (graphConnected_of_isGraphPath hPath).2 x hxe (c a) hPath.left_mem
      have hrN : Relation.ReflTransGen N.Adj x (c a) := Relation.ReflTransGen.mono
        (fun _ _ h ↦ by obtain ⟨edge, he⟩ := h; exact ⟨edge, he.mono hPath.le⟩)
        x (c a) hr
      exact hrN.trans (hcentres a r)
  exact ⟨⟨c r, hcentres_mem r⟩, fun x hx y hy ↦
    (htoRoot x hx).trans (Std.Symm.symm _ _ (htoRoot y hy))⟩

/-- Two connected subgraphs meeting at a vertex have connected union.
This joins the subdivided comb to its target-root path on page 55. -/
theorem graphConnected_subgraphUnion {α β : Type*} {G A B : Graph α β}
    (hA : A ≤ G) (hB : B ≤ G) (hcA : GraphConnected A) (hcB : GraphConnected B)
    (hmeet : (V(A) ∩ V(B)).Nonempty) : GraphConnected (subgraphUnion G A B) := by
  obtain ⟨z, hzA, hzB⟩ := hmeet
  let H := subgraphUnion G A B
  have hAH : A ≤ H := le_subgraphUnion_left hA hB
  have hBH : B ≤ H := le_subgraphUnion_right hA hB
  have htoz : ∀ x ∈ V(H), Relation.ReflTransGen H.Adj x z := by
    intro x hx
    rcases hx with hxA | hxB
    · exact Relation.ReflTransGen.mono
        (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hAH⟩)
        x z (hcA.2 x hxA z hzA)
    · exact Relation.ReflTransGen.mono
        (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hBH⟩)
        x z (hcB.2 x hxB z hzB)
  exact ⟨⟨z, Or.inl hzA⟩, fun x hx y hy ↦
    (htoz x hx).trans (Std.Symm.symm _ _ (htoz y hy))⟩

end GraphMinor.GM01
