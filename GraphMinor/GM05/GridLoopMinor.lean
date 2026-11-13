module

public import GraphMinor.GM05.LoopCopies
public import GraphMinor.GM01.Defs
import GraphMinor.Minor.Basic
import GraphMinor.GM09.Basic

/-!
# Disjoint loop minors in a grid

Place disjoint squares in the first two rows of a grid. In each square,
contract the path of three sides and retain the fourth side as a loop.
This supplies the finite obstruction used for Graph Minors V, (8.1).
-/

public section

namespace GraphMinor.GM05

open Graph Set SimpleGraph GM01 GM09 Surface

private def corner {k : ℕ} (i : Fin k) (r c : Fin 2) : Fin (2*k+6) × Fin (2*k+6) :=
  (⟨r.val, by omega⟩, ⟨2*i.val+c.val, by omega⟩)

private lemma corner_eq {k : ℕ} {i j : Fin k} {r c s d : Fin 2} :
    corner i r c = corner j s d ↔ i=j ∧ r=s ∧ c=d := by
  constructor
  · intro h
    have hr := congrArg (fun x ↦ x.1.val) h
    have hc := congrArg (fun x ↦ x.2.val) h
    dsimp [corner] at hr hc
    have hi : i=j := Fin.ext (by omega)
    exact ⟨hi, Fin.ext hr, Fin.ext (by have := congrArg Fin.val hi; omega)⟩
  · rintro ⟨rfl,rfl,rfl⟩; rfl

private lemma corner_link {k : ℕ} (i : Fin k) {r c s d : Fin 2}
    (h : (r.val+1=s.val ∨ s.val+1=r.val) ∧ c=d ∨
      (c.val+1=d.val ∨ d.val+1=c.val) ∧ r=s) :
    (gridGraph (2*k+6)).IsLink s(corner i r c, corner i s d)
      (corner i r c) (corner i s d) := by
  refine ⟨rfl, ?_⟩
  change (pathGraph (2*k+6) □ pathGraph (2*k+6)).Adj _ _
  simp only [boxProd_adj, pathGraph_adj]
  rcases h with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · exact Or.inl ⟨by simpa [corner] using h, rfl⟩
  · right
    refine ⟨?_,rfl⟩
    dsimp [corner]
    rcases h with h|h
    · left; omega
    · right; omega

private def squareWalk {k : ℕ} (i : Fin k) :
    GraphWalk (gridGraph (2*k+6)) (corner i 0 0) (corner i 0 1) :=
  .cons (corner_link i (r:=0) (c:=0) (s:=1) (d:=0) (Or.inl ⟨Or.inl rfl,rfl⟩))
    (.cons (corner_link i (r:=1) (c:=0) (s:=1) (d:=1) (Or.inr ⟨Or.inl rfl,rfl⟩))
      (.cons (corner_link i (r:=1) (c:=1) (s:=0) (d:=1) (Or.inl ⟨Or.inr rfl,rfl⟩)) (.nil (mem_univ _))))

private lemma walk_connected {α β : Type*} {G : Graph α β} {a b : α}
    (W : GraphWalk G a b) : GraphConnected (walkSubgraph W) := by
  obtain ⟨W', hs, _⟩ := exists_walk_walkSubgraph W
  have reach : ∀ {x y}, GraphWalk (walkSubgraph W) x y →
      Relation.ReflTransGen (walkSubgraph W).Adj x y := by
    intro x y P
    induction P with
    | nil => exact .refl
    | cons h P ih => exact (Relation.ReflTransGen.single ⟨_,h⟩).trans ih
  refine ⟨⟨a, by rw [vertexSet_walkSubgraph]; exact W.start_mem_support⟩, ?_⟩
  intro x hx y hy
  rw [vertexSet_walkSubgraph] at hx hy
  rw [←hs] at hx hy
  obtain ⟨P, Q, _⟩ := W'.exists_append_of_mem hx
  obtain ⟨R, S, _⟩ := W'.exists_append_of_mem hy
  exact reach (P.reverse.append R)

/-- The `(2*k+6)`-grid has a minor consisting of `k` disjoint loops. -/
theorem loopCopies_minor_grid (k : ℕ) : IsIsoMinor (loopCopies k) (gridGraph (2*k+6)) := by
  classical
  let B (i : Fin k) := V(walkSubgraph (squareWalk i))
  let e (i : Fin k) := s(corner i 0 0,corner i 0 1)
  have hB (i : Fin k) (x) : x ∈ B i ↔
      x=corner i 0 0 ∨ x=corner i 1 0 ∨ x=corner i 1 1 ∨ x=corner i 0 1 := by
    simp [B, vertexSet_walkSubgraph, squareWalk, GraphWalk.support]
  have he (i : Fin k) : (gridGraph (2*k+6)).IsLink (e i) (corner i 0 0) (corner i 0 1) :=
    corner_link i (Or.inr ⟨Or.inl rfl,rfl⟩)
  have ends (i : Fin k) (x) (hx : (gridGraph (2*k+6)).Inc (e i) x) : x ∈ B i := by
    rcases hx.eq_or_eq_of_isLink (he i) with rfl|rfl
    · exact (hB i _).mpr (Or.inl rfl)
    · exact (hB i _).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have disj (i j : Fin k) (hij : i≠j) : Disjoint (B i) (B j) := by
    rw [Set.disjoint_left]
    intro x hx hy
    rcases (hB i x).mp hx with rfl|rfl|rfl|rfl <;>
      rcases (hB j _).mp hy with h|h|h|h <;>
      exact hij ((corner_eq.mp h).1)
  apply isIsoMinor_of_isMinorModel (loopCopies k) (gridGraph (2*k+6))
    (finite_univ) (finite_univ) (finite_univ) (toFinite _) B e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i _; exact ⟨_,(hB i _).mpr (Or.inl rfl)⟩
  · intro i _ x _; exact mem_univ x
  · intro i _; exact (he i).edge_mem
  · intro i _ j _ hij; exact disj i j hij
  · intro i _ j _ hij
    have hx : (gridGraph (2*k+6)).Inc (e j) (corner i 0 0) := hij ▸ (he i).inc_left
    rcases hx.eq_or_eq_of_isLink (he j) with h|h <;> exact (corner_eq.mp h).1
  · intro i _ j _
    rw [loopCopies_inc]
    constructor
    · intro hij
      subst j
      exact ⟨_,(hB i _).mpr (Or.inl rfl),(he i).inc_left⟩
    · rintro ⟨x,hx,hy⟩
      by_contra hne
      exact Set.disjoint_left.mp (disj i j (Ne.symm hne)) hx (ends j x hy)
  · intro i _ j _
    rw [loopCopies_isLoopAt]
    constructor
    · intro hij
      subst j
      exact ends i
    · intro h
      have hx := h _ (he j).inc_left
      by_contra hne
      exact Set.disjoint_left.mp (disj i j (Ne.symm hne)) hx (ends j _ (he j).inc_left)
  · intro i _
    refine ⟨walkSubgraph (squareWalk i), ?_, rfl, walk_connected _⟩
    refine ⟨?_, ?_⟩
    · exact (walkSubgraph_le _).vertexSet_mono
    · intro f x y hf
      have hG := (walkSubgraph_le _).isLink_mono hf
      refine ⟨hG, ?_⟩
      rintro ⟨j,_,hje⟩
      have hxB : x ∈ B i := hf.left_mem
      have hxJ : x ∈ B j := ends j x (hje.symm ▸ hG.inc_left)
      have hij : i=j := by
        by_contra hne
        exact Set.disjoint_left.mp (disj i j hne) hxB hxJ
      subst j
      have hfE := (walkSubgraph_isLink (squareWalk i)).mp hf
      have hnot : e i ∉ (squareWalk i).edges := by
        simp only [squareWalk, GraphWalk.edges, List.mem_cons, List.not_mem_nil, or_false]
        simp [e, corner_eq]
      exact hnot (hje ▸ hfE.1)

end GraphMinor.GM05
