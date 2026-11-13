module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Chordless shortest paths

A shortest walk has no chord: an edge between its start and a later
vertex must already be the first edge, since its prefix is also shortest.
Induction applies the same argument to the remaining walk. These paths
are used in the separator proof of Graph Minors V, (8.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {a b : V}

private lemma start_edge_mem {p : G.Walk a b} (hp : p.length=G.dist a b)
    {x : V} (hx : x∈p.support) (hax : G.Adj a x) : s(a,x)∈p.edges := by
  classical
  let q := p.takeUntil x hx
  have hq : q.IsSubwalk p := p.isSubwalk_takeUntil hx
  have hlen : q.length=1 := (length_eq_dist_of_subwalk hp hq).trans (dist_eq_one_iff_adj.mpr hax)
  apply hq.edges_subset
  apply q.mk_mem_edges_iff_exists.mpr
  refine ⟨0,by omega,?_⟩
  rw [q.getVert_zero,←hlen,Nat.zero_add,q.getVert_length]

/-- A shortest walk has no chord in its ambient graph. -/
theorem chordless_of_length_eq_dist {p : G.Walk a b} (hp : p.length=G.dist a b) :
    p.IsChordless := by
  induction p with
  | @nil a =>
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    have hx' : x=a := by simpa using hx
    have hy' : y=a := by simpa using hy
    exact (hxy.ne (hx'.trans hy'.symm)).elim
  | @cons a c b hac q ih =>
    have hq : q.length=G.dist c b := length_eq_dist_of_subwalk hp (q.isSubwalk_cons hac)
    have hc := ih hq
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    simp only [Walk.support_cons,List.mem_cons] at hx hy
    rcases hx with rfl|hx
    · exact start_edge_mem hp (by simpa only [Walk.support_cons,List.mem_cons] using hy) hxy
    · rcases hy with rfl|hy
      · rw [Sym2.eq_swap]
        exact start_edge_mem hp (by simp only [Walk.support_cons,List.mem_cons]; exact Or.inr hx) hxy.symm
      · exact List.mem_cons_of_mem _ (hc.mem_edges hx hy hxy)

/-- Induced embeddings preserve the absence of chords. -/
theorem chordless_map_embedding {W : Type*} {H : SimpleGraph W}
    (f : G ↪g H) {p : G.Walk a b} (hp : p.IsChordless) :
    (p.map f.toHom).IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  rw [Walk.support_map] at hx hy
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
  have he := hp.mem_edges hu hv (f.map_adj_iff.mp hxy)
  rw [Walk.edges_map]
  exact List.mem_map.mpr ⟨s(u,v),he,rfl⟩

/-- Reachable vertices are joined by a path having no chord. -/
theorem exists_chordless_path (h : G.Reachable a b) :
    ∃ p : G.Walk a b, p.IsPath ∧ p.IsChordless := by
  obtain ⟨p,hp,hlen⟩ := h.exists_path_of_dist
  exact ⟨p,hp,chordless_of_length_eq_dist hlen⟩

end GraphMinor.GM05
