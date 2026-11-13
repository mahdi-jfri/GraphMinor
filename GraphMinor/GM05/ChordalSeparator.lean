module

public import GraphMinor.GM05.ChordalDefs
import GraphMinor.GM05.ChordalCycles
import GraphMinor.GM05.ChordlessPaths
import GraphMinor.GM05.MinimalSeparator

/-!
# Minimal separators in chordal graphs are cliques

Every vertex in a minimal separator has a neighbor in each of two full
components. If two separator vertices were nonadjacent, shortest paths
through the two components would form an induced circuit of length at
least four. The components have no edges between them, so the circuit has
no chord. This contradicts chordality and supplies the separator step in
the proof of Graph Minors V, (8.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

private lemma path_through_set {A : Set V} (hA : (G.induce A).Connected)
    {s t : V} (hs : ∃ x∈A, G.Adj s x) (ht : ∃ y∈A, G.Adj t y) :
    ∃ p : G.Walk s t, p.IsPath ∧ p.IsChordless ∧
      ∀ z∈p.support, z=s ∨ z=t ∨ z∈A := by
  obtain ⟨x,hx,hsx⟩ := hs
  obtain ⟨y,hy,hty⟩ := ht
  let U := insert s (insert t A)
  let f : G.induce A →g G.induce U := {
    toFun z := ⟨z.1,Or.inr (Or.inr z.2)⟩
    map_rel' := fun h ↦ h }
  let su : U := ⟨s,Or.inl rfl⟩
  let tu : U := ⟨t,Or.inr (Or.inl rfl)⟩
  have hsu : (G.induce U).Adj su (f ⟨x,hx⟩) := hsx
  have htu : (G.induce U).Adj (f ⟨y,hy⟩) tu := hty.symm
  have hr := hsu.reachable.trans (((hA ⟨x,hx⟩ ⟨y,hy⟩).map f).trans htu.reachable)
  obtain ⟨p,hp,hc⟩ := exists_chordless_path hr
  let e : G.induce U ↪g G := Embedding.induce U
  have hbound : ∀ z∈(p.map e.toHom).support, z=s ∨ z=t ∨ z∈A := by
    intro z hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact w.2
  exact ⟨p.map e.toHom,hp.map e.injective,chordless_map_embedding e hc,hbound⟩

private lemma start_not_tail {s t : V} {p : G.Walk s t} (hp : p.IsPath) :
    s∉p.support.tail := by
  have h := hp.support_nodup
  rw [←p.cons_tail_support] at h
  exact (List.nodup_cons.mp h).1

private lemma adj_of_separated_paths (hG : IsChordal G) {A B : Set V}
    (hAB : Disjoint A B) (hcross : ∀ x∈A, ∀ y∈B, ¬G.Adj x y)
    {s t : V} (hst : s≠t)
    {p q : G.Walk s t} (hp : p.IsPath) (hq : q.IsPath)
    (hcp : p.IsChordless) (hcq : q.IsChordless)
    (hPA : ∀ x∈p.support, x=s ∨ x=t ∨ x∈A)
    (hQB : ∀ x∈q.support, x=s ∨ x=t ∨ x∈B) : G.Adj s t := by
  by_contra hno
  have hlen (r : G.Walk s t) : 2≤r.length := by
    by_contra hn
    have he : r.length=0 ∨ r.length=1 := by omega
    rcases he with he|he
    · exact hst (Walk.eq_of_length_eq_zero he)
    · exact hno (Walk.adj_of_length_eq_one he)
  have htail : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro x hx hy
    have hxp := List.mem_of_mem_tail hx
    have hxq : x∈q.support := by
      simpa only [Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail hy
    have hxs : x≠s := fun he ↦ start_not_tail hp (he ▸ hx)
    have hxt : x≠t := fun he ↦ start_not_tail hq.reverse (he ▸ hy)
    have hxA : x∈A := ((hPA x hxp).resolve_left hxs).resolve_left hxt
    have hxB : x∈B := ((hQB x hxq).resolve_left hxs).resolve_left hxt
    exact Set.disjoint_left.mp hAB hxA hxB
  have hcycle := hp.isCycle_append hq.reverse htail (Or.inl (by have := hlen p; omega))
  have cross_edges : ∀ x∈p.support, ∀ y∈q.support, G.Adj x y →
      s(x,y)∈p.edges ∨ s(x,y)∈q.edges := by
    intro x hx y hy hxy
    rcases hPA x hx with rfl|rfl|hxA
    · exact Or.inr (hcq.mem_edges q.start_mem_support hy hxy)
    · exact Or.inr (hcq.mem_edges q.end_mem_support hy hxy)
    · rcases hQB y hy with rfl|rfl|hyB
      · exact Or.inl (hcp.mem_edges hx p.start_mem_support hxy)
      · exact Or.inl (hcp.mem_edges hx p.end_mem_support hxy)
      · exact (hcross x hxA y hyB hxy).elim
  have hc : (p.append q.reverse).IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    have hm : ∀ z, z∈(p.append q.reverse).support → z∈p.support ∨ z∈q.support := by
      intro z hz
      simpa only [Walk.mem_support_append_iff,Walk.support_reverse,List.mem_reverse] using hz
    have he : s(x,y)∈p.edges ∨ s(x,y)∈q.edges := by
      rcases hm x hx with hx|hx
      · rcases hm y hy with hy|hy
        · exact Or.inl (hcp.mem_edges hx hy hxy)
        · exact cross_edges x hx y hy hxy
      · rcases hm y hy with hy|hy
        · have hh := cross_edges y hy x hx hxy.symm
          simpa only [Sym2.eq_swap] using hh
        · exact Or.inr (hcq.mem_edges hx hy hxy)
    simpa only [Walk.edges_append,Walk.edges_reverse,List.mem_append,List.mem_reverse] using he
  have hbound := hG.chordless_cycle_length_le hcycle hc
  have hpL := hlen p
  have hqL := hlen q
  simp only [Walk.length_append,Walk.length_reverse] at hbound
  omega

/-- A finite chordal graph with two distinct nonadjacent vertices has a
clique separator with two full components. -/
theorem exists_clique_separator [Finite V] (hG : IsChordal G)
    {a b : V} (hab : a≠b) (hn : ¬G.Adj a b) :
    ∃ S A B : Set V,
      G.IsClique S ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ Disjoint A S ∧ Disjoint B S ∧
      (∀ x∈A, ∀ y, G.Adj x y → y∈A ∨ y∈S) ∧
      (∀ x∈B, ∀ y, G.Adj x y → y∈B ∨ y∈S) := by
  obtain ⟨S,A,B,hA,hB,hAB,hAS,hBS,hconnA,hconnB,hN,hclosedA,hclosedB⟩ :=
    exists_full_components hab hn
  refine ⟨S,A,B,?_,hA,hB,hAB,hAS,hBS,hclosedA,hclosedB⟩
  intro s hs t ht hst
  obtain ⟨p,hp,hcp,hPA⟩ := path_through_set hconnA (hN s hs).1 (hN t ht).1
  obtain ⟨q,hq,hcq,hQB⟩ := path_through_set hconnB (hN s hs).2 (hN t ht).2
  have hcross : ∀ x∈A, ∀ y∈B, ¬G.Adj x y := by
    intro x hx y hy hxy
    rcases hclosedA x hx y hxy with hyA|hyS
    · exact Set.disjoint_left.mp hAB hyA hy
    · exact Set.disjoint_left.mp hBS hy hyS
  exact adj_of_separated_paths hG hAB hcross hst
    hp hq hcp hcq hPA hQB

end GraphMinor.GM05
