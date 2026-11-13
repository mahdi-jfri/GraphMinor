module

public import GraphMinor.GM05.FullWebDefs
import GraphMinor.GM05.Section4

/-!
# Valency in the union of actual web paths

Each path contributes at most two incident edges at a vertex. At most one
path in each vertex-disjoint family can contain a given vertex. Thus the
union of both families has maximum actual valency four, including when
opposite paths use parallel edges.
-/

public section
namespace GraphMinor.GM05.Full
open Graph Set SimpleGraph
variable {α β : Type*}

/-- Incidence in the host transfers to a path when the edge belongs to it. -/
theorem Path.inc_of_mem_edge {P : Path α β} {G : Graph α β} (hle : P.IsIn G)
    {e : β} {x : α} (hi : G.Inc e x) (he : e ∈ P.edgeSet) : P.toGraph.Inc e x := by
  obtain ⟨a, b, hab⟩ := exists_isLink_of_mem_edgeSet he
  rcases hi.eq_or_eq_of_isLink (hab.mono hle) with rfl | rfl
  · exact hab.inc_left
  · exact hab.inc_right

/-- A path has at most two incident actual edges at any vertex. -/
theorem Path.incident_ncard_le_two (P : Path α β) (x : α) :
    {e | P.toGraph.Inc e x}.ncard ≤ 2 := by
  let N : Set α := P.seq.toSubgraph.neighborSet x
  have hN : N.Finite := (List.finite_toSet P.seq.walk.support).subset (by
    intro y hy
    exact P.seq.walk.mem_verts_toSubgraph.mp (P.seq.toSubgraph.edge_vert hy.symm))
  letI : Finite N := hN.to_subtype
  let f : {e | P.toGraph.Inc e x} → N := fun e =>
    ⟨e.property.other, by
      have hne : x ≠ e.property.other := by
        intro h
        apply P.no_loops e.val x
        simpa only [← h] using e.property.isLink_other
      have hadj : (simpleShadow P.toGraph).Adj x e.property.other :=
        ⟨hne, e.val, e.property.isLink_other⟩
      rw [P.shadow_eq] at hadj
      exact hadj⟩
  have hinj : Function.Injective f := by
    intro e d hed
    have hother : e.property.other = d.property.other := congrArg Subtype.val hed
    apply Subtype.ext
    exact P.no_parallel e.val d.val x e.property.other e.property.isLink_other
      (hother.symm ▸ d.property.isLink_other)
  have hcard := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcard
  exact hcard.trans (GM05.walk_neighborSet_ncard_le_two P.seq.walk P.seq.isPath x)

/-- The actual incident edges used by a vertex-disjoint path family come
from at most one member, and hence number at most two. -/
theorem family_incident_ncard_le_two {G : Graph α β} {n : ℕ}
    (P : Fin n → Path α β) (hle : ∀ i, (P i).IsIn G)
    (hd : Pairwise fun i j => Disjoint (P i).verts (P j).verts) (x : α) :
    {e | G.Inc e x ∧ ∃ i, e ∈ (P i).edgeSet}.ncard ≤ 2 := by
  classical
  by_cases hx : ∃ i, x ∈ (P i).verts
  · obtain ⟨i, hxi⟩ := hx
    have heq : {e | G.Inc e x ∧ ∃ j, e ∈ (P j).edgeSet} =
        {e | (P i).toGraph.Inc e x} := by
      ext e
      constructor
      · rintro ⟨he, j, hej⟩
        have hij : j = i := by
          by_contra hne
          have hxj := (P j).inc_of_mem_edge (hle j) he hej
          exact Set.disjoint_left.mp (hd hne)
            ((P j).vertexSet_eq ▸ hxj.vertex_mem) hxi
        subst j
        exact (P i).inc_of_mem_edge (hle i) he hej
      · intro he
        obtain ⟨y, hey⟩ := he
        exact ⟨(hey.mono (hle i)).inc_left, i, hey.edge_mem⟩
    rw [heq]
    exact (P i).incident_ncard_le_two x
  · have heq : {e | G.Inc e x ∧ ∃ i, e ∈ (P i).edgeSet} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro e ⟨he, i, hei⟩
      have hxi := (P i).inc_of_mem_edge (hle i) he hei
      exact hx ⟨i, (P i).vertexSet_eq ▸ hxi.vertex_mem⟩
    rw [heq, Set.ncard_empty]
    exact Nat.zero_le _

/-- Restricting a host to the actual edges of a web gives maximum valency
four. Loops cannot occur because no input path uses them. -/
theorem IsWeb.restrict_valency_le_four {G : Graph α β} {m n : ℕ}
    {A : Fin m → Path α β} {B : Fin n → Path α β} (hw : IsWeb G A B) (x : α) :
    valency (G.restrict ((⋃ i, (A i).edgeSet) ∪ ⋃ j, (B j).edgeSet)) x ≤ 4 := by
  classical
  let F := (⋃ i, (A i).edgeSet) ∪ ⋃ j, (B j).edgeSet
  let K := G.restrict F
  have hinc : {e | K.Inc e x} =
      {e | G.Inc e x ∧ ∃ i, e ∈ (A i).edgeSet} ∪
      {e | G.Inc e x ∧ ∃ j, e ∈ (B j).edgeSet} := by
    ext e
    simp only [K, Graph.restrict_inc, F, Set.mem_union, Set.mem_iUnion,
      Set.mem_ofPred_eq, and_or_left]
  have hnoloop : {e | K.IsLoopAt e x} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have hlink : G.IsLink e x x := he.2
    rcases he.1 with heA | heB
    · obtain ⟨i, hei⟩ := Set.mem_iUnion.mp heA
      have hi := (A i).inc_of_mem_edge (hw.isIn_left i) hlink.inc_left hei
      obtain ⟨y, hiy⟩ := hi
      have hyx : y = x := (hiy.mono (hw.isIn_left i)).right_unique hlink
      exact (A i).no_loops e x (hyx ▸ hiy)
    · obtain ⟨i, hei⟩ := Set.mem_iUnion.mp heB
      have hi := (B i).inc_of_mem_edge (hw.isIn_right i) hlink.inc_left hei
      obtain ⟨y, hiy⟩ := hi
      have hyx : y = x := (hiy.mono (hw.isIn_right i)).right_unique hlink
      exact (B i).no_loops e x (hyx ▸ hiy)
  change {e | K.Inc e x}.ncard + {e | K.IsLoopAt e x}.ncard ≤ 4
  rw [hnoloop, Set.ncard_empty, Nat.add_zero, hinc]
  have hA := family_incident_ncard_le_two A hw.isIn_left hw.disjoint_left x
  have hB := family_incident_ncard_le_two B hw.isIn_right hw.disjoint_right x
  exact (Set.ncard_union_le _ _).trans (Nat.add_le_add hA hB)

end GraphMinor.GM05.Full
