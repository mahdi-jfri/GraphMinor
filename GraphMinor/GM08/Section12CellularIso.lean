module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section9DiscContext

/-!
# The graph isomorphism of the cellular loop replacement

The old vertices keep their positions. Each non-loop edge stays fixed,
and each loop edge goes to its petal boundary minus the marked end.
The petal edges are nonempty, mutually disjoint, and miss the old drawing,
so this is a bijection of edges. Their end sets are unchanged, giving
the graph isomorphism needed for the cellular graft drawing in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The petal replacement changes no abstract graph or root position.
This is the isomorphism check for the cellular drawing used in VIII,
Section 12, page 274. -/
theorem exists_iso_loop_replacement {S : Type u} [TopologicalSpace S]
    (D H : Drawing S)
    (v : {e : Set S // e ∈ D.E ∧ D.IsLoop e} → S)
    (E : {e : Set S // e ∈ D.E ∧ D.IsLoop e} → Set S)
    (hE : ∀ i, closure i.1 ∩ D.V = {v i} ∧ IsClosedDisc (E i) ∧
      v i ∈ discBd (E i) ∧ E i ∩ D.U = {v i} ∧
      closure (discBd (E i) \ {v i}) = discBd (E i))
    (hEE : ∀ i j, i ≠ j → E i ∩ E j ⊆ {v i} ∩ {v j})
    (hV : H.V = D.V)
    (hEdges : H.E = {e ∈ D.E | ¬ D.IsLoop e} ∪ range (fun i => discBd (E i) \ {v i})) :
    ∃ a : Iso D.toGraph H.toGraph, ∀ x : Graph.vertexSet D.toGraph,
      (a.vertexEquiv x).1 = x.1 := by
  classical
  let L := {e : Set S // e ∈ D.E ∧ D.IsLoop e}
  let edge : Graph.edgeSet D.toGraph → Set S := fun e =>
    if hl : D.IsLoop e.1 then discBd (E ⟨e.1, e.2, hl⟩) \ {v ⟨e.1, e.2, hl⟩} else e.1
  have hmem : ∀ e, edge e ∈ H.E := by
    intro e
    rw [hEdges]
    by_cases hl : D.IsLoop e.1
    · exact .inr ⟨⟨e.1, e.2, hl⟩, by simp only [edge, dite_eq_left hl]⟩
    · simpa only [edge, dite_eq_right hl] using
        (show e.1 ∈ {e ∈ D.E | ¬ D.IsLoop e} ∪ range (fun i => discBd (E i) \ {v i}) from .inl ⟨e.2, hl⟩)
  have hoff : ∀ i : L, Disjoint (discBd (E i) \ {v i}) D.U := by
    intro i
    apply disjoint_left.mpr
    rintro x ⟨hxb, hxv⟩ hxU
    exact hxv ((hE i).2.2.2.1 ▸ And.intro (discBd_subset _ hxb) hxU)
  have hpair : ∀ i j : L, i ≠ j → Disjoint (discBd (E i) \ {v i}) (discBd (E j) \ {v j}) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨hxi, hxv⟩ ⟨hxj, -⟩
    exact hxv (hEE i j hij ⟨discBd_subset _ hxi, discBd_subset _ hxj⟩).1
  have hinj : Function.Injective edge := by
    intro e f hef
    by_cases he : D.IsLoop e.1
    · by_cases hf : D.IsLoop f.1
      · let i : L := ⟨e.1, e.2, he⟩
        let j : L := ⟨f.1, f.2, hf⟩
        have heq : discBd (E i) \ {v i} = discBd (E j) \ {v j} := by
          simpa only [edge, dite_eq_left he, dite_eq_left hf] using hef
        by_contra hne
        have hij : i ≠ j := by
          intro h
          have hv := congrArg (fun k : L => k.1) h
          exact hne (Subtype.ext hv)
        obtain ⟨x, hx⟩ := (hmem e).1
        have hxi : x ∈ discBd (E i) \ {v i} := by simpa only [edge, dite_eq_left he] using hx
        exact disjoint_left.mp (hpair i j hij) hxi (heq ▸ hxi)
      · obtain ⟨x, hx⟩ := (hmem e).1
        have hxi : x ∈ discBd (E ⟨e.1, e.2, he⟩) \ {v ⟨e.1, e.2, he⟩} := by
          simpa only [edge, dite_eq_left he] using hx
        have hxF : x ∈ edge f := by rw [← hef]; exact hx
        have hxf : x ∈ f.1 := by simpa only [edge, dite_eq_right hf] using hxF
        exact False.elim (disjoint_left.mp (hoff _) hxi ((f.2.2.1 hxf).1))
    · by_cases hf : D.IsLoop f.1
      · obtain ⟨x, hx⟩ := (hmem f).1
        have hxj : x ∈ discBd (E ⟨f.1, f.2, hf⟩) \ {v ⟨f.1, f.2, hf⟩} := by
          simpa only [edge, dite_eq_left hf] using hx
        have hxE : x ∈ edge e := by rw [hef]; exact hx
        have hxe : x ∈ e.1 := by simpa only [edge, dite_eq_right he] using hxE
        exact False.elim (disjoint_left.mp (hoff _) hxj ((e.2.2.1 hxe).1))
      · apply Subtype.ext
        simpa only [edge, dite_eq_right he, dite_eq_right hf] using hef
  let f : Graph.edgeSet D.toGraph → Graph.edgeSet H.toGraph := fun e => ⟨edge e, hmem e⟩
  have hf : Function.Bijective f := by
    refine ⟨fun e e' heq => hinj (congrArg Subtype.val heq), ?_⟩
    rintro ⟨e, he⟩
    change e ∈ H.E at he
    rw [hEdges] at he
    rcases he with ⟨heD, hnl⟩ | ⟨i, rfl⟩
    · exact ⟨⟨e, heD⟩, Subtype.ext (by simp only [f, edge, dite_eq_right hnl])⟩
    · exact ⟨⟨i.1, i.2.1⟩, Subtype.ext (by simp only [f, edge, dite_eq_left i.2.2])⟩
  have hcap : ∀ e : Graph.edgeSet D.toGraph, closure (edge e) ∩ H.V = closure e.1 ∩ D.V := by
    intro e
    rw [hV]
    by_cases hl : D.IsLoop e.1
    · let i : L := ⟨e.1, e.2, hl⟩
      have heq : edge e = discBd (E i) \ {v i} := by simp only [edge, i, dite_eq_left hl]
      rw [heq, (hE i).2.2.2.2, (hE i).1]
      apply Subset.antisymm
      · intro x hx
        exact (hE i).2.2.2.1 ▸ And.intro (discBd_subset _ hx.1) (D.V_subset_U hx.2)
      · intro x hx
        have hxv : x = v i := mem_singleton_iff.mp hx
        rw [hxv]
        have hvpair : v i ∈ closure i.1 ∩ D.V := (hE i).1.symm ▸ mem_singleton (v i)
        exact ⟨(hE i).2.2.1, hvpair.2⟩
    · simp only [edge, dite_eq_right hl]
  let a : Iso D.toGraph H.toGraph := {
    vertexEquiv := {
      toFun := fun x => ⟨x.1, by change x.1 ∈ H.V; rw [hV]; exact x.2⟩
      invFun := fun x => ⟨x.1, by change x.1 ∈ D.V; rw [← hV]; exact x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    edgeEquiv := Equiv.ofBijective f hf
    isLink_iff := fun e x y => by
      change D.toGraph.IsLink e.1 x.1 y.1 ↔ H.toGraph.IsLink (edge e) x.1 y.1
      constructor
      · intro hl
        refine ⟨hmem e, hV.symm ▸ x.2, hV.symm ▸ y.2, ?_⟩
        rw [hcap e]
        exact hl.2.2.2
      · intro hl
        refine ⟨e.2, x.2, y.2, ?_⟩
        rw [← hcap e]
        exact hl.2.2.2 }
  exact ⟨a, fun _ => rfl⟩

end GraphMinor.GM08
