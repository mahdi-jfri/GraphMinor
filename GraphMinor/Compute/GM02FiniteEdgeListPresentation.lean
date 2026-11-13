module

public import GraphMinor.Compute.GM02EdgeListInput

/-!
# Edge-list presentations of finite fixed graphs

Number the actual vertices and edges independently. Choose the two
ends of each actual edge and list their numbered images in edge order.
This represents every finite graph, including isolated vertices, loops,
and repeated edges. Only the fixed target is numbered this way, so no
derived data is added to an algorithm's host input.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- Every finite graph has an isomorphic ordinary edge-list presentation. -/
theorem exists_gm02EdgeListPresentation {A B : Type*} (H : Graph A B)
    (hV : V(H).Finite) (hE : E(H).Finite) :
    ∃ x : GM02EdgeListInput, Nonempty (Iso H x.graph) := by
  let : Fintype V(H) := hV.fintype
  let : Fintype E(H) := hE.fintype
  let n := Fintype.card V(H)
  let m := Fintype.card E(H)
  let a : V(H) ≃ Fin n := Fintype.equivFin _
  let b : E(H) ≃ Fin m := Fintype.equivFin _
  choose l r hr using fun i : Fin m => Graph.exists_isLink_of_mem_edgeSet (b.symm i).property
  let left : Fin m → V(H) := fun i => ⟨l i, (hr i).left_mem⟩
  let right : Fin m → V(H) := fun i => ⟨r i, (hr i).right_mem⟩
  let ends : Fin m → Fin n × Fin n := fun i => (a (left i), a (right i))
  let x : GM02EdgeListInput := ⟨n, List.ofFn ends⟩
  let va : V(H) ≃ V(x.graph) := a.trans {
    toFun := fun i => ⟨i.val, i.isLt⟩
    invFun := fun i => ⟨i.val, i.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  let eb : E(H) ≃ E(x.graph) := {
    toFun := fun e => ⟨(b e).val, by simpa only [GM02EdgeListInput.graph_edges, x, List.length_ofFn, Set.mem_Iio] using (b e).isLt⟩
    invFun := fun e => b.symm ⟨e.val, by simpa only [GM02EdgeListInput.graph_edges, x, List.length_ofFn, Set.mem_Iio] using e.property⟩
    left_inv := fun e => b.symm_apply_apply e
    right_inv := fun e => by apply Subtype.ext; exact congrArg Fin.val (b.apply_symm_apply _) }
  refine ⟨x, ⟨{ vertexEquiv := va, edgeEquiv := eb, isLink_iff := ?_ }⟩⟩
  intro e u v
  have hlink : H.IsLink e.val (left (b e)).val (right (b e)).val := by
    simpa only [left, right, Equiv.symm_apply_apply] using hr (b e)
  have he : (b e).val < x.edges.length := by simpa only [GM02EdgeListInput.graph_edges, x, List.length_ofFn, Set.mem_Iio] using (b e).isLt
  change H.IsLink e.val u.val v.val ↔ x.graph.IsLink (b e).val (a u).val (a v).val
  constructor
  · intro h
    refine ⟨he, ?_⟩
    change s((a u).val, (a v).val) = s((x.edges[(b e).val]'he).1.val, (x.edges[(b e).val]'he).2.val)
    simp only [x, List.getElem_ofFn, Fin.eta, ends]
    rcases h.eq_and_eq_or_eq_and_eq hlink with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Sym2.eq_iff.2 (Or.inl ⟨congrArg (fun z => (a z).val) (Subtype.ext hu),
        congrArg (fun z => (a z).val) (Subtype.ext hv)⟩)
    · exact Sym2.eq_iff.2 (Or.inr ⟨congrArg (fun z => (a z).val) (Subtype.ext hu),
        congrArg (fun z => (a z).val) (Subtype.ext hv)⟩)
  · rintro ⟨_, h⟩
    change s((a u).val, (a v).val) = s((x.edges[(b e).val]'he).1.val, (x.edges[(b e).val]'he).2.val) at h
    simp only [x, List.getElem_ofFn, Fin.eta, ends] at h
    rcases Sym2.eq_iff.1 h with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · have hu' := congrArg Subtype.val (a.injective (Fin.ext hu))
      have hv' := congrArg Subtype.val (a.injective (Fin.ext hv))
      rw [hu', hv']
      exact hlink
    · have hu' := congrArg Subtype.val (a.injective (Fin.ext hu))
      have hv' := congrArg Subtype.val (a.injective (Fin.ext hv))
      rw [hu', hv']
      exact hlink.symm

end GraphMinor.Compute
