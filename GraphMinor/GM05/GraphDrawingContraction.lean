module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Statement
import GraphMinor.GM05.DrawingSetContraction
import GraphMinor.GM05.DrawingContractionClasses
import GraphMinor.GM05.ContractionReachIso
import GraphMinor.GM05.ContractionImageIso
import GraphMinor.GM19.Section6a

/-!
# Contracting an abstract graph drawing

For GM V, (8.14), transfer the selected abstract edges through the
isomorphism of a graph drawing, contract their geometric arcs, and
identify the result with the abstract contraction. All maps are on
the actual vertex and edge supports, so empty graphs and unused names
need no extra assumptions.
-/

public section
namespace GraphMinor.GM05
open Set Topology Graph Surface
universe u v

/-- The contraction step used in GM V, proof of (8.14), page 113:
contracting edges of a graph drawn on a closed surface preserves its
drawability, including loops, parallel edges and empty supports. -/
theorem graphDrawing_contract {α : Type u} {β : Type v} {G : Graph α β}
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S) (Γ : GraphDrawing G S)
    (C : Set β) : Nonempty (GraphDrawing (contract G C) S) := by
  classical
  let : T2Space S := hS.2.1
  let D := Γ.drawing
  let C' : Set (Set S) := {e | ∃ a : E(G),a.val∈C ∧ (Γ.iso.edgeEquiv a).val=e}
  have hC' : C'⊆D.E := by
    rintro e ⟨a,ha,rfl⟩
    exact (Γ.iso.edgeEquiv a).prop
  have hCmap : ∀ e : E(G),e.val∈C ↔ (Γ.iso.edgeEquiv e).val∈C' := by
    intro e
    constructor
    · exact fun he ↦ ⟨e,he,rfl⟩
    · rintro ⟨a,ha,he⟩
      have hae : a=e := Γ.iso.edgeEquiv.injective (Subtype.ext he)
      exact hae ▸ ha
  obtain ⟨H,π,ε,hHV,hπ,hε,hεt⟩ := exists_drawing_contract_set hS D hC'
  let F : V(G) → V(H.toGraph) := fun x ↦
    ⟨π (Γ.iso.vertexEquiv x).val,by
      change π (Γ.iso.vertexEquiv x).val∈H.V
      rw [hHV]
      exact mem_image_of_mem _ (Γ.iso.vertexEquiv x).prop⟩
  have hFs : Function.Surjective F := by
    intro y
    have hyH : y.val∈H.V := y.prop
    have hy : y.val∈π '' D.V := by simpa only [hHV] using hyH
    obtain ⟨z,hz,hzy⟩ := hy
    refine ⟨Γ.iso.vertexEquiv.symm ⟨z,hz⟩,Subtype.ext ?_⟩
    change π (Γ.iso.vertexEquiv (Γ.iso.vertexEquiv.symm ⟨z,hz⟩)).val=y.val
    rw [Equiv.apply_symm_apply]
    exact hzy
  have hFk : ∀ x y : V(G),F x=F y ↔ y.val∈contractionClass G C x.val := by
    intro x y
    change (⟨π (Γ.iso.vertexEquiv x).val,_⟩ : V(H.toGraph))=⟨π (Γ.iso.vertexEquiv y).val,_⟩ ↔ _
    rw [Subtype.ext_iff]
    exact (hπ _ (Γ.iso.vertexEquiv x).prop _ (Γ.iso.vertexEquiv y).prop).trans
      ((drawing_endpoint_equiv_iff_reach D hC' _ _).trans
        (contraction_reach_iff_of_iso Γ.iso hCmap x y).symm)
  let η : E(contract G C) → E(contract D.toGraph C') := fun e ↦
    ⟨(Γ.iso.edgeEquiv ⟨e.val,e.prop.1⟩).val,
      (Γ.iso.edgeEquiv ⟨e.val,e.prop.1⟩).prop,fun he ↦ e.prop.2 ((hCmap _).mpr he)⟩
  have hηi : Function.Injective η := by
    intro e f he
    have hval : (Γ.iso.edgeEquiv ⟨e.val,e.prop.1⟩).val=(Γ.iso.edgeEquiv ⟨f.val,f.prop.1⟩).val :=
      congrArg (fun z : E(contract D.toGraph C') ↦ z.val) he
    have hh := Γ.iso.edgeEquiv.injective (Subtype.ext hval)
    exact Subtype.ext (congrArg (fun x : E(G) ↦ x.val) hh)
  have hηs : Function.Surjective η := by
    intro e
    let a := Γ.iso.edgeEquiv.symm ⟨e.val,e.prop.1⟩
    have ha : a.val∉C := by
      intro hac
      have hh := (hCmap a).mp hac
      have heq : (Γ.iso.edgeEquiv a).val=e.val := by simp only [a,Equiv.apply_symm_apply]
      exact e.prop.2 (heq ▸ hh)
    refine ⟨⟨a.val,a.prop,ha⟩,Subtype.ext ?_⟩
    change (Γ.iso.edgeEquiv a).val=e.val
    exact congrArg Subtype.val (Γ.iso.edgeEquiv.apply_symm_apply ⟨e.val,e.prop.1⟩)
  let E : E(contract G C) → E(H.toGraph) := (Set.BijOn.equiv ε hε)∘η
  have hEb : Function.Bijective E := (Set.BijOn.equiv ε hε).bijective.comp ⟨hηi,hηs⟩
  have hlink : ∀ (e : E(contract G C)) (x y : V(G)),G.IsLink e.val x.val y.val →
      H.toGraph.IsLink (E e).val (F x).val (F y).val := by
    intro e x y hxy
    have hd := (Γ.iso.isLink_iff ⟨e.val,e.prop.1⟩ x y).mp hxy
    have hpair : tilde (E e).val={(F x).val,(F y).val} := by
      change tilde (ε (Γ.iso.edgeEquiv ⟨e.val,e.prop.1⟩).val)=_
      rw [hεt _ (η e).prop,GM19.tilde_eq_inter_V D (Γ.iso.edgeEquiv ⟨e.val,e.prop.1⟩).prop,
        hd.2.2.2,image_pair]
    refine ⟨(E e).prop,(F x).prop,(F y).prop,?_⟩
    exact (GM19.tilde_eq_inter_V H (E e).prop).symm.trans hpair
  obtain ⟨φ⟩ := exists_iso_contraction_of_support_maps G H.toGraph C F hFs hFk E hEb hlink
  exact ⟨⟨H,φ⟩⟩

end GraphMinor.GM05
