module

public import GraphMinor.GM05.GraphCopies

/-!
# Isomorphisms of disjoint copy graphs

Apply a graph isomorphism separately in each copy, retaining the copy
index. Subgraph inclusions are preserved in the same way. These facts
allow the contraction witnesses used in (8.8) to be copied without any
assumption on ambient vertex or edge labels.
-/

public section

namespace GraphMinor.GM05

open Graph Set

private def copySetEquiv {α γ : Type*} {S : Set α} {T : Set γ}
    (k : ℕ) (e : S ≃ T) : (univ ×ˢ S : Set (Fin k × α)) ≃ (univ ×ˢ T : Set (Fin k × γ)) where
  toFun x := ⟨(x.1.1,(e ⟨x.1.2,x.2.2⟩).1),mem_univ _,(e ⟨x.1.2,x.2.2⟩).2⟩
  invFun x := ⟨(x.1.1,(e.symm ⟨x.1.2,x.2.2⟩).1),mem_univ _,(e.symm ⟨x.1.2,x.2.2⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (e.symm_apply_apply ⟨x.1.2,x.2.2⟩)
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨x.1.2,x.2.2⟩)

/-- Apply an isomorphism in every disjoint copy, preserving the copy index. -/
def copiesIso {α β γ δ : Type*} {H : Graph α β} {K : Graph γ δ}
    (k : ℕ) (φ : Iso H K) : Iso (graphCopies k H) (graphCopies k K) where
  vertexEquiv := copySetEquiv k φ.vertexEquiv
  edgeEquiv := copySetEquiv k φ.edgeEquiv
  isLink_iff e x y :=
    and_congr Iff.rfl (and_congr Iff.rfl
      (φ.isLink_iff ⟨e.1.2,e.2.2⟩ ⟨x.1.2,x.2.2⟩ ⟨y.1.2,y.2.2⟩))

/-- Copying preserves subgraph inclusions. -/
theorem graphCopies_mono {α β : Type*} {H G : Graph α β} (k : ℕ) (h : H≤G) :
    graphCopies k H≤graphCopies k G := by
  refine ⟨fun x hx ↦ ⟨mem_univ _,h.vertexSet_mono hx.2⟩,?_⟩
  intro e x y hxy
  exact ⟨hxy.1,hxy.2.1,h.isLink_mono hxy.2.2⟩

end GraphMinor.GM05
