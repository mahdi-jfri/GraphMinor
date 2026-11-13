module

public import GraphMinor.Kruskal.AddressIntervals
public import GraphMinor.Kruskal.EdgeChains

/-!
# Injective names for the replacing paths

Map original vertices by the address embedding and internal chain vertices
by prefixes along the image edge paths. No internal point is an image
vertex. Two internal points can agree only on the same source edge and at
the same depth. The chain segments have distinct heads, so the same map
also gives injective edge names in the target address tree.
-/

@[expose] public section

namespace GraphMinor.Kruskal.OrderedTree.AddressEmbedding

open Graph

/-- The chain lengths prescribed by the image paths of an address embedding. -/
noncomputable abbrev chains {s t : OrderedTree} (φ : AddressEmbedding s t) :=
  edgeChains s.addressParent s.addressChild φ.internalCount

/-- The address assigned to an original or internal chain vertex. -/
def rawVertex {s t : OrderedTree} (φ : AddressEmbedding s t) :
    V(rootedGraph s.toRootedTree) ⊕ (E(rootedGraph s.toRootedTree) × ℕ) → List ℕ
  | Sum.inl v => (φ.vertices v).val
  | Sum.inr (e, k) => φ.internalPoint e k

/-- Every actual chain vertex maps to an address of the target. -/
theorem rawVertex_mem {s t : OrderedTree} (φ : AddressEmbedding s t) (x : V(φ.chains)) :
    φ.rawVertex x.val ∈ t.addresses := by
  obtain ⟨x, hx⟩ := x
  cases x with
  | inl v => exact (φ.vertices v).property
  | inr p => exact φ.internalPoint_mem p.1 p.2

/-- The vertex map on the chain graph is injective. -/
theorem rawVertex_injective {s t : OrderedTree} (φ : AddressEmbedding s t) :
    Function.Injective (fun x : V(φ.chains) ↦ φ.rawVertex x.val) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  apply Subtype.ext
  cases x with
  | inl v =>
    cases y with
    | inl w =>
      have h : φ.vertices v = φ.vertices w := Subtype.ext hxy
      exact congrArg Sum.inl (φ.vertices.injective h)
    | inr p =>
      obtain ⟨e, k⟩ := p
      exact (φ.internalPoint_ne_image e hy v hxy.symm).elim
  | inr p =>
    obtain ⟨e, k⟩ := p
    cases y with
    | inl v => exact (φ.internalPoint_ne_image e hx v hxy).elim
    | inr p =>
      obtain ⟨f, l⟩ := p
      obtain ⟨hef, hkl⟩ := (φ.internalPoint_eq_iff e f hx hy).1 hxy
      subst f
      subst l
      rfl

/-- Injective target vertex names for the actual chain vertices. -/
def chainVertices {s t : OrderedTree} (φ : AddressEmbedding s t) : V(φ.chains) ↪ List ℕ :=
  ⟨fun x ↦ φ.rawVertex x.val, φ.rawVertex_injective⟩

/-- The head of a chain segment, oriented toward its source child. -/
noncomputable def chainHead {s t : OrderedTree} (φ : AddressEmbedding s t)
    (d : E(φ.chains)) : V(φ.chains) :=
  ⟨chainFinish s.addressChild φ.internalCount d.val, by
    have h : φ.chains.IsLink d.val
        (chainStem s.addressParent d.val.1 (d.val.2 / 2))
        (chainFinish s.addressChild φ.internalCount d.val) :=
      ⟨d.property, Or.inl ⟨rfl, rfl⟩⟩
    exact h.right_mem⟩

private theorem chainFinish_injective_aux {s t : OrderedTree} (φ : AddressEmbedding s t)
    {e f : E(rootedGraph s.toRootedTree)} {j l : ℕ}
    (hj : chainSlot φ.internalCount (e, j)) (hl : chainSlot φ.internalCount (f, l))
    (h : chainFinish s.addressChild φ.internalCount (e, j) =
      chainFinish s.addressChild φ.internalCount (f, l)) : (e, j) = (f, l) := by
  classical
  by_cases hj₀ : j = 2 * φ.internalCount e
  · by_cases hl₀ : l = 2 * φ.internalCount f
    · simp only [chainFinish, hj₀, hl₀, ↓reduceIte] at h
      have hchild : s.addressChild e = s.addressChild f := Sum.inl.inj h
      have hef : e = f := Subtype.ext
        (congrArg (fun p : {p // p ∈ s.addresses} ↦ p.val) hchild)
      subst f
      exact Prod.ext rfl (hj₀.trans hl₀.symm)
    · simp only [chainFinish, hj₀, hl₀, ↓reduceIte] at h
      cases h
  · by_cases hl₀ : l = 2 * φ.internalCount f
    · simp only [chainFinish, hj₀, hl₀, ↓reduceIte] at h
      cases h
    · simp only [chainFinish, hj₀, hl₀, ↓reduceIte] at h
      obtain ⟨hef, hdiv⟩ := Prod.mk.inj (Sum.inr.inj h)
      subst f
      have hjl : j = l := by
        change j = 2 * φ.internalCount e ∨ j % 2 = 1 ∧ j < 2 * φ.internalCount e at hj
        change l = 2 * φ.internalCount e ∨ l % 2 = 1 ∧ l < 2 * φ.internalCount e at hl
        omega
      exact Prod.ext rfl hjl

/-- Distinct chain segments have distinct heads. -/
theorem chainHead_injective {s t : OrderedTree} (φ : AddressEmbedding s t) :
    Function.Injective φ.chainHead := by
  intro d f h
  exact Subtype.ext (chainFinish_injective_aux φ d.property f.property (congrArg Subtype.val h))

/-- Injective target edge names, given by the addresses of the segment heads. -/
noncomputable def chainEdges {s t : OrderedTree} (φ : AddressEmbedding s t) :
    E(φ.chains) ↪ List ℕ :=
  (⟨φ.chainHead, φ.chainHead_injective⟩ : E(φ.chains) ↪ V(φ.chains)).trans φ.chainVertices

end GraphMinor.Kruskal.OrderedTree.AddressEmbedding
