module

public import GraphMinor.Kruskal.AddressMeet

/-!
# Embeddings on vertex addresses

A homeomorphic tree embedding sends distinct branches to distinct branches.
In terms of addresses, its injective vertex map preserves last common
ancestors. This implies preservation and reflection of ancestry. Prefixing
a target branch index preserves these properties and places an embedding
inside that target branch.
-/

@[expose] public section

namespace GraphMinor.Kruskal.OrderedTree

/-- The address form of a homeomorphic embedding: an injective map on
vertices that preserves the last common ancestor of every pair. The image
of the source root may lie below the target root. -/
structure AddressEmbedding (s t : OrderedTree) where
  vertices : {p // p ∈ s.addresses} ↪ {q // q ∈ t.addresses}
  meet_eq : ∀ p q : {p // p ∈ s.addresses},
    addressMeet (vertices p).val (vertices q).val =
      (vertices ⟨addressMeet p.val q.val, s.addressMeet_mem p.property⟩).val

namespace AddressEmbedding

/-- Ancestors map to ancestors. -/
theorem map_prefix {s t : OrderedTree} (φ : AddressEmbedding s t)
    (p q : {p // p ∈ s.addresses}) (hpq : p.val <+: q.val) :
    (φ.vertices p).val <+: (φ.vertices q).val := by
  have hm := φ.meet_eq p q
  have heq : (⟨addressMeet p.val q.val, s.addressMeet_mem p.property⟩ :
      {p // p ∈ s.addresses}) = p := Subtype.ext ((addressMeet_eq_left_iff _ _).2 hpq)
  rw [heq] at hm
  exact (addressMeet_eq_left_iff _ _).1 hm

/-- The embedding does not turn incomparable source vertices into ancestors
of one another. -/
theorem reflect_prefix {s t : OrderedTree} (φ : AddressEmbedding s t)
    (p q : {p // p ∈ s.addresses})
    (hpq : (φ.vertices p).val <+: (φ.vertices q).val) : p.val <+: q.val := by
  have hm := φ.meet_eq p q
  have ht := (addressMeet_eq_left_iff _ _).2 hpq
  have heq : φ.vertices ⟨addressMeet p.val q.val, s.addressMeet_mem p.property⟩ =
      φ.vertices p := Subtype.ext (hm.symm.trans ht)
  have hs := congrArg Subtype.val (φ.vertices.injective heq)
  exact (addressMeet_eq_left_iff _ _).1 hs

/-- An embedding into one branch gives an embedding into the whole target.
Prefixing every image address by the branch index preserves common ancestors. -/
def dive {s : OrderedTree} {ts : List OrderedTree} (i : Fin ts.length)
    (φ : AddressEmbedding s ts[i]) : AddressEmbedding s (.node ts) where
  vertices := {
    toFun := fun p ↦ ⟨i.val :: (φ.vertices p).val,
      (cons_mem_addresses_iff ts i.val _).2 ⟨i, rfl, (φ.vertices p).property⟩⟩
    inj' := by
      intro p q hpq
      have h := (List.cons.inj (congrArg Subtype.val hpq)).2
      exact φ.vertices.injective (Subtype.ext h) }
  meet_eq p q := by
    change addressMeet (i.val :: (φ.vertices p).val) (i.val :: (φ.vertices q).val) =
      i.val :: (φ.vertices ⟨addressMeet p.val q.val, s.addressMeet_mem p.property⟩).val
    simp only [addressMeet, ↓reduceIte, φ.meet_eq]

end AddressEmbedding
end GraphMinor.Kruskal.OrderedTree
