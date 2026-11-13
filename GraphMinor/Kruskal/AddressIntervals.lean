module

public import GraphMinor.Kruskal.AddressEmbedding
public import GraphMinor.Kruskal.RootedGraph

/-!
# The paths replacing edges of an address embedding

An edge joins a vertex to its parent address. Its image is the prefix path
between the two image addresses. Preservation of last common ancestors forces
these open paths to avoid all image vertices and the open paths of other
edges. We prove the separation fact and the lengths needed to name their
internal vertices.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph OrderedTree

/-- Every proper prefix stops at or before the parent address. -/
theorem proper_prefix_dropLast {p q : List ℕ} (hp : p <+: q) (hne : p ≠ q) :
    p <+: q.dropLast := by
  have hlt : p.length < q.length := by
    rcases Nat.eq_or_lt_of_le hp.length_le with h | h
    · exact (hne (hp.eq_of_length h)).elim
    · exact h
  apply List.prefix_of_prefix_length_le hp (List.dropLast_prefix q)
  rw [List.length_dropLast]
  omega

namespace OrderedTree

/-- The child end of an edge of the underlying address tree. -/
def addressChild (s : OrderedTree) (e : E(rootedGraph s.toRootedTree)) :
    {p // p ∈ s.addresses} :=
  ⟨e.val, s.toRootedTree.mem_verts_of_mem_edges e.property⟩

/-- The parent end of that edge. -/
def addressParent (s : OrderedTree) (e : E(rootedGraph s.toRootedTree)) :
    {p // p ∈ s.addresses} :=
  ⟨e.val.dropLast, s.dropLast_mem_addresses e.val (s.addressChild e).property⟩

namespace AddressEmbedding

/-- Image parents are ancestors of image children. -/
theorem parent_prefix_child {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) :
    (φ.vertices (s.addressParent e)).val <+: (φ.vertices (s.addressChild e)).val :=
  φ.map_prefix _ _ (List.dropLast_prefix e.val)

/-- A source edge maps to a path of positive length. -/
theorem parent_length_lt_child {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) :
    (φ.vertices (s.addressParent e)).val.length < (φ.vertices (s.addressChild e)).val.length := by
  have hne : (φ.vertices (s.addressParent e)).val ≠ (φ.vertices (s.addressChild e)).val := by
    intro h
    have heq := φ.vertices.injective (Subtype.ext h)
    have hlen : e.val.dropLast.length = e.val.length := congrArg (fun x ↦ x.val.length) heq
    have hen : e.val ≠ [] := s.toRootedTree.ne_root_of_mem_edges e.property
    have hpos : 0 < e.val.length := List.length_pos_iff.2 hen
    rw [List.length_dropLast] at hlen
    omega
  have hp := φ.parent_prefix_child e
  rcases Nat.eq_or_lt_of_le hp.length_le with h | h
  · exact (hne (hp.eq_of_length h)).elim
  · exact h

/-- The number of internal vertices on the path replacing a source edge. -/
def internalCount {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) : ℕ :=
  (φ.vertices (s.addressChild e)).val.length - (φ.vertices (s.addressParent e)).val.length - 1

/-- The replacing path has one more edge than internal vertices. -/
theorem child_length_eq {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) :
    (φ.vertices (s.addressChild e)).val.length =
      (φ.vertices (s.addressParent e)).val.length + φ.internalCount e + 1 := by
  have h := φ.parent_length_lt_child e
  unfold internalCount
  omega

/-- A point beyond the image parent which is an ancestor of two image
vertices forces the source child to be an ancestor of the second vertex. -/
theorem child_prefix_of_common_point {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (w : {p // p ∈ s.addresses}) (r : List ℕ)
    (hrv : r <+: (φ.vertices (s.addressChild e)).val)
    (hrw : r <+: (φ.vertices w).val)
    (hlen : (φ.vertices (s.addressParent e)).val.length < r.length) :
    e.val <+: w.val := by
  by_contra hnot
  let m : {p // p ∈ s.addresses} :=
    ⟨addressMeet e.val w.val, s.addressMeet_mem (s.addressChild e).property⟩
  have hmne : m.val ≠ e.val := by
    intro h
    exact hnot ((addressMeet_eq_left_iff e.val w.val).1 h)
  have hmparent : m.val <+: (s.addressParent e).val :=
    proper_prefix_dropLast (addressMeet_prefix_left e.val w.val) hmne
  have himg := φ.map_prefix m (s.addressParent e) hmparent
  have hrm : r <+: (φ.vertices m).val := by
    have h := prefix_addressMeet hrv hrw
    rw [φ.meet_eq] at h
    exact h
  have h₁ := hrm.length_le
  have h₂ := himg.length_le
  omega

/-- The `k`th internal point, read as a prefix of the image child address. -/
def internalPoint {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (k : ℕ) : List ℕ :=
  (φ.vertices (s.addressChild e)).val.take
    ((φ.vertices (s.addressParent e)).val.length + k + 1)

/-- The named point is an ancestor of its image child. -/
theorem internalPoint_prefix {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (k : ℕ) :
    φ.internalPoint e k <+: (φ.vertices (s.addressChild e)).val :=
  List.take_prefix _ _

/-- Every named point is a vertex of the target tree. -/
theorem internalPoint_mem {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) (k : ℕ) : φ.internalPoint e k ∈ t.addresses :=
  t.prefix_mem_addresses (φ.vertices (s.addressChild e)).property (φ.internalPoint_prefix e k)

/-- Internal points have their prescribed depths. -/
theorem internalPoint_length {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) {k : ℕ} (hk : k < φ.internalCount e) :
    (φ.internalPoint e k).length = (φ.vertices (s.addressParent e)).val.length + k + 1 := by
  have hlen := φ.child_length_eq e
  rw [internalPoint, List.length_take]
  exact Nat.min_eq_left (by omega)

/-- No internal point is an image of a source vertex. -/
theorem internalPoint_ne_image {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e : E(rootedGraph s.toRootedTree)) {k : ℕ} (hk : k < φ.internalCount e)
    (w : {p // p ∈ s.addresses}) : φ.internalPoint e k ≠ (φ.vertices w).val := by
  intro heq
  have hlen := φ.internalPoint_length e hk
  have hprefix : e.val <+: w.val := φ.child_prefix_of_common_point e w
    (φ.internalPoint e k) (φ.internalPoint_prefix e k)
    (heq.symm ▸ List.prefix_rfl) (by omega)
  have hi := (φ.map_prefix (s.addressChild e) w hprefix).length_le
  have hc := φ.child_length_eq e
  have hpoint : (φ.internalPoint e k).length = (φ.vertices w).val.length := congrArg List.length heq
  omega

/-- Internal points from different source edges are disjoint, and distinct
positions on the same edge have distinct depths. -/
theorem internalPoint_eq_iff {s t : OrderedTree} (φ : AddressEmbedding s t)
    (e f : E(rootedGraph s.toRootedTree)) {k l : ℕ}
    (hk : k < φ.internalCount e) (hl : l < φ.internalCount f) :
    φ.internalPoint e k = φ.internalPoint f l ↔ e = f ∧ k = l := by
  constructor
  · intro heq
    have hke := φ.internalPoint_length e hk
    have hlf := φ.internalPoint_length f hl
    have heflen : (φ.internalPoint e k).length = (φ.internalPoint f l).length :=
      congrArg List.length heq
    have hef : e.val <+: f.val := φ.child_prefix_of_common_point e (s.addressChild f)
      (φ.internalPoint e k) (φ.internalPoint_prefix e k)
      (by simpa only [heq] using φ.internalPoint_prefix f l) (by omega)
    have hfe : f.val <+: e.val := φ.child_prefix_of_common_point f (s.addressChild e)
      (φ.internalPoint f l) (φ.internalPoint_prefix f l)
      (by simpa only [← heq] using φ.internalPoint_prefix e k) (by omega)
    have hef' : e = f := Subtype.ext (hef.sublist.antisymm hfe.sublist)
    subst f
    refine ⟨rfl, ?_⟩
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

end AddressEmbedding
end OrderedTree
end GraphMinor.Kruskal
