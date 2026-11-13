module

public import GraphMinor.GM01.BinaryLeafCover
public import GraphMinor.GM09.Basic
import GraphMinor.GM01.BinaryLeafPaths
import GraphMinor.GM01.SubdivisionPathLifting

/-!
# Covering the rooted binary subdivision by leaf paths

Graph Minors I, page 60, covers `B_0` by `2^γ` root-to-leaf paths.
Lift the explicit parent path of each full-height word through the
subdivision, then add the separate ambient-root path. The latter
meets the subdivision only at its root centre. Every centre and every
replacing-path interior lies on one lifted path, so their union
covers all vertices of `B_0`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual root-to-leaf path cover asserted on page 60 of GM01.
The index set has cardinal `2^γ` by `binaryTree_full_height_ncard`. -/
theorem exists_binary_subdivision_leaf_cover {α β : Type*} {γ : ℕ}
    {G N R : Graph α β} (hNG : N ≤ G)
    {c : (binaryTree γ).verts → α} (hc : Injective c)
    {P : (binaryTree γ).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (binaryTree γ).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    {root : α} (hR : IsGraphPathWithEnds G R root (c ⟨[], binaryTree_root_mem γ⟩))
    (hMeet : V(R) ∩ V(N) = {c ⟨[], binaryTree_root_mem γ⟩}) :
    ∃ Q : {leaf : List Bool // leaf.length = γ} → Graph α β,
      (∀ leaf, IsGraphPathWithEnds G (Q leaf) root (c ⟨leaf.val, leaf.property.le⟩)) ∧
      (∀ leaf, Q leaf ≤ subgraphUnion G N R) ∧
      V(N) ∪ V(R) ⊆ ⋃ leaf, V(Q leaf) := by
  classical
  let r : (binaryTree γ).verts := ⟨[], binaryTree_root_mem γ⟩
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hChoice : ∀ leaf : {word : List Bool // word.length = γ},
      ∃ Q : Graph α β, IsGraphPathWithEnds N Q (c r) (c ⟨leaf.val, leaf.property.le⟩) ∧
        (∀ v, c v ∈ V(Q) ↔ v.val <:+ leaf.val) ∧
        (∀ (v : List Bool) (bit : Bool) (hv : bit :: v ∈ (binaryTree γ).verts)
          (hparent : v ∈ (binaryTree γ).verts), bit :: v <:+ leaf.val →
          V(P ⟨s(⟨bit :: v,hv⟩,⟨v,hparent⟩),
            ⟨hv,hparent,Or.inr ⟨bit,rfl⟩⟩⟩) ⊆ V(Q)) := by
    intro leaf
    obtain ⟨p, hp, hsupport, hedges⟩ := binaryTree_exists_parent_path leaf.val leaf.property.le
    obtain ⟨Q, hQ, hCQ, hPQ, _⟩ := exists_subdivision_path_lift hc hcentres hPaths hInter p hp
    refine ⟨Q, hQ.symm, ?_, ?_⟩
    · intro v
      exact (hCQ v).trans (hsupport v)
    · intro v bit hv hparent hs
      exact hPQ _ (hedges v bit hv hparent hs)
  choose D hD hCD hPD using hChoice
  let Q := fun leaf ↦ subgraphUnion G R (D leaf)
  have hRD : ∀ leaf, V(R) ∩ V(D leaf) = {c r} := by
    intro leaf
    apply Subset.antisymm
    · rintro x ⟨hxR,hxD⟩
      exact hMeet ▸ ⟨hxR, (hD leaf).le.vertexSet_mono hxD⟩
    · exact singleton_subset_iff.mpr ⟨hR.right_mem, (hD leaf).left_mem⟩
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro leaf
    exact hR.subgraphUnion ((hD leaf).mono hNG) (hRD leaf)
  · intro leaf
    apply (subgraphUnion_le_iff hR.le ((hD leaf).le.trans hNG) (subgraphUnion_le hNG hR.le)).mpr
    constructor
    · exact le_subgraphUnion_right hNG hR.le
    · exact (hD leaf).le.trans (le_subgraphUnion_left hNG hR.le)
  · rintro x (hxN | hxR)
    · rw [hV] at hxN
      rcases hxN with ⟨v,rfl⟩ | hxP
      · obtain ⟨leaf, hlen, hs⟩ := binaryTree_vertex_suffix_leaf v.property
        exact mem_iUnion.mpr ⟨⟨leaf,hlen⟩, Or.inr ((hCD ⟨leaf,hlen⟩ v).mpr hs)⟩
      · obtain ⟨e,hxe⟩ := mem_iUnion.mp hxP
        obtain ⟨a,b,he,hPath,hRange⟩ := hPaths e
        have hab : (binaryTree γ).coe.Adj a b := by
          have hep := e.property
          rw [he] at hep
          exact hep
        obtain ⟨leaf,hlen,ha,hb⟩ := binaryTree_edge_suffix_leaf hab
        have hOn : V(P e) ⊆ V(D ⟨leaf,hlen⟩) := by
          rcases hab.2.2 with ⟨bit, hbEq⟩ | ⟨bit,haEq⟩
          · have hchild : bit :: a.val ∈ (binaryTree γ).verts := hbEq ▸ b.property
            have hSub := hPD ⟨leaf,hlen⟩ a.val bit hchild a.property (hbEq ▸ hb)
            have heq : e = ⟨s(⟨bit :: a.val, hchild⟩,a),
                ⟨hchild,a.property,Or.inr ⟨bit,rfl⟩⟩⟩ := by
              apply Subtype.ext
              rw [he, Sym2.eq_swap]
              exact congrArg (fun v ↦ s(v,a)) (Subtype.ext hbEq)
            rw [heq]
            exact hSub
          · have hchild : bit :: b.val ∈ (binaryTree γ).verts := haEq ▸ a.property
            have hSub := hPD ⟨leaf,hlen⟩ b.val bit hchild b.property (haEq ▸ ha)
            have heq : e = ⟨s(⟨bit :: b.val, hchild⟩,b),
                ⟨hchild,b.property,Or.inr ⟨bit,rfl⟩⟩⟩ := by
              apply Subtype.ext
              rw [he]
              exact congrArg (fun v ↦ s(v,b)) (Subtype.ext haEq)
            rw [heq]
            exact hSub
        exact mem_iUnion.mpr ⟨⟨leaf,hlen⟩, Or.inr (hOn hxe)⟩
    · let leaf : {word : List Bool // word.length = γ} := ⟨List.replicate γ false, List.length_replicate⟩
      exact mem_iUnion.mpr ⟨leaf, Or.inl hxR⟩

end GraphMinor.GM01
