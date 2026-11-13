module

public import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.SubdivisionConnected

/-!
# Vertices attached to one block

Graph Minors I, page 56, defines `Z_j` by paths to `S_j` avoiding all
other blocks. Here `U` is the union of the blocks and `S` is one block.
Reachability after deleting `U \ S` gives the attachment region. Its
intersection with the union is exactly its own block, and a path that
avoids the other blocks puts each of its vertices in this region.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09

/-- Graph Minors I, page 56: vertices that can be joined to a vertex of
one block by a path avoiding all the other blocks. -/
def blockAttachmentRegion {α β : Type*} (G : Graph α β) (U S : Set α) : Set α :=
  {x | x ∈ V(G.deleteVerts (U \ S)) ∧
    ∃ s ∈ S, ReflTransGen (G.deleteVerts (U \ S)).Adj x s}

/-- An attachment region consists of vertices of the ambient graph. -/
theorem blockAttachmentRegion_subset {α β : Type*} (G : Graph α β) (U S : Set α) :
    blockAttachmentRegion G U S ⊆ V(G) := by
  intro x hx
  exact (((G.vertexSet_deleteVerts (U \ S)) ▸ hx.1)).1

/-- Every vertex of a block belongs to its attachment region, using the
path of length zero. -/
theorem subset_blockAttachmentRegion {α β : Type*} {G : Graph α β} {U S : Set α}
    (hS : S ⊆ V(G)) : S ⊆ blockAttachmentRegion G U S := by
  intro s hs
  refine ⟨?_, s, hs, .refl⟩
  rw [vertexSet_deleteVerts]
  exact ⟨hS hs, fun h ↦ h.2 hs⟩

/-- The assertion immediately after the definition of `Z_j` on page 56:
its intersection with the union of all blocks is its own block. -/
theorem blockAttachmentRegion_inter {α β : Type*} {G : Graph α β} {U S : Set α}
    (hSU : S ⊆ U) (hSG : S ⊆ V(G)) :
    blockAttachmentRegion G U S ∩ U = S := by
  apply Set.Subset.antisymm
  · intro x hx
    have hxAvoid := (((G.vertexSet_deleteVerts (U \ S)) ▸ hx.1.1)).2
    by_contra hxS
    exact hxAvoid ⟨hx.2, hxS⟩
  · intro x hx
    exact ⟨subset_blockAttachmentRegion hSG hx, hSU hx⟩

/-- A path to a block that avoids all other blocks places every vertex
of the path in that block's attachment region. -/
theorem path_subset_blockAttachmentRegion {α β : Type*} {G P : Graph α β}
    {U S : Set α} {a s : α} (hP : IsGraphPathWithEnds G P a s)
    (hs : s ∈ S) (hAvoid : Disjoint V(P) (U \ S)) :
    V(P) ⊆ blockAttachmentRegion G U S := by
  have hPdel : P ≤ G.deleteVerts (U \ S) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts]
      exact ⟨hP.le.vertexSet_mono hx, fun h ↦ Set.disjoint_left.mp hAvoid hx h⟩
    · intro e x y he
      exact (G.deleteVerts_isLink (U \ S)).mpr ⟨he.mono hP.le,
        fun h ↦ Set.disjoint_left.mp hAvoid he.left_mem h,
        fun h ↦ Set.disjoint_left.mp hAvoid he.right_mem h⟩
  intro x hx
  refine ⟨hPdel.vertexSet_mono hx, s, hs, ?_⟩
  have hr := (graphConnected_of_isGraphPath hP).2 x hx s hP.right_mem
  exact ReflTransGen.mono
    (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hPdel⟩) x s hr

/-- The attachment sets cover a connected graph when their blocks have
nonempty union. Follow a path to that union and stop at its first vertex
in a block, as in the assertion preceding GM01 (4.3), page 56. -/
theorem iUnion_blockAttachmentRegion {α β ι : Type*} {G : Graph α β}
    (S : ι → Set α) (hG : GraphConnected G)
    (hS : ∀ i, S i ⊆ V(G)) (hne : (⋃ i, S i).Nonempty) :
    (⋃ i, blockAttachmentRegion G (⋃ j, S j) (S i)) = V(G) := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact blockAttachmentRegion_subset G _ _ hi
  · intro x hx
    obtain ⟨s, hs⟩ := hne
    obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp hs
    have hr := hG.2 x hx s (hS i hsi)
    have step : ∀ {a}, ReflTransGen G.Adj a s →
        ∃ i, a ∈ blockAttachmentRegion G (⋃ j, S j) (S i) := by
      intro a ha
      induction ha using ReflTransGen.head_induction_on with
      | refl => exact ⟨i, subset_blockAttachmentRegion (hS i) hsi⟩
      | @head a c hac hcs ih =>
        by_cases haU : a ∈ ⋃ j, S j
        · obtain ⟨j, haj⟩ := Set.mem_iUnion.mp haU
          exact ⟨j, subset_blockAttachmentRegion (hS j) haj⟩
        · obtain ⟨j, hc, t, ht, hct⟩ := ih
          obtain ⟨e, he⟩ := hac
          have haNot : a ∉ (⋃ j, S j) \ S j := fun h ↦ haU h.1
          have hcNot := (((G.vertexSet_deleteVerts ((⋃ k, S k) \ S j)) ▸ hc)).2
          have hdel := (G.deleteVerts_isLink ((⋃ k, S k) \ S j)).mpr
            ⟨he, haNot, hcNot⟩
          exact ⟨j, hdel.left_mem, t, ht, hct.head ⟨e, hdel⟩⟩
    obtain ⟨j, hj⟩ := step hr
    exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- A vertex of an attachment region has a path to its block wholly
inside that attachment region, as used in GM01 (4.5), page 57. -/
theorem exists_path_in_blockAttachmentRegion {α β : Type*} {G : Graph α β}
    {U S : Set α} {x : α} (hx : x ∈ blockAttachmentRegion G U S) :
    ∃ s ∈ S, ∃ P : Graph α β, IsGraphPathWithEnds G P x s ∧
      V(P) ⊆ blockAttachmentRegion G U S := by
  obtain ⟨hxv, s, hs, hxs⟩ := hx
  obtain ⟨P, hP⟩ := exists_path_of_adj_reachable hxv hxs
  have hPG := hP.mono Graph.deleteVerts_le
  have hAvoid : Disjoint V(P) (U \ S) := by
    apply Set.disjoint_left.mpr
    intro y hy hyCut
    have hyv := hP.le.vertexSet_mono hy
    exact (((G.vertexSet_deleteVerts _) ▸ hyv)).2 hyCut
  exact ⟨s, hs, P, hPG, path_subset_blockAttachmentRegion hPG hs hAvoid⟩

/-- Attachment to a union of blocks entails attachment to one of them.
On an attachment path, stop at its first vertex in that union. -/
theorem blockAttachmentRegion_iUnion_subset {α β ι : Type*} {G : Graph α β}
    {U : Set α} (S : ι → Set α) :
    blockAttachmentRegion G U (⋃ i, S i) ⊆
      ⋃ i, blockAttachmentRegion G U (S i) := by
  classical
  intro x hx
  obtain ⟨hxv, t, ht, hxt⟩ := hx
  obtain ⟨i, hti⟩ := Set.mem_iUnion.mp ht
  have htG : t ∈ V(G) := by
    have htV : t ∈ V(G.deleteVerts (U \ ⋃ i, S i)) := by
      induction hxt with
      | refl => exact hxv
      | tail _ hstep _ => obtain ⟨e, he⟩ := hstep; exact he.right_mem
    exact ((G.vertexSet_deleteVerts _) ▸ htV).1
  have step : ∀ {a}, ReflTransGen (G.deleteVerts (U \ ⋃ i, S i)).Adj a t →
      a ∈ V(G.deleteVerts (U \ ⋃ i, S i)) →
      ∃ i, a ∈ blockAttachmentRegion G U (S i) := by
    intro a ha
    induction ha using ReflTransGen.head_induction_on with
    | refl =>
      intro _
      refine ⟨i, ?_, t, hti, .refl⟩
      rw [vertexSet_deleteVerts]
      exact ⟨htG, fun h ↦ h.2 hti⟩
    | @head a c hac hct ih =>
      intro hav
      by_cases haD : a ∈ ⋃ i, S i
      · obtain ⟨j, haj⟩ := Set.mem_iUnion.mp haD
        refine ⟨j, ?_, a, haj, .refl⟩
        rw [vertexSet_deleteVerts]
        exact ⟨((G.vertexSet_deleteVerts _) ▸ hav).1, fun h ↦ h.2 haj⟩
      · obtain ⟨e, he⟩ := hac
        obtain ⟨j, hcv, s, hs, hcs⟩ := ih he.right_mem
        have haU : a ∉ U := by
          intro h
          exact (((G.vertexSet_deleteVerts _) ▸ hav)).2 ⟨h, haD⟩
        have hcNot := (((G.vertexSet_deleteVerts (U \ S j)) ▸ hcv)).2
        have hdel := (G.deleteVerts_isLink (U \ S j)).mpr
          ⟨he.mono Graph.deleteVerts_le, fun h ↦ haU h.1, hcNot⟩
        exact ⟨j, hdel.left_mem, s, hs, hcs.head ⟨e, hdel⟩⟩
  obtain ⟨j, hj⟩ := step hxt hxv
  exact Set.mem_iUnion.mpr ⟨j, hj⟩

/-- Attachment paths can be read in a graph with a smaller deleted set.
This lets a separator between two blocks also separate their attachment
regions whenever its vertices lie in other blocks. -/
theorem blockAttachmentRegion_reachable {α β : Type*} {G : Graph α β}
    {U S C : Set α} {x : α} (hx : x ∈ blockAttachmentRegion G U S)
    (hC : C ⊆ U \ S) :
    x ∈ V(G.deleteVerts C) ∧
      ∃ s ∈ S, s ∈ V(G.deleteVerts C) ∧ ReflTransGen (G.deleteVerts C).Adj x s := by
  have hle : G.deleteVerts (U \ S) ≤ G.deleteVerts C := by
    refine ⟨?_, ?_⟩
    · intro y hy
      have hyv := (G.vertexSet_deleteVerts (U \ S)) ▸ hy
      rw [vertexSet_deleteVerts]
      exact ⟨hyv.1, fun h ↦ hyv.2 (hC h)⟩
    · intro e a b he
      have he' := (G.deleteVerts_isLink (U \ S)).mp he
      exact (G.deleteVerts_isLink C).mpr
        ⟨he'.1, fun h ↦ he'.2.1 (hC h), fun h ↦ he'.2.2 (hC h)⟩
  obtain ⟨hxv, s, hs, hrs⟩ := hx
  have hsv : s ∈ V(G.deleteVerts (U \ S)) := by
    induction hrs with
    | refl => exact hxv
    | tail _ hstep _ => obtain ⟨e, he⟩ := hstep; exact he.right_mem
  exact ⟨hle.vertexSet_mono hxv, s, hs, hle.vertexSet_mono hsv,
    ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hle⟩) x s hrs⟩

/-- The observation before GM01 (4.3), page 56: if a third block
separates two blocks, the attachment regions of those two blocks are
disjoint. The separating set is contained in the other blocks. -/
theorem disjoint_blockAttachmentRegion_of_separator {α β : Type*} {G : Graph α β}
    {U A B C : Set α} (hsep : GraphSeparates G C A B)
    (hCA : C ⊆ U \ A) (hCB : C ⊆ U \ B) :
    Disjoint (blockAttachmentRegion G U A) (blockAttachmentRegion G U B) := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨_, a, ha, hav, hra⟩ := blockAttachmentRegion_reachable hxA hCA
  obtain ⟨_, b, hb, hbv, hrb⟩ := blockAttachmentRegion_reachable hxB hCB
  exact hsep a ha b hb hav hbv ((Std.Symm.symm _ _ hra).trans hrb)

end GraphMinor.GM01
