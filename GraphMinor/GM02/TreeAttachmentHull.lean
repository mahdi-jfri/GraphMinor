module

public import GraphMinor.GM10.Defs
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# Pruning branch trees to their attachment vertices

For the reduced patterns in II (4.8), only paths joining the attachment
vertices of a branch tree are needed. Their union is again a tree, and
its leaves are attachment vertices. Thus this pruning introduces no new
leaves away from the attachments.
-/

@[expose] public section

namespace GraphMinor.GM02

open SimpleGraph Set Classical

/-- The vertices on tree paths between attachment vertices. -/
def treeAttachmentHull {α : Type*} (T : SimpleGraph α) (A : Set α) : Set α :=
  {v | ∃ a ∈ A, ∃ b ∈ A, GM10.OnTreePath T a b v}

/-- Every attachment vertex lies in its hull, by the path to itself. -/
theorem subset_treeAttachmentHull {α : Type*} (T : SimpleGraph α) (A : Set α) :
    A ⊆ treeAttachmentHull T A := by
  intro a ha
  exact ⟨a, ha, a, ha, GM10.onTreePath_refl_left T a a⟩

/-- The hull is closed under taking tree paths. -/
theorem treeAttachmentHull_convex {α : Type*} {T : SimpleGraph α}
    (hT : T.IsTree) {A : Set α} {a b c : α}
    (ha : a ∈ treeAttachmentHull T A) (hb : b ∈ treeAttachmentHull T A)
    (hp : GM10.OnTreePath T a b c) : c ∈ treeAttachmentHull T A :=
  GM10.isConvex_exists_onTreePath hT ha hb hp

/-- Every path between hull vertices stays in the hull. -/
theorem path_support_subset_treeAttachmentHull {α : Type*} {T : SimpleGraph α}
    (hT : T.IsTree) {A : Set α} {a b : α}
    (ha : a ∈ treeAttachmentHull T A) (hb : b ∈ treeAttachmentHull T A)
    {p : T.Walk a b} (hp : p.IsPath) :
    ∀ c ∈ p.support, c ∈ treeAttachmentHull T A := by
  intro c hc
  exact treeAttachmentHull_convex hT ha hb
    ((GM10.onTreePath_iff_of_isPath hT hp).2 hc)

/-- The paths joining a nonempty set of attachments form a tree. -/
theorem isTree_induce_treeAttachmentHull {α : Type*} {T : SimpleGraph α}
    (hT : T.IsTree) {A : Set α} (hA : A.Nonempty) :
    (T.induce (treeAttachmentHull T A)).IsTree := by
  obtain ⟨a, ha⟩ := hA
  let : Nonempty (treeAttachmentHull T A) := ⟨⟨a, subset_treeAttachmentHull T A ha⟩⟩
  refine ⟨SimpleGraph.Connected.mk ?_, hT.isAcyclic.induce _⟩
  intro x y
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath x.val y.val
  exact ⟨p.induce (treeAttachmentHull T A)
    (path_support_subset_treeAttachmentHull hT x.property y.property hp)⟩

/-- Every leaf of a branch tree pruned to its attachment hull is an
attachment vertex. A vertex in the hull lies on a path between two
attachments, and a leaf on a path is one of its ends. -/
theorem mem_attachments_of_degree_one_hull {α : Type*} [Fintype α]
    {T : SimpleGraph α} (hT : T.IsTree) {A : Set α}
    (v : treeAttachmentHull T A)
    (hv : (T.induce (treeAttachmentHull T A)).degree v = 1) : v.val ∈ A := by
  obtain ⟨a, ha, b, hb, habv⟩ := v.property
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath a b
  have has := subset_treeAttachmentHull T A ha
  have hbs := subset_treeAttachmentHull T A hb
  have hsupport := path_support_subset_treeAttachmentHull hT has hbs hp
  let q := p.induce (treeAttachmentHull T A) hsupport
  have hq : q.IsPath := by
    rw [Walk.isPath_def]
    apply List.Nodup.of_map Subtype.val
    dsimp only [q]
    rw [Walk.support_induce]
    change ((p.support.attachWith (fun c => c ∈ treeAttachmentHull T A) hsupport).map
      (fun x => id x.val)).Nodup
    rw [List.attachWith_map_val, List.map_id]
    exact hp.support_nodup
  have hvmem : v ∈ q.support := by
    change v ∈ (p.induce (treeAttachmentHull T A) hsupport).support
    rw [Walk.support_induce, List.mem_attachWith]
    exact habv p hp
  obtain ⟨w, _, hw⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.1 hv
  have huniq : ∀ w₁ w₂, (T.induce (treeAttachmentHull T A)).Adj v w₁ →
      (T.induce (treeAttachmentHull T A)).Adj v w₂ → w₁ = w₂ :=
    fun w₁ w₂ h₁ h₂ => (hw w₁ h₁).trans (hw w₂ h₂).symm
  rcases GM10.eq_fst_or_eq_snd_of_mem_support_of_unique_adj huniq hq hvmem with h | h
  · exact congrArg Subtype.val h ▸ ha
  · exact congrArg Subtype.val h ▸ hb

end GraphMinor.GM02
