module

public import GraphMinor.GM01.BinaryTrees
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The source paths from binary leaves to the root

Graph Minors I, page 60, covers the binary subdivision by paths to
its leaves. In the word representation, the path removes the first
bit at every step. Its vertices are exactly the suffixes of the
starting word. Every parent edge whose child is such a suffix occurs
on this path. The subdivision lifting lemma can therefore retain
all the replacing-path interiors as well as the centres.
-/

public section

namespace GraphMinor.GM01

open Set SimpleGraph

/-- The explicit parent path from a binary-tree vertex to the root,
with its centres and parent edges, used in the leaf cover on GM01 page 60. -/
theorem binaryTree_exists_parent_path {γ : ℕ} (word : List Bool)
    (hw : word ∈ (binaryTree γ).verts) :
    ∃ p : (binaryTree γ).coe.Walk ⟨word, hw⟩ ⟨[], binaryTree_root_mem γ⟩,
      p.support.Nodup ∧
      (∀ v : (binaryTree γ).verts, v ∈ p.support ↔ v.val <:+ word) ∧
      (∀ (v : List Bool) (bit : Bool) (hv : bit :: v ∈ (binaryTree γ).verts)
        (hparent : v ∈ (binaryTree γ).verts), bit :: v <:+ word →
        s(⟨bit :: v, hv⟩, ⟨v, hparent⟩) ∈ p.edges) := by
  induction word with
  | nil =>
    refine ⟨.nil, List.nodup_singleton _, ?_, ?_⟩
    · intro v
      simp only [Walk.support_nil, List.mem_singleton, List.suffix_nil]
      exact Subtype.ext_iff
    · intro v bit hv hparent hs
      have h := hs.length_le
      simp only [List.length_cons, List.length_nil] at h
      omega
  | cons bit word ih =>
    have hw' : word ∈ (binaryTree γ).verts := by
      change word.length ≤ γ
      change (bit :: word).length ≤ γ at hw
      simp only [List.length_cons] at hw
      omega
    obtain ⟨p, hp, hsupport, hedges⟩ := ih hw'
    have hadj : (binaryTree γ).coe.Adj ⟨bit :: word, hw⟩ ⟨word, hw'⟩ :=
      ⟨hw, hw', Or.inr ⟨bit, rfl⟩⟩
    refine ⟨.cons hadj p, ?_, ?_, ?_⟩
    · apply List.nodup_cons.mpr
      refine ⟨?_, hp⟩
      intro hm
      have h := ((hsupport ⟨bit :: word, hw⟩).mp hm).length_le
      simp only [List.length_cons] at h
      omega
    · intro v
      simp only [Walk.support_cons, List.mem_cons, hsupport, List.suffix_cons_iff]
      exact or_congr Subtype.ext_iff Iff.rfl
    · intro v b hv hparent hs
      rcases List.suffix_cons_iff.mp hs with heq | hs
      · obtain ⟨rfl, rfl⟩ := List.cons.inj heq
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hedges v b hv hparent hs)

end GraphMinor.GM01
