module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.Minor.Basic
import GraphMinor.GM02.MinorWidth
import GraphMinor.GM10.TreeWidthBasic
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# Tree-width under minors

Graph Minors II (2.7) follows by replacing each bag by the branch sets of a
minor model that it meets. The bag-transfer argument is in `MinorWidth`.
If the ambient edge type is empty, every minor is edgeless. A star with
singleton leaf bags gives such a graph width zero, avoiding an unnecessary
inhabitance assumption on edge labels.
-/

public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v u' v'

private theorem width_zero_of_edgeless {α : Type u} {β : Type v} {G : Graph α β}
    (hV : (V(G)).Finite) (hE : E(G) = ∅) : TreeWidthLE G 0 := by
  let _ := hV.fintype
  let e := (Fintype.equivFin V(G)).symm
  let B : Option (Fin (Fintype.card V(G))) → Set α :=
    fun t => t.elim ∅ (fun v => {(e v).val})
  refine ⟨Option (Fin (Fintype.card V(G))), inferInstance, starGraph none, B, ⟨isTree_starGraph _, ?_, ?_, ?_⟩, ?_⟩
  · ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | none => exact ht.elim
      | some v => exact ht ▸ (e v).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨some i, congrArg Subtype.val hi |>.symm⟩
  · intro e a b hab
    have h := hab.edge_mem
    rw [hE] at h
    exact h.elim
  · intro a c b hp x hx
    cases a with
    | none => exact hx.1.elim
    | some a =>
      cases b with
      | none => exact hx.2.elim
      | some b =>
        have hab : a = b := e.injective (Subtype.ext (hx.1.symm.trans hx.2))
        subst b
        have hc := GM10.onTreePath_self_iff.mp hp
        exact hc ▸ hx.1
  · intro t
    cases t <;> simp [B]

/-- Transfer a width bound to a minor, including empty ambient edge types. -/
theorem TreeWidthLE.of_isIsoMinor_unrestricted
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (hVG : (V(G)).Finite)
    (hEG : (E(G)).Finite) (hVH : (V(H)).Finite) (hminor : IsIsoMinor H G)
    {w : ℕ} (hw : TreeWidthLE G w) : TreeWidthLE H w := by
  cases isEmpty_or_nonempty β with
  | inl hβ =>
    let _ := hβ
    obtain ⟨G', _, C, _, ⟨e⟩⟩ := hminor
    have hEH : E(H) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro f hf
      exact isEmptyElim (e.edgeEquiv ⟨f, hf⟩).val
    obtain ⟨ι, hi, T, X, hD, hX⟩ := width_zero_of_edgeless hVH hEH
    exact ⟨ι, hi, T, X, hD, fun i => (hX i).trans (Nat.succ_le_succ (Nat.zero_le w))⟩
  | inr hβ =>
    let _ := hβ
    exact hw.of_isIsoMinor hVG hEG hminor

/-- Graph Minors II, (2.7), page 314:
"If $G$ has tree-width $< w$, so does every minor of $G$." -/
theorem theorem_2_7_proof {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (hVG : (V(G)).Finite)
    (hEG : (E(G)).Finite) (hVH : (V(H)).Finite) (hEH : (E(H)).Finite)
    (hminor : IsIsoMinor H G) {w : ℕ} (hw : treeWidth G hVG hEG < w) :
    treeWidth H hVH hEH < w := by
  have hwpos : 0 < w := Nat.zero_lt_of_lt hw
  have hwidth := (treeWidth_le_iff G hVG hEG (w - 1)).1 (by omega : treeWidth G hVG hEG ≤ w - 1)
  have hH := hwidth.of_isIsoMinor_unrestricted hVG hEG hVH hminor
  have hle := (treeWidth_le_iff H hVH hEH (w - 1)).2 hH
  omega

end GraphMinor.GM02
