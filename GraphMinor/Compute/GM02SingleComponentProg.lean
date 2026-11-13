module

public import GraphMinor.Compute.GM02ComponentSearch
import GraphMinor.Compute.CrossingOpsBasic

/-!
# A RAM search from one vertex

Initialize the source array with one vertex number and run the existing
breadth-first search. With separator-forbidden labels already in place,
its queue history is exactly the remaining component of that vertex.
This is the search operation used in the component test of II (3.1).
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths Classical

/-- Search from the vertex in register 181, using the existing forbidden labels. -/
def gm02SingleComponentProg (gS gE gEnt : Arr) : Cmd :=
  .seq (.alloc aSrc (.const 1))
    (.seq (.write aSrc (.const 0) (.reg 181)) (searchProg gS gE gEnt))

/-- A single-source search returns the exact component, without repeated
vertices, in linear time in the adjacency-list size. -/
theorem gm02SingleComponentProg_exec {n w : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (gS gE gEnt : Arr)
    (hgS : gS < 60) (hgE : gE < 60) (hgEnt : gEnt < 60)
    (X : Finset (Fin n)) (a : Fin n) (ha : a ∉ X) (s : State)
    (hadj : IsAdjList G gS gE gEnt lists s) (hent : (s.arrs gEnt).length < 2 ^ w)
    (hrn : s.regs 40 = n) (hra : s.regs 181 = a.val)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hlab : s.arrs aLab = List.ofFn (gm02ComponentLabels X)) :
    ∃ s' t items, Exec w (gm02SingleComponentProg gS gE gEnt) s s' t ∧
      t ≤ 60 + 21 * n + 29 * totalAdjEntries lists ∧ items.Nodup ∧
      (∀ b : Fin n, b.val ∈ items ↔
        b ∈ GM02.deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a) ∧
      SInv G (gm02ComponentLabels X) [a.val]
        ((s.setArr aSrc [0]).writeArr aSrc 0 a.val) items items.length s' := by
  dsimp only [Arr] at hgS hgE hgEnt
  let s₁ := s.setArr aSrc [0]
  let s₂ := s₁.writeArr aSrc 0 a.val
  have halloc : Exec w (.alloc aSrc (.const 1)) s s₁ 2 :=
    .alloc (eval_const (by omega))
  have hwrite : Exec w (.write aSrc (.const 0) (.reg 181)) s₁ s₂ 3 := by
    apply Exec.write (eval_const (Nat.two_pow_pos w))
      (eval_reg (by simpa [s₁] using hra) (a.isLt.trans hn))
    simp [s₁]
  have hadj₂ : IsAdjList G gS gE gEnt lists s₂ :=
    hadj.of_arrs_eq (by simp [s₂, s₁, aSrc, show gS ≠ 63 by dsimp only [Arr]; omega])
      (by simp [s₂, s₁, aSrc, show gE ≠ 63 by dsimp only [Arr]; omega])
      (by simp [s₂, s₁, aSrc, show gEnt ≠ 63 by dsimp only [Arr]; omega])
  have hsrc₂ : s₂.arrs aSrc = [a.val] := by simp [s₂, s₁]
  obtain ⟨s', t, items, hex, ht, hs⟩ := searchProg_exec G lists gS gE gEnt hgS hgE hgEnt
    (gm02ComponentLabels X) (fun v => by unfold gm02ComponentLabels; split_ifs <;> omega)
    [a.val] (by intro v hv; exact (List.mem_singleton.1 hv) ▸ a.isLt) s₂ hadj₂
    (by simpa [s₂, s₁, aSrc, show gEnt ≠ 63 by dsimp only [Arr]; omega] using hent)
    (by simpa [s₂, s₁] using hrn) hw hn (by simpa using (show 1 < 2 ^ w by omega))
    (by simpa [s₂, s₁, aLab, aSrc] using hlab) hsrc₂
  refine ⟨s', 2 + (3 + t), items, .seq halloc (.seq hwrite hex), ?_, hs.nodup,
    fun b => gm02ComponentSearch_mem_iff ha hs, hs⟩
  simp only [List.length_singleton] at ht
  omega

end GraphMinor.Compute
