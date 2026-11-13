module

public import GraphMinor.Compute.Case3StepsCompassGraph

/-!
# The four corners keep their cyclic order

The compact society used by (8.6) lists the wall corners in perimeter order.
Renaming these four vertices gives the cyclic permutation of the original
wall society (XIII, Section 9, pages 103--104).
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport Classical

/-- Renaming a cyclic order twice is renaming along the composite embedding. -/
theorem case3RelabelCyclicPerm_trans {α β γ : Type*} (f : α ↪ β) (g : β ↪ γ)
    (Ω : CyclicPerm α) :
    relabelCyclicPerm g (relabelCyclicPerm f Ω) = relabelCyclicPerm (f.trans g) Ω := by
  apply cyclicPerm_ext
  · change g '' (f '' Ω.bar) = (f.trans g) '' Ω.bar
    rw [Set.image_image]
    rfl
  · funext z
    by_cases hz : z ∈ Set.range g
    · obtain ⟨y, rfl⟩ := hz
      change relabelPermFun g (relabelCyclicPerm f Ω) (g y) = _
      rw [relabelPermFun_apply]
      by_cases hy : y ∈ Set.range f
      · obtain ⟨a, rfl⟩ := hy
        change g (relabelPermFun f Ω (f a)) = relabelPermFun (f.trans g) Ω ((f.trans g) a)
        rw [relabelPermFun_apply, relabelPermFun_apply]
        rfl
      · have hn : g y ∉ Set.range (f.trans g) := by
          rintro ⟨a, ha⟩
          exact hy ⟨a, g.injective ha⟩
        change g (relabelPermFun f Ω y) = relabelPermFun (f.trans g) Ω (g y)
        simp only [relabelPermFun, hy, hn, ↓reduceDIte]
    · have hn : z ∉ Set.range (f.trans g) := by
        rintro ⟨a, ha⟩
        exact hz ⟨f a, ha⟩
      change relabelPermFun g (relabelCyclicPerm f Ω) z = relabelPermFun (f.trans g) Ω z
      simp only [relabelPermFun, hz, hn, ↓reduceDIte]

private theorem case3FourCycle_apply {α : Type*} (c : Fin 4 → α)
    (hc : Function.Injective c) (i : Fin 4) :
    (cyclicPermOfNodupList (List.ofFn c) (List.nodup_ofFn.mpr hc)) (c i) =
      c ⟨(i.1 + 1) % 4, Nat.mod_lt _ (by decide)⟩ := by
  have hne : List.ofFn c ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    contradiction
  simp only [cyclicPermOfNodupList, hne, ↓reduceDIte]
  change CyclicPerm.ofNodupListFun (List.ofFn c) hne (c i) = _
  have h := CyclicPerm.ofNodupListFun_getElem (List.ofFn c) (List.nodup_ofFn.mpr hc) hne i.2
  have hci : (List.ofFn c)[i.1]'i.2 = c i := List.getElem_ofFn (f := c) (i := i.1) (h := i.2)
  rw [hci] at h
  simpa only [List.length_ofFn, List.getElem_ofFn] using h

private theorem case3FourCycle_fixed {α : Type*} (c : Fin 4 → α)
    (hc : Function.Injective c) {a : α} (ha : a ∉ Set.range c) :
    (cyclicPermOfNodupList (List.ofFn c) (List.nodup_ofFn.mpr hc)) a = a := by
  have hmem : a ∉ List.ofFn c := fun h => ha (List.mem_ofFn.mp h)
  have hne : List.ofFn c ≠ [] := by
    intro h
    have := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at this
    contradiction
  simp only [cyclicPermOfNodupList, hne, ↓reduceDIte]
  change CyclicPerm.ofNodupListFun (List.ofFn c) hne a = a
  simp only [CyclicPerm.ofNodupListFun, hmem, ↓reduceDIte]

/-- A list of four distinct vertices, renamed to the four wall corners in
order, gives exactly the wall's cyclic permutation. -/
theorem case3RelabelFourCycle_eq {α β ι : Type*} (W : Wall β ι)
    (c : Fin 4 → α) (hc : Function.Injective c) (k : α ↪ β)
    (hcorner : ∀ i, k (c i) = W.corner i) :
    relabelCyclicPerm k (cyclicPermOfNodupList (List.ofFn c) (List.nodup_ofFn.mpr hc)) =
      wallCornerCyclicPerm W := by
  apply cyclicPerm_ext
  · change k '' (cyclicPermOfNodupList (List.ofFn c) _).bar = Set.range W.corner
    rw [bar_cyclicPermOfNodupList]
    ext a
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
      exact ⟨i, (hcorner i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨c i, List.mem_ofFn.mpr ⟨i, rfl⟩, hcorner i⟩
  · funext a
    by_cases ha : a ∈ Set.range W.corner
    · obtain ⟨i, rfl⟩ := ha
      change relabelPermFun k _ (W.corner i) = _
      rw [← hcorner i, relabelPermFun_apply, case3FourCycle_apply c hc, hcorner]
      fin_cases i <;> simp [hcorner, wallCornerCyclicPerm, W.corner_injective.eq_iff]
    · have hfixed : (wallCornerCyclicPerm W) a = a := by
        have hne : ∀ i, a ≠ W.corner i := fun i h => ha ⟨i, h.symm⟩
        simp only [wallCornerCyclicPerm, hne, ↓reduceIte]
      rw [hfixed]
      by_cases hk : a ∈ Set.range k
      · obtain ⟨u, rfl⟩ := hk
        have hu : u ∉ Set.range c := by
          rintro ⟨i, rfl⟩
          exact ha ⟨i, (hcorner i).symm⟩
        change relabelPermFun k _ (k u) = k u
        rw [relabelPermFun_apply, case3FourCycle_fixed c hc hu]
      · change relabelPermFun k _ a = a
        simp only [relabelPermFun, hk, ↓reduceDIte]

/-- The compact compass corner order becomes the wall society order in the
original vertex labels. -/
theorem case3CompactCornerOrder_relabel {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    relabelCyclicPerm (origVertexEmb (compassEmb W) (compassEmb W).injective)
      (relabelCyclicPerm ⟨Fin.val, Fin.val_injective⟩
        (case3Alg81Input D W h2 he hW).toSociety.Ω) =
      wallCornerCyclicPerm (W.toGMWall h2 he hW) := by
  rw [case3RelabelCyclicPerm_trans]
  apply case3RelabelFourCycle_eq (W.toGMWall h2 he hW)
    (compactCorner W h2 he) (compactCorner_injective W h2 he hW)
  intro i
  change origVertexEmb (compassEmb W) (compassEmb W).injective (compactCorner W h2 he i).1 = _
  rw [origVertexEmb_apply_val, compassEmb_compactCorner, WallOfHeight.toGMWall_corner_eq_cornerVert]

end GraphMinor.Compute
