module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

/-!
# Ordering the attachment indices

In the page-60 contraction of Graph Minors I, the disjoint attachment
paths have distinct endpoints on their common covering path. Sort
the finite set of endpoint coordinates. The original injective
coordinate map and the sorted enumeration are two bijections onto
that set, so their composite gives a permutation of the attachment
indices with strictly increasing coordinates.
-/

public section

namespace GraphMinor.GM01

open Set Function

/-- Relabel distinct attachment coordinates in increasing order,
without discarding any attachment, for the GM01 page-60 contraction. -/
theorem exists_strictMono_attachment_reindexing {δ N : ℕ}
    (f : Fin δ → Fin N) (hf : Injective f) :
    ∃ e : Fin δ ≃ Fin δ, StrictMono (fun i ↦ f (e i)) := by
  classical
  let s := Finset.univ.image f
  have hs : s.card = δ := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have hRange : range f = (s : Set (Fin N)) := by
    ext x
    simp only [s, Finset.coe_image, Finset.coe_univ, image_univ]
  let ef : Fin δ ≃ s := (Equiv.ofInjective f hf).trans (Set.equivOfEq hRange)
  let sorted := s.orderIsoOfFin hs
  let e := sorted.toEquiv.trans ef.symm
  have hfe : ∀ i, f (e i) = (sorted i).val := by
    intro i
    exact congrArg Subtype.val (ef.apply_symm_apply (sorted i))
  refine ⟨e,?_⟩
  intro i j hij
  change f (e i) < f (e j)
  rw [hfe i,hfe j]
  exact sorted.strictMono hij

end GraphMinor.GM01
