module

public import GraphMinor.Surface.CircleMove
public import Mathlib.Order.Fin.Basic
import GraphMinor.Surface.DiscGrow
import GraphMinor.GM19.PadFlower
import Mathlib.Data.Finset.Sort

/-!
# Ordering four prescribed boundary marks

In XII (4.5), claim (1), page 253, each prescribed disc comes
with an unordered set of four boundary marks. Parametrize its
boundary by the circle, choose each mark's angle in one turn,
and sort the four distinct angles. This produces the ordered
parameters required by the four-marked disc matching theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Four prescribed boundary points have distinct increasing
parameters in one turn of a boundary parametrization. This
supplies the ordered enumeration in XII (4.5), claim (1),
page 253, from the actual four-point set. -/
theorem exists_four_boundary_parameters {S : Type*} [TopologicalSpace S] [T2Space S]
    {D N : Set S} (hD : IsClosedDisc D) (hN : N ⊆ discBd D)
    (hfin : N.Finite) (hcard : N.ncard = 4) :
    ∃ (q : Circle → S) (b : Fin 4 → ℝ), Continuous q ∧ Function.Injective q ∧
      range q = discBd D ∧ StrictMono b ∧ (∀ i, b i ∈ Ico 0 1) ∧
      N = range (fun i => q (ee (b i))) := by
  classical
  obtain ⟨φ⟩ := hD.isOArc_discBd
  let q := fun w : Circle => (φ w).val
  have hqc : Continuous q := continuous_subtype_val.comp φ.continuous
  have hqi : Function.Injective q := Subtype.val_injective.comp φ.injective
  have hqr : range q = discBd D := by
    ext z
    exact ⟨fun ⟨w, hw⟩ => hw ▸ (φ w).property,
      fun hz => ⟨φ.symm ⟨z, hz⟩, congrArg Subtype.val (φ.apply_symm_apply ⟨z, hz⟩)⟩⟩
  let : Fintype N := hfin.fintype
  have hex : ∀ n : N, ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ φ.symm ⟨n.val, hN n.property⟩ = ee t :=
    fun n => GM19.exists_ee (φ.symm ⟨n.val, hN n.property⟩)
  choose t ht0 ht1 ht using hex
  have hmark : ∀ n : N, q (ee (t n)) = n.val := by
    intro n
    rw [← ht n]
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨n.val, hN n.property⟩)
  have hti : Function.Injective t := by
    intro n m hnm
    apply Subtype.ext
    rw [← hmark n, ← hmark m, hnm]
  let τ : N ≃ range t := Equiv.ofInjective t hti
  let : Fintype (range t) := (finite_range t).fintype
  have hcardN : Fintype.card N = 4 := (fintypeCard_eq_ncard N).trans hcard
  have hcardT : Fintype.card (range t) = 4 := (Fintype.card_congr τ).symm.trans hcardN
  let σ : Fin 4 ≃o range t := Fintype.orderIsoFinOfCardEq _ hcardT
  let b := fun i => (σ i).val
  have hb : StrictMono b := fun _ _ hij => σ.strictMono hij
  have hb01 : ∀ i, b i ∈ Ico (0 : ℝ) 1 := by
    intro i
    obtain ⟨n, hn⟩ := (σ i).property
    change t n = b i at hn
    rw [← hn]
    exact ⟨ht0 n, ht1 n⟩
  refine ⟨q, b, hqc, hqi, hqr, hb, hb01, ?_⟩
  apply Subset.antisymm
  · intro n hn
    let z : range t := ⟨t ⟨n, hn⟩, mem_range_self (f := t) (⟨n, hn⟩ : N)⟩
    refine ⟨σ.symm z, ?_⟩
    change q (ee (b (σ.symm z))) = n
    have hβ : b (σ.symm z) = t ⟨n, hn⟩ := congrArg Subtype.val (σ.apply_symm_apply z)
    rw [hβ]
    exact hmark ⟨n, hn⟩
  · rintro _ ⟨i, rfl⟩
    change q (ee (b i)) ∈ N
    obtain ⟨n, hn⟩ := (σ i).property
    change t n = b i at hn
    rw [← hn, hmark n]
    exact n.property

end GraphMinor.GM12
