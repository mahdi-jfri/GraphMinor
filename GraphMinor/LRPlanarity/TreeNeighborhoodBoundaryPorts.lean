module

public import GraphMinor.Surface.TopologyStatements
public import Mathlib.Data.Finset.Sort
import GraphMinor.Surface.EdgeLoop
import GraphMinor.Surface.Triangulate

/-!
# Listing finite ports along a boundary circle

Part IV, Section 7b of the planarity note traverses the neighborhood
boundary and reads its ports. Choose a starting point outside the finite
port set. A once-around parametrization then gives each port a unique
parameter strictly between zero and one. Sorting those parameters lists
every port once and records their boundary order.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: finitely many distinct points of a boundary circle
have a list in strict traversal order, with every point appearing once. -/
theorem exists_ordered_boundary_ports_at {α : Type*} [Finite α] {C : Set ℂ}
    (hC : IsOArc C) (port : α → ℂ) (hinj : Function.Injective port) (hport : ∀ a, port a ∈ C)
    (base : ℂ) (hbaseC : base ∈ C) (hbase : base ∉ range port) :
    ∃ (word : List α) (f : ℝ → ℂ) (parameter : α → ℝ),
      word.Nodup ∧ (∀ a, a ∈ word) ∧
      Continuous f ∧ InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = C ∧ f 0 = base ∧ f 1 = base ∧
      (∀ a, parameter a ∈ Ioo (0 : ℝ) 1 ∧ f (parameter a) = port a) ∧
      word.Pairwise (fun a b => parameter a < parameter b) := by
  classical
  obtain ⟨f,hf,hzero,hone,hIco,hIoc,himage⟩ := hC.exists_iota hbaseC
  have hparameters : ∀ a, ∃ t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧ f t = port a := by
    intro a
    obtain ⟨t,ht,he⟩ := himage.symm ▸ hport a
    have ht0 : 0 < t := by
      apply lt_of_not_ge
      intro ht0
      have heq : t = 0 := le_antisymm ht0 ht.1
      have hp : port a = base := he.symm.trans ((congrArg f heq).trans hzero)
      exact hbase ⟨a,hp⟩
    exact ⟨t,⟨ht0,ht.2⟩,he⟩
  choose parameter hparameter using hparameters
  have hparaminj : Function.Injective parameter := by
    intro a b he
    apply hinj
    exact (hparameter a).2.symm.trans ((congrArg f he).trans (hparameter b).2)
  let : Fintype α := Fintype.ofFinite α
  let : LinearOrder α := LinearOrder.lift' parameter hparaminj
  let word := (Finset.univ : Finset α).sort (· ≤ ·)
  have hsorted : word.Pairwise (fun a b => parameter a < parameter b) :=
    (Finset.sortedLT_sort (Finset.univ : Finset α)).pairwise
  have hfull : f '' Icc (0 : ℝ) 1 = C := by
    apply Subset.antisymm
    · rintro x ⟨t,ht,rfl⟩
      by_cases ht1 : t < 1
      · exact himage ▸ mem_image_of_mem f ⟨ht.1,ht1⟩
      · have heq : t = 1 := le_antisymm ht.2 (le_of_not_gt ht1)
        rw [heq,hone]
        exact hbaseC
    · intro x hx
      obtain ⟨t,ht,he⟩ := himage.symm ▸ hx
      exact ⟨t,⟨ht.1,ht.2.le⟩,he⟩
  exact ⟨word,f,parameter,Finset.sort_nodup _ _,
    fun a => (Finset.mem_sort _).mpr (Finset.mem_univ a),hf,hIco,hIoc,hfull,hzero,hone,hparameter,hsorted⟩

/-- Part IV, Section 7b: choose a starting point off the finite port set,
then list each port once in strict boundary traversal order. -/
theorem exists_ordered_boundary_ports {α : Type*} [Finite α] {C : Set ℂ}
    (hC : IsOArc C) (port : α → ℂ) (hinj : Function.Injective port) (hport : ∀ a, port a ∈ C) :
    ∃ (word : List α) (f : ℝ → ℂ) (parameter : α → ℝ),
      word.Nodup ∧ (∀ a, a ∈ word) ∧
      Continuous f ∧ InjOn f (Ico (0 : ℝ) 1) ∧ InjOn f (Ioc (0 : ℝ) 1) ∧
      f '' Icc (0 : ℝ) 1 = C ∧
      (∀ a, parameter a ∈ Ioo (0 : ℝ) 1 ∧ f (parameter a) = port a) ∧
      word.Pairwise (fun a b => parameter a < parameter b) := by
  obtain ⟨base,hbaseC,hbase⟩ := ((isOArc_infinite hC).sdiff (Set.toFinite (range port))).nonempty
  obtain ⟨word,f,parameter,hnd,hall,hf,hIco,hIoc,himage,_,_,hparam,hsorted⟩ :=
    exists_ordered_boundary_ports_at hC port hinj hport base hbaseC hbase
  exact ⟨word,f,parameter,hnd,hall,hf,hIco,hIoc,himage,hparam,hsorted⟩

end GraphMinor.LRPlanarity
