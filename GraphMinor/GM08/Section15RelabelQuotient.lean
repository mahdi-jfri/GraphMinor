module

public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15VertexLabels
import GraphMinor.GM08.Section15Reconstruction
import Mathlib.Data.Set.Function

/-!
# Reconstructing after finite vertex relabelling

Place the finite cut graft in the original infinite vertex label type.
The inverse on its vertex set transports the quotient map, its paired
fibres, and its root rule. The proved identification chain then ends
at a graft isomorphic to the original. This puts the short-tube cut
and its reconstruction in one graft class for VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set Graph Function

universe u v w

/-- A paired-fibre quotient can be reconstructed using the target's
infinite vertex label type while keeping the source's graft isomorphism
type and index. This is finite label transport in VIII (15.4), page 282. -/
theorem exists_relabelled_vertexIdChain {γ : Type u} {α : Type v} {β : Type w}
    [Nonempty γ] [Infinite α] (A : Graft γ β) (X : Graft α β) (f : γ → α)
    (hG : X.G = A.G.map f) (hf : ∀ x, {y ∈ V(A.G) | f y = x}.ncard ≤ 2)
    (hroot : ∀ y ∈ V(A.G), y ∈ A.T ↔
      f y ∈ X.T ∨ ∃ z ∈ V(A.G), z ≠ y ∧ f z = f y) :
    ∃ B : Graft α β, IsGraftIso A B ∧ B.index = A.index ∧
      ∃ (n : ℕ) (Z : Graft α β), ObtainedByVertexIdChain n B Z ∧ IsGraftIso Z X := by
  classical
  obtain ⟨B, g, hBG, hBT, hginj, hiso, hindex⟩ := exists_vertex_relabel_graft (α := α) A
  let d := Function.invFunOn g V(A.G)
  let f' := f ∘ d
  have hd : ∀ y ∈ V(A.G), d (g y) = y := hginj.leftInvOn_invFunOn
  have hcomp : ∀ y ∈ V(A.G), f' (g y) = f y := fun y hy => congrArg f (hd y hy)
  have hVB : V(B.G) = g '' V(A.G) := by rw [hBG, vertexSet_map]
  have hquot : X.G = B.G.map f' := by
    rw [hBG, map_map]
    exact hG.trans (map_eq_of_eqOn_vertices A.G (fun y hy => (hcomp y hy).symm))
  have hfB : ∀ x, {y ∈ V(B.G) | f' y = x}.ncard ≤ 2 := by
    intro x
    have heq : {y ∈ V(B.G) | f' y = x} = g '' {y ∈ V(A.G) | f y = x} := by
      apply subset_antisymm
      · rintro y ⟨hy, hfy⟩
        rw [hVB] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        exact ⟨z, ⟨hz, (hcomp z hz).symm.trans hfy⟩, rfl⟩
      · rintro y ⟨z, ⟨hz, hfz⟩, rfl⟩
        exact ⟨hVB ▸ mem_image_of_mem g hz, (hcomp z hz).trans hfz⟩
    rw [heq, (hginj.mono (sep_subset _ _)).ncard_image]
    exact hf x
  have hrB : ∀ y ∈ V(B.G), y ∈ B.T ↔
      f' y ∈ X.T ∨ ∃ z ∈ V(B.G), z ≠ y ∧ f' z = f' y := by
    intro y hy
    rw [hVB] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    have hmem : g a ∈ B.T ↔ a ∈ A.T := by
      rw [hBT]
      constructor
      · rintro ⟨z, hz, he⟩
        exact hginj (A.T_subset hz) ha he ▸ hz
      · exact fun h => mem_image_of_mem g h
    constructor
    · intro h
      rcases (hroot a ha).mp (hmem.mp h) with hold | ⟨z, hz, hza, he⟩
      · exact .inl ((hcomp a ha).symm ▸ hold)
      · refine .inr ⟨g z, hVB ▸ mem_image_of_mem g hz,
          (fun h => hza (hginj hz ha h)), ?_⟩
        rw [hcomp z hz, hcomp a ha, he]
    · rintro (hold | ⟨z, hz, hza, he⟩)
      · apply hmem.mpr
        apply (hroot a ha).mpr
        exact .inl (hcomp a ha ▸ hold)
      · rw [hVB] at hz
        obtain ⟨b, hb, rfl⟩ := hz
        apply hmem.mpr
        apply (hroot a ha).mpr
        refine .inr ⟨b, hb, (fun h => hza (congrArg g h)), ?_⟩
        rwa [hcomp b hb, hcomp a ha] at he
  obtain ⟨n, Z, hchain, hi⟩ := exists_vertexIdChain_of_paired_fibres B X f' hquot hfB hrB
  exact ⟨B, hiso, hindex, n, Z, hchain, hi⟩

end GraphMinor.GM08
