module

public import GraphMinor.GM01.PathBagBoundaries
import GraphMinor.GM01.PathDecompositionPadding
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Concatenating refinements of path-decomposition bags

In Graph Minors I, (1.6), page 40, replace each outer bag by its
refinement. Keep its shared boundary in every inner bag. Pad the
refinements by repeating their final bags, and concatenate them in
the outer order. A vertex occurring in two outer bags belongs to
the boundary of every intervening bag. This proves the interval
condition across different refinements.
-/

public section

namespace GraphMinor.GM01

open Set Graph

private theorem outer_le {r N : ℕ} {i j : Fin (r * N)} (hij : i ≤ j) : i.divNat ≤ j.divNat := by
  change i.val / N ≤ j.val / N
  exact Nat.div_le_div_right (show i.val ≤ j.val from hij)

private theorem inner_le_of_outer_eq {r N : ℕ} {i j : Fin (r * N)}
    (hij : i ≤ j) (houter : i.divNat = j.divNat) : i.modNat ≤ j.modNat := by
  change i.val % N ≤ j.val % N
  have ho := congrArg Fin.val houter
  change i.val / N = j.val / N at ho
  have hi := Nat.mod_add_div i.val N
  have hj := Nat.mod_add_div j.val N
  rw [← ho] at hj
  have hval : i.val ≤ j.val := hij
  omega

/-- Concatenate nonempty refinements that keep each shared boundary
in every bag. This is the concatenation step of GM01 (1.6), page 40. -/
theorem hasPathWidthLE_of_bag_refinements {α β : Type*} {G : Graph α β}
    (D : PathDecomposition G) (E : ∀ i : Fin D.length, PathDecomposition (G.induce (D.bag i)))
    (hpos : ∀ i, 0 < (E i).length) {k : ℕ}
    (hbound : ∀ i j, ((E i).bag j).Finite ∧ ((E i).bag j).ncard ≤ k + 1)
    (hboundary : ∀ i j, D.boundary i ⊆ (E i).bag j) : HasPathWidthLE G k := by
  classical
  let N := Finset.univ.sup (fun i ↦ (E i).length)
  have hlen : ∀ i, (E i).length ≤ N := fun i ↦ Finset.le_sup (f := fun i ↦ (E i).length) (Finset.mem_univ i)
  let F := fun i ↦ (E i).pad (hpos i) N (hlen i)
  have hFbound : ∀ i (j : Fin N), ((F i).bag j).Finite ∧ ((F i).bag j).ncard ≤ k + 1 :=
    fun i j ↦ hbound i _
  have hFboundary : ∀ i (j : Fin N), D.boundary i ⊆ (F i).bag j := fun i j ↦ hboundary i _
  have hFsub : ∀ i (j : Fin N), (F i).bag j ⊆ D.bag i := fun i j ↦ (F i).bag_subset j
  let bag : Fin (D.length * N) → Set α := fun t ↦ (F t.divNat).bag t.modNat
  refine ⟨⟨D.length * N, bag, ?_, ?_, ?_⟩, fun i ↦ hFbound i.divNat i.modNat⟩
  · intro i x hx
    exact D.bag_subset i.divNat (hFsub i.divNat i.modNat hx)
  · intro edge x y he
    obtain ⟨i, hxi, hyi⟩ := D.edge_covered edge x y he
    obtain ⟨j, hxj, hyj⟩ := (F i).edge_covered edge x y ⟨he, hxi, hyi⟩
    let e : Fin D.length × Fin N ≃ Fin (D.length * N) := finProdFinEquiv
    have hp := e.symm_apply_apply (i,j)
    have hfst : (e (i,j)).divNat = i := congrArg Prod.fst hp
    have hsnd : (e (i,j)).modNat = j := congrArg Prod.snd hp
    refine ⟨e (i,j), ?_, ?_⟩
    · change x ∈ (F (e (i,j)).divNat).bag (e (i,j)).modNat
      rw [hfst, hsnd]
      exact hxj
    · change y ∈ (F (e (i,j)).divNat).bag (e (i,j)).modNat
      rw [hfst, hsnd]
      exact hyj
  · intro i j l hij hjl x hx
    have hIJ := outer_le hij
    have hJL := outer_le hjl
    change x ∈ (F i.divNat).bag i.modNat ∩ (F l.divNat).bag l.modNat at hx
    change x ∈ (F j.divNat).bag j.modNat
    by_cases hil : i.divNat = l.divNat
    · have hji : j.divNat = i.divNat := le_antisymm (hil ▸ hJL) hIJ
      have hmij := inner_le_of_outer_eq hij hji.symm
      have hmjl := inner_le_of_outer_eq hjl (hji.trans hil)
      rw [← hil] at hx
      rw [hji]
      exact (F i.divNat).interval i.modNat j.modNat l.modNat hmij hmjl hx
    · have hxi := hFsub i.divNat i.modNat hx.1
      have hxl := hFsub l.divNat l.modNat hx.2
      by_cases hji : j.divNat = i.divNat
      · apply hFboundary j.divNat j.modNat
        rw [hji]
        exact D.mem_boundary_of_mem_two_bags (Ne.symm hil) hxi hxl
      · have hxj := D.interval i.divNat j.divNat l.divNat hIJ hJL ⟨hxi, hxl⟩
        exact hFboundary j.divNat j.modNat
          (D.mem_boundary_of_mem_two_bags (Ne.symm hji) hxj hxi)

end GraphMinor.GM01
