module

public import GraphMinor.GM08.Section16PrintedWidth
public import GraphMinor.GM08.Section15Menger
import GraphMinor.GM08.Section16Step

/-!
# Obtaining linkage from the printed width

If both boundary hoops have at least the required number of vertices,
the two exceptions in the printed width definition satisfy the same
lower bound as every other normal hoop. The tube Menger theorem then
gives the required disjoint skeleton paths. This supplies the central
linkage in the application of VII (9.3) within VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Printed width gives linkage when its two exceptional boundary
vertex sets are also large enough, as used in VIII (17.2), page 284. -/
theorem Tube.hasDisjointPaths_of_printedWidth {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r : ℕ} (hw : (r : ℕ∞) ≤ τ.printedWidth)
    (h₁ : r ≤ (τ.Γ.V ∩ τ.F₁).ncard) (h₂ : r ≤ (τ.Γ.V ∩ τ.F₂).ncard) :
    HasDisjointPaths τ.Γ.toHypergraph.skeleton
      (τ.Γ.V ∩ τ.F₁) (τ.Γ.V ∩ τ.F₂) r := by
  apply τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge
    τ.laminar τ.isNormal_F₁ τ.isNormal_F₂
  intro H hH hNH hsub
  rcases (τ.le_printedWidth_iff.mp hw) H hH hNH hsub with heq | heq | hbound
  · rw [inter_comm τ.Γ.V H, heq, inter_comm]
    exact h₁
  · rw [inter_comm τ.Γ.V H, heq, inter_comm]
    exact h₂
  · rw [inter_comm]
    exact_mod_cast hbound

/-- In a tube of length at least four, printed width is at most one
more than the first boundary count. The inward step has just one new
vertex, and its vertex set is neither printed exception. This is the
boundary-count estimate for VIII (17.2), page 284. -/
theorem Tube.le_first_boundary_ncard_add_one_of_le_printedWidth {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {r : ℕ}
    (hw : (r : ℕ∞) ≤ τ.printedWidth) (hlen : 4 ≤ τ.length) :
    r ≤ (τ.Γ.V ∩ τ.F₁).ncard + 1 := by
  obtain ⟨K, hlam, hNK, hKsub, ⟨v, hvV, hvK, hvF, hverts⟩, hlenK⟩ :=
    τ.exists_hoop_step_inward_refined (s := 2) hlen
  have hne₁ : K ∩ τ.Γ.V ≠ τ.F₁ ∩ τ.Γ.V := by
    intro heq
    exact hvF (heq.subset ⟨hvK, hvV⟩).1
  have hne₂ : K ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V := by
    intro heq
    exact disjoint_left.mp ((τ.subTube hlam hNK τ.isNormal_F₂).disjoint_of_two_le_length hlenK)
      hvK (heq.subset ⟨hvK, hvV⟩).1
  have hr : r ≤ (K ∩ τ.Γ.V).ncard := by
    have h := (((τ.le_printedWidth_iff.mp hw) K hlam.2.1 hNK hKsub).resolve_left hne₁).resolve_left hne₂
    exact_mod_cast h
  have hsub : K ∩ τ.Γ.V ⊆ (τ.F₁ ∩ τ.Γ.V) ∪ {v} := by
    intro x hx
    rcases hverts hx with hxF | hxv
    · exact .inl ⟨hxF, hx.2⟩
    · exact .inr hxv
  have hcard := (ncard_le_ncard hsub
    ((τ.Γ.finite_V.inter_of_right τ.F₁).union (finite_singleton v))).trans
    (ncard_union_le (τ.F₁ ∩ τ.Γ.V) {v})
  rw [ncard_singleton, inter_comm τ.F₁ τ.Γ.V] at hcard
  exact hr.trans hcard

/-- Printed width one larger than the desired path count gives central
linkage whenever the tube length is at least four. This supplies the
path-count condition in the application of VII (9.3) to VIII (17.2). -/
theorem Tube.hasDisjointPaths_of_printedWidth_add_one {S : Type w}
    [TopologicalSpace S] (τ : Tube S) {r : ℕ}
    (hw : ((r + 1 : ℕ) : ℕ∞) ≤ τ.printedWidth) (hlen : 4 ≤ τ.length) :
    HasDisjointPaths τ.Γ.toHypergraph.skeleton
      (τ.Γ.V ∩ τ.F₁) (τ.Γ.V ∩ τ.F₂) r := by
  have hleft := τ.le_first_boundary_ncard_add_one_of_le_printedWidth hw hlen
  have hright := τ.symm.le_first_boundary_ncard_add_one_of_le_printedWidth
    (by simpa only [Tube.printedWidth_symm] using hw)
    (by simpa only [Tube.length_symm] using hlen)
  change r + 1 ≤ (τ.Γ.V ∩ τ.F₂).ncard + 1 at hright
  exact τ.hasDisjointPaths_of_printedWidth
    ((by exact_mod_cast Nat.le_succ r : (r : ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞)).trans hw)
    (by omega) (by omega)

end GraphMinor.GM08
