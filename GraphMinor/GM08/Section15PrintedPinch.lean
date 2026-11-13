module

public import GraphMinor.GM08.Section15PrintedConcat

/-!
# Graph Minors VIII, (15.1) with the printed width: pinched tubes

Two tools for our proof of the printed (15.1) (`Section15PrintedFinal.lean`).

* Every hoop of $\Sigma(F_1, F_2)$ contains $F_1 \cap F_2$
  (`Tube.inter_subset_of_hoop`). The reason: such a hoop $H$ lies between $F_1$
  and $F_2$, so a point on both $F_1$ and $F_2$ lies in the closed $F_1$-side of
  $H$ and in its closed $F_2$-side, and these two closed sides meet only in $H$.
* So if $F_1$ and $F_2$ carry the same vertex set $A$ ("the tube is pinched at
  $A$"), every hoop contains $A$. A hoop is then either exempt, or has at least
  $|A| + 1$ vertices, and the printed width is at least $|A| + 1$
  (`Tube.printedWidth_ge_of_pinched`).

We also record (15.1) for $r = 0$ with the printed width
(`theorem_15_1_printed_zero`). For $r = 0$ the hypothesis on the width is empty,
so the side-qualified (15.1) applies directly.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set

universe u v w

/-- Every hoop of $\Sigma(F_1, F_2)$ contains $F_1 \cap F_2$. -/
theorem Tube.inter_subset_of_hoop {S : Type w} [TopologicalSpace S] (τ : Tube S) {H : Set S}
    (hH : IsHoop H) (hsub : H ⊆ cylinderBetween τ.F₁ τ.F₂) : τ.F₁ ∩ τ.F₂ ⊆ H := by
  have : T2Space S := τ.t2Space
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂
    τ.laminar
  obtain ⟨h1, h2⟩ := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂
    hH hle).mp hsub
  have h2' : cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂ ⊆ cap.disc₂ τ.isCylinder.1 hH :=
    (cap.disc₂_subset_iff_disc₁_subset τ.isCylinder.1 hH τ.isHoop_F₂).mpr h2
  rintro x ⟨hx₁, hx₂⟩
  obtain ⟨-, -, hb₁, -, -, -, -, -⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
  obtain ⟨-, -, -, hb₂, -, -, -, -⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
  obtain ⟨-, -, -, -, -, hcapH, -, -⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 hH
  have hxa : cap.j x ∈ cap.disc₁ τ.isCylinder.1 hH :=
    h1 (Surface.discBd_subset _ (hb₁ ▸ mem_image_of_mem _ hx₁))
  have hxb : cap.j x ∈ cap.disc₂ τ.isCylinder.1 hH :=
    h2' (Surface.discBd_subset _ (hb₂ ▸ mem_image_of_mem _ hx₂))
  have hxab : cap.j x ∈ cap.disc₁ τ.isCylinder.1 hH ∩ cap.disc₂ τ.isCylinder.1 hH := ⟨hxa, hxb⟩
  rw [hcapH] at hxab
  obtain ⟨y, hy, hyx⟩ := hxab
  exact cap.inj hyx ▸ hy

/-- A tube whose two hoops carry the same vertex set $A$ has printed width at least
$|A| + 1$: every hoop contains $A$ (`Tube.inter_subset_of_hoop`), so its vertex set is
either $A$, which is exempt, or a strictly larger finite set. -/
theorem Tube.printedWidth_ge_of_pinched {S : Type w} [TopologicalSpace S] (τ : Tube S)
    (hpin : τ.F₁ ∩ τ.Γ.V = τ.F₂ ∩ τ.Γ.V) :
    (((τ.F₁ ∩ τ.Γ.V).ncard + 1 : ℕ) : ℕ∞) ≤ τ.printedWidth := by
  refine τ.le_printedWidth_iff.mpr fun H hH _ hsub => ?_
  have hA : τ.F₁ ∩ τ.Γ.V ⊆ H ∩ τ.Γ.V := by
    intro x hx
    have hx₂ : x ∈ τ.F₂ := (hpin ▸ hx).1
    exact ⟨τ.inter_subset_of_hoop hH hsub ⟨hx.1, hx₂⟩, hx.2⟩
  by_cases heq : H ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V
  · exact Or.inl heq
  · refine Or.inr (Or.inr ?_)
    have hfin : (H ∩ τ.Γ.V).Finite := τ.Γ.finite_V.subset inter_subset_right
    have hlt : (τ.F₁ ∩ τ.Γ.V).ncard < (H ∩ τ.Γ.V).ncard :=
      ncard_lt_ncard (hA.ssubset_of_ne (Ne.symm heq)) hfin
    exact_mod_cast hlt

/-- **Graph Minors VIII, (15.1)** with the printed width, for $r = 0$:
every tubular graft of index $\le k$ is a $0$-train of tubular grafts of printed width
$\ge 1$ and index $\le k$. The side-qualified (15.1) (`GM08.theorem_15_1_side_qualified`) applies, since
every tubular graft has side-qualified width $\ge 0$, and each piece has printed width at
least its side-qualified width. -/
theorem theorem_15_1_printed_zero {α : Type u} {β : Type v} (k : ℕ) :
    printedTubularClass (α := α) (β := β) 0 k ⊆
      LKGraftClass 0 (printedTubularClass (0 + 1) (k + 2 * 0)) := by
  rintro X ⟨htub, -, hk⟩
  have hX : X ∈ tubularClass 0 k := ⟨htub, by simp, hk⟩
  exact LKGraftClass_mono 0 (tubularClass_subset_printedTubularClass _ _) (theorem_15_1_side_qualified 0 k hX)

end GraphMinor.GM08
