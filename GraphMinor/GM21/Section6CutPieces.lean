module

public import GraphMinor.GM21.Section6CutLift
public import GraphMinor.GM21.Section6CutHalves

/-!
# Graph Minors XXI, (6.3), claim (2): the lifts of the pieces of the supports

The new supports on the cut surface `Σ'` are the lifts of pieces of the old supports. A piece `P`
is a support of `Γ` that meets the line `F` only in its ends. Its lift `lift ψ F P` is the closure
of the part of `ψ⁻¹(P)` off `ψ⁻¹(F)`.

* `lift_piece`: `ψ` is one to one on the lift, which lies over `P` and holds every point over
  `P \ F`.
* `isSupport_of_lift`: a set `K` between the lift and `ψ⁻¹(P)`, mapped one to one onto `P`, is a
  support of `Γ'`. (When `P = {a}`, the lift is empty, and `K` is one of the two points over `a`.)
* `exists_sides`: at an end `a` of `F`, two pieces `A₁, A₂` that meet only in `a` lift to sets that
  hold different points over `a`. So the two points over `a` can be named `a₋, a₊`, with `a₋` the
  only one that the lift of `A₁` may hold, and `a₊` the only one that the lift of `A₂` may hold.
  This is `lift_end_ne`, which rests on the fact that three lines from one point of an `O`-arc
  cannot meet only in that point.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

/-- A proper line with ends `a, b` is one with ends `b, a`. -/
theorem IsProperLineInSurface.swap (hF : IsProperLineInSurface F a b) :
    IsProperLineInSurface F b a :=
  ⟨hF.1.symm, hF.2.2.1, hF.2.1, by rw [pair_comm]; exact hF.2.2.2⟩

/-- The cut along `F` read from the other end of `F`. -/
theorem IsLineCut.symm (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) :
    IsLineCut ψ F b a X Y b₁ a₁ b₂ a₂ :=
  ⟨h.surface, h.cutting, h.disjoint, h.union, h.lineX.symm, h.lineY.symm, h.bijX, h.bijY,
    h.map_b₁, h.map_a₁, h.map_b₂, h.map_a₂⟩

/-- Two disjoint subsingletons inside a two-point set lie in different points of it. -/
theorem exists_sides {T : Type*} {p₁ p₂ : T} (hne : p₁ ≠ p₂) {Z₁ Z₂ : Set T}
    (h₁ : Z₁ ⊆ {p₁, p₂}) (h₂ : Z₂ ⊆ {p₁, p₂}) (hs₁ : Z₁.Subsingleton) (hs₂ : Z₂.Subsingleton)
    (hd : Disjoint Z₁ Z₂) :
    ∃ m p : T, ({m, p} : Set T) = {p₁, p₂} ∧ m ≠ p ∧ Z₁ ⊆ {m} ∧ Z₂ ⊆ {p} := by
  by_cases hp₂ : p₂ ∈ Z₂
  · refine ⟨p₁, p₂, rfl, hne, fun z hz => ?_, fun z hz => hs₂ hz hp₂⟩
    rcases h₁ hz with rfl | rfl
    · rfl
    · exact absurd hp₂ (disjoint_left.mp hd hz)
  · by_cases hp₁ : p₁ ∈ Z₁
    · refine ⟨p₁, p₂, rfl, hne, fun z hz => hs₁ hz hp₁, fun z hz => ?_⟩
      rcases h₂ hz with rfl | rfl
      · exact absurd hp₁ (disjoint_right.mp hd hz)
      · rfl
    · refine ⟨p₂, p₁, pair_comm _ _, hne.symm, fun z hz => ?_, fun z hz => ?_⟩
      · rcases h₁ hz with rfl | rfl
        · exact absurd hz hp₁
        · rfl
      · rcases h₂ hz with rfl | rfl
        · rfl
        · exact absurd hz hp₂

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
include h

/-- **The lift of a piece.** Let `P` be a support of `Γ` with ends `u, w`, meeting `F` only in its
ends. Then `ψ` is one to one on the lift of `P`, which lies over `P` and holds every point over
`P \ F`. -/
theorem lift_piece (hS : IsSurface S) {Γ : Drawing S} {P : Set S} {u w : S}
    (hsup : SupportHasEnds Γ P u w) (hPF : P ∩ F ⊆ {u, w}) :
    InjOn ψ (lift ψ F P) ∧ lift ψ F P ⊆ ψ ⁻¹' P ∧ ψ ⁻¹' (P \ F) ⊆ lift ψ F P := by
  have : T2Space S := hS.2.1
  have : T2Space S' := h.t2Space
  have hPc : IsClosed P := GM21.Supports.isClosed_of_supportHasEnds hS hsup
  refine ⟨?_, h.lift_subset_preimage hS hPc, subset_closure⟩
  rcases hsup with ⟨v, -, hPv, -, -⟩ | ⟨-, hne, -, -, hline⟩
  · subst hPv
    by_cases hvF : v ∈ F
    · have : lift ψ F {v} = ∅ := by
        rw [lift, show ({v} : Set S) \ F = ∅ from sdiff_eq_empty.mpr (singleton_subset_iff.mpr hvF), preimage_empty, closure_empty]
      rw [this]
      exact injOn_empty _
    · have hcl : lift ψ F {v} = ψ ⁻¹' {v} := by
        rw [lift, show ({v} : Set S) \ F = {v} from sdiff_eq_left.mpr (disjoint_singleton_left.mpr hvF)]
        exact (h.finite_fiber v).isClosed.closure_eq
      rw [hcl]
      refine h.injOn_compl.mono fun z hz => ?_
      have : ψ z = v := hz
      show ψ z ∉ F
      rw [this]
      exact hvF
  · exact (h.isLineWithEnds_lift hS hne hline hPF).choose_spec.choose_spec.2.2.2.2

/-- **A lifted piece is a support of `Γ'`.** -/
theorem isSupport_of_lift (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V) {P : Set S} {u w : S}
    (hsup : SupportHasEnds Γ P u w) (hPF : P ∩ F ⊆ {u, w}) {K : Set S'}
    (hK₁ : lift ψ F P ⊆ K) (hK₂ : K ⊆ ψ ⁻¹' P) (hinj : InjOn ψ K) (himg : ψ '' K = P) :
    IsSupportOfDrawing Γ' K := by
  have : T2Space S := hS.2.1
  have hPbd : P ⊆ bd S := GM21.Supports.subset_bd_of_isSupportOfDrawing ⟨u, w, hsup⟩
  have hKbd : K ⊆ bd S' := fun z hz => by
    rw [h.bd_eq hS hF]
    exact Or.inl (hPbd (hK₂ hz))
  have hKV : ∀ z ∈ K, z ∈ Γ'.V ↔ ψ z ∈ Γ.V := fun z _ => by rw [hV]; rfl
  rcases hsup with ⟨v, hv, hPv, -, -⟩ | ⟨hsub, hne, hu, hw, hline⟩
  · subst hPv
    obtain ⟨k, hk, hkv⟩ : (v : S) ∈ ψ '' K := himg ▸ mem_singleton v
    have hKk : K = {k} := by
      apply Subset.antisymm
      · intro z hz
        have hz' : ψ z = v := hK₂ hz
        exact hinj hz hk (hz'.trans hkv.symm)
      · exact singleton_subset_iff.mpr hk
    refine ⟨k, k, Or.inl ⟨k, ⟨(hKV k hk).mpr (hkv ▸ hv.1), hKbd hk⟩, hKk, rfl, rfl⟩⟩
  · obtain ⟨u', w', hL, hu', hw', himgL, -⟩ := h.isLineWithEnds_lift hS hne hline hPF
    have hKL : K = lift ψ F P := by
      apply Subset.antisymm _ hK₁
      intro z hz
      obtain ⟨l, hl, hlz⟩ : ψ z ∈ ψ '' lift ψ F P := himgL.symm ▸ hK₂ hz
      rwa [← hinj (hK₁ hl) hz hlz]
    rw [hKL] at hKbd ⊢
    refine ⟨u', w', Or.inr ⟨hKbd, fun he => hne (by rw [← hu', ← hw', he]), ⟨?_, hKbd hL.left_mem⟩,
      ⟨?_, hKbd hL.right_mem⟩, hL⟩⟩
    · rw [hV]; show ψ u' ∈ Γ.V; rw [hu']; exact hu.1
    · rw [hV]; show ψ w' ∈ Γ.V; rw [hw']; exact hw.1

/-- **The two sides at `a`.** Two pieces with end `a` that meet only in `a` lift to sets holding
different points over `a`. -/
theorem exists_sides_at (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    {A₁ A₂ : Set S} {u₁ u₂ : S} (h₁ : SupportHasEnds Γ A₁ a u₁) (h₂ : SupportHasEnds Γ A₂ a u₂)
    (hF₁ : A₁ ∩ F ⊆ {a, u₁}) (hF₂ : A₂ ∩ F ⊆ {a, u₂}) (hint : A₁ ∩ A₂ = {a}) :
    ∃ m p : S', ψ ⁻¹' {a} = {m, p} ∧ m ≠ p ∧ lift ψ F A₁ ∩ ψ ⁻¹' {a} ⊆ {m} ∧
      lift ψ F A₂ ∩ ψ ⁻¹' {a} ⊆ {p} := by
  have haF : a ∈ F := a_mem hF
  have hsub : ∀ {A : Set S} {u : S}, SupportHasEnds Γ A a u → A ∩ F ⊆ {a, u} →
      (lift ψ F A ∩ ψ ⁻¹' {a}).Subsingleton := fun hA hAF x hx y hy =>
    (h.lift_piece hS hA hAF).1 hx.1 hy.1 (by
      have h1 : ψ x = a := hx.2
      have h2 : ψ y = a := hy.2
      rw [h1, h2])
  -- A degenerate piece `{a}` has an empty lift.
  have hempty : ∀ {A : Set S}, (∀ x ∈ A, x = a) → lift ψ F A = ∅ := fun hA => by
    rw [lift, show _ \ F = ∅ from by
      ext x
      simp only [mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      rw [hA x hx]
      exact haF, preimage_empty, closure_empty]
  have hdisj : Disjoint (lift ψ F A₁ ∩ ψ ⁻¹' {a}) (lift ψ F A₂ ∩ ψ ⁻¹' {a}) := by
    rw [disjoint_left]
    rintro z ⟨hz₁, hza⟩ ⟨hz₂, -⟩
    rcases h₁ with ⟨v, -, hAv, hav, -⟩ | ⟨hbd₁, hne₁, -, -, hl₁⟩
    · rw [hempty (fun x hx => by rw [hAv] at hx; rw [hx, hav])] at hz₁
      exact hz₁
    rcases h₂ with ⟨v, -, hAv, hav, -⟩ | ⟨hbd₂, hne₂, -, -, hl₂⟩
    · rw [hempty (fun x hx => by rw [hAv] at hx; rw [hx, hav])] at hz₂
      exact hz₂
    exact h.lift_end_ne hS hF hl₁ hl₂ hne₁ hne₂ hbd₁ hbd₂ hF₁ hF₂ (hint ▸ finite_singleton a)
      hz₁ hz₂ hza hza rfl
  rw [h.preimage_a hF] at hdisj ⊢
  obtain ⟨m, p, hmp, hne, hm, hp⟩ := exists_sides h.a₁_ne_a₂ inter_subset_right
    inter_subset_right (by rw [← h.preimage_a hF]; exact hsub h₁ hF₁)
    (by rw [← h.preimage_a hF]; exact hsub h₂ hF₂) hdisj
  exact ⟨m, p, hmp.symm, hne, hm, hp⟩

end IsLineCut

end CutLine
end GM21
end GraphMinor
