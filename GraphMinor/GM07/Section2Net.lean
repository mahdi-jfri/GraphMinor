module

public import GraphMinor.GM07.NetExistsCut
public import GraphMinor.GM07.Defs

/-!
# A net from a cut that is a closed disc

For the converse of Graph Minors VII, (2.1) (page 216), the surface `Σ` is cut along the edges of
`J - bd(Σ)`, and the cut surface `Δ` is a closed disc. Here we turn such a cut into a net
(`exists_net_of_netCut`). The disc of the net is the cut surface, the associated surjection is the
cutting map, and the pairs of the net are the two lifts of each path that is cut along. The seam
graph has the image of `bd(Δ)` as its point set, and the ends of these paths as its vertices.

One point needs an argument: an arc-map of a net is one to one, so the two ends of a lift must
differ. On a cuff that carries another arc, an arc cannot close up, since it would then go once
around the cuff and meet the other arc (`IsArcFamily.ends_ne`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology GraphMinor.Surface

universe u

section arcs

variable {Z ι : Type*} [TopologicalSpace Z] {ℓ : ι → ℝ → Z}

/-- A point inside an arc of a family is on no other arc. -/
theorem IsArcFamily.ne_of_ne (hf : IsArcFamily ℓ) {α β : ι} (hne : α ≠ β) {u v : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) : ℓ α u ≠ ℓ β v := by
  rcases eq_or_lt_of_le hv.1 with rfl | h1
  · exact (hf.off α β u hu).1
  rcases eq_or_lt_of_le hv.2 with rfl | h2
  · exact (hf.off α β u hu).2
  exact hf.disj α β hne u hu v ⟨h1, h2⟩

/-- **An arc on a cuff with another arc does not close up.** If the arc `α` lies on a cuff `C` and
another arc `β` meets `C`, then the two ends of `α` differ. Otherwise `α` goes once around `C`
(its lift to the real line has length one), so the middle point of `β` is a point of `α`. -/
theorem IsArcFamily.ends_ne (hS : IsSurface Z) (hf : IsArcFamily ℓ) {C : Set Z} (hC : C ∈ cuffs Z)
    {α β : ι} (hne : α ≠ β) (hα : ℓ α 0 ∈ C) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) (hβ : ℓ β w ∈ C) :
    ℓ α 0 ≠ ℓ α 1 := by
  intro h01
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have hαC := arc_sub_cuff hf hC h0 hα
  have hβC := arc_sub_cuff hf hC hw hβ
  obtain ⟨φ⟩ := (cuff_statement Z hS).2.2 C hC
  obtain ⟨σ, n, hnc, hnm, hn, hn1⟩ := exists_dir_lift hf φ α hαC
  have hend : ∀ s : Bool, ∀ t ∈ ({0, 1} : Set ℝ), ℓ α (ofs s t) = ℓ α 0 := by
    intro s t ht
    rcases ht with rfl | rfl <;> cases s <;> simp [ofs_true, ofs_false, h01]
  have hee : ee (n 0) = ee (n 1) := by
    apply φ.injective
    apply Subtype.ext
    rw [hn 0 h0, hn 1 h1, hend σ 0 (by simp), hend σ 1 (by simp)]
  obtain ⟨m, hm⟩ := ee_eq_iff.mp hee
  have hlt : n 0 < n 1 := hnm h0 h1 zero_lt_one
  have hm1 : (m : ℝ) = -1 := by
    have h2 : (m : ℝ) < 0 := by linarith
    have h3 : (-1 : ℝ) ≤ m := by linarith
    have h4 : m < 0 := by exact_mod_cast h2
    have h5 : -1 ≤ m := by exact_mod_cast h3
    have : m = -1 := by omega
    rw [this]
    norm_num
  have hn01 : n 1 = n 0 + 1 := by linarith
  have hh : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  set x : C := ⟨ℓ β (1 / 2), hβC _ ⟨hh.1.le, hh.2.le⟩⟩
  obtain ⟨s, hs⟩ := ee_surjective (φ.symm x)
  set s' : ℝ := s - ⌊s - n 0⌋ with hs'
  have hs'1 : n 0 ≤ s' := by
    have := Int.floor_le (s - n 0)
    linarith
  have hs'2 : s' < n 0 + 1 := by
    have := Int.lt_floor_add_one (s - n 0)
    linarith
  have hee' : ee s' = ee s := ee_eq_iff.mpr ⟨-⌊s - n 0⌋, by push_cast; ring⟩
  obtain ⟨v, hv, hnv⟩ := intermediate_value_Icc zero_le_one hnc ⟨hs'1, hn01 ▸ hs'2.le⟩
  have hv1 : v ≠ 1 := by
    rintro rfl
    linarith
  have hpt : ℓ α (ofs σ v) = ℓ β (1 / 2) := by
    rw [← hn v hv, hnv, hee', hs, φ.apply_symm_apply]
  rcases eq_or_lt_of_le hv.1 with rfl | hv0
  · exact (hf.off β α _ hh).1 (by rw [← hpt, hend σ 0 (by simp)])
  · have hvI : v ∈ Ioo (0 : ℝ) 1 := ⟨hv0, lt_of_le_of_ne hv.2 hv1⟩
    exact hf.ne_of_ne hne (ofs_Ioo σ hvI) ⟨hh.1.le, hh.2.le⟩ hpt

/-- An arc whose two ends differ is one to one. -/
theorem IsArcFamily.injOn_Icc (hf : IsArcFamily ℓ) (α : ι) (h01 : ℓ α 0 ≠ ℓ α 1) :
    InjOn (ℓ α) (Icc 0 1) := by
  intro x hx y hy he
  rcases eq_or_lt_of_le hx.2 with rfl | hx1
  · rcases eq_or_lt_of_le hy.2 with rfl | hy1
    · rfl
    rcases eq_or_lt_of_le hy.1 with rfl | hy0
    · exact absurd he.symm h01
    · exact absurd he.symm (hf.off α α y ⟨hy0, hy1⟩).2
  rcases eq_or_lt_of_le hy.2 with rfl | hy1
  · rcases eq_or_lt_of_le hx.1 with rfl | hx0
    · exact absurd he h01
    · exact absurd he (hf.off α α x ⟨hx0, hx1⟩).2
  exact hf.injOn_Ico α ⟨hx.1, hx1⟩ ⟨hy.1, hy1⟩ he

end arcs

/-- If no step of a relation starts or ends at `x`, then `x` is related only to itself by the
equivalence it generates. -/
theorem eqvGen_eq_of_isolated {X : Type*} {r : X → X → Prop} {x : X}
    (hx : ∀ a b, r a b → a ≠ x ∧ b ≠ x) {y : X} (h : Relation.EqvGen r x y) : x = y := by
  have key : ∀ a b, Relation.EqvGen r a b → (a = x ↔ b = x) := by
    intro a b hab
    induction hab with
    | rel a b hs => exact ⟨fun h => absurd h (hx a b hs).1, fun h => absurd h (hx a b hs).2⟩
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ h1 h2 => exact h1.trans h2
  exact ((key x y h).mp rfl).symm

/-- The boundary of a closed disc is connected. -/
theorem isPreconnected_bd_of_isClosedDisc {Y : Type*} [TopologicalSpace Y]
    (hD : IsClosedDisc (univ : Set Y)) : IsPreconnected (bd Y) := by
  have heq : discBd (univ : Set Y) = bd Y := image_bd_homeomorph (Homeomorph.Set.univ Y)
  obtain ⟨φ⟩ := heq ▸ hD.isOArc_discBd
  have h : bd Y = range fun x : Circle => (φ x).1 := by
    ext y
    exact ⟨fun hy => ⟨φ.symm ⟨y, hy⟩, by simp⟩, by rintro ⟨x, rfl⟩; exact (φ x).2⟩
  rw [h]
  exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)

/-- **A net from a cut that is a closed disc.** Let `ψ : Y → S` cut `S` along the paths `a k`,
with lifts `ξ k` and `η k`, and suppose that `Y` is a closed disc and that some path is inner.
Then there is a net whose disc is `Y`, whose associated surjection is `ψ`, and whose pairs are
the lifts of the inner paths. Its seam is `ψ(bd(Y))`, and its seam vertices are the ends of the
inner paths. -/
theorem exists_net_of_netCut {S Y κ : Type u} [TopologicalSpace S] [T2Space S] [TopologicalSpace Y]
    [Finite κ] {a : κ → ℝ → S} {inner : κ → Prop} {ψ : Y → S} {ξ η : κ → ℝ → Y}
    (hY : IsSurface Y) (hD : IsClosedDisc (univ : Set Y)) (h : IsNetCut a inner ψ ξ η)
    (hin : ∃ k, inner k) :
    ∃ N : Net S, 0 < N.r ∧ N.seamU = ψ '' bd Y ∧
      N.seamV = {z | ∃ k, inner k ∧ (a k 0 = z ∨ a k 1 = z)} := by
  classical
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have hf := h.isArcFamily
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  set K := {k // inner k}
  have : Finite K := inferInstance
  set e : K ≃ Fin (Nat.card K) := Finite.equivFin K
  -- the two lifts of an inner path, as members of the arc family
  let A : K → NetArc inner := fun k => ⟨(k.1, true), .inl rfl⟩
  let B : K → NetArc inner := fun k => ⟨(k.1, false), .inr k.2⟩
  have hA : ∀ k : K, netL ξ η (A k) = ξ k.1 := fun k => rfl
  have hB : ∀ k : K, netL ξ η (B k) = η k.1 := fun k => rfl
  have hAB : ∀ k : K, A k ≠ B k := fun k hk => by
    have := congrArg (fun x : NetArc inner => x.1.2) hk
    simp [A, B] at this
  have hAinj : ∀ k k' : K, A k = A k' → k = k' := fun k k' hk =>
    Subtype.ext (congrArg (fun x : NetArc inner => x.1.1) hk)
  have hBinj : ∀ k k' : K, B k = B k' → k = k' := fun k k' hk =>
    Subtype.ext (congrArg (fun x : NetArc inner => x.1.1) hk)
  have hAB' : ∀ k k' : K, A k ≠ B k' := fun k k' hk => by
    have := congrArg (fun x : NetArc inner => x.1.2) hk
    simp [A, B] at this
  -- the boundary of `Y` is one cuff
  have hbdc := isPreconnected_bd_of_isClosedDisc hD
  have hcuff : ∀ y ∈ bd Y, bd Y ∈ cuffs Y := fun y hy =>
    ⟨y, hy, hbdc.connectedComponentIn hy⟩
  have hends : ∀ (α β : NetArc inner), α ≠ β → netL ξ η α 0 ≠ netL ξ η α 1 := fun α β hne =>
    hf.ends_ne hY (hcuff _ (hf.mem α 0 h0)) hne (hf.mem α 0 h0) h0 (hf.mem β 0 h0)
  have hinjI : ∀ α : NetArc inner, (∃ β, α ≠ β) → InjOn (netL ξ η α) (Icc 0 1) :=
    fun α ⟨β, hne⟩ => hf.injOn_Icc α (hends α β hne)
  have hcont : ∀ (c : ℝ → Y), ContinuousOn c (Icc 0 1) → Continuous fun t : unitInterval => c t :=
    fun c hc => hc.comp_continuous continuous_subtype_val fun t => t.2
  let f : Fin (Nat.card K) → Curve Y := fun i => ⟨fun t => ξ (e.symm i).1 t, hcont _ (h.cξ _)⟩
  let g : Fin (Nat.card K) → Curve Y := fun i => ⟨fun t => η (e.symm i).1 t, hcont _ (h.cη _)⟩
  have hfv : ∀ i t, f i t = netL ξ η (A (e.symm i)) t := fun i t => rfl
  have hgv : ∀ i t, g i t = netL ξ η (B (e.symm i)) t := fun i t => rfl
  have hinjL : ∀ α : NetArc inner, (∃ β, α ≠ β) → ∀ s t : unitInterval,
      netL ξ η α s = netL ξ η α t → s = t := fun α hα s t hst =>
    Subtype.ext (hinjI α hα s.2 t.2 hst)
  have hdisjL : ∀ α β : NetArc inner, α ≠ β → ∀ x ∈ Ioo (0 : unitInterval) 1,
      ∀ y : unitInterval, netL ξ η α x ≠ netL ξ η β y := fun α β hne x hx y =>
    hf.ne_of_ne hne ⟨hx.1, hx.2⟩ y.2
  have hstep : ∀ p q : Y, (∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q = η k u) →
      Relation.EqvGen (fun a b : Y => ∃ (i : Fin (Nat.card K)) (t : unitInterval),
        a = f i t ∧ b = g i t) p q := by
    rintro p q ⟨k, u, hu, rfl, rfl⟩
    by_cases hk : inner k
    · refine .rel _ _ ⟨e ⟨k, hk⟩, ⟨u, hu⟩, ?_, ?_⟩
      · show ξ k u = ξ (e.symm (e ⟨k, hk⟩)).1 u
        rw [e.symm_apply_apply]
      · show η k u = η (e.symm (e ⟨k, hk⟩)).1 u
        rw [e.symm_apply_apply]
    · rw [h.eqb k hk u hu]
      exact .refl _
  have hψc : Continuous ψ := h.cont
  refine ⟨{ D := Y
            isSurface_D := hY
            isClosedDisc_D := hD
            r := Nat.card K
            f := f
            g := g
            φ := ψ
            injective_f := fun i s t hst => hinjL (A (e.symm i)) ⟨_, hAB _⟩ s t hst
            range_f_subset_bd := fun i => range_subset_iff.mpr fun t => h.bdξ _ t t.2
            injective_g := fun i s t hst => hinjL (B (e.symm i)) ⟨_, (hAB _).symm⟩ s t hst
            range_g_subset_bd := fun i => range_subset_iff.mpr fun t => h.bdη _ t t.2
            internally_disjoint_ff := fun i j hij x hx ⟨y, hy⟩ => hdisjL (A (e.symm i))
              (A (e.symm j)) (fun hk => hij (e.symm.injective (hAinj _ _ hk))) x hx y hy.symm
            internally_disjoint_gg := fun i j hij x hx ⟨y, hy⟩ => hdisjL (B (e.symm i))
              (B (e.symm j)) (fun hk => hij (e.symm.injective (hBinj _ _ hk))) x hx y hy.symm
            internally_disjoint_fg := fun i j x hx ⟨y, hy⟩ =>
              hdisjL (A (e.symm i)) (B (e.symm j)) (hAB' _ _) x hx y hy.symm
            internally_disjoint_gf := fun i j x hx ⟨y, hy⟩ =>
              hdisjL (B (e.symm i)) (A (e.symm j)) (fun hk => hAB' _ _ hk.symm) x hx y hy.symm
            quotientMap_φ := hψc.isClosedMap.isQuotientMap hψc h.surj
            pasting_eq := fun i t => by
              show ψ (ξ _ t) = ψ (η _ t)
              rw [h.hξ _ t t.2, h.hη _ t t.2]
            interior_inj := fun x hx y hxy => by
              refine eqvGen_eq_of_isolated (r := fun p q : Y =>
                ∃ k, ∃ u ∈ Icc (0 : ℝ) 1, p = ξ k u ∧ q = η k u) ?_ (h.fib x y hxy)
              rintro p q ⟨k, u, hu, rfl, rfl⟩
              exact ⟨fun he => hx (he ▸ h.bdξ k u hu), fun he => hx (he ▸ h.bdη k u hu)⟩
            bd_eq_iff := fun x y => ⟨fun hxy => by
                have hr := h.fib x y hxy
                clear hxy
                induction hr with
                | rel p q hs => exact hstep p q hs
                | refl _ => exact .refl _
                | symm _ _ _ ih => exact .symm _ _ ih
                | trans _ _ _ _ _ h1 h2 => exact .trans _ _ _ h1 h2,
              fun hxy => by
                induction hxy with
                | rel p q hs =>
                  obtain ⟨i, t, rfl, rfl⟩ := hs
                  show ψ (ξ _ t) = ψ (η _ t)
                  rw [h.hξ _ t t.2, h.hη _ t t.2]
                | refl _ => rfl
                | symm _ _ _ ih => exact ih.symm
                | trans _ _ _ _ _ h1 h2 => exact h1.trans h2⟩ }, ?_, rfl, ?_⟩
  · obtain ⟨k, hk⟩ := hin
    have : Nonempty K := ⟨⟨k, hk⟩⟩
    exact Nat.card_pos
  · ext z
    simp only [Net.seamV, mem_ofPred_eq]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨(e.symm i).1, (e.symm i).2, ?_⟩
      have e0 : ψ (f i 0) = a (e.symm i).1 0 := h.hξ _ 0 h0
      have e1 : ψ (f i 1) = a (e.symm i).1 1 := h.hξ _ 1 h1
      rcases hi with hi | hi
      · exact .inl (e0.symm.trans hi)
      · exact .inr (e1.symm.trans hi)
    · rintro ⟨k, hk, hz⟩
      refine ⟨e ⟨k, hk⟩, ?_⟩
      have e0 : ψ (f (e ⟨k, hk⟩) 0) = a k 0 := by
        show ψ (ξ (e.symm (e ⟨k, hk⟩)).1 0) = a k 0
        rw [e.symm_apply_apply]
        exact h.hξ k 0 h0
      have e1 : ψ (f (e ⟨k, hk⟩) 1) = a k 1 := by
        show ψ (ξ (e.symm (e ⟨k, hk⟩)).1 1) = a k 1
        rw [e.symm_apply_apply]
        exact h.hξ k 1 h1
      rcases hz with hz | hz
      · exact .inl (e0.trans hz)
      · exact .inr (e1.trans hz)

end GraphMinor.GM07
