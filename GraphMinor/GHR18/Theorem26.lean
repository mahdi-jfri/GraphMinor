module

public import GraphMinor.GHR18.BandSum
public import GraphMinor.GHR18.ArcType

/-!
# Geelen–Huynh–Richter (2018), Theorem 2.6

Given a connected compact surface `S`, a non-separating proper `I`-arc `P` with distinct boundary
endpoints `s ≠ t`, and a finite family `Q : Fin m → Set S` of pairwise disjoint proper `I`-arcs
avoiding `{s, t}`, there exists a boundary-fixing homeomorphism `β : S ≃ₜ S` such that `β '' P`
meets every `Q i` in at most `2` points.

## Proof outline
1. `exists_transverse_arc` (`Transverse.lean`): move `P` by a boundary-fixing homeomorphism `α` and
   perform local disc straightening to obtain a transverse proper `I`-arc `P_tr` in the same
   boundary-relative `ZMod 2` cohomology class and with the same `w₁` integral as `α '' P`.
2. `parity_surgery` (`ParitySurgery.lean`): eliminate pairs of consecutive crossings on each
   `Q i` by rectangle band surgery, obtaining a transverse proper 1-manifold `M₁` with at most `1`
   crossing on each `Q i`, preserving `w₁` and boundary-relative cohomology.
3. `eliminate_oArcs_of_transverse` (`BandSum.lean`): iteratively merge `O`-arc components of `M₁`
   along shortest chains across the complement, obtaining a single proper `I`-arc `P'` meeting
   every `Q i` in at most `2` points, still in the same boundary-relative cohomology class and with
   the same `w₁` integral as `α '' P`.
4. `parallel_of_cocycle_eq` (`ArcType.lean`): since `α '' P` is non-separating, equal
   boundary-relative cohomology and equal `w₁` parity imply a boundary-fixing homeomorphism `β₀`
   carrying `α '' P` to `P'`. Composing `α.trans β₀` completes the proof.
-/

@[expose] public section

namespace GraphMinor.GHR18

open Set Topology Function GraphMinor.Surface

variable {S : Type} [TopologicalSpace S]

/-- **Geelen–Huynh–Richter (2018), Theorem 2.6**:
For a non-separating proper `I`-arc `P` with distinct boundary endpoints `s ≠ t` on a connected
compact surface `S` and pairwise disjoint proper `I`-arcs `Q : Fin m → Set S` avoiding `{s, t}`,
there exists a boundary-fixing homeomorphism `β : S ≃ₜ S` such that `β '' P` meets each `Q i` in
at most `2` points. -/
theorem ghr18_theorem_2_6 [ConnectedSpace S] (hS : IsSurface S)
    {P : Set S} {s t : S} (hst : s ≠ t) (hPb : P ∩ bd S = {s, t}) (hPl : IsLineWithEnds P s t)
    (hnonsep : IsPreconnected (Pᶜ : Set S))
    {m : ℕ} (Q : Fin m → Set S)
    (hQ : ∀ i, ∃ u v, u ≠ v ∧ IsLineWithEnds (Q i) u v ∧ Q i ∩ bd S = {u, v})
    (hQdisj : Pairwise fun i j => Disjoint (Q i) (Q j))
    (hsQ : ∀ i, s ∉ Q i) (htQ : ∀ i, t ∉ Q i) :
    ∃ β : S ≃ₜ S,
      (∀ x ∈ bd S, β x = x) ∧
      (∀ i : Fin m, (β '' P ∩ Q i).Finite ∧ (β '' P ∩ Q i).ncard ≤ 2 ∧ IsSimpleCrossing (β '' P) (Q i)) := by
  classical
  obtain ⟨AS⟩ := exists_surfAtlas hS
  have ⟨φ, hφ0, hφ1⟩ := hPl
  let γ : ℝ → S := fun r => if hr : r ∈ Icc (0 : ℝ) 1 then (φ ⟨r, hr⟩).1 else s
  have hγc : ContinuousOn γ (Icc 0 1) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp φ.continuous).congr fun r => by
      simp only [Set.domRestrict, Function.comp, γ, dite_eq_left r.2]
  have hγi : InjOn γ (Icc 0 1) := fun r₁ hr₁ r₂ hr₂ he => by
    simp only [γ, dite_eq_left hr₁, dite_eq_left hr₂] at he
    exact congrArg Subtype.val (φ.injective (Subtype.ext he))
  have hγ0 : γ 0 = s := by
    have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    dsimp only [γ]; rw [dite_eq_left h0]; exact hφ0
  have hγ1 : γ 1 = t := by
    have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    dsimp only [γ]; rw [dite_eq_left h1]; exact hφ1
  have hγim : γ '' Icc 0 1 = P := by
    ext y; constructor
    · rintro ⟨r, hr, rfl⟩; simp only [γ, dite_eq_left hr]; exact (φ ⟨r, hr⟩).2
    · intro hy; let r := φ.symm ⟨y, hy⟩
      refine ⟨r.1, r.2, ?_⟩
      simp only [γ, dite_eq_left r.2]
      exact congrArg Subtype.val (φ.apply_symm_apply ⟨y, hy⟩)
  -- Step 0: Transversality
  obtain ⟨sb, α, P_tr, γ_tr, hPb', hPl', hP₁b, hP₁l, hαfix,
    hγtrc, hγtri, hγtr0, hγtr1, hγtrim, hcoh_tr, hw1_tr, htips_tr, hX_ex⟩ :=
    exists_transverse_arc hS AS hst hPb hPl hγc hγi hγ0 hγ1 hγim Q hQ hQdisj hsQ htQ
  choose X hX_in hX_eq using hX_ex
  let M₀ : ProperManifold S s t :=
    { P₀ := P_tr, γ₀ := γ_tr, hP₀b := hPb', hP₀l := hPl',
      hγ₀c := hγtrc, hγ₀i := hγtri, hγ₀0 := hγtr0, hγ₀1 := hγtr1, hγ₀im := hγtrim,
      Os := [], hOs_disj := List.Pairwise.nil, hP₀_disj := fun _ h => (List.not_mem_nil h).elim }
  have hM₀U : M₀.U = P_tr := by simp [M₀, ProperManifold.U, ProperManifold.listUnion]
  have hM₀tr : M₀.IsTransverse sb X := ⟨fun i => hM₀U ▸ htips_tr i, hX_in, fun i => hM₀U ▸ hX_eq i⟩
  have hM₀w1 : M₀.w1Total AS = cocInt (w1 AS) γ_tr := by simp [M₀, ProperManifold.w1Total]
  -- Step 1: Parity reduction (`|X₁ i| ≤ 1` for every `i`)
  obtain ⟨sb₁, M₁, X₁, htr₁, hcard₁, hw1₁, hcoh₁⟩ := parity_surgery hS AS hst sb M₀ X hM₀tr
  -- Step 2: Eliminate all `O`-arcs (`|P' ∩ Q i| ≤ 2` for every `i`)
  choose uQ vQ _ hQl hQb using hQ
  obtain ⟨P', γ', hP'b, hP'l, hγ'c, _, hγ'0, hγ'1, hγ'im, hw1', hcoh', hcard'⟩ :=
    eliminate_oArcs_of_transverse hS AS hst hQb hQl hQdisj (fun j => ⟨hsQ j, htQ j⟩) M₁ htr₁ hcard₁
  -- Step 3: Match cohomology and `w₁`, then apply `parallel_of_cocycle_eq`
  obtain ⟨⟨ω₁, hω₁⟩, -⟩ := M₁.exists_crossingCocycle hS hst
  have hω₀ : IsCrossingCocycle M₀.U (arcCocycle hS hst hPb' hPl') :=
    hM₀U.symm ▸ (arcCocycle_isCrossingCocycle hS hst hPb' hPl').1
  have hrel : BdCohRel s t (arcCocycle hS hst hP'b hP'l) (arcCocycle hS hst hP₁b hP₁l) :=
    bdCohRel_trans (hcoh' ω₁ hω₁) (bdCohRel_trans (hcoh₁ _ ω₁ hω₀ hω₁) hcoh_tr)
  have hw1_eq : cocInt (w1 AS) γ' = cocInt (w1 AS) (α ∘ γ) :=
    hw1'.trans (hw1₁.trans (hM₀w1.trans hw1_tr))
  have hnonsep₁ : IsPreconnected ((α '' P)ᶜ : Set S) := by
    rw [← Set.image_compl_eq α.bijective]
    exact hnonsep.image α α.continuous.continuousOn
  have hsbd : s ∈ bd S := (hPb.symm ▸ Or.inl rfl : s ∈ P ∩ bd S).2
  have htbd : t ∈ bd S := (hPb.symm ▸ Or.inr rfl : t ∈ P ∩ bd S).2
  obtain ⟨β₀, hβ₀im, hβ₀fix⟩ := parallel_of_cocycle_eq hS hst hP₁b hP'b hP₁l hP'l hnonsep₁ AS hrel
    (α.continuous.comp_continuousOn hγc) hγ'c
    (by rw [Set.image_comp, hγim]) (hγ'im ▸ subset_rfl)
    (by simp [hγ0, hαfix s hsbd]) (by simp [hγ1, hαfix t htbd]) hγ'0 hγ'1 hw1_eq
  refine ⟨α.trans β₀, fun x hx => by simp [hαfix x hx, hβ₀fix x hx], fun i => ?_⟩
  have him : (α.trans β₀) '' P = P' := by
    change (β₀ ∘ α) '' P = P'
    rw [Set.image_comp, hβ₀im]
  rw [him]
  exact hcard' i

end GraphMinor.GHR18
