module

public import GraphMinor.Compute.GM06SuccessorGraphRep
public import GraphMinor.GM11.Rotation
import GraphMinor.GM11.EvenCircuit
import Mathlib.Tactic

/-!
# Edge parametrizations aligned with the supplied endpoint order

The drawing input of VI (5.11), page 134, retains the consecutive
endpoint labels used by (5.7). Choose parametrizations whose zero
and one ends agree with that supplied order. Reverse an existing
parametrization when its ends occur in the other order. Loops keep
two distinct parameter ends even though their endpoint vertices
coincide. The parametrizations are geometric interpretation witnesses
in Prop, not extra fields of the finite input.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- Every supplied graph labelling has simultaneous edge
parametrizations oriented exactly as its ordered endpoint pairs. -/
theorem alg511_exists_edgePar_with_prescribed_ends
    {S : Type u} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (x : GM06SuccessorInput) {G : Drawing S} (rep : GM06SuccessorGraphRep x G.toGraph) :
    ∃ γ : Set S → I → S, EdgePar G γ ∧
      ∀ i : Fin rep.pairs.length,
        γ (rep.edge i).val 0 = (rep.vertex rep.pairs[i.val].1).val ∧
        γ (rep.edge i).val 1 = (rep.vertex rep.pairs[i.val].2).val := by
  classical
  obtain ⟨γ₀, hγ₀⟩ := exists_edgePar G
  have hσ (t : I) (ht : t ∈ Ioo (0 : I) 1) : σ t ∈ Ioo (0 : I) 1 :=
    ⟨by simpa using unitInterval.strictAnti_symm ht.2,
      by simpa using unitInterval.strictAnti_symm ht.1⟩
  have hchoice : ∀ i : Fin rep.pairs.length, ∃ f : I → S,
      Continuous f ∧ f 0 = (rep.vertex rep.pairs[i.val].1).val ∧
      f 1 = (rep.vertex rep.pairs[i.val].2).val ∧
      InjOn f (Ioo 0 1) ∧ f '' Ioo 0 1 = (rep.edge i).val := by
    intro i
    have hlink := isLink_ends hγ₀ (Drawing.IsSubdrawing.refl G) (rep.edge i).property false
    have hends := hlink.eq_and_eq_or_eq_and_eq (rep.link i)
    change (γ₀ (rep.edge i).val 0 = _ ∧ γ₀ (rep.edge i).val 1 = _) ∨
      (γ₀ (rep.edge i).val 0 = _ ∧ γ₀ (rep.edge i).val 1 = _) at hends
    rcases hends with h | h
    · exact ⟨γ₀ (rep.edge i).val, hγ₀.cont _ (rep.edge i).property,
        h.1, h.2, hγ₀.inj _ (rep.edge i).property, hγ₀.image _ (rep.edge i).property⟩
    · refine ⟨fun t => γ₀ (rep.edge i).val (σ t),
        (hγ₀.cont _ (rep.edge i).property).comp unitInterval.continuous_symm,
        by simpa using h.2, by simpa using h.1, ?_, ?_⟩
      · intro a ha b hb hab
        have heq := hγ₀.inj _ (rep.edge i).property (hσ a ha) (hσ b hb) hab
        exact unitInterval.symm_bijective.injective heq
      · rw [← image_image]
        have hs : σ '' Ioo (0 : I) 1 = Ioo 0 1 := by
          ext t
          constructor
          · rintro ⟨s, hs, rfl⟩
            exact hσ s hs
          · intro ht
            exact ⟨σ t, hσ t ht, by simp⟩
        rw [hs]
        exact hγ₀.image _ (rep.edge i).property
  choose f hfcont hfzero hfone hfinj hfimage using hchoice
  let γ : Set S → I → S := fun e => if he : e ∈ G.E then
    f (rep.edge.symm ⟨e, he⟩) else γ₀ e
  have hγ (e : Set S) (he : e ∈ G.E) : γ e = f (rep.edge.symm ⟨e, he⟩) := by
    simp only [γ, dite_eq_left he]
  have hpar : EdgePar G γ := {
    cont := by intro e he; rw [hγ e he]; exact hfcont _
    zero := by
      intro e he
      rw [hγ e he, hfzero]
      exact (rep.vertex _).property
    one := by
      intro e he
      rw [hγ e he, hfone]
      exact (rep.vertex _).property
    inj := by intro e he; rw [hγ e he]; exact hfinj _
    image := by
      intro e he
      rw [hγ e he, hfimage]
      exact congrArg Subtype.val (rep.edge.apply_symm_apply ⟨e, he⟩) }
  refine ⟨γ, hpar, ?_⟩
  intro i
  rw [hγ (rep.edge i).val (rep.edge i).property]
  change f (rep.edge.symm (rep.edge i)) 0 = _ ∧ f (rep.edge.symm (rep.edge i)) 1 = _
  rw [rep.edge.symm_apply_apply]
  exact ⟨hfzero i, hfone i⟩

end GraphMinor.GM06
