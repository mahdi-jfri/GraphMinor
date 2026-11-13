module

public import GraphMinor.Surface.Annulus
import GraphMinor.Surface.PlaneDisc
import GraphMinor.Surface.InvarianceOfDomain

/-!
# Matching the four sides of a strip disc

For the contraction in VI Reduction 3, page 129, strip coordinates
must agree on their shared linkage path. Prescribing all four side
parametrizations gives a homeomorphism of the boundary circles.
The Jordan extension theorem carries it to the closed discs and
keeps the prescribed values on each side.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Prescribed parametrizations of the four sides of two plane discs
extend to inverse maps of the discs. This gives compatible coordinates
on the linkage strips used for Reduction 3. -/
theorem exists_closed_disc_match_of_quads
    {D E : Set ℂ} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    {u p m x u' p' m' x' : unitInterval → ℂ}
    (Q : IsQuad u p m x) (Q' : IsQuad u' p' m' x')
    (hDb : discBd D = quadSet u p m x) (hEb : discBd E = quadSet u' p' m' x') :
    ∃ h k : ℂ → ℂ, BdMatch D E h k ∧
      (∀ t, h (u t) = u' t) ∧ (∀ t, h (p t) = p' t) ∧
      (∀ t, h (m t) = m' t) ∧ (∀ t, h (x t) = x' t) := by
  have hF : Nonempty (Circle ≃ₜ quadSet u p m x) := hDb ▸ hD.isOArc_discBd
  have hF' : Nonempty (Circle ≃ₜ quadSet u' p' m' x') := hEb ▸ hE.isOArc_discBd
  obtain ⟨h, k, hm, hu, hp, hmo, hx⟩ := exists_bdMatch_of_quads Q Q'
  obtain ⟨ψ, χ, hm', heq⟩ := exists_bdMatch_closedInner hF hF' hm
  rw [← eq_closedInner_of_discBd hF hD hDb, ← eq_closedInner_of_discBd hF' hE hEb] at hm'
  refine ⟨ψ, χ, hm', ?_, ?_, ?_, ?_⟩
  · intro t
    exact (heq (Or.inl (Or.inl (Or.inl (mem_range_self t))))).trans (hu t)
  · intro t
    exact (heq (Or.inl (Or.inl (Or.inr (mem_range_self t))))).trans (hp t)
  · intro t
    exact (heq (Or.inl (Or.inr (mem_range_self t)))).trans (hmo t)
  · intro t
    exact (heq (Or.inr (mem_range_self t))).trans (hx t)

end GraphMinor.GM06
