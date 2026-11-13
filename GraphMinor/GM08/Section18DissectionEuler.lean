module

public import GraphMinor.Surface.Dissection
public import GraphMinor.Surface.Defs
import GraphMinor.Surface.TriGraph
import GraphMinor.Surface.CapCoh
import Lean.Elab.Tactic.Omega

/-!
# Euler's formula for a surface dissection

Triangulate a dissection while preserving its Euler sum. The proved
Euler formula for triangulations and the cohomology count of the surface
model identify that sum with the model's Euler characteristic. This is
the Euler bridge used in the proof of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- Euler's formula for a dissection of a closed connected surface,
as used in VIII (18.2), page 286. Isolated vertices are trimmed before
counting, as in the dissection-to-triangulation construction. -/
theorem dissection_euler_eq_closed_model {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) {a b : ℕ}
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕) :
    ((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard = 2 - 2 * (a : ℤ) - (b : ℤ) := by
  have : T2Space S := hS.2.1
  obtain ⟨V', E', 𝓕', ht, _, _, hcount⟩ := hd.exists_triang
  obtain ⟨κ, hκ, hEuler⟩ := ht.euler_ncard hS
  obtain ⟨e⟩ := he
  have hmodel := card_kCl_of_model e
  have hκeq : κ = 2 * a + b :=
    Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)) (hκ.symm.trans hmodel)
  rw [hκeq, hcount] at hEuler
  push_cast at hEuler
  omega

end GraphMinor.GM08
