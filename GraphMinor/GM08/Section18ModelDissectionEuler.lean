module

public import GraphMinor.Surface.Dissection
public import GraphMinor.Surface.Defs
import GraphMinor.GM08.Section18DissectionEuler
import GraphMinor.GM08.Section18CappedDissection
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.Section5a
import GraphMinor.Surface.PasteModel
import Lean.Elab.Tactic.Omega

/-!
# Euler's formula with cuffs

Cap one cuff at a time. Each cap adds one to the dissection Euler sum
and removes one cuff from the surface model. At zero cuffs, use the
closed-surface Euler formula. This identifies the dissection sum with
`2 - 2a - b - c`, as used in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- The Euler sum of a dissection of `Σ(a,b,c)` is `2 - 2a - b - c`.
This identifies the Euler characteristic used in VIII (18.2), page 286,
with the counted source and cut dissections. -/
theorem dissection_euler_eq_model {S : Type} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) {a b c : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕) :
    ((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard =
      2 - 2 * (a : ℤ) - (b : ℤ) - (c : ℤ) := by
  have hmain : ∀ c : ℕ, ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S],
      IsSurface S → Nonempty (S ≃ₜ SurfaceModel a b c) →
      ∀ (V : Set S) (E 𝓕 : Set (Set S)), IsDissection V E 𝓕 →
        ((V ∩ ⋃₀ E).ncard : ℤ) - E.ncard + 𝓕.ncard =
          2 - 2 * (a : ℤ) - (b : ℤ) - (c : ℤ) := by
    intro c
    induction c with
    | zero =>
      intro S _ _ hS he V E 𝓕 hd
      have : T2Space S := hS.2.1
      have hcf : cuffs S = ∅ :=
        (ncard_eq_zero (cuff_statement S hS).2.1).mp (GM07.ncard_cuffs_of_homeomorph_surfaceModel he)
      have hbd : bd S = ∅ := by rw [← sUnion_cuffs, hcf, sUnion_empty]
      have hclosed : IsClosedSurface S := ⟨hS.1, inferInstance, fun x => by
        by_contra hn
        have hx : x ∈ bd S := hn
        rw [hbd] at hx
        exact hx⟩
      simpa only [Nat.cast_zero, sub_zero] using dissection_euler_eq_closed_model hclosed he hd
    | succ c ih =>
      intro S _ _ hS he V E 𝓕 hd
      have : T2Space S := hS.2.1
      have : CompactSpace S := hS.1
      have hcf : (cuffs S).Nonempty := (ncard_pos (cuff_statement S hS).2.1).mp (by
        rw [GM07.ncard_cuffs_of_homeomorph_surfaceModel he]
        exact Nat.succ_pos c)
      obtain ⟨C, hC⟩ := hcf
      obtain ⟨T, tT, j, D, hcap, _⟩ := GM07.exists_cappedCuff hS hC
      have : T2Space T := hcap.isSurface.2.1
      have : ConnectedSpace T := hcap.connectedSpace hS
      obtain ⟨e⟩ := he
      have hpaste := paste_model hS hC hcap.isSurface
        (hcap.isEmbedding.continuous.isClosedEmbedding hcap.isEmbedding.injective)
        hcap.isClosedDisc hcap.union_eq hcap.inter_eq hcap.discBd_eq e
      have heT : Nonempty (T ≃ₜ SurfaceModel a b c) := by simpa only [Nat.succ_sub_one] using hpaste.2
      obtain ⟨hdis, hEuler⟩ := isDissection_capped_cuff hS hcap hd
      have hTcount := ih T hcap.isSurface heT (j '' V) ((image j) '' E) (insert D ((image j) '' 𝓕)) hdis
      rw [hEuler] at hTcount
      push_cast at hTcount ⊢
      omega
  exact hmain c S hS he V E 𝓕 hd

end GraphMinor.GM08
