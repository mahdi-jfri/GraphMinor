module

public import GraphMinor.Surface.CutEdges
import GraphMinor.GM08.Section18CutOrbitCount

/-!
# Vertex fibres of the word cut

A point over a graph vertex is represented by a side end of a polygon.
The cut identifies these ends exactly along the cut involution orbits.
Counting the fixed ends therefore gives twice the vertex fibre size.
This is the local vertex calculation for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

/-- For the explicit word-cut map, twice the number of points over a
cut vertex equals the number of free side ends at that vertex. This is
the vertex count in the Euler calculation of VIII (18.2), page 286. -/
theorem word_cut_vertex_fibre_count {S Y : Type u} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] [T2Space Y]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {L : Set ℕ} {g : ℕ × ℂ → Y}
    (hg : Presents (cutW W L) g) {ψ : Y → S}
    (hψ : ∀ a ∈ Dsk W, ψ (g a) = f a) (c : SE W)
    (hc : prtL W L c = c) (hv : f (spe W c) ∈ V ∩ ⋃₀ E) :
    {a : SE W | f (spe W a) = f (spe W c) ∧ prtL W L a = a}.ncard =
      2 * (ψ ⁻¹' {f (spe W c)}).ncard := by
  have : Finite (SE W) := finite_se hw.fin
  have hmem : ∀ a : SE W, spe W a ∈ Dsk (cutW W L) := by
    intro a
    rw [dsk_cut]
    exact spe_mem a
  have hcut : ∀ a b : SE W, g (spe W a) = g (spe W b) ↔ Orb W L a b := by
    intro a b
    constructor
    · intro heq
      exact orb_of_spe hw.paired ((hg.2.2 _ (hmem a) _ (hmem b)).mp heq)
    · intro hab
      exact (hg.2.2 _ (hmem a) _ (hmem b)).mpr (prel_of_orb hw.paired hab)
  have horig : ∀ a : SE W, Orb W ∅ c a ↔ f (spe W a) = f (spe W c) := by
    intro a
    constructor
    · intro ha
      exact ((hw.pres.2.2 _ (spe_mem c) _ (spe_mem a)).mpr
        (prel_of_prel_cut (prel_of_orb hw.paired ha))).symm
    · intro ha
      exact orb_empty hw.paired ((hw.pres.2.2 _ (spe_mem c) _ (spe_mem a)).mp ha.symm)
  have himage : (fun a : SE W => g (spe W a)) '' {a | Orb W ∅ c a} =
      ψ ⁻¹' {f (spe W c)} := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      change ψ (g (spe W a)) = f (spe W c)
      rw [hψ _ (spe_mem a)]
      exact (horig a).mp ha
    · intro hy
      have hy' : y ∈ g '' Dsk (cutW W L) := hg.2.1.symm ▸ mem_univ y
      obtain ⟨a, ha, rfl⟩ := hy'
      rw [dsk_cut] at ha
      have hfa : f a = f (spe W c) := (hψ a ha).symm.trans hy
      obtain ⟨d, hd⟩ := hw.corner_of ha (hfa.symm ▸ hv.2) (hfa.symm ▸ hv.1)
      refine ⟨d, (horig d).mpr ?_, congrArg g hd⟩
      rw [hd]
      exact hfa
  have hcount := fixed_ends_ncard_eq_twice_cut_images (twn_invol (W := W))
    (prtL_invol hw.paired) (prtL_invol hw.paired) (twn_ne (W := W))
    (prtL_cases hw.paired) hc (fun a : SE W => g (spe W a)) hcut
  rw [himage] at hcount
  have hfixed : {a : SE W | Orb W ∅ c a ∧ prtL W L a = a} =
      {a : SE W | f (spe W a) = f (spe W c) ∧ prtL W L a = a} := by
    ext a
    exact and_congr_left (fun _ => horig a)
  rw [hfixed] at hcount
  exact hcount

end GraphMinor.GM08
