module

public import GraphMinor.Compute.GM06CalibrateSector
public import GraphMinor.Compute.GM06DeleteSectorEdge

/-!
# Deleting an active edge after sector calibration

The reduction scan for VI (5.7), page 133, calibrates the signed
cuff and path markers, searches both ends of each active edge,
and clears a qualifying edge bit. It either excludes all such
edges or lowers the active-edge count by one. All other arrays
are preserved, and the execution has an explicit polynomial bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Calibrate the row markers and clear one active edge in the selected sector. -/
def gm06DeleteCalibratedEdgeProg (rot active : Arr) : Cmd :=
  .seq (gm06CalibrateSectorProg rot) (gm06DeleteSectorEdgeProg rot active)

/-- A calibrated deletion excludes every eligible active edge or
clears exactly one such edge, with strict active-count progress. -/
theorem gm06DeleteCalibratedEdgeProg_exec {w : ℕ} (rot active : ℕ) (xs mask : List ℕ)
    (p q c : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hc : c ∈ xs) (hm : 2 * mask.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h39 : s.regs 39 = c) :
    ∃ s' t, Exec w (gm06DeleteCalibratedEdgeProg rot active) s s' t ∧
      t ≤ 61 + 39 * xs.length + mask.length * (120 + 104 * xs.length) ∧
      Keeps [36, 37, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60] [active] s s' ∧
      ((s'.regs 60 = 0 ∧ s'.arrs active = mask ∧ ∀ e (he : e < mask.length),
        ¬(mask[e] = 1 ∧ (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
          gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1))) ∨
        (s'.regs 60 = 1 ∧ ∃ (e : ℕ) (he : e < mask.length),
          s'.regs 55 = e ∧ s'.arrs active = mask.set e 0 ∧ mask[e] = 1 ∧
          (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
            gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1) ∧
          (s'.arrs active).count 1 + 1 = mask.count 1)) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hp₁, hq₁⟩ := gm06CalibrateSectorProg_exec rot xs p q c s
    hw hn hx hnd hp hq hc ha h36 h37 h39
  have hmem : (gm06SectorMarkers xs p q c).1 ∈ xs ∧ (gm06SectorMarkers xs p q c).2 ∈ xs := by
    rcases gm06SectorMarkers_cases xs p q c with hh | hh
    · rw [hh]
      exact ⟨hp, hq⟩
    · rw [hh]
      exact ⟨hq, hp⟩
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hgood⟩ := gm06DeleteSectorEdgeProg_exec rot active xs mask
    (gm06SectorMarkers xs p q c).1 (gm06SectorMarkers xs p q c).2 s₁ hw hn hx hnd
    hmem.1 hmem.2 hm hbits ((hk₁.2 rot (by simp)).trans ha)
    ((hk₁.2 active (by simp)).trans hb) hp₁ hq₁
  let R := [36, 37, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
  have hk₁' : Keeps R [active] s s₁ := hk₁.mono
    (by simp [R]) (by simp)
  have hframe : Keeps R [active] s s₂ := hk₁'.trans hk₂
    (by simp [R]) (by simp)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hframe, ?_⟩
  simpa only [gm06CalibratedSectorFlag] using hgood

end GraphMinor.Compute
