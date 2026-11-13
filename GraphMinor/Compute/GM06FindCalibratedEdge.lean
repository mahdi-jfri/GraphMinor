module

public import GraphMinor.Compute.GM06CalibrateSector
public import GraphMinor.Compute.GM06FindSectorEdge

/-!
# Finding an active edge after sector calibration

The finite selector for VI (5.7), page 133, first calibrates the
boundary markers against the outside cuff marker, then scans the
active edges and their two directed ends. The program returns a
qualifying original edge or excludes every active edge. Arrays
are preserved and its running time is polynomial in the row and
edge counts.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Calibrate the row markers and find an active edge in the resulting sector. -/
def gm06FindCalibratedEdgeProg (rot active : Arr) : Cmd :=
  .seq (gm06CalibrateSectorProg rot) (gm06FindSectorEdgeProg rot active)

/-- The calibrated edge scan finds a qualifying active edge or
excludes all of them, with both ends of every loop tested. -/
theorem gm06FindCalibratedEdgeProg_exec {w : ℕ} (rot active : ℕ) (xs mask : List ℕ)
    (p q c : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hc : c ∈ xs) (hm : 2 * mask.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h39 : s.regs 39 = c) :
    ∃ s' t, Exec w (gm06FindCalibratedEdgeProg rot active) s s' t ∧
      t ≤ 51 + 39 * xs.length + mask.length * (120 + 104 * xs.length) ∧
      Keeps [36, 37, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54] [] s s' ∧
      ((s'.regs 55 = mask.length ∧ ∀ e (he : e < mask.length),
        ¬(mask[e] = 1 ∧ (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
          gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1))) ∨
        ∃ (e : ℕ) (he : e < mask.length), s'.regs 55 = e ∧ mask[e] = 1 ∧
          (gm06CalibratedSectorFlag xs p q c (2 * e) = 1 ∨
            gm06CalibratedSectorFlag xs p q c (2 * e + 1) = 1)) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hp₁, hq₁⟩ := gm06CalibrateSectorProg_exec rot xs p q c s
    hw hn hx hnd hp hq hc ha h36 h37 h39
  have hmem : (gm06SectorMarkers xs p q c).1 ∈ xs ∧ (gm06SectorMarkers xs p q c).2 ∈ xs := by
    rcases gm06SectorMarkers_cases xs p q c with hh | hh
    · rw [hh]
      exact ⟨hp, hq⟩
    · rw [hh]
      exact ⟨hq, hp⟩
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hgood⟩ := gm06FindSectorEdgeProg_exec rot active xs mask
    (gm06SectorMarkers xs p q c).1 (gm06SectorMarkers xs p q c).2 s₁ hw hn hx hnd
    hmem.1 hmem.2 hm hbits ((hk₁.2 rot (by simp)).trans ha)
    ((hk₁.2 active (by simp)).trans hb) hp₁ hq₁
  let R := [36, 37, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54]
  have hk₁' : Keeps R [] s s₁ := hk₁.mono
    (by simp [R]) (by simp)
  have hframe : Keeps R [] s s₂ := hk₁'.trans hk₂
    (by simp [R]) (by simp)
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, hframe, ?_⟩
  simpa only [gm06CalibratedSectorFlag] using hgood

end GraphMinor.Compute
