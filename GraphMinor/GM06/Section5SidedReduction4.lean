module

public import GraphMinor.GM06.Defs

/-!
# Agreement of the corrected fourth reduction with its printed case

VI Reduction 4, page 129, retains its printed incidence condition for
at least two paths. For one path it uses incidence in a chosen lifted
region. These lemmas expose the two cases for the proofs that use them.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Surface

/-- With at least two paths, the corrected Reduction 4 is exactly its
printed region and path configuration from VI, page 129. -/
theorem section5Reduction4Step_iff_of_two_le
    {k : ℕ} {G G' : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {L' : CylinderLinkage k G'} (hk : 1 < k) :
    Section5Reduction4Step k G L G' L' ↔
      G' = G ∧ Section5Reduction4PrintedCondition k G L G' L' := by
  constructor
  · rintro ⟨hG, ⟨_, h⟩ | ⟨hk1, _⟩⟩
    · exact ⟨hG, h⟩
    · omega
  · rintro ⟨hG, h⟩
    exact ⟨hG, Or.inl ⟨hk, h⟩⟩

/-- With one path, the corrected Reduction 4 uses the actual lifted
region, prefix and contact vertex. -/
theorem section5Reduction4Step_iff_of_one
    {G G' : Drawing ClosedCylinder} {L : CylinderLinkage 1 G}
    {L' : CylinderLinkage 1 G'} :
    Section5Reduction4Step 1 G L G' L' ↔
      G' = G ∧ Section5Reduction4SideCondition 1 G L G' L' := by
  constructor
  · rintro ⟨hG, ⟨hk, _⟩ | ⟨_, h⟩⟩
    · exact (Nat.lt_irrefl 1 hk).elim
    · exact ⟨hG, h⟩
  · rintro ⟨hG, h⟩
    exact ⟨hG, Or.inr ⟨rfl, h⟩⟩

end GraphMinor.GM06
