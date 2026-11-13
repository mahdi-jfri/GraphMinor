module

public import GraphMinor.Compute.Case3StepsMemberEdgesInitProg
public import GraphMinor.Compute.Case3StepsCopyBucketLoopProg

/-!
# Writing one member's full multigraph edge records

The bucket head and count initialize the member encoding. Following those
pointers copies exactly the ordered input triples for the member. The
encoding retains the ambient compact vertex labels until the later member
renumbering, while shared vertices stay in the separate ordered vertex list.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Allocate a member encoding and copy all records of its selected owner bucket. -/
def case3MemberEdgesProg : Cmd := .seq case3MemberEdgesInitProg case3CopyBucketLoopProg

/-- A member's full multiplicity records are written in linear bucket size.
All arrays except the member encoding survive, as do the outer scan registers. -/
theorem case3MemberEdgesProg_exec {w n L : ℕ} (D : MultiDigraph n)
    (owner : Fin D.numActivePairs → ℕ) (label : ℕ) (hb : label < L)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (hL : L < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc)
    (hheads : s.arrs 35 = case3BucketHeads owner L 0)
    (hnext : s.arrs 36 = case3BucketNext owner 0)
    (hcounts : s.arrs 37 = case3BucketCounts owner L 0)
    (hrn : s.regs 14 = n) (hrb : s.regs 54 = label) :
    ∃ s' t, Exec w case3MemberEdgesProg s s' t ∧
      t ≤ 83 * (case3BucketIndices owner label 0).length + 24 ∧
      s'.arrs 39 = [n, (case3BucketIndices owner label 0).length] ++
        case3IndexedTriples D (case3BucketIndices owner label 0) ∧
      (∀ a, a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 70 ∨ 78 ≤ r → s'.regs r = s.regs r) := by
  let next := case3BucketNext owner 0
  let count := (case3BucketIndices owner label 0).length
  let head := (case3BucketIndices owner label 0).headD D.numActivePairs
  have hnextlen : next.length = D.numActivePairs := by
    simp only [next, case3BucketNext, List.length_ofFn]
  have hnextwords : ∀ z ∈ next, z < 2 ^ w := by
    intro z hz
    have hle := case3BucketNext_words owner 0 z hz
    omega
  have hcA : count ≤ D.numActivePairs := case3BucketIndices_length_le owner label 0
  have hvalid : ∀ j ∈ case3FollowBucket next head count, j < D.numActivePairs := by
    intro j hj
    rw [case3FollowBucket_eq_indices owner label] at hj
    obtain ⟨hjA, _, _⟩ := case3BucketIndices_mem owner label 0 j hj
    exact hjA
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hcnt₁, hhead₁, hq₁, h3₁, harr₁, hreg₁⟩ :=
    case3MemberEdgesInitProg_exec owner n label hb hw hn hA hL hheads hcounts hrn hrb
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ :=
    case3CopyBucketLoopProg_exec D next hnextlen hnextwords count 0 head [n, count] []
      (by simp only [List.length_cons, List.length_nil]) hvalid hw hn he hA (by omega)
      (s := s₁) ((harr₁ 3 (by decide)).trans hD) ((harr₁ 36 (by decide)).trans hnext)
      (by simpa only [List.append_nil] using hbuf₁) hcnt₁ hhead₁ hq₁ h3₁
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, ?_, ?_, ?_⟩
  · have hf : case3FollowBucket next head count = case3BucketIndices owner label 0 :=
      case3FollowBucket_eq_indices owner label
    simpa only [hf, count, List.append_nil] using hdst₂
  · intro a ha
    exact (harr₂ a ha).trans (harr₁ a ha)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
