module

public import GraphMinor.Compute.Case3StepsMemberVertexListProg
public import GraphMinor.Compute.Case3StepsMemberEdgesProg
public import GraphMinor.Compute.Case3StepsBucketEncoding

/-!
# Computing one selected member's vertex and multigraph encodings

The program prepares the boundary key, vertex bitset, and increasing vertex
list, then copies the exact full multiplicity records from the computed
owner buckets. Its graph encoding agrees with the routed multigraph member,
which is the edge lift with the computed ordered loop assignment.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare a selected member's vertex data and exact multigraph encoding. -/
def case3MemberEncodingProg : Cmd := .seq case3MemberVertexListProg case3MemberEdgesProg

/-- One member is encoded with linear vertex work and linear work in its
stored positive pairs. All input and grouping arrays survive. -/
theorem case3MemberEncodingProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w)
    (he : D.numEdges < 2 ^ w) (hA : 2 + 3 * D.numActivePairs < 2 ^ w) {s : State}
    (hD : s.arrs 3 = D.enc) (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hheads : s.arrs 35 = case3BucketHeads (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hnext : s.arrs 36 = case3BucketNext (case3ActivePairOwner x D d.core.Z) 0)
    (hcounts : s.arrs 37 = case3BucketCounts (case3ActivePairOwner x D d.core.Z)
      (x.n + (case3InputEdges x).length) 0)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1) :
    ∃ s' t, Exec w case3MemberEncodingProg s s' t ∧
      t ≤ 78 * x.n + 83 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs + 129 ∧
      s'.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i.1) ∧
      s'.arrs 30 = bitSetList (case3SelectedMember x d.core.Z i).verts ∧
      s'.arrs 31 = (case3BoundaryVertices (case3SelectedMember x d.core.Z i).verts).map Fin.val ++
        List.replicate (x.n - (case3SelectedMember x d.core.Z i).verts.card) 0 ∧
      s'.regs 62 = (case3SelectedMember x d.core.Z i).verts.card ∧
      s'.arrs 39 = (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).enc ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 31 → a ≠ 39 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 78 ≤ r →
        s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey₁, hbits₁, hverts₁, hcount₁, harr₁, hreg₁⟩ :=
    case3MemberVertexListProg_exec x d hd i hw hn hkeys hm hsize hin hZ htab hreps hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, henc₂, harr₂, hreg₂⟩ :=
    case3MemberEdgesProg_exec D (case3ActivePairOwner x D d.core.Z) (case3RawIndexLabel x i.1)
      (case3RawIndexLabel_lt x i.1) (by omega) (by omega) he hA hsize (s := s₁)
      ((harr₁ 3 (by decide) (by decide) (by decide)).trans hD)
      ((harr₁ 35 (by decide) (by decide) (by decide)).trans hheads)
      ((harr₁ 36 (by decide) (by decide) (by decide)).trans hnext)
      ((harr₁ 37 (by decide) (by decide) (by decide)).trans hcounts)
      ((hreg₁ 14 (by decide)).trans hrn) ((hreg₁ 54 (by decide)).trans hrg)
  rw [case3BucketIndices_length_eq_routed] at ht₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    (harr₂ 25 (by decide)).trans hkey₁, (harr₂ 30 (by decide)).trans hbits₁,
    (harr₂ 31 (by decide)).trans hverts₁, (hreg₂ 62 (by decide)).trans hcount₁,
    henc₂.trans (case3BucketEncoding_eq x D d.core.Z (case3RawIndexLabel x i.1)), ?_, ?_⟩
  · intro a h25 h30 h31 h39
    exact (harr₂ a h39).trans (harr₁ a h25 h30 h31)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
