module

public import GraphMinor.Compute.Case3StepsPrepareMemberRecord
public import GraphMinor.Compute.Case3StepsStorePlaceholderRecord
public import GraphMinor.Compute.Case3StepsScanRecords
import Mathlib.Data.List.FinRange

/-!
# Preparing and storing one noninterior member

The compact graph and composed inverse labels determine the prescribed
placeholder record. Prepare those data, serialize the record, and append
it to the same buffer as the interior records. Only its actual length is
consumed, and the remaining routing inputs stay available.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare a compact member and append its one-vertex placeholder record. -/
def case3NoninteriorMemberProg : Cmd :=
  .seq case3PrepareMemberRecordProg case3StorePlaceholderRecordProg

/-- Complete noninterior-member record processing has fixed linear cost
and preserves every scan register except the two updated buffer counters. -/
theorem case3NoninteriorMemberProg_exec {w N count remaining : ℕ}
    (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
    (i : Case3SelectedGroup x Z) (e : Fin x.n ↪ Fin N) (pre : List ℕ)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hN : N < 2 ^ w)
    (hRA : 2 + 3 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w)
    (hRe : (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w)
    (hCA : 2 + 3 * (case3CompactMember x D Z i).numActivePairs < 2 ^ w)
    (hCe : (case3CompactMember x D Z i).numEdges < 2 ^ w)
    (hremaining : case3SelectedRecordCapacity x D Z i ≤ remaining)
    (hcapacity : pre.length + remaining < 2 ^ w) (hcount : count + 1 < 2 ^ w)
    {s : State}
    (hverts : s.arrs 30 = bitSetList (case3SelectedMember x Z i).verts)
    (henc : s.arrs 39 = (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).enc)
    (hrn : s.regs 14 = x.n)
    (hmember : s.arrs 31 = (case3BoundaryVertices (case3SelectedMember x Z i).verts).map Fin.val ++
      List.replicate (x.n - (case3SelectedMember x Z i).verts.card) 0)
    (hmembercount : s.regs 62 = (case3SelectedMember x Z i).verts.card)
    (hlistlen : x.n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (e u).1)
    (hwords : ∀ z ∈ s.arrs 32, z < 2 ^ w)
    (hbuf : s.arrs 57 = pre ++ List.replicate remaining 0)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w case3NoninteriorMemberProg s s' t ∧
      t ≤ 2000 * (x.n + (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs +
        (case3CompactMember x D Z i).numActivePairs + (case3CompactMember x D Z i).numEdges + 1) ∧
      let r := case3SelectedRecord x D Z e i (case3PlaceholderCode (case3CompactMember x D Z i).numEdges)
      s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0 ∧
      s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ∉ [38, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] → s'.arrs a = s.arrs a) ∧
      (∀ q < 78, q ≠ 1 → q ≠ 2 → s'.regs q = s.regs q) := by
  let A := case3SelectedMember x Z i
  let Gm := case3CompactMember x D Z i
  let orig := fun u : Fin A.verts.card => e (A.verts.orderEmbOfFin rfl u)
  have hinj : Function.Injective orig := e.injective.comp (A.verts.orderEmbOfFin rfl).injective
  have hAc : A.verts.card ≤ x.n := by simpa only [Fintype.card_fin] using Finset.card_le_univ A.verts
  obtain ⟨s₁, t₁, hex₁, ht₁, hsave, horig, harr₁, hreg₁⟩ :=
    case3PrepareMemberRecordProg_exec x D Z i e hw hn hRA hRe hCA hCe hverts henc hrn hmember
      hmembercount hlistlen hlist hwords
  have horig' : s₁.arrs 47 = List.ofFn (fun u : Fin A.verts.card => (orig u).1) := by
    rw [List.ofFn_eq_map]
    exact horig
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuffer, hused₂, hnum₂, harr₂, hreg₂⟩ :=
    case3StorePlaceholderRecordProg_exec (w := w) (count := count) (remaining := remaining)
      Gm orig hinj pre hw (lt_of_le_of_lt hAc hn) hN hCA hremaining hcapacity hcount hsave horig'
      ((harr₁ 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbuf)
      ((hreg₁ 1 (by decide)).trans hused) ((hreg₁ 2 (by decide)).trans hnum)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hbuffer, hused₂, hnum₂, ?_, ?_⟩
  · change t₂ ≤ 1500 * (A.verts.card + Gm.numEdges + Gm.numActivePairs + 1) at ht₂
    change t₁ ≤ 160 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs +
      45 * Gm.numActivePairs + 47 * x.n + 170 at ht₁
    change _ ≤ 2000 * (x.n + _ + Gm.numActivePairs + Gm.numEdges + 1)
    omega
  · intro a hnot
    have hne (q : ℕ) (hq : q ∈ [38, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128]) : a ≠ q :=
      fun heq => hnot (heq ▸ hq)
    exact (harr₂ a (hne 48 (by decide)) (hne 49 (by decide)) (hne 50 (by decide))
      (hne 51 (by decide)) (hne 52 (by decide)) (hne 53 (by decide)) (hne 57 (by decide))).trans
      (harr₁ a (hne 38 (by decide)) (hne 40 (by decide)) (hne 41 (by decide)) (hne 42 (by decide))
        (hne 47 (by decide)) (hne 128 (by decide)))
  · intro q hq h1 h2
    exact (hreg₂ q (by romega) h1 h2).trans (hreg₁ q hq)

end GraphMinor.Compute
