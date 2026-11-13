module

public import GraphMinor.Compute.Case3StepsNoninteriorScanBody
import GraphMinor.Compute.Case3StepsMemberScanBody

/-!
# Writing the selected noninterior candidate

Construct the selected member, test its perimeter intersection, and append
the prescribed placeholder record. The body retains its candidate index
for the surrounding counting loop, along with the routing arrays needed
for every later label.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem member_time (k a c m p q r : ℕ)
    (hp : p ≤ 78 * k + 83 * a + 129) (hq : q ≤ 19 * k + 9)
    (hr : r ≤ 2000 * (k + a + c + m + 1)) :
    2 + (p + (q + (1 + r))) ≤ 2500 * (k + a + c + m + 1) := by omega

/-- A selected noninterior candidate writes its exact record and advances
the buffer counters with fixed linear vertex, pair, and full-edge cost. -/
theorem case3NoninteriorScanBody_member_exec {w N count remaining : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
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
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1)
    (e : Fin x.n ↪ Fin N) (pre : List ℕ) (P : Finset (Fin x.n))
    (hP : IsBitSet P 20 s) (hnon : ¬ Disjoint (case3SelectedMember x d.core.Z i).verts P)
    (hmask : s.arrs 29 = bitSetList (case3GroupLabelSet x d.core.Z))
    (hN : N < 2 ^ w)
    (hRA : 2 + 3 * (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w)
    (hRe : (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w)
    (hCA : 2 + 3 * (case3CompactMember x D d.core.Z i).numActivePairs < 2 ^ w)
    (hCe : (case3CompactMember x D d.core.Z i).numEdges < 2 ^ w)
    (hremaining : case3SelectedRecordCapacity x D d.core.Z i ≤ remaining)
    (hcapacity : pre.length + remaining < 2 ^ w) (hcount : count + 1 < 2 ^ w)
    (hlistlen : x.n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (e u).1)
    (hwords : ∀ z ∈ s.arrs 32, z < 2 ^ w)
    (hbuf : s.arrs 57 = pre ++ List.replicate remaining 0)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w case3NoninteriorScanBody s s' t ∧
      t ≤ 2500 * (x.n + (case3RoutedMember x D d.core.Z (case3RawIndexLabel x i.1)).numActivePairs +
        (case3CompactMember x D d.core.Z i).numActivePairs +
        (case3CompactMember x D d.core.Z i).numEdges + 1) ∧
      let r := case3SelectedRecord x D d.core.Z e i
        (case3PlaceholderCode (case3CompactMember x D d.core.Z i).numEdges)
      s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0 ∧
      s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ∉ [25, 30, 31, 38, 39, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 1 → r ≠ 2 → (r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54) →
        s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, _, hverts, hmember, hmembercount, henc, harr₁, hreg₁⟩ :=
    case3MemberEncodingProg_exec x D d hd i hw hn hkeys hm hsize he hA
      hD hin hZ htab hreps hheads hnext hcounts hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, htest, harr₂, hreg₂⟩ :=
    case3InteriorProg_exec (w := w) (s := s₁) (case3SelectedMember x d.core.Z i).verts P (by omega) (by omega)
      (IsBitSet.of_bitSetList _ _ _ hverts)
      (hP.of_arr_eq (harr₁ 20 (by decide) (by decide) (by decide) (by decide)))
      ((hreg₁ 14 (by decide)).trans hrn)
  have hzero : s₂.regs 100 = 0 := by simpa only [hnon, ↓reduceIte] using htest
  have hcond : (Expr.reg 100).eval w s₂ = some 0 := by
    simp only [Expr.eval, checkWord, hzero, Nat.two_pow_pos, ↓reduceIte]
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuffer, hused₃, hnum₃, harr₃, hreg₃⟩ :=
    case3NoninteriorMemberProg_exec (w := w) (count := count) (remaining := remaining)
      x D d.core.Z i e pre (by omega) (by omega) hN hRA hRe hCA hCe hremaining hcapacity hcount
      ((harr₂ 30).trans hverts) ((harr₂ 39).trans henc)
      ((hreg₂ 14 (by decide)).trans ((hreg₁ 14 (by decide)).trans hrn))
      ((harr₂ 31).trans hmember) ((hreg₂ 62 (by decide)).trans hmembercount)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlistlen)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlist)
      (by rw [harr₂ 32, harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hwords)
      (by rw [harr₂ 57, harr₁ 57 (by decide) (by decide) (by decide) (by decide)]; exact hbuf)
      ((hreg₂ 1 (by decide)).trans ((hreg₁ 1 (by decide)).trans hused))
      ((hreg₂ 2 (by decide)).trans ((hreg₁ 2 (by decide)).trans hnum))
  have hmasktest := case3MemberMask_eval (w := w) (s := s) (case3GroupLabelSet x d.core.Z)
    (case3GroupLabelEquiv x i.1) (by omega) hsize hmask
    (by rw [case3GroupLabelEquiv_val]; exact hrg)
  rw [ite_eq_left ((mem_case3GroupLabelSet x d.core.Z i.1).mpr i.2)] at hmasktest
  refine ⟨s₃, 2 + (t₁ + (t₂ + (1 + t₃))),
    .ite_true hmasktest (by decide) (.seq hex₁ (.seq hex₂ (.ite_false hcond hex₃))),
    member_time _ _ _ _ _ _ _ ht₁ ht₂ ht₃, hbuffer, hused₃, hnum₃, ?_, ?_⟩
  · intro a hnot
    have hne (q : ℕ) (hq : q ∈ [25, 30, 31, 38, 39, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128]) : a ≠ q :=
      fun heq => hnot (heq ▸ hq)
    have hnot₃ : a ∉ [38, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] := by
      have hsub : ([38, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] : List ℕ) ⊆
          [25, 30, 31, 38, 39, 40, 41, 42, 47, 48, 49, 50, 51, 52, 53, 57, 128] := by decide
      exact fun hm => hnot (hsub hm)
    exact (harr₃ a hnot₃).trans ((harr₂ a).trans
      (harr₁ a (hne 25 (by decide)) (hne 30 (by decide)) (hne 31 (by decide)) (hne 39 (by decide))))
  · intro r h1 h2 hr
    have hr78 : r < 78 := by rcases hr with hr | hr | hr | hr | hr <;> romega
    rw [hreg₃ r hr78 h1 h2, hreg₂ r (by romega)]
    apply hreg₁ r
    rcases hr with hr | hr | hr | hr | hr
    · exact Or.inl hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inl hr))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hr))))

end GraphMinor.Compute
