module

public import GraphMinor.Compute.Case3StepsMemberScanBody
public import GraphMinor.Compute.Case3StepsMemberResultExec
import Mathlib.Data.List.FinRange

/-!
# Running and processing one interior member

The compact member call and the result writer are composed here. The input
is saved before (7.2), and the original vertex labels are retained. Both
returned cases are processed with one uniform constant. Copying a returned
wall is paid for by the call's bound on its output length.
-/

public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

private theorem interior_time_bound (C b k a c m N v p q out : ℕ)
    (hv : v ≤ k) (hp : p ≤ C * b + 160 * a + 45 * c + 47 * k + 170)
    (hq : q ≤ 1500 * (v + m + c + 1) + 60 * out + 38 * a + 14 * v + 2 * N + 130)
    (hout : out ≤ C * b) :
    p + q ≤ (61 * C + 3000) * (b + k + a + c + m + N + 1) := by
  let K := 61 * C + 3000
  have hb : 61 * (C * b) ≤ K * b := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_right b (by dsimp only [K]; omega)
  have ha : 198 * a ≤ K * a := Nat.mul_le_mul_right a (by dsimp only [K]; omega)
  have hc : 1545 * c ≤ K * c := Nat.mul_le_mul_right c (by dsimp only [K]; omega)
  have hm : 1500 * m ≤ K * m := Nat.mul_le_mul_right m (by dsimp only [K]; omega)
  have hN : 2 * N ≤ K * N := Nat.mul_le_mul_right N (by dsimp only [K]; omega)
  have hK : 1800 ≤ K := by dsimp only [K]; omega
  calc
    _ ≤ 61 * (C * b) + 1561 * k + 198 * a + 1545 * c + 1500 * m + 2 * N + 1800 := by omega
    _ ≤ K * b + K * k + K * a + K * c + K * m + K * N + K := by
      have hk' : 1561 * k ≤ K * k := Nat.mul_le_mul_right k (by dsimp only [K]; omega)
      omega
    _ = _ := by dsimp only [K]; ring

/-- A supplied (7.2) program gives a uniform execution of an interior
member, followed by exact original-label branch storage or wall output. -/
theorem case3InteriorMemberProg_exec (ω h : ℕ) (h2 : 2 ≤ h) (heven : Even h)
    (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h)
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
        (om : List (Fin S.card)) (hom : om.Nodup) (Z : Finset (Fin S.card)),
      let x := case3SimpleSocietyInput D om hom
      ∀ i : Case3SelectedGroup x Z,
      let A := case3SelectedMember x Z i
      let R := case3RoutedMember x D Z (case3RawIndexLabel x i.1)
      let Gm := case3CompactMember x D Z i
      let B := algorithm72Size (case3MemberAlgorithm72Input x D Z i)
      ∀ w : ℕ, wordSize c B ≤ w →
        (case3GroupBoundary x Z i.1).card ≤ 3 →
        6 < 2 ^ w → S.card + 1 < 2 ^ w → N < 2 ^ w →
        2 + 3 * R.numActivePairs < 2 ^ w → R.numEdges < 2 ^ w →
        2 + 3 * Gm.numActivePairs < 2 ^ w → Gm.numEdges < 2 ^ w →
        ∀ (pre : List ℕ) (remaining count : ℕ),
        A.verts.card + 6 * Gm.numEdges + 4 ≤ remaining →
        pre.length + remaining < 2 ^ w → count + 1 < 2 ^ w →
        ∀ s : State,
        s.arrs 30 = bitSetList A.verts → s.arrs 39 = R.enc → s.regs 14 = S.card →
        s.arrs 31 = (case3BoundaryVertices A.verts).map Fin.val ++
          List.replicate (S.card - A.verts.card) 0 → s.regs 62 = A.verts.card →
        (s.arrs 2).length = N → S.card ≤ (s.arrs 32).length →
        (∀ u : Fin S.card, (s.arrs 32).getD u.1 0 = (S.orderEmbOfFin rfl u).1) →
        (∀ z ∈ s.arrs 32, z < 2 ^ w) →
        s.arrs 25 = case3BoundaryKey (case3GroupBoundary x Z i.1) →
        s.arrs 57 = pre ++ List.replicate remaining 0 →
        s.regs 1 = pre.length → s.regs 2 = count →
        ∃ s' t, Exec w (case3InteriorMemberProg h P72) s s' t ∧
          t ≤ C * (B + S.card + R.numActivePairs + Gm.numActivePairs + Gm.numEdges + N + 1) ∧
          ((∃ code : List ℕ, IsValidBranchDecompCode ω Gm code ∧
            let orig := fun u : Fin A.verts.card => S.orderEmbOfFin rfl (A.verts.orderEmbOfFin rfl u)
            let r := case3BranchRecord Gm
              (origVertexEmb orig ((S.orderEmbOfFin rfl).injective.comp (A.verts.orderEmbOfFin rfl).injective))
              (origEdgeEmb orig ((S.orderEmbOfFin rfl).injective.comp (A.verts.orderEmbOfFin rfl).injective)) code
            s'.regs 0 = 0 ∧ s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
            s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0) ∨
          (s'.regs 0 = 1 ∧
            let P := case3PushMultigraph S R
            let V := A.verts.image (S.orderEmbOfFin rfl)
            s'.arrs 54 = P.enc ∧ IsBitSet V 55 s' ∧
              IsBitSet ((case3GroupBoundary x Z i.1).image (S.orderEmbOfFin rfl)) 56 s' ∧
            (∃ WA : WallOfHeight h (P.deleteVerticesCompact Vᶜ), WA.IsValid ∧
              ∃ hnext : (WA.moveOrig P (compactEmb Vᶜ)).IsValid,
                ((WA.moveOrig P (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
                  P.toGMDigraph.toGraph.induce V.toNatSet ∧
                s'.arrs 46 = (WA.moveOrig P (compactEmb Vᶜ)).encList))) ∧
          (∀ a < 128, a ≠ 38 → a ≠ 40 → a ≠ 41 → a ≠ 42 → a ≠ 46 → a ≠ 47 →
            a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 →
            a ≠ 54 → a ≠ 55 → a ≠ 56 → a ≠ 57 → s'.arrs a = s.arrs a) ∧
          (∀ r < 70, r ≠ 0 → r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := case3PrepareMember72Prog_exec ω h P72 h72
  refine ⟨61 * C + 3000, c, by omega, hc, ?_⟩
  intro N S D om hom Z x i A R Gm B w hw hbd hw6 hcard hN hRA hRe hCA hCe
    pre remaining count hremaining hcapacity hcount s hverts henc hrn hmember hmembercount
    hrank hlistlen hlist hwords hkey hbuf hused hnum
  have hAc : A.verts.card ≤ S.card := by simpa only [Fintype.card_fin] using Finset.card_le_univ A.verts
  obtain ⟨s₁, t₁, hex₁, ht₁, hsave, horig, hout, houtlen, houtwords, harr₁, hreg₁, houtputtime⟩ :=
    hrun w x D Z i N (S.orderEmbOfFin rfl) hw (by omega) (by change S.card < 2 ^ w; omega) hRA hRe hCA hCe s
      hverts henc hrn hmember hmembercount hlistlen hlist hwords
  have horig' : s₁.arrs 47 = List.ofFn (fun u : Fin A.verts.card =>
      (S.orderEmbOfFin rfl (A.verts.orderEmbOfFin rfl u)).1) := by
    rw [List.ofFn_eq_map]
    exact horig
  obtain ⟨s₂, t₂, hex₂, ht₂, hresult, harr₂, hreg₂⟩ :=
    case3MemberResultStoreProg_exec (w := w) (ω := ω) (count := count) (remaining := remaining)
      S R A.verts (case3GroupBoundary x Z i.1) hbd h2 heven hw6 hcard hN hRA hRe hCA
      pre hremaining hcapacity hcount hout houtlen houtwords
      ((harr₁ 39 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans henc)
      hsave
      (by rw [harr₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hrank)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlistlen)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlist)
      ((harr₁ 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmember)
      ((hreg₁ 62 (by decide)).trans hmembercount)
      ((harr₁ 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hkey)
      horig'
      ((harr₁ 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbuf)
      ((hreg₁ 1 (by decide)).trans hused) ((hreg₁ 2 (by decide)).trans hnum)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hresult, ?_, ?_⟩
  · exact interior_time_bound C B S.card R.numActivePairs Gm.numActivePairs Gm.numEdges N
      A.verts.card t₁ t₂ (s₁.arrs 129).length hAc ht₁ ht₂ houtputtime
  · intro a ha h38 h40 h41 h42 h46 h47 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57
    exact (harr₂ a h46 h48 h49 h50 h51 h52 h53 h54 h55 h56 h57).trans
      (harr₁ a ha h38 h40 h41 h42 h47)
  · intro r hr h0 h1 h2ne
    exact (hreg₂ r hr h0 h1 h2ne).trans (hreg₁ r (by romega))

end GraphMinor.Compute
