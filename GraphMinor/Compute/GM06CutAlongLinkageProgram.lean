module

public import GraphMinor.Compute.GM06CutOutput
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Complete finite RAM cut along the linkage

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) cuts the
marked rotations along the linkage, connects assigned edge ends, searches
components through their inner cuff edges and returns their induced
graphs. This program composes all those finite passes from the original
lists. The output parser recovers the exact pure component list from
physically written masks and induced rotations. All table, source and
buffer bounds are derived from the input sizes, giving a cubic time bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem uniform_payload_length (n : ℕ) (masks : List (List ℕ))
    (h : ∀ mask ∈ masks, mask.length = n) :
    (gm06EncodeRowsPayload masks).length = masks.length * (n + 1) := by
  induction masks with
  | nil => simp [gm06EncodeRowsPayload]
  | cons mask masks ih =>
    have hh := h mask List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
      gm06EncodeNatList, List.length_cons, hh, Nat.add_mul, Nat.one_mul]
    change (masks.flatMap gm06EncodeNatList).length = _ at ht
    omega

/-- The search graph pass retains the exact allocated common rotation buffer. -/
theorem gm06CutSearchGraphProg_output_bounds {w : ℕ} (rows : List (List ℕ)) (s sf : State) (t : ℕ)
    (hw : 2 < 2 ^ w) (h600 : s.arrs 600 = gm06EncodeRows rows)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (he : Exec w gm06CutSearchGraphProg s sf t) :
    (sf.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length ∧ ∀ x ∈ sf.arrs 625, x < 2 ^ w := by
  cases he with
  | seq hd hs =>
    obtain ⟨hl, hwds⟩ := gm06CutDataProg_output_bounds rows s _ _ hw h600 hfit hd
    exact ⟨(gm06Exec_length_eq hs 625 (by decide)).trans hl, hs.arrs_lt 625 hwds⟩

/-- Full finite cut program, including physical induced component rotations. -/
def gm06CutAlongLinkageProg : Cmd :=
  .seq gm06CutCuffMembershipProg
    (.seq (.assign 647 (gm06CutSizeExpr 4))
      (.seq (gm06IncidenceBitsProg 628 627 647) gm06CutMaterializeProg))

/-- Registers used by the complete cut program. -/
def gm06CutAlongLinkageRegs : List ℕ := gm06CutCuffMembershipRegs ++ [647, 610, 611, 612] ++ gm06CutMaterializeRegs

/-- Arrays used by the complete cut program. -/
def gm06CutAlongLinkageArrs : List ℕ := gm06CutCuffMembershipArrs ++ [601, 611, 615, 616, 627, 630]

/-- Explicit polynomial cost in permanent input sizes and row lengths. -/
def gm06CutAlongLinkageCost (n m c k p l r d z : ℕ) : ℕ :=
  240 + 172 * n + 23 * k + 56 * p + 31 * c + 138 * l + 2 * r +
    n * (6000 + 26 * (m + c)) + 6334 * d + 328 * (m + c) + 84 * (n * n) +
    z * (132 + 2 * r + 4480 * n + 4400 * d + 116 * (n * n))

/-- The finite cut returns exactly the pure list of cuff-indexed
components from the original graph and linkage lists. No cut graph,
component mask, adjacency table or side assignment is an input. -/
theorem gm06CutAlongLinkageProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 4 * (m + inner.length + outer.length) + 3 < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hrows : rows.length = n) (hnd : rows.flatten.Nodup)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length))
    (hlive : ∀ v ∈ live, v < n) (hliveFit : 2 * live.length + 2 < 2 ^ w)
    (hpathCode : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hsearchFit : (2 * n) * (2 * n) + 2 < 2 ^ w)
    (hcomponentFit : 3 + inner.length * (2 * n + 1) < 2 ^ w)
    (hmaterialFit : 3 + inner.length * (1 + 2 * (gm06EncodeRows rows).length) < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h601 : s.arrs 601 = origins)
    (h608 : s.arrs 608 = gm06EncodeRows paths) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h618 : s.arrs 618 = live) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    ∃ sf t, Exec w gm06CutAlongLinkageProg s sf t ∧
      t ≤ gm06CutAlongLinkageCost n m (inner.length + outer.length) paths.length paths.flatten.length
        live.length (gm06EncodeRows rows).length rows.flatten.length inner.length ∧
      Keeps gm06CutAlongLinkageRegs gm06CutAlongLinkageArrs s sf ∧
      gm06CutAlongLinkageResult sf = some (gm06CutAlongLinkage n m origins paths inner outer rows live) := by
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  let masks := gm06CutCuffMembership n m origins paths inner outer rows live
  let aug := m + inner.length + outer.length
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hL := gm06FaceCode_length rows
  have h2n : 2 * n + 1 < 2 ^ w := by omega
  have h4aug : 4 * aug < 2 ^ w := by dsimp only [aug]; omega
  have hsizes := gm06CutDataOfLinkage_sizes n m origins paths inner outer rows live
  have hbounds := gm06CutDataOfLinkage_dart_bounds (n := n) origins paths inner outer rows live hkeys
  have hvalues := gm06CutDataOfLinkage_origin_bounds origins paths inner outer rows live hrows horig hv hci hco
  have hroots : ∀ i, i < inner.length → gm06CutInnerRoot data m i < 2 * n := by
    intro i hi
    have hidx := gm06CutDataOfLinkage_inner_dart_bound (n := n) (m := m) origins paths inner outer rows live hi
    simpa only [gm06CutInnerRoot, data, List.getElem?_eq_getElem hidx, Option.getD_some] using
      hvalues _ (List.getElem_mem hidx)
  have hmasksLen : masks.length = inner.length := gm06CutComponentBitsFrom_length _ _ _ _ _
  have hmaskLen : ∀ mask ∈ masks, mask.length = 2 * n :=
    gm06CutComponentBitsFrom_row_lengths (2 * n) data m 0 inner.length (fun i _ hi => hroots i (by omega))
  have hmaskBits : ∀ mask ∈ masks, ∀ x ∈ mask, x = 0 ∨ x = 1 := gm06CutComponentBitsFrom_words _ _ _ _ _
  have hactiveLen : data.activeDarts.length ≤ 4 * aug := hbounds.2.2
  have hcutDarts : data.rotations.flatten.length ≤ 2 * rows.flatten.length := gm06SplitRotationRows_length_le _ _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₁, ho₁, ha₁, hv₁, hN₁, hadj₁, hent₁⟩ := gm06CutSearchGraphProg_exec
    origins paths inner outer rows live s hw hn hsize horig hv hd hci hco hrows hnd hkeys hlive hliveFit
    hpathCode hpathWords hrotFit hrotWords hsearchFit h600 h601 h608 h609 h610 h618 h648 h649
  have hphysical₁ := gm06CutSearchGraphProg_output_bounds rows s s₁ t₁ hw2 h600 hrotFit he₁
  have horgLen : data.origins.length = 4 * aug := hsizes.2.1
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout₂⟩ := gm06CutComponentRowsProg_exec data inner s₁ hw h2n hcomponentFit
    (by rw [horgLen]; exact h4aug)
    (fun i hi => gm06CutDataOfLinkage_inner_dart_bound origins paths inner outer rows live hi) hvalues
    ((hk₁.2 609 (by decide)).trans h609) hN₁ ((hk₁.1 649 (by decide)).trans h649) ho₁ hadj₁
    (by rw [hent₁]; omega)
  have hphysical₂ := gm06CutComponentRowsProg_output_bounds inner s₁ s₂ t₂ hw1 h2n hcomponentFit
    ((hk₁.2 609 (by decide)).trans h609) hN₁ he₂
  have h600code : s₂.arrs 600 = gm06EncodeRows masks := by
    have hsub : (gm06EncodeRows masks).Sublist (s₂.arrs 600) := by
      change (s₂.arrs 600).take (s₂.regs 655) = gm06EncodeRows masks at hout₂
      rw [← hout₂]
      exact List.take_sublist _ _
    apply (hsub.eq_of_length ?_).symm
    rw [hphysical₂.1]
    simp only [gm06EncodeRows, List.length_cons, uniform_payload_length (2 * n) masks hmaskLen, hmasksLen]
    omega
  have hphysical : (s₂.arrs 625).length = 1 + 2 * (gm06EncodeRows rows).length ∧
      ∀ x ∈ s₂.arrs 625, x < 2 ^ w := by rw [hk₂.2 625 (by decide)]; exact hphysical₁
  have hcommon : (s₂.arrs 625).take (s₂.regs 658) = gm06EncodeRows data.rotations := by
    rw [hk₂.2 625 (by decide), hk₂.1 658 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])]
    exact hr₁
  let padding := (s₂.arrs 625).drop (s₂.regs 658)
  have hsource625 : s₂.arrs 625 = gm06EncodeRows data.rotations ++ padding := by
    rw [← hcommon]
    exact (List.take_append_drop _ _).symm
  let s₃ := s₂.setReg 647 (4 * aug)
  have he₃ : Exec w (.assign 647 (gm06CutSizeExpr 4)) s₂ s₃ 8 :=
    .assign (gm06CutSizeExpr_eval inner outer s₂ hw (by dsimp only [aug] at h4aug; omega) h4aug
      ((hk₂.1 649 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])).trans ((hk₁.1 649 (by decide)).trans h649))
      ((hk₂.2 609 (by decide)).trans ((hk₁.2 609 (by decide)).trans h609))
      ((hk₂.2 610 (by decide)).trans ((hk₁.2 610 (by decide)).trans h610)))
  let darts : List (Fin (4 * aug)) := data.activeDarts.attach.map
    (fun d => ⟨d.val, hbounds.2.1 d.val d.property⟩)
  have hdarts : darts.map Fin.val = data.activeDarts := by simp [darts, List.map_map]
  have hdartsLen : darts.length = data.activeDarts.length := by simp only [darts, List.length_map, List.length_attach]
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hb₄⟩ := gm06IncidenceBitsProg_exec
    628 627 647 (by decide) darts s₃ hw1 h4aug (by rw [hdartsLen]; omega) (by simp [s₃])
    (by simpa only [hdarts, s₃, State.setReg_arrs] using (hk₂.2 628 (by decide)).trans ha₁)
  have hk₂₄ : Keeps [647, 610, 611, 612] [627] s₂ s₄ :=
    ((Keeps.refl _ _ s₂).setReg (by simp) _).trans hk₄ (by simp) (fun _ h => h)
  obtain ⟨sf, tf, hef, htf, hkf, houtf⟩ := gm06CutMaterializeProg_exec
    (n := 2 * n) (m := 2 * aug) data masks inner [] padding s₄ hw2 (by omega) (by omega)
    (by simpa only [hrows] using hsizes.1)
    (by rw [horgLen]; omega) hvalues (fun d hd => by have h := hbounds.1 d hd; dsimp only [aug]; omega)
    hmasksLen hmaskLen hmaskBits
    (by simpa only [List.append_nil] using (hk₂₄.2 600 (by decide)).trans h600code)
    (by rw [hk₂₄.2 600 (by decide), hphysical₂.1]; omega)
    (by rw [hk₂₄.2 600 (by decide)]; exact hphysical₂.2)
    ((hk₂₄.2 625 (by decide)).trans hsource625)
    (by rw [hk₂₄.2 625 (by decide), hphysical.1]; omega)
    (by rw [hk₂₄.2 625 (by decide)]; exact hphysical.2)
    ((hk₂₄.2 626 (by decide)).trans ((hk₂.2 626 (by decide)).trans ho₁))
    (by rw [show 2 * (2 * aug) = 4 * aug by omega]; simpa only [hdarts] using hb₄)
    ((hk₂₄.2 609 (by decide)).trans ((hk₂.2 609 (by decide)).trans ((hk₁.2 609 (by decide)).trans h609)))
    ((hk₂₄.1 620 (by decide)).trans ((hk₂.1 620 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])).trans hN₁))
    (by rw [hk₂₄.2 625 (by decide), hphysical.1]; exact hmaterialFit)
  have hk₀₂ : Keeps gm06CutAlongLinkageRegs gm06CutAlongLinkageArrs s s₂ :=
    (hk₁.mono
      (by intro r hr; simp [gm06CutAlongLinkageRegs, gm06CutCuffMembershipRegs, hr])
      (by intro a ha; exact List.mem_append_left _ (List.mem_append_left _ ha))).trans hk₂
      (by intro r hr; simp [gm06CutAlongLinkageRegs, gm06CutCuffMembershipRegs, hr])
      (by intro a ha; exact List.mem_append_left _ (List.mem_append_right _ ha))
  have hk₂f : Keeps gm06CutAlongLinkageRegs gm06CutAlongLinkageArrs s₂ sf :=
    (hk₂₄.mono (by simp [gm06CutAlongLinkageRegs]) (by simp [gm06CutAlongLinkageArrs])).trans hkf
      (by simp [gm06CutAlongLinkageRegs, gm06CutMaterializeRegs, gm06CutComponentRotationsRegs])
      (by simp [gm06CutAlongLinkageArrs])
  refine ⟨sf, (t₁ + t₂) + (8 + (t₄ + tf)), .seq (.seq he₁ he₂) (.seq he₃ (.seq he₄ hef)), ?_,
    hk₀₂.trans hk₂f (fun _ h => h) (fun _ h => h), ?_⟩
  · have hM := totalAdjEntries_le hadj₁.2
    have hper : 91 + 40 * (2 * n) + 29 * totalAdjEntries (gm06CutAdjacencyLists (2 * n) data) ≤
        91 + 80 * n + 116 * (n * n) := by nlinarith only [hM]
    have htime₂ := ht₂.trans (Nat.add_le_add_left (Nat.mul_le_mul_left inner.length hper) 18)
    rw [hdartsLen] at ht₄
    rw [hk₂₄.2 625 (by decide), hphysical.1] at htf
    have hmatPer : (1 + 2 * (gm06EncodeRows rows).length) + 40 + 2200 * (2 * n) +
        2200 * data.rotations.flatten.length ≤
        41 + 2 * (gm06EncodeRows rows).length + 4400 * n + 4400 * rows.flatten.length := by omega
    have htimef := htf.trans (Nat.add_le_add_left (Nat.mul_le_mul_left inner.length hmatPer) 16)
    dsimp only [gm06CutAlongLinkageCost]
    dsimp only [aug] at hactiveLen ht₄
    nlinarith only [ht₁, htime₂, ht₄, htimef, hactiveLen]
  · have hcoverage : ∀ d ∈ data.activeDarts, d ∈ data.rotations.flatten := by
      intro d hd
      exact ((gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live d).mp hd).2
    have hdcode := gm06CutAlongLinkageResult_eq data masks sf hcoverage
      ((hkf.2 600 (by decide)).trans ((hk₂₄.2 600 (by decide)).trans h600code))
      (by simpa only [hmasksLen] using houtf)
      ((hkf.1 620 (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs])).trans
        ((hk₂₄.1 620 (by decide)).trans ((hk₂.1 620 (by simp [gm06CutComponentRowsRegs, List.mem_range'_1])).trans hN₁)))
      ((hkf.2 626 (by decide)).trans ((hk₂₄.2 626 (by decide)).trans ((hk₂.2 626 (by decide)).trans ho₁)))
      ((hkf.2 628 (by decide)).trans ((hk₂₄.2 628 (by decide)).trans ((hk₂.2 628 (by decide)).trans ha₁)))
    exact hdcode

/-- A uniform cubic bound for the complete finite cut program. -/
theorem gm06CutAlongLinkageCost_le_polynomial (n m c k p l r d z : ℕ) :
    gm06CutAlongLinkageCost n m c k p l r d z ≤
      1000000 * (n + m + c + k + p + l + r + d + z + 1) ^ 3 := by
  let N := n + m + c + k + p + l + r + d + z + 1
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hn : n ≤ N := by dsimp only [N]; omega
  have hmc : m + c ≤ N := by dsimp only [N]; omega
  have hz : z ≤ N := by dsimp only [N]; omega
  have hnn : n * n ≤ N * N := Nat.mul_le_mul hn hn
  have hcross : n * (m + c) ≤ N * N := Nat.mul_le_mul hn hmc
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have hNNN : N * N ≤ N * N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N * N) hN
  have hNcube : N ≤ N * N * N := hNN.trans hNNN
  have hlinear : 240 + 6172 * n + 23 * k + 56 * p + 31 * c + 138 * l + 2 * r +
      6334 * d + 328 * (m + c) ≤ 15000 * N := by dsimp only [N]; omega
  have hinside : 132 + 2 * r + 4480 * n + 4400 * d ≤ 10000 * N := by dsimp only [N]; omega
  have hzinside : z * (132 + 2 * r + 4480 * n + 4400 * d) ≤ 10000 * (N * N) := by
    calc
      _ ≤ N * (10000 * N) := Nat.mul_le_mul hz hinside
      _ = _ := by ring
  have hzcube : z * (n * n) ≤ N * N * N := by
    calc
      _ ≤ N * (N * N) := Nat.mul_le_mul hz hnn
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have heq : gm06CutAlongLinkageCost n m c k p l r d z =
      (240 + 6172 * n + 23 * k + 56 * p + 31 * c + 138 * l + 2 * r + 6334 * d + 328 * (m + c)) +
      26 * (n * (m + c)) + 84 * (n * n) + z * (132 + 2 * r + 4480 * n + 4400 * d) +
      116 * (z * (n * n)) := by unfold gm06CutAlongLinkageCost; ring
  rw [heq]
  change _ ≤ 1000000 * N ^ 3
  have hpow : N ^ 3 = N * N * N := by ring
  rw [hpow]
  omega

/-- On finite original input, the returned graphs are exactly the
components selected by the positive copied inner cuff edges. -/
theorem gm06CutAlongLinkage_components {n m : ℕ} (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ)
    (hrows : rows.length = n) (horig : origins.length = 2 * m)
    (hv : ∀ v ∈ origins, v < n) (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n) :
    (gm06CutAlongLinkage n m origins paths inner outer rows live).map some =
      gm06CutComponents (2 * n) m inner.length (gm06CutDataOfLinkage n m origins paths inner outer rows live) := by
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  have hvalues := gm06CutDataOfLinkage_origin_bounds origins paths inner outer rows live hrows horig hv hci hco
  have hroots : ∀ i, 0 ≤ i → i < 0 + inner.length → gm06CutInnerRoot data m i < 2 * n := by
    intro i _ hi
    have hidx := gm06CutDataOfLinkage_inner_dart_bound (n := n) (m := m) origins paths inner outer rows live (by omega : i < inner.length)
    simpa only [gm06CutInnerRoot, data, List.getElem?_eq_getElem hidx, Option.getD_some] using hvalues _ (List.getElem_mem hidx)
  have h := gm06CutInducedByVertices_bitsFrom (2 * n) data m 0 inner.length hroots
  simpa only [gm06CutAlongLinkage, gm06CutCuffMembership, List.map_map, Function.comp_def,
    gm06CutComponents, ← List.range_eq_range'] using h

end GraphMinor.Compute
