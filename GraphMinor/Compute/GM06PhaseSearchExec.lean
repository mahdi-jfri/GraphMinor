module

public import GraphMinor.Compute.GM06PhaseLoadBoundaries
public import GraphMinor.Compute.GM06PhaseComponentData
public import GraphMinor.Compute.GM06PhaseSearchFacts
import GraphMinor.Compute.GM06CutCSR

/-!
# Exact search and installation for one computed component

Sections 12 and 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) run
FIND_4 on the incidence of the selected face. This proof composes
boundary loading, ordinary-edge flags, the directed search, and the
conditional core splice. Failed searches preserve the core linkage
and bit. A successful search installs exactly its computed witness.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Cost of one search, including its possible core installation. -/
def gm06Reduction4PhaseSearchCost (x : GM06SuccessorInput) (m i : ℕ) (part : GM06CutData) : ℕ :=
  1000 + 1000 * (gm06EncodeRows x.linkage).length + 400 * x.vertexCount +
    100 * (m + x.innerCuff.length + x.outerCuff.length) +
    gm06Find4DartsCost (2 * x.vertexCount) (2 * (m + x.innerCuff.length + x.outerCuff.length))
      (x.linkage[i]?.getD []).length
      ((x.linkage[gm06PhaseNext x i]?.getD []).length + 1) part.rotations.flatten.length

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem search_frame {w t : ℕ} {s sf : State}
    (he : Exec w gm06Reduction4PhaseSearchProg s sf t) :
    Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf := by
  have hr : gm06Reduction4PhaseSearchProg.writtenRegs ⊆ gm06Reduction4PhaseRegs.toFinset := by decide
  have ha : gm06Reduction4PhaseSearchProg.writtenArrs ⊆ gm06Reduction4PhaseArrs.toFinset := by decide
  constructor
  · intro r hnot
    exact he.regs_eq_of_not_mem_writtenRegs (fun h => hnot (by simpa only [List.mem_toFinset] using hr h))
  · intro a hnot
    exact he.arrs_eq_of_not_mem_writtenArrs (fun h => hnot (by simpa only [List.mem_toFinset] using ha h))

/-- One computed component's search returns its exact pure result
and conditionally updates only the core linkage and continuation bit.
The selected face is the actual preceding incidence query's output. -/
theorem gm06Reduction4PhaseSearchProg_exec {w m i : ℕ} (x : GM06SuccessorInput)
    (part : GM06CutData) (s : State) (row incV incE : List ℕ)
    (hw : 4 < 2 ^ w) (hn : 2 * x.vertexCount + 4 < 2 ^ w)
    (hm : 4 * (m + x.innerCuff.length + x.outerCuff.length) < 2 ^ w)
    (hspace : (2 * x.vertexCount) * (2 * x.vertexCount) + 2 < 2 ^ w)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length) (hi : i < x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hp : part ∈ gm06PhaseComponents x m)
    (hfit : (gm06EncodeRows x.linkage).length + 2 * x.vertexCount + 5 < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeRows x.linkage, a < 2 ^ w)
    (hpartCode : (gm06EncodeRows part.rotations).length < 2 ^ w)
    (hpartWords : ∀ a ∈ gm06EncodeRows part.rotations, a < 2 ^ w)
    (hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) = some (row, incV, incE))
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h642 : s.arrs 642 = gm06EncodeRows x.linkage) (h8 : s.arrs 8 = gm06EncodeRows x.linkage)
    (h625 : s.arrs 625 = gm06EncodeRows part.rotations) (h626 : s.arrs 626 = part.origins)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE)
    (h681 : s.regs 681 = i) (h685 : s.regs 685 = x.innerCuff.length)
    (h682 : s.regs 682 = 2 * x.vertexCount) (h684 : s.regs 684 = m)
    (h649 : s.regs 649 = 2 * (m + x.innerCuff.length + x.outerCuff.length)) (h646 : s.regs 646 = 0) :
    ∃ sf t, Exec w gm06Reduction4PhaseSearchProg s sf t ∧
      t ≤ gm06Reduction4PhaseSearchCost x m i part ∧
      Keeps gm06Reduction4PhaseRegs gm06Reduction4PhaseArrs s sf ∧
      (match gm06Reduction4PhaseComponent x m i part with
      | none => sf.regs 646 = 0 ∧ sf.arrs 8 = s.arrs 8 ∧ sf.regs 329 = s.regs 329
      | some (j, darts) => sf.regs 646 = 1 ∧
          sf.arrs 8 = gm06EncodeRows (gm06Apply4Paths darts x.linkage i j) ∧ sf.regs 329 = 0) := by
  let aug := m + x.innerCuff.length + x.outerCuff.length
  let N := 2 * x.vertexCount
  let M := 2 * aug
  have hik : i < x.linkage.length := by omega
  have hk : 0 < x.innerCuff.length := by omega
  have hnext : gm06PhaseNext x i < x.innerCuff.length := Nat.mod_lt _ hk
  have hnextPath : gm06PhaseNext x i < x.linkage.length := by omega
  have hcodeLen := gm06FaceCode_length x.linkage
  have hiw : i < 2 ^ w := by omega
  have hleftLen : x.linkage[i].length ≤ (gm06EncodeRows x.linkage).length := by
    have hs : [x.linkage[i]].Sublist x.linkage := List.singleton_sublist.mpr (List.getElem_mem hik)
    have hl : x.linkage[i].length ≤ x.linkage.flatten.length := by simpa using hs.flatten.length_le
    omega
  have hupperLen : x.linkage[gm06PhaseNext x i].length ≤ (gm06EncodeRows x.linkage).length := by
    have hs : [x.linkage[gm06PhaseNext x i]].Sublist x.linkage := List.singleton_sublist.mpr (List.getElem_mem hnextPath)
    have hl : x.linkage[gm06PhaseNext x i].length ≤ x.linkage.flatten.length := by simpa using hs.flatten.length_le
    omega
  obtain ⟨hlen, horg, hvals, hds⟩ := gm06PhaseComponents_sizes x hrows horig hvalues hinner houter hnd hkeys part hp
  obtain ⟨_, _, _, hpnd, hcanon, hpair⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hcover : ∀ d, d ∈ part.activeDarts ↔ d ∈ part.rotations.flatten := by
    intro d
    rw [hcanon, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact and_iff_right_of_imp (hds d)
  obtain ⟨hV, hE, _, _, _, hinc⟩ := gm06CutFaceIncidence_some_facts part hpnd
    (by intro d hd; have := hds d hd; omega)
    (fun d hd => by have := hds d ((hcover d).mp hd); omega)
    hcover hpair (by omega) hface
  have hVlen : incV.length = N := by simp only [hV, gm06IncV, gm06IncidenceBits, List.length_ofFn]; rfl
  have hElen : incE.length = M := by simp only [hE, gm06IncE, gm06IncidenceBits, List.length_ofFn]; rfl
  have hVwords : ∀ a ∈ incV, a < 2 ^ w := by
    intro a ha
    rcases gm06IncidenceBits_words N (gm06FaceVertices part.origins row) (a := a) (by simpa only [hV, gm06IncV, N] using ha) with h | h <;> omega
  have hEwords : ∀ a ∈ incE, a < 2 ^ w := by
    intro a ha
    rcases gm06IncidenceBits_words M (gm06FaceEdges row) (a := a) (by simpa only [hE, gm06IncE, M, aug] using ha) with h | h <;> omega
  let source := 2 * x.innerCuff[i]?.getD 0
  have hsource : source < N := by
    have hv := hinner _ (List.getElem_mem hi)
    simp only [source, List.getElem?_eq_getElem hi, Option.getD_some, N]
    omega
  have hN : 0 < N := Nat.zero_lt_of_lt hsource
  let start : Fin N := ⟨source, hsource⟩
  let steps := gm06PhaseLeftSteps x i
  have hstepValues : ∀ p ∈ steps, p.2 < N := by
    intro p hp'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp'
    have hdi : d < 2 * m := hdarts d (List.mem_flatten.mpr
      ⟨x.linkage[i], List.getElem_mem hik, by simpa only [List.getElem?_eq_getElem hik, Option.getD_some] using hd⟩)
    have hb : gm06DartMate d < x.endpoints.length := horig ▸ gm06DartMate_lt hdi
    have hv := hvalues _ (List.getElem_mem hb)
    simp only [List.getElem?_eq_getElem hb, Option.getD_some, N]
    omega
  let typedSteps := gm06PhaseFinSteps N hN steps
  have hmap := gm06PhaseFinSteps_map_val hN steps hstepValues
  have hstepLen : typedSteps.length = x.linkage[i].length := by
    simp only [typedSteps, gm06PhaseFinSteps, steps, gm06PhaseLeftSteps,
      List.length_map, List.getElem?_eq_getElem hik, Option.getD_some]
  have hstepsFst : typedSteps.map Prod.fst = steps.map Prod.fst := by
    have h := congrArg (List.map Prod.fst) hmap
    simpa only [List.map_map, Function.comp_def] using h
  have hstepsSnd : typedSteps.map (fun p => p.2.val) = steps.map Prod.snd := by
    have h := congrArg (List.map Prod.snd) hmap
    simpa only [List.map_map, Function.comp_def] using h
  have hvertices : gm06Find4PathVertices start typedSteps = gm06PhaseBoundaryVertices x i 0 := by
    rw [gm06Find4PathVertices, hstepsSnd]
    exact gm06PhaseLeftSteps_vertices x i
  have hstepEdges : ∀ p ∈ typedSteps, p.1 < M := by
    intro p hp'
    have hp'' : (p.1, p.2.val) ∈ steps := hmap ▸ List.mem_map.mpr ⟨p, hp', rfl⟩
    obtain ⟨d, hd, heq⟩ := List.mem_map.mp hp''
    have hdi : d < 2 * m := hdarts d (List.mem_flatten.mpr
      ⟨x.linkage[i], List.getElem_mem hik, by simpa only [List.getElem?_eq_getElem hik, Option.getD_some] using hd⟩)
    have he := congrArg Prod.fst heq
    simp only [M, aug]
    change 2 * (d / 2) = p.1 at he
    omega
  have hupperBound : ∀ v ∈ gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1, v < N := by
    have hv := hinner _ (List.getElem_mem hnext)
    have hd : ∀ d ∈ x.linkage[gm06PhaseNext x i], d < 2 * m := fun d hd => hdarts d
      (List.mem_flatten.mpr ⟨_, List.getElem_mem hnextPath, hd⟩)
    simpa only [gm06PhaseBoundaryVertices, gm06PhaseBoundaryRow, List.getElem?_eq_getElem hnextPath,
      List.getElem?_eq_getElem hnext, Option.getD_some] using
      gm06PhaseBoundaryRow_bounds x.endpoints x.linkage[gm06PhaseNext x i] horig hvalues hd hv (by decide : 1 ≤ 1)
  have hupperSize : (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1).length =
      x.linkage[gm06PhaseNext x i].length + 1 := by
    simp only [gm06PhaseBoundaryVertices, List.length_cons, List.length_map,
      List.getElem?_eq_getElem hnextPath, Option.getD_some]
  have hfindEq : gm06PhaseFind4Words N M part.origins (gm06CandidateOrdinary M m) incV incE
      (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) source steps =
      gm06Find4Darts M part.origins (gm06CandidateOrdinary M m) incV incE
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) start typedSteps := by
    calc
      _ = gm06PhaseFind4Words N M part.origins (gm06CandidateOrdinary M m) incV incE
          (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) source
          (typedSteps.map (fun p => (p.1, p.2.val))) := congrArg _ hmap.symm
      _ = _ := gm06PhaseFind4Words_eq _ _ _ _ _ start typedSteps
  have hcomponent : gm06Reduction4PhaseComponent x m i part =
      gm06Find4Darts M part.origins (gm06CandidateOrdinary M m) incV incE
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) start typedSteps := by
    simpa only [gm06Reduction4PhaseComponent, hface, Option.bind_eq_bind, Option.bind_some,
      N, M, aug, source, steps] using hfindEq
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hl₁, hu₁, hed₁⟩ := gm06PhaseLoadBoundariesProg_exec x s (by omega)
    (by omega) (by omega) horig hvalues hdarts hinner hcount hi
    (by omega) hwords h3 h6 h642 h681 h685
  let s₂ := s₁.setReg 670 m
  let s₃ := s₂.setReg 620 N
  have he₂ : Exec w (.assign 670 (.reg 684)) s₁ s₂ 2 := .assign
    (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 684 (by decide)).trans h684) (by omega))
  have he₃ : Exec w (.assign 620 (.reg 682)) s₂ s₃ 2 := .assign
    (GraphMinor.Compute.Crossing.eval_reg (w := w) (s := s₂) (r := 682) (by simpa [s₂, N] using ((hk₁.1 682 (by decide)).trans h682)) (by simp only [N]; omega))
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, ho₄⟩ := gm06CandidateOrdinaryProg_exec (w := w) (m := M) (original := m) s₃ (by omega)
    (by have hM : M = 2 * (m + x.innerCuff.length + x.outerCuff.length) := rfl; omega) (by omega)
    (by simpa [s₃, s₂, M, aug] using ((hk₁.1 649 (by decide)).trans h649))
    (by simp [s₃, s₂])
  have hepre : Exec w (.seq gm06PhaseLoadBoundariesProg (.seq (.assign 670 (.reg 684))
      (.seq (.assign 620 (.reg 682)) gm06CandidateOrdinaryProg))) s s₄ (t₁ + (2 + (2 + t₄))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hr₅⟩ := gm06Find4DartsProg_exec (n := N) (m := M) part
    (gm06CandidateOrdinary M m) incV incE (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) [] start typedSteps s₄
    hn (by have hM : M = 2 * (m + x.innerCuff.length + x.outerCuff.length) := rfl; omega) hspace hlen (by have hM : M = 2 * (m + x.innerCuff.length + x.outerCuff.length) := rfl; omega)
    hvals (by intro d hd; have := hds d hd; omega)
    (gm06PhaseComponents_origin_row_iff x hrows hnd hkeys part hp) hinc hVlen hElen
    (gm06CandidateOrdinary_length M m) hVwords hEwords (by rw [hstepLen]; omega) hstepEdges
    (by rw [hupperSize]; omega) hupperBound
    ((hepre.arrs_eq_of_not_mem_writtenArrs (a := 606) (by decide)).trans h606)
    ((hepre.arrs_eq_of_not_mem_writtenArrs (a := 607) (by decide)).trans h607)
    ((hk₄.2 608 (by decide)).trans hu₁)
    (by rw [hvertices]; exact (hk₄.2 609 (by decide)).trans hl₁)
    (by rw [hstepsFst]; exact (hk₄.2 610 (by decide)).trans hed₁) ho₄
    (by simpa only [List.append_nil] using (hepre.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide)).trans h625)
    (by rw [hepre.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide), h625]; exact hpartCode)
    (by rw [hepre.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide), h625]; exact hpartWords)
    ((hepre.arrs_eq_of_not_mem_writtenArrs (a := 626) (by decide)).trans h626)
    (by rw [hk₄.1 620 (by decide)]; simp [s₃])
    ((hepre.regs_eq_of_not_mem_writtenRegs (r := 649) (by decide)).trans h649)
  have hflagWord : s₅.regs 646 < 2 ^ w := gm06Exec_reg_lt he₅ 646 (by
    rw [hepre.regs_eq_of_not_mem_writtenRegs (r := 646) (by decide), h646]
    exact Nat.two_pow_pos w)
  have hpreCore : s₅.arrs 8 = s.arrs 8 := (hk₅.2 8 (by decide)).trans
    (hepre.arrs_eq_of_not_mem_writtenArrs (a := 8) (by decide))
  have hpreBit : s₅.regs 329 = s.regs 329 := (hk₅.1 329 (by decide)).trans
    (hepre.regs_eq_of_not_mem_writtenRegs (r := 329) (by decide))
  cases hans : gm06Reduction4PhaseComponent x m i part with
  | none =>
    have hnone : gm06Find4DartsResult s₅ = none := hr₅.trans (hcomponent.symm.trans hans)
    have hz : s₅.regs 646 = 0 := by
      by_contra hz
      simp only [gm06Find4DartsResult, hz, ↓reduceIte, reduceCtorEq] at hnone
    have hite : Exec w (.ite (.reg 646) gm06PhaseApply4Prog .skip) s₅ s₅ 2 :=
      .ite_false (GraphMinor.Compute.Crossing.eval_reg hz (Nat.two_pow_pos w)) (.skip s₅)
    have he : Exec w gm06Reduction4PhaseSearchProg s s₅ (t₁ + (2 + (2 + (t₄ + (t₅ + 2))))) :=
      .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ hite))))
    refine ⟨s₅, _, he, ?_, search_frame he, ?_⟩
    · unfold gm06Reduction4PhaseSearchCost
      rw [hstepLen, hupperSize] at ht₅
      simp only [List.getElem?_eq_getElem hik, List.getElem?_eq_getElem hnextPath, Option.getD_some]
      simp only [N, M, aug] at ht₄ ht₅
      omega
    · simp only [hans]
      exact ⟨hz, hpreCore, hpreBit⟩
  | some result =>
    obtain ⟨j, darts⟩ := result
    have hsome : gm06Find4DartsResult s₅ = some (j, darts) := hr₅.trans (hcomponent.symm.trans hans)
    have hflag : s₅.regs 646 ≠ 0 := by
      intro hz
      simp only [gm06Find4DartsResult, hz, ↓reduceIte, reduceCtorEq] at hsome
    have hresult : (s₅.regs 678, s₅.arrs 635) = (j, darts) := by
      simpa only [gm06Find4DartsResult, hflag, ↓reduceIte, Option.some.injEq] using hsome
    have hj := congrArg Prod.fst hresult
    have hd := congrArg Prod.snd hresult
    have hwordsResult : gm06PhaseFind4Words N M part.origins (gm06CandidateOrdinary M m) incV incE
        (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) source steps = some (j, darts) :=
      hfindEq.trans (hcomponent.symm.trans hans)
    obtain ⟨_, hjbound, hreplaceLen, hreplace⟩ := gm06PhaseFind4Words_bounds part.origins
      (gm06CandidateOrdinary M m) incV incE (gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1) steps darts
      (by omega) hvals hwordsResult
    have hstepsLen : steps.length = x.linkage[i].length := by
      simp only [steps, gm06PhaseLeftSteps, List.length_map, List.getElem?_eq_getElem hik, Option.getD_some]
    obtain ⟨sf, tf, hef, htf, _, hout, hbit, hret⟩ := gm06PhaseApply4Prog_exec darts x.linkage hik
      (by rw [hstepsLen] at hjbound; exact hjbound) s₅ hw (by omega)
      hwords (fun d hd => (hreplace d hd).trans (by have hM : M = 2 * (m + x.innerCuff.length + x.outerCuff.length) := rfl; omega)) (hpreCore.trans h8) hd
      ((hk₅.1 681 (by decide)).trans ((hepre.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)).trans h681)) hj
    have hite := Exec.ite_true (c₂ := .skip) (GraphMinor.Compute.Crossing.eval_reg (w := w) (r := 646) rfl hflagWord) hflag hef
    have he : Exec w gm06Reduction4PhaseSearchProg s sf (t₁ + (2 + (2 + (t₄ + (t₅ + (1 + tf)))))) :=
      .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ hite))))
    refine ⟨sf, _, he, ?_, search_frame he, ?_⟩
    · unfold gm06Reduction4PhaseSearchCost
      rw [hstepLen, hupperSize] at ht₅
      simp only [List.getElem?_eq_getElem hik, List.getElem?_eq_getElem hnextPath, Option.getD_some]
      simp only [N, M, aug] at ht₄ ht₅ hreplaceLen
      omega
    · simp only [hans]
      exact ⟨hret, hout, hbit⟩

end GraphMinor.Compute
