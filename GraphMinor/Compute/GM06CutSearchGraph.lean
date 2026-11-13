module

public import GraphMinor.Compute.GM06CutSearchAdjacency
public import GraphMinor.Compute.GM06CutDataBounds
import GraphMinor.Compute.GM06FaceBuffers

/-!
# From original linkage data to the cut search graph

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) first
computes the copied rotations and endpoints, then searches the resulting
graph. This file composes the full input-to-cut-data program with
the adjacency construction. It derives every adjacency premise from
the original finite inputs. The saved rotation-prefix length keeps
the complete cut graph available for later component and face work.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Construct all cut data and its search graph from the original input. -/
def gm06CutSearchGraphProg : Cmd :=
  .seq gm06CutDataProg
    (.seq (.assign 658 (.reg 655))
      (.seq (.assign 620 (.op .mul (.const 2) (.reg 648)))
        (.seq (.assign 647 (gm06CutSizeExpr 4)) gm06CutSearchAdjacencyProg)))

/-- Registers changed by the complete finite cut search-graph construction. -/
def gm06CutSearchGraphRegs : List ℕ :=
  gm06CutRotationRegs ++ [658, 620, 647] ++ gm06CutAdjacencyRegs

/-- Arrays changed by the complete finite cut search-graph construction. -/
def gm06CutSearchGraphArrs : List ℕ := gm06CutDataArrs ++ 627 :: gm06CutAdjacencyArrs

/-- Exact copied graph and adjacency representation from the original
paths and both cuffs. The explicit time bound is quadratic in the
original list sizes and permanent label counts. -/
theorem gm06CutSearchGraphProg_exec {w n m : ℕ}
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
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h601 : s.arrs 601 = origins)
    (h608 : s.arrs 608 = gm06EncodeRows paths) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h618 : s.arrs 618 = live) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    ∃ sf t, Exec w gm06CutSearchGraphProg s sf t ∧
      t ≤ 188 + 172 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) + 138 * live.length + 2 * (gm06EncodeRows rows).length +
        n * (6000 + 26 * (m + inner.length + outer.length)) + 6334 * rows.flatten.length +
        268 * (m + inner.length + outer.length) + 84 * (n * n) ∧
      Keeps gm06CutSearchGraphRegs gm06CutSearchGraphArrs s sf ∧
      (sf.arrs 625).take (sf.regs 658) = gm06EncodeRows data.rotations ∧
      sf.arrs 626 = data.origins ∧ sf.arrs 628 = data.activeDarts ∧ sf.arrs 629 = data.vertices ∧
      sf.regs 620 = 2 * n ∧
      IsAdjList (gm06CutGraph (2 * n) data) 620 621 622 (gm06CutAdjacencyLists (2 * n) data) sf ∧
      (sf.arrs 622).length = (2 * n) * (2 * n) := by
  dsimp only
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  let aug := m + inner.length + outer.length
  have hw2 : 2 < 2 ^ w := by omega
  have hL := gm06FaceCode_length rows
  have h2n : 2 * n < 2 ^ w := by omega
  have h4aug : 4 * aug < 2 ^ w := by dsimp only [aug]; omega
  have hsizes := gm06CutDataOfLinkage_sizes n m origins paths inner outer rows live
  have hrotLen : data.rotations.length = 2 * n := hsizes.1.trans (congrArg (2 * ·) hrows)
  have hcutBounds := gm06CutDataOfLinkage_dart_bounds (n := n) origins paths inner outer rows live hkeys
  have hcutValues := gm06CutDataOfLinkage_origin_bounds origins paths inner outer rows live hrows horig hv hci hco
  have hcutLive := gm06CutVertices_bound (gm06BuildCutTables n m origins paths inner outer) live hlive
  have hcutVertexLen : data.vertices.length ≤ 2 * live.length := hsizes.2.2
  have hcutActiveLen : data.activeDarts.length ≤ 4 * aug := hcutBounds.2.2
  have hcopiedLen : data.rotations.flatten.length ≤ 2 * rows.flatten.length := gm06SplitRotationRows_length_le _ _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hr₁, ho₁, ha₁, hv₁⟩ := gm06CutDataProg_exec
    origins paths inner outer rows live s hw hn hsize horig hv hd hci hco hrows
    (fun row hr => hnd.sublist (List.sublist_flatten_of_mem hr)) hkeys hlive hliveFit
    hpathCode hpathWords hrotFit hrotWords h600 h601 h608 h609 h610 h618 h648 h649
  have hphysical := gm06CutDataProg_output_bounds rows s s₁ t₁ hw2 h600 hrotFit he₁
  let padding := (s₁.arrs 625).drop (s₁.regs 655)
  have hsource : s₁.arrs 625 = gm06EncodeRows data.rotations ++ padding := by
    change (s₁.arrs 625).take (s₁.regs 655) = gm06EncodeRows data.rotations at hr₁
    rw [← hr₁]
    exact (List.take_append_drop _ _).symm
  have hcursorFit := gm06CutDataProg_cursor_lt rows s s₁ t₁ hw2 h600 hrotFit he₁
  let s₂ := s₁.setReg 658 (s₁.regs 655)
  let s₃ := s₂.setReg 620 (2 * n)
  let s₄ := s₃.setReg 647 (4 * aug)
  have he₂ : Exec w (.assign 658 (.reg 655)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg rfl hcursorFit)
  have he₃ : Exec w (.assign 620 (.op .mul (.const 2) (.reg 648))) s₂ s₃ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw2)
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂] using (hk₁.1 648 (by decide)).trans h648) hn) h2n)
  have he₄ : Exec w (.assign 647 (gm06CutSizeExpr 4)) s₃ s₄ 8 :=
    .assign (gm06CutSizeExpr_eval inner outer s₃ hw (by dsimp only [aug] at h4aug; omega) h4aug
      (by simpa [s₃, s₂] using (hk₁.1 649 (by decide)).trans h649)
      ((hk₁.2 609 (by decide)).trans h609) ((hk₁.2 610 (by decide)).trans h610))
  have hk₁₄ : Keeps [658, 620, 647] [] s₁ s₄ :=
    (((Keeps.refl _ _ s₁).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  obtain ⟨sf, tf, hef, htf, hkf, hadjf, hentries⟩ := gm06CutSearchAdjacencyProg_exec
    (n := 2 * n) (m := 2 * aug) data padding s₄ hw2 h2n (by omega) hsearchFit hrotLen
    (by have h := hsizes.2.1; change data.origins.length = _ at h; dsimp only [aug]; omega) hcutValues
    (fun d hd => by have h := hcutBounds.1 d hd; dsimp only [aug]; omega) hcutLive
    (by omega)
    (fun d hd => by have h := hcutBounds.2.1 d hd; dsimp only [aug]; omega)
    (by omega)
    (fun d hd u => gm06CutDataOfLinkage_origin_row_iff origins paths inner outer rows live hrows hnd hd u.isLt)
    hsource (by change (s₁.arrs 625).length < 2 ^ w; rw [hphysical.1]; omega) hphysical.2 ho₁ ha₁ hv₁
    (by simp [s₄, s₃]) (by simp [s₄]; omega)
  have hk₀₄ : Keeps gm06CutSearchGraphRegs gm06CutSearchGraphArrs s s₄ :=
    (hk₁.mono
      (by simp [gm06CutSearchGraphRegs, gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs,
        gm06CutSplitRowsRegs, gm06CutSplitVertexRegs, gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs])
      (by simp [gm06CutSearchGraphArrs, gm06CutDataArrs, gm06CutAdjacencyArrs])).trans hk₁₄
      (by simp [gm06CutSearchGraphRegs, gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs,
        gm06CutSplitRowsRegs, gm06CutSplitVertexRegs, gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs]) (by simp)
  refine ⟨sf, t₁ + (2 + (4 + (8 + tf))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef))), ?_,
    hk₀₄.trans hkf
      (by simp [gm06CutSearchGraphRegs, gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs,
        gm06CutSplitRowsRegs, gm06CutSplitVertexRegs, gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs])
      (by simp [gm06CutSearchGraphArrs, gm06CutDataArrs, gm06CutAdjacencyArrs]), ?_, ?_, ?_, ?_, ?_, hadjf, hentries⟩
  · have hvl := hcutVertexLen
    have hal : data.activeDarts.length ≤ 4 * (m + inner.length + outer.length) := hcutActiveLen
    dsimp only [aug] at htf
    nlinarith only [ht₁, htf, hvl, hal, hcopiedLen]
  · rw [hkf.2 625 (by decide), hkf.1 658 (by decide)]
    simpa only [s₄, s₃, s₂, State.setReg_arrs, State.setReg_regs_ne _ _ (by decide : (658 : ℕ) ≠ 647),
      State.setReg_regs_ne _ _ (by decide : (658 : ℕ) ≠ 620), State.setReg_regs_self, gm06CutRowsResult] using hr₁
  · exact (hkf.2 626 (by decide)).trans ho₁
  · exact (hkf.2 628 (by decide)).trans ha₁
  · exact (hkf.2 629 (by decide)).trans hv₁
  · exact (hkf.1 620 (by decide)).trans (by simp [s₄, s₃])

end GraphMinor.Compute
