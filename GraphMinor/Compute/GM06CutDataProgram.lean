module

public import GraphMinor.Compute.GM06CutBufferBounds
public import GraphMinor.Compute.GM06CutVertexProgram
public import GraphMinor.Compute.GM06CutOriginProgram
public import GraphMinor.Compute.GM06CutActiveProgram
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Constructing the finite graph data of the cut along the linkage

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes the
cut positions, induced rotations, live vertex copies and copied endpoints
before searching for components. This file composes all those finite
passes from the original paths, both cuff orders and marked rotations.
The resulting lists contain only graph data. Component searches can
use them without reading any geometric or side-assignment certificate.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Finite rotation, endpoint and active-label data, with no proof fields. -/
structure GM06CutData where
  rotations : List (List ℕ)
  origins : List ℕ
  activeDarts : List ℕ
  vertices : List ℕ
  deriving DecidableEq, Repr

/-- Exact finite split graph data computed from the linkage and both cuffs. -/
def gm06CutDataOfLinkage (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) : GM06CutData :=
  let marks := gm06BuildCutTables n m origins paths inner outer
  let rotations := gm06SplitRotationRows marks rows
  { rotations := rotations
    origins := gm06CutOrigins (m + inner.length + outer.length) rotations
    activeDarts := gm06CutActiveDarts (m + inner.length + outer.length) rotations
    vertices := gm06CutVertices marks live }

/-- Compute a multiple of the augmented edge-label count from original inputs. -/
def gm06CutSizeExpr (factor : ℕ) : Expr :=
  .op .mul (.const factor) (.op .add (.op .add (.reg 649) (.len 609)) (.len 610))

/-- All size arithmetic is computed from original permanent labels and cuff lengths. -/
theorem gm06CutSizeExpr_eval {w m factor : ℕ} (inner outer : List ℕ) (s : State)
    (hf : factor < 2 ^ w) (ha : m + inner.length + outer.length < 2 ^ w)
    (hsize : factor * (m + inner.length + outer.length) < 2 ^ w)
    (h649 : s.regs 649 = m) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer) :
    (gm06CutSizeExpr factor).eval w s = some (factor * (m + inner.length + outer.length)) := by
  exact GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hf)
    (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg h649 (by omega))
        (GraphMinor.Compute.Crossing.eval_len h609 (by omega)) (by omega))
      (GraphMinor.Compute.Crossing.eval_len h610 (by omega)) ha) hsize

/-- Mark, copy live vertices, split rotations, then compute copied origins
and the increasing active-dart list. Source live vertices are in 618. -/
def gm06CutDataProg : Cmd :=
  .seq gm06CutMarkProg
    (.seq gm06CutVertexProg
      (.seq (.assign 647 (gm06CutSizeExpr 2))
        (.seq gm06CutRowsProg
          (.seq (.assign 647 (gm06CutSizeExpr 4)) (.seq gm06CutOriginProg gm06CutActiveProg)))))

/-- Arrays changed by the complete finite graph-data construction. -/
def gm06CutDataArrs : List ℕ := [611, 614, 615, 616, 619, 620, 621, 623, 624, 625, 626, 627, 628, 629]

/-- Complete construction of the finite cut graph data from original
list inputs. Live copied vertices exclude unused permanent slots,
while the endpoint and dart arrays keep the permanent copied labels. -/
theorem gm06CutDataProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 4 * (m + inner.length + outer.length) + 3 < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hrows : rows.length = n) (hnd : ∀ row ∈ rows, row.Nodup)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length))
    (hlive : ∀ v ∈ live, v < n) (hliveFit : 2 * live.length + 2 < 2 ^ w)
    (hpathCode : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h601 : s.arrs 601 = origins)
    (h608 : s.arrs 608 = gm06EncodeRows paths) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h618 : s.arrs 618 = live) (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    ∃ sf t, Exec w gm06CutDataProg s sf t ∧
      t ≤ 134 + 58 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) + 110 * live.length + 2 * (gm06EncodeRows rows).length +
        n * (6000 + 26 * (m + inner.length + outer.length)) + 6076 * rows.flatten.length +
        208 * (m + inner.length + outer.length) ∧
      Keeps gm06CutRotationRegs gm06CutDataArrs s sf ∧
      gm06CutRowsResult sf = gm06EncodeRows data.rotations ∧
      sf.arrs 626 = data.origins ∧ sf.arrs 628 = data.activeDarts ∧ sf.arrs 629 = data.vertices := by
  dsimp only
  have hw2 : 2 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let aug := m + inner.length + outer.length
  let marks := gm06BuildCutTables n m origins paths inner outer
  let copied := gm06SplitRotationRows marks rows
  have hAug : aug < 2 ^ w := by dsimp only [aug]; omega
  have hTwoAug : 2 * aug < 2 ^ w := by dsimp only [aug]; omega
  have hFourAug : 4 * aug < 2 ^ w := by dsimp only [aug]; omega
  have hmarkSize : 2 * aug + 1 < 2 ^ w := by dsimp only [aug]; omega
  have hL := gm06FaceCode_length rows
  have hTwoN : 2 * n < 2 ^ w := by omega
  have hmarkLens := gm06BuildCutTables_lengths n m origins paths inner outer
  have hmarkWords := gm06BuildCutTables_words (n := n) origins paths inner outer hmarkSize hd
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hi₁, ho₁, hp₁, hn₁⟩ := gm06CutMarkProg_exec
    origins paths inner outer s hw2 hn hmarkSize horig hv hd hci hco hpathCode hpathWords
    h601 h608 h609 h610 h648 h649
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hv₂⟩ := gm06CutVertexProg_exec marks live s₁ hw2 hTwoN hliveFit
    hmarkLens.1 hmarkLens.2.1
    (fun x hx => hmarkWords x (List.mem_append_left _ (List.mem_append_left _ hx))) hlive hi₁ ho₁
    ((hk₁.2 618 (by decide)).trans h618)
  have hk₀₂ : Keeps gm06CutRotationRegs gm06CutDataArrs s s₂ :=
    (hk₁.mono (by simp [gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs])
      (by simp [gm06CutDataArrs])).trans hk₂
        (by simp [gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp [gm06CutDataArrs])
  let s₃ := s₂.setReg 647 (2 * aug)
  have he₃ : Exec w (.assign 647 (gm06CutSizeExpr 2)) s₂ s₃ 8 :=
    .assign (gm06CutSizeExpr_eval inner outer s₂ hw2 hAug hTwoAug
      ((hk₀₂.1 649 (by decide)).trans h649) ((hk₀₂.2 609 (by decide)).trans h609)
      ((hk₀₂.2 610 (by decide)).trans h610))
  have hk₀₃ := hk₀₂.setReg (by simp [gm06CutRotationRegs] : 647 ∈ gm06CutRotationRegs) (2 * aug)
  have hsource₃ : s₃.arrs 600 = gm06EncodeRows rows := (hk₀₃.2 600 (by decide)).trans h600
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hrows₄⟩ := gm06CutRowsProg_exec marks rows s₃ hw hn hFourAug
    hrows hnd hkeys hmarkLens hmarkWords
    ((hk₂.2 620 (by decide)).trans hi₁) ((hk₂.2 621 (by decide)).trans ho₁)
    ((hk₂.2 623 (by decide)).trans hp₁) ((hk₂.2 624 (by decide)).trans hn₁)
    hsource₃ (by simp [s₃]) hrotFit hrotWords
  have hk₀₄ : Keeps gm06CutRotationRegs gm06CutDataArrs s s₄ :=
    hk₀₃.trans hk₄ (by simp [gm06CutRotationRegs, gm06CutSplitRowsRegs, gm06CutSplitVertexRegs])
      (by simp [gm06CutDataArrs])
  have hphysical := gm06CutRowsProg_output_bounds rows s₃ s₄ t₄ hw2 hsource₃ hrotFit he₄
  let tail := (s₄.arrs 625).drop (s₄.regs 655)
  have hprefix : (s₄.arrs 625).take (s₄.regs 655) = gm06EncodeRows copied := hrows₄
  have hbuffer : s₄.arrs 625 = gm06EncodeRows copied ++ tail := by
    rw [← hprefix]
    exact (List.take_append_drop _ _).symm
  let s₅ := s₄.setReg 647 (4 * aug)
  have he₅ : Exec w (.assign 647 (gm06CutSizeExpr 4)) s₄ s₅ 8 :=
    .assign (gm06CutSizeExpr_eval inner outer s₄ hw hAug hFourAug
      ((hk₀₄.1 649 (by decide)).trans h649) ((hk₀₄.2 609 (by decide)).trans h609)
      ((hk₀₄.2 610 (by decide)).trans h610))
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, ho₆, ha₆⟩ := gm06CutOriginProg_exec copied tail s₅ hw1 hFourAug
    (fun d hd => by
      obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
      exact (gm06SplitRotationRows_row_bounds marks rows row hr hkeys).2 d hd)
    hbuffer (by simpa only [s₅, State.setReg_arrs, hphysical.1] using (by omega : 1 + 2 * (gm06EncodeRows rows).length < 2 ^ w))
    hphysical.2 (by simp [s₅])
  have hk₀₆ : Keeps gm06CutRotationRegs gm06CutDataArrs s s₆ :=
    (hk₀₄.setReg (by simp [gm06CutRotationRegs]) _).trans hk₆
      (by simp [gm06CutRotationRegs, gm06CutOriginRowsRegs, gm06CutMarkRegs, gm06CutLinkageRegs,
        gm06CutSplitRowsRegs, gm06CutSplitVertexRegs]) (by simp [gm06CutDataArrs])
  obtain ⟨sf, tf, hef, htf, hkf, haf⟩ := gm06CutActiveProg_exec copied.flatten s₆ hw1
    (by have hs : 4 * aug + 3 < 2 ^ w := hsize; omega)
    ((hk₆.1 647 (by decide)).trans (by simp [s₅])) ha₆
  have hCopiedLength : copied.length = 2 * n := by dsimp only [copied]; rw [gm06SplitRotationRows_length, hrows]
  have hCopiedDarts : copied.flatten.length ≤ 2 * rows.flatten.length := gm06SplitRotationRows_length_le marks rows
  refine ⟨sf, t₁ + (t₂ + (8 + (t₄ + (8 + (t₆ + tf))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ hef))))), ?_,
    hk₀₆.trans hkf
      (by simp [gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp [gm06CutDataArrs]),
    ?_, ?_, ?_, ?_⟩
  · rw [hrows] at ht₄
    rw [hCopiedLength] at ht₆
    dsimp only [aug] at ht₄ ht₆ htf
    nlinarith only [ht₁, ht₂, ht₄, ht₆, htf, hCopiedDarts]
  · have h625 : sf.arrs 625 = s₄.arrs 625 := (hkf.2 625 (by decide)).trans (hk₆.2 625 (by decide))
    have h655 : sf.regs 655 = s₄.regs 655 := (hkf.1 655 (by decide)).trans (hk₆.1 655 (by decide))
    simpa only [gm06CutDataOfLinkage, gm06CutRowsResult, h625, h655] using hrows₄
  · exact (hkf.2 626 (by decide)).trans ho₆
  · simpa only [gm06CutDataOfLinkage, gm06CutActiveDarts] using haf
  · exact (hkf.2 629 (by decide)).trans ((hk₆.2 629 (by decide)).trans ((hk₄.2 629 (by decide)).trans hv₂))

/-- The computed rotation slots and origin-label space retain their
fixed permanent sizes, and live vertices grow by at most a factor two. -/
theorem gm06CutDataOfLinkage_sizes (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    data.rotations.length = 2 * rows.length ∧
      data.origins.length = 4 * (m + inner.length + outer.length) ∧ data.vertices.length ≤ 2 * live.length := by
  exact ⟨gm06SplitRotationRows_length _ _, gm06CutOrigins_length _ _, gm06CutVertices_length_le _ _⟩

/-- Active labels are exactly the copied outgoing ends in the induced rows. -/
theorem gm06CutDataOfLinkage_active_iff (n m : ℕ) (origins : List ℕ) (paths : List (List ℕ))
    (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ) (d : ℕ) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    d ∈ data.activeDarts ↔ d < 4 * (m + inner.length + outer.length) ∧ d ∈ data.rotations.flatten :=
  gm06CutActiveDarts_mem_iff _ _ _

/-- The complete finite-data construction has a fixed quadratic
bound in its input list and permanent label-space sizes. -/
theorem gm06CutData_cost_le_polynomial (n m k p c l r d : ℕ) :
    134 + 58 * n + 23 * k + 56 * p + 31 * c + 110 * l + 2 * r +
      n * (6000 + 26 * (m + c)) + 6076 * d + 208 * (m + c) ≤
      100000 * (n + m + c + k + p + l + r + d + 1) ^ 2 := by
  let N := n + m + c + k + p + l + r + d + 1
  have hn : n ≤ N := by dsimp only [N]; omega
  have hmc : m + c ≤ N := by dsimp only [N]; omega
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hcross : n * (m + c) ≤ N * N := Nat.mul_le_mul hn hmc
  have hlinear : 134 + 58 * n + 23 * k + 56 * p + 31 * c + 110 * l + 2 * r +
      6000 * n + 6076 * d + 208 * (m + c) ≤ 10000 * N := by
    dsimp only [N]
    omega
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have he : 134 + 58 * n + 23 * k + 56 * p + 31 * c + 110 * l + 2 * r +
      n * (6000 + 26 * (m + c)) + 6076 * d + 208 * (m + c) =
      (134 + 58 * n + 23 * k + 56 * p + 31 * c + 110 * l + 2 * r + 6000 * n + 6076 * d + 208 * (m + c)) +
        26 * (n * (m + c)) := by ring
  rw [he]
  change _ ≤ 100000 * N ^ 2
  rw [pow_two]
  omega

end GraphMinor.Compute
