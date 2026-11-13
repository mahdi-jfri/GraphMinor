module

public import GraphMinor.Compute.GM06CutRotationProgram
import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the current core into the cut workspace

The loop of VI (5.7), page 133, keeps rotations, ordinary endpoints,
given paths and the two cuffs in arrays 4, 3, 8, 6 and 7. The cut
program reads copies in its reserved workspace. This adapter copies
exactly those five arrays and loads the fixed original vertex and
edge-label counts. It then calls the proved cut-rotation program.
All core arrays and the loop bit are preserved. The adapter does
not read a precomputed cut, incidence table or region row.
-/

public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

private theorem copy_cut_field_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (xs : List ℕ) (s : State) (hw : 1 < 2 ^ w) (hlen : xs.length < 2 ^ w)
    (hwords : ∀ x ∈ xs, x < 2 ^ w) (hsrc : s.arrs src = xs) :
    ∃ s' t, Exec w (copyArrCmd src dst) s s' t ∧ t ≤ 22 * xs.length + 10 ∧
      Keeps [7, 8, 9, 11] [dst] s s' ∧ s'.arrs dst = xs := by
  obtain ⟨s', t, he, ht, hout, hr, ha⟩ := copyArrCmd_exec src dst hne hw
    (hsrc.symm ▸ hlen) (by simpa only [hsrc] using hwords)
  refine ⟨s', t, he, by simpa only [hsrc] using ht, ⟨?_, ?_⟩, hout.trans hsrc⟩
  · intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    exact hr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2
  · intro a ha'
    exact ha a (by simpa only [List.mem_singleton] using ha')

/-- Copy the current primitive arrays and fixed counts to the
reserved cut-program inputs. All edge labels keep their original base. -/
@[expose] def gm06LoadCurrentCutInputsProg : Cmd :=
  .seq (copyArrCmd 4 600)
    (.seq (copyArrCmd 3 601)
      (.seq (copyArrCmd 8 608)
        (.seq (copyArrCmd 6 609)
          (.seq (copyArrCmd 7 610)
            (.seq (.assign 648 (.reg 100)) (.assign 649 (.len 12)))))))

/-- The adapter supplies the cut workspace with exact copies of all
five current fields, with a linear time bound and a full core frame. -/
theorem gm06LoadCurrentCutInputsProg_exec {w n m : ℕ}
    (origins inner outer : List ℕ) (rows paths : List (List ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hm : m < 2 ^ w)
    (hoLen : origins.length < 2 ^ w) (hoWords : ∀ x ∈ origins, x < 2 ^ w)
    (hiLen : inner.length < 2 ^ w) (hiWords : ∀ x ∈ inner, x < 2 ^ w)
    (htLen : outer.length < 2 ^ w) (htWords : ∀ x ∈ outer, x < 2 ^ w)
    (hrLen : (gm06EncodeRows rows).length < 2 ^ w)
    (hrWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h3 : s.arrs 3 = origins)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h6 : s.arrs 6 = inner) (h7 : s.arrs 7 = outer)
    (h100 : s.regs 100 = n) (h12 : (s.arrs 12).length = m) :
    ∃ sf t, Exec w gm06LoadCurrentCutInputsProg s sf t ∧
      t ≤ 54 + 22 * ((gm06EncodeRows rows).length + origins.length +
        (gm06EncodeRows paths).length + inner.length + outer.length) ∧
      Keeps [7, 8, 9, 11, 648, 649] [600, 601, 608, 609, 610] s sf ∧
      sf.arrs 600 = gm06EncodeRows rows ∧ sf.arrs 601 = origins ∧
      sf.arrs 608 = gm06EncodeRows paths ∧ sf.arrs 609 = inner ∧ sf.arrs 610 = outer ∧
      sf.regs 648 = n ∧ sf.regs 649 = m := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, h600⟩ := copy_cut_field_exec 4 600 (by decide)
    (gm06EncodeRows rows) s hw hrLen hrWords h4
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h601⟩ := copy_cut_field_exec 3 601 (by decide)
    origins s₁ hw hoLen hoWords ((hk₁.2 3 (by decide)).trans h3)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h608⟩ := copy_cut_field_exec 8 608 (by decide)
    (gm06EncodeRows paths) s₂ hw hpLen hpWords
    ((hk₂.2 8 (by decide)).trans ((hk₁.2 8 (by decide)).trans h8))
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, h609⟩ := copy_cut_field_exec 6 609 (by decide)
    inner s₃ hw hiLen hiWords
    ((hk₃.2 6 (by decide)).trans ((hk₂.2 6 (by decide)).trans ((hk₁.2 6 (by decide)).trans h6)))
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, h610⟩ := copy_cut_field_exec 7 610 (by decide)
    outer s₄ hw htLen htWords
    ((hk₄.2 7 (by decide)).trans ((hk₃.2 7 (by decide)).trans
      ((hk₂.2 7 (by decide)).trans ((hk₁.2 7 (by decide)).trans h7))))
  let R := [7, 8, 9, 11, 648, 649]
  let A := [600, 601, 608, 609, 610]
  have hk : Keeps R A s s₅ :=
    ((((hk₁.mono (by simp [R]) (by simp [A])).trans hk₂ (by simp [R]) (by simp [A])).trans
      hk₃ (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])).trans
      hk₅ (by simp [R]) (by simp [A])
  have h100' : s₅.regs 100 = n := (hk.1 100 (by decide)).trans h100
  have h12' : (s₅.arrs 12).length = m := congrArg List.length (hk.2 12 (by decide)) |>.trans h12
  let s₆ := s₅.setReg 648 n
  let s₇ := s₆.setReg 649 m
  have he₆ : Exec w (.assign 648 (.reg 100)) s₅ s₆ 2 := .assign (eval_reg h100' hn)
  have he₇ : Exec w (.assign 649 (.len 12)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₆, h12', hm])
  refine ⟨s₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (2 + 2))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))), by omega,
    (hk.setReg (by simp [R]) _).setReg (by simp [R]) _, ?_, ?_, ?_, ?_, ?_,
    by simp [s₇, s₆], by simp [s₇]⟩
  · exact (hk₅.2 600 (by decide)).trans ((hk₄.2 600 (by decide)).trans
      ((hk₃.2 600 (by decide)).trans ((hk₂.2 600 (by decide)).trans h600)))
  · exact (hk₅.2 601 (by decide)).trans ((hk₄.2 601 (by decide)).trans ((hk₃.2 601 (by decide)).trans h601))
  · exact (hk₅.2 608 (by decide)).trans ((hk₄.2 608 (by decide)).trans h608)
  · exact (hk₅.2 609 (by decide)).trans h609
  · exact h610

/-- Build the cut rotations directly from the current core fields. -/
@[expose] def gm06CurrentCutRotationProg : Cmd :=
  .seq gm06LoadCurrentCutInputsProg gm06CutRotationProg

/-- The current-core adapter and the actual helper program compute
precisely the pure cut rotations. They preserve every core array and
the loop bit in register 329, including on disconnected inputs. -/
theorem gm06CurrentCutRotationProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 4 * (m + inner.length + outer.length) < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hrows : rows.length = n) (hnd : ∀ row ∈ rows, row.Nodup)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length))
    (hpathCode : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h3 : s.arrs 3 = origins)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h6 : s.arrs 6 = inner) (h7 : s.arrs 7 = outer)
    (h100 : s.regs 100 = n) (h12 : (s.arrs 12).length = m) :
    ∃ sf t, Exec w gm06CurrentCutRotationProg s sf t ∧
      t ≤ 110 + 4 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) + 2 * (gm06EncodeRows rows).length +
        n * (6000 + 26 * (m + inner.length + outer.length)) + 6000 * rows.flatten.length +
        22 * ((gm06EncodeRows rows).length + origins.length +
          (gm06EncodeRows paths).length + inner.length + outer.length) ∧
      Keeps ([7, 8, 9, 11, 648, 649] ++ gm06CutRotationRegs)
        ([600, 601, 608, 609, 610] ++ [611, 614, 615, 616, 620, 621, 623, 624, 625]) s sf ∧
      (∀ a < 600, sf.arrs a = s.arrs a) ∧ sf.regs 329 = s.regs 329 ∧
      gm06CutRowsResult sf = gm06EncodeRows
        (gm06CutAlongLinkageRotations n m origins paths inner outer rows) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, h600, h601, h608, h609, h610, h648, h649⟩ :=
    gm06LoadCurrentCutInputsProg_exec origins inner outer rows paths s (by omega) hn (by omega)
      (by omega) (fun v hv' => (hv v hv').trans hn) (by omega)
      (fun v hv' => (hci v hv').trans hn) (by omega) (fun v hv' => (hco v hv').trans hn)
      (by omega) hrotWords hpathCode hpathWords h4 h3 h8 h6 h7 h100 h12
  obtain ⟨sf, t₂, he₂, ht₂, hk₂, hout⟩ := gm06CutRotationProg_exec
    origins paths inner outer rows s₁ hw hn hsize horig hv hd hci hco hrows hnd hkeys
      hpathCode hpathWords hrotFit hrotWords h600 h601 h608 h609 h610 h648 h649
  let R := [7, 8, 9, 11, 648, 649] ++ gm06CutRotationRegs
  let A := [600, 601, 608, 609, 610] ++ [611, 614, 615, 616, 620, 621, 623, 624, 625]
  have hk : Keeps R A s sf := (hk₁.mono (by simp [R]) (by simp [A])).trans hk₂
    (by intro r hr; exact List.mem_append_right _ hr) (by simp [A])
  refine ⟨sf, t₁ + t₂, .seq he₁ he₂, by omega, hk, ?_, hk.1 329 (by decide), hout⟩
  intro a ha
  apply hk.2 a
  have hlarge : ∀ b ∈ A, 600 ≤ b := by decide
  exact fun hb => (Nat.not_le_of_gt ha) (hlarge a hb)

end GraphMinor.Compute
