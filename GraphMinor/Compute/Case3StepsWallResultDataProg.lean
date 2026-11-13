module

public import GraphMinor.Compute.Case3StepsRelabelWallProg
public import GraphMinor.Compute.Case3StepsPushMemberProg
public import GraphMinor.Compute.Case3StepsOriginalBitsProg
public import GraphMinor.Compute.Case3StepsCompactImageWall

/-!
# Computing the wall result data of one member call

The returned wall is renamed through the member inverse list. The member
multigraph and its vertex and boundary bitsets are then restored to original
ambient labels. The wall has a representative on exactly the compact graph
type required by output (b), and its moved graph lies inside the member.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Write the four original-label data arrays for a wall returned by (7.2). -/
def case3WallResultDataProg (h : ℕ) : Cmd :=
  .seq (case3RelabelWallProg h)
    (.seq case3PushMemberProg (.seq case3OriginalMemberBitsProg case3OriginalBoundaryBitsProg))

/-- The wall-result data are computed exactly, with linear copying work
and preserved lower registers. No rural-division or boundary fact is assumed
by the copying program; those facts are proved for the selected member. -/
theorem case3WallResultDataProg_exec {w h N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (T bd : Finset (Fin S.card)) (hbd : bd.card ≤ 3)
    (W : WallOfHeight h (D.induce (T.orderEmbOfFin rfl))) (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid)
    (hw : 6 < 2 ^ w) (hcard : S.card + 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    (hlen : (1 :: W.encList).length < 2 ^ w) (hwords : ∀ x ∈ W.encList, x < 2 ^ w)
    {s : State} (hwall : s.arrs 129 = 1 :: W.encList) (hD : s.arrs 39 = D.enc)
    (hrank : (s.arrs 2).length = N)
    (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin S.card, (s.arrs 32).getD i.1 0 = (S.orderEmbOfFin rfl i).1)
    (hmember : s.arrs 31 = (case3BoundaryVertices T).map Fin.val ++ List.replicate (S.card - T.card) 0)
    (hcount : s.regs 62 = T.card) (hkey : s.arrs 25 = case3BoundaryKey bd)
    (horig : s.arrs 47 = List.ofFn (fun i : Fin T.card =>
      (S.orderEmbOfFin rfl (T.orderEmbOfFin rfl i)).1)) :
    ∃ s' t, Exec w (case3WallResultDataProg h) s s' t ∧
      t ≤ 60 * W.encList.length + 38 * D.numActivePairs + 14 * T.card + 2 * N + 124 ∧
      let P := case3PushMultigraph S D
      let V := T.image (S.orderEmbOfFin rfl)
      s'.arrs 54 = P.enc ∧ IsBitSet V 55 s' ∧ IsBitSet (bd.image (S.orderEmbOfFin rfl)) 56 s' ∧
      (∃ W_A : WallOfHeight h (P.deleteVerticesCompact Vᶜ), W_A.IsValid ∧
        ∃ hnext : (W_A.moveOrig P (compactEmb Vᶜ)).IsValid,
          ((W_A.moveOrig P (compactEmb Vᶜ)).toGMWall h2 heven hnext).graph ≤
            P.toGMDigraph.toGraph.induce V.toNatSet ∧
          s'.arrs 46 = (W_A.moveOrig P (compactEmb Vᶜ)).encList) ∧
      (∀ a, a ≠ 46 → a ≠ 54 → a ≠ 55 → a ≠ 56 → s'.arrs a = s.arrs a) ∧
      (∀ r < 90, s'.regs r = s.regs r) := by
  have hTcard : T.card ≤ S.card := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
  let P := case3PushMultigraph S D
  obtain ⟨s₁, t₁, hex₁, ht₁, hwall₁, harr₁, hreg₁⟩ := case3RelabelWallProg_exec (w := w) (s := s) W P
    (fun i => S.orderEmbOfFin rfl (T.orderEmbOfFin rfl i)) (by omega) (by omega) hN hlen hwords hwall horig
  obtain ⟨s₂, t₂, hex₂, ht₂, hD₂, harr₂, hreg₂⟩ := case3PushMemberProg_exec (w := w) (s := s₁) S D (by omega) (by omega) hN hA he
    ((harr₁ 39 (by decide)).trans hD)
    (by rw [harr₁ 2 (by decide)]; exact hrank)
    (by rw [harr₁ 32 (by decide)]; exact hlistlen)
    (by intro i; rw [harr₁ 32 (by decide)]; exact hlist i)
  obtain ⟨s₃, t₃, hex₃, ht₃, hV₃, harr₃, hreg₃⟩ := case3OriginalMemberBitsProg_exec (w := w) (s := s₂) T (S.orderEmbOfFin rfl)
    (by omega) hcard hN
    (by rw [harr₂ 2 (by decide), harr₁ 2 (by decide)]; exact hrank)
    ((harr₂ 31 (by decide)).trans ((harr₁ 31 (by decide)).trans hmember))
    (by rw [hreg₂ 62 (by decide), hreg₁ 62 (by decide)]; exact hcount)
    (by rw [harr₂ 32 (by decide), harr₁ 32 (by decide)]; exact hlistlen)
    (by intro i; rw [harr₂ 32 (by decide), harr₁ 32 (by decide)]; exact hlist i)
  obtain ⟨s₄, t₄, hex₄, ht₄, hbd₄, harr₄, hreg₄⟩ := case3OriginalBoundaryBitsProg_exec (w := w) (s := s₃) bd hbd (S.orderEmbOfFin rfl)
    hw (by omega) hN
    (by rw [harr₃ 2 (by decide), harr₂ 2 (by decide), harr₁ 2 (by decide)]; exact hrank)
    ((harr₃ 25 (by decide)).trans ((harr₂ 25 (by decide)).trans ((harr₁ 25 (by decide)).trans hkey)))
    (by rw [harr₃ 32 (by decide), harr₂ 32 (by decide), harr₁ 32 (by decide)]; exact hlistlen)
    (by intro i; rw [harr₃ 32 (by decide), harr₂ 32 (by decide), harr₁ 32 (by decide)]; exact hlist i)
  have hex : Exec w (case3WallResultDataProg h) s s₄ (t₁ + (t₂ + (t₃ + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), hex, by omega, ?_, ?_, hbd₄, ?_, ?_, ?_⟩
  · exact (harr₄ 54 (by decide)).trans ((harr₃ 54 (by decide)).trans hD₂)
  · exact hV₃.of_arr_eq (harr₄ 55 (by decide))
  · obtain ⟨W_A, hWA, hnext, hle, heq⟩ := case3CompactImageWall_exists_le S D T W h2 heven hW
    refine ⟨W_A, hWA, hnext, hle, ?_⟩
    rw [harr₄ 46 (by decide), harr₃ 46 (by decide), harr₂ 46 (by decide), hwall₁, heq]
  · intro a h46 h54 h55 h56
    exact (harr₄ a h56).trans ((harr₃ a h55).trans ((harr₂ a h54).trans (harr₁ a h46)))
  · intro r hr
    rw [hreg₄ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega)
        (by dsimp only [Reg] at *; omega),
      hreg₃ r (by dsimp only [Reg] at *; omega) (by dsimp only [Reg] at *; omega), hreg₂ r hr,
      hreg₁ r (by dsimp only [Reg] at *; omega)]

end GraphMinor.Compute
