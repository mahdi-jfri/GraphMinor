module

public import GraphMinor.GM08.Section15Tube
public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15ShortFraming
import GraphMinor.GM08.Section15CylinderCut
import GraphMinor.GM08.Section15ArcPullback
import GraphMinor.GM08.Section15LabelledCut
import GraphMinor.GM08.Section15RelabelQuotient
import GraphMinor.GM08.Section15GraftIsoEmbedding
import GraphMinor.GM08.Section18Map

/-!
# Short tubular grafts come from bounded-index disc grafts

Choose a framing attaining the graft length. Put all roots on actual
cylinder cuffs, then cut a short normal arc into a disc. The labelled
cut graft has the required index bound. Relabel its finite vertices
and identify the paired roots to recover a graft isomorphic to the
original. This proves the inclusion used in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- A tubular graft of index at most `m` and length below `s` is
isomorphic to a member of `W(ℬ)`, where `ℬ` consists of disc grafts of
index at most `m + 2s`. This is the short-tube inclusion in Graph Minors
VIII (15.4), page 282. The isomorphism only changes finite labels. -/
theorem mem_iso_W_disc_of_tubularLength_lt {α : Type u} {β : Type v}
    [Infinite α] {X : Graft α β} {m s : ℕ} (hX : IsTubularGraft X)
    (hlength : tubularLength X < s) (hindex : X.index ≤ m) :
    X ∈ isoGraftClass (WGraftClass
      {B : Graft α β | B.index ≤ m + 2 * s ∧ EmbedsGraft ClosedUnitDisc B}) := by
  classical
  obtain ⟨S, tS, τ, ⟨fr⟩, hlen⟩ := hX.exists_framing_tubularLength
  have hs : τ.length < s := by rwa [hlen]
  obtain ⟨T, tT, hT, gd, C, D, J, a, b, hC, hD, hCD, hJ, ha, hb, hbd, hn, hcount⟩ :=
    fr.exists_short_cylinder_drawing hs
  have : Nonempty T := hT.nonempty
  have : T2Space T := hT.t2Space
  have hab : a ≠ b := fun he => disjoint_left.mp (cuffs_disjoint hC hD hCD) ha (he ▸ hb)
  obtain ⟨Y, tY, ψ, hY, hdisc, hc, _⟩ :=
    exists_disc_cut_of_cylinder_arc hT hC hD hCD ha hb hJ hbd
  have hcut := GM07.IsCutAlongSet.of_isCutting hY hT.1 hJ.isCompact.isClosed hc
  obtain ⟨H, hp, hH, he⟩ :=
    exists_pullback_drawing_of_normal_arc hT.1 hab hJ hbd.subset hcut gd.drawing gd.isProper hn
  obtain ⟨A, hAdraw, hAindex, f, hquot, hf, hroot⟩ :=
    exists_labelled_graft_of_arc_cut hT.1 gd hcut hc H hp hH he
  obtain ⟨eD⟩ := hdisc
  have : Nonempty Y := by
    have : Nonempty ClosedUnitDisc := ⟨⟨0, by simp [ClosedUnitDisc]⟩⟩
    exact ⟨(eD (Classical.arbitrary ClosedUnitDisc)).1⟩
  obtain ⟨B, hAB, hBindex, n, Z, hchain, hZX⟩ :=
    exists_relabelled_vertexIdChain A X f hquot hf hroot
  have hBdraw : EmbedsGraft ClosedUnitDisc B := by
    obtain ⟨bdraw⟩ := embedsGraft_of_isGraftIso hAB hAdraw
    let e : Y ≃ₜ ClosedUnitDisc := (Homeomorph.Set.univ Y).symm.trans eD.symm
    exact ⟨mapGraftDrawing e bdraw⟩
  have hBbound : B.index ≤ m + 2 * s := by
    rw [hBindex]
    apply hAindex.trans
    exact Nat.add_le_add hindex (Nat.mul_le_mul_left 2 (by
      rw [inter_comm]
      exact Nat.le_of_lt hcount))
  refine ⟨Z, mem_WGraftClass_of_obtainedByVertexIdChain ⟨hBbound, hBdraw⟩ hchain, hZX⟩

end GraphMinor.GM08
