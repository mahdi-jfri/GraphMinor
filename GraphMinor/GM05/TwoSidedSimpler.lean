module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.CutConnected
import GraphMinor.Surface.CutOArc

/-!
# A connected two-sided circle cut is simpler

For the connected-cut case of Graph Minors V, (8.10), use the library's
normal-word calculation for pasting the two lifted boundary circles.
It adds a handle or two crosscaps and removes two cuffs. In either case
the connected surface before pasting is simpler. This retains the
actual cutting map and its two boundary lifts.
-/

public section

namespace GraphMinor.GM05

open Set Topology Function Surface

universe u

/-- The connected two-sided case of the library circle-cut proof,
with the cutting map and boundary lifts retained for the later capping
construction in Graph Minors V, (8.10). -/
theorem simpler_two_sided_cut {Y S : Type u} [TopologicalSpace Y]
    [TopologicalSpace S] [T2Space S] [ConnectedSpace Y] (hY : IsSurface Y)
    {ψ : Y → S} {X X' : Set Y} {C : Set S}
    (hψ : IsCutting ψ C) (hdX : Disjoint X X') (hunX : X ∪ X'=ψ ⁻¹' C)
    (hOX : IsOArc X) (hOX' : IsOArc X') (b1 : BijOn ψ X C) (b2 : BijOn ψ X' C) :
    IsSimplerThan Y S := by
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  have hdcuff := cuff_statement Y hY
  have ne₁ : X.Nonempty := by obtain ⟨e⟩ := hOX; exact ⟨_,(e 1).2⟩
  have ne₂ : X'.Nonempty := by obtain ⟨e⟩ := hOX'; exact ⟨_,(e 1).2⟩
  obtain ⟨x,hx⟩ := ne₁
  obtain ⟨y,hy⟩ := ne₂
  let : Nonempty S := ⟨ψ x⟩
  have hXb : X ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inl hz)
  have hXb' : X' ⊆ bd Y := fun z hz ↦ hψ.2.2.2.2 (hunX ▸ Or.inr hz)
  obtain ⟨a,b,c,⟨e⟩⟩ := classification Y hY inferInstance
  have hC : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨_,hXb hx,rfl⟩
  have hC' : connectedComponentIn (bd Y) y ∈ cuffs Y := ⟨_,hXb' hy,rfl⟩
  obtain ⟨φ₀⟩ := hdcuff.2.2 _ hC
  obtain ⟨φ₀'⟩ := hdcuff.2.2 _ hC'
  have eX := oarc_eq φ₀ hOX (hOX.isPreconnected.subset_connectedComponentIn hx hXb)
  have eX' := oarc_eq φ₀' hOX' (hOX'.isPreconnected.subset_connectedComponentIn hy hXb')
  have hCC : connectedComponentIn (bd Y) x ≠ connectedComponentIn (bd Y) y := by
    intro he
    rw [← eX,← eX'] at he
    exact Set.disjoint_left.mp hdX hx (he ▸ hx)
  obtain ⟨i,hi',j,hj,hij,φ,φ',g,hg,hs,hs'⟩ := exists_two_holes e hC hC' hCC
  obtain ⟨hN,hLf⟩ := erase_erase_facts c i j
  rw [eX,eX'] at hunX
  rw [eX] at b1
  rw [eX'] at b2
  have hdis := cuffs_disjoint hC hC' hCC
  obtain ⟨σ,g',hp⟩ := loop_two_aux hY hψ hC' (hdcuff.2.2 _ hC).isCompact.isClosed
    (hdcuff.2.2 _ hC').isCompact.isClosed hdis hunX b1 b2 φ φ' hij hi' hj hLf hg hs hs'
  replace hp := hp.1
  have hn := nf_blkE (a := a) (b := b) (c := c) hij hi' hj hN hLf σ
  have hlen := length_erase_erase hij hi' hj
  cases σ with
  | false =>
    obtain ⟨w,h5,h6⟩ := hn.1 rfl
    obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
    rw [hlen] at e'
    exact simpler_cut_of_connected (.inl (cutIsSimpler_of_connected e e' (by omega) (by omega) (by omega)))
  | true =>
    obtain ⟨w,h5,h6⟩ := hn.2 rfl
    obtain ⟨e'⟩ := homeo_of_nf hp h5 h6
    rw [hlen] at e'
    exact simpler_cut_of_connected (.inl (cutIsSimpler_of_connected e e' (by omega) (by omega) (by omega)))

end GraphMinor.GM05
