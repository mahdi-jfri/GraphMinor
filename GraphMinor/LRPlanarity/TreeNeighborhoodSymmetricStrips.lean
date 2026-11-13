module

public import GraphMinor.LRPlanarity.TreeNeighborhoodStripCoordinates
public import GraphMinor.HP25.Web
import GraphMinor.LRPlanarity.TreeNeighborhoodDrawingStrips

/-!
# One strip for each unordered straight edge

Part IV, Section 7b of the planarity note assigns one strip to each
straight tree piece. To use paths in either orientation, index the strip
construction by unordered drawing edges. A chosen representative supplies
coordinates, while exact endpoint intersections define the attachment
interval at either vertex. The resulting strip family is symmetric.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: the constructed strip family can be indexed
symmetrically by its endpoints, retaining both local attachment properties,
separation, and containment of the whole edge in the local interior. -/
theorem exists_symmetric_straight_strips {V : Type*} [Finite V]
    {G : SimpleGraph V} (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v →
      drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v))
    (angle : ∀ u, {v // G.Adj u v} → ℝ) (directions : V → Finset ℝ) (r : V → ℝ)
    (hangle : ∀ u v, eC (angle u v) =
      ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u))
    (hmem : ∀ u v, angle u v ∈ directions u) (hr : ∀ u, 0 < r u)
    (hlength : ∀ u v, u ≠ v → r u + r v < dist (drawing.pt u) (drawing.pt v))
    (haway : ∀ w u v, G.Adj u v → u ≠ w → v ≠ w → Disjoint
      (vertexPolygonAt (drawing.pt w) (directions w) (r w)) (drawing.line u v)) :
    let P := fun u => vertexPolygonAt (drawing.pt u) (directions u) (r u)
    ∃ R : V → V → Set ℂ,
      (∀ u v, R u v = R v u) ∧
      (∀ u v, G.Adj u v → IsClosedDisc (R u v) ∧
        (∃ a b, IsLineWithEnds (R u v ∩ P u) a b) ∧
        R u v ∩ P u ⊆ discBd (P u) ∧ R u v ∩ P u ⊆ discBd (R u v) ∧
        drawing.line u v ⊆ interior (P u ∪ R u v ∪ P v)) ∧
      (∀ u v, G.Adj u v → ∀ z t, G.Adj z t → s(u,v) ≠ s(z,t) → Disjoint (R u v) (R z t)) ∧
      (∀ u v, G.Adj u v → ∀ z, z ≠ u → z ≠ v → Disjoint (R u v) (P z)) ∧
      (∀ u v, G.Adj u v → ∀ z t, G.Adj z t → s(u,v) ≠ s(z,t) →
        Disjoint (R u v) (drawing.line z t)) := by
  classical
  intro P
  let E := {e : Sym2 V // e ∈ G.edgeSet}
  let source : E → V := fun e => e.val.out.1
  let target : E → V := fun e => e.val.out.2
  have hends : ∀ e : E, s(source e, target e) = e.val := fun e => e.val.out_eq
  have hedge : ∀ e : E, G.Adj (source e) (target e) := by
    intro e
    apply (G.mem_edgeSet).mp
    rw [hends]
    exact e.property
  have hindex : Function.Injective (fun e : E => s(source e, target e)) := by
    intro e f he
    apply Subtype.ext
    simpa only [hends] using he
  obtain ⟨width, _, hsep, hnonincident, hother, hlocal⟩ := exists_straight_drawing_strips
    drawing hstraight source target hedge hindex angle directions r hangle hmem hr hlength
    (fun e w hws hwt => haway w _ _ (hedge e) hws.symm hwt.symm)
  let Rf := fun e : E => orientedStrip (drawing.pt (source e))
    (angle (source e) ⟨target e, hedge e⟩) (r (source e))
    (‖drawing.pt (target e) - drawing.pt (source e)‖ - r (target e)) (width e)
  let R := fun u v => if h : G.Adj u v then Rf ⟨s(u,v), h⟩ else ∅
  have hR : ∀ u v (h : G.Adj u v), R u v = Rf ⟨s(u,v), h⟩ := by
    intro u v h
    exact dite_eq_left h
  have hcomm : ∀ u v, R u v = R v u := by
    intro u v
    by_cases huv : G.Adj u v
    · rw [hR u v huv, hR v u huv.symm]
      congr 1
      exact Subtype.ext Sym2.eq_swap
    · have hvu : ¬G.Adj v u := fun h => huv h.symm
      simp only [R, dite_eq_right huv, dite_eq_right hvu]
  have horient : ∀ u v (h : G.Adj u v),
      (source ⟨s(u,v), h⟩ = u ∧ target ⟨s(u,v), h⟩ = v) ∨
      (source ⟨s(u,v), h⟩ = v ∧ target ⟨s(u,v), h⟩ = u) := by
    intro u v h
    exact Sym2.eq_iff.mp (hends ⟨s(u,v), h⟩)
  refine ⟨R, hcomm, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    let e : E := ⟨s(u,v), huv⟩
    obtain ⟨L, K, a, b, c, d, hS, hL, hK, hI, hJ, hLP, hLS, hKS, hKP, hinside⟩ := hlocal e
    change IsClosedDisc (Rf e) at hS
    change P (source e) ∩ Rf e = L at hI
    change Rf e ∩ P (target e) = K at hJ
    change L ⊆ discBd (P (source e)) at hLP
    change L ⊆ discBd (Rf e) at hLS
    change K ⊆ discBd (Rf e) at hKS
    change K ⊆ discBd (P (target e)) at hKP
    change drawing.line (source e) (target e) ⊆ interior
      (P (source e) ∪ Rf e ∪ P (target e)) at hinside
    rw [hR u v huv]
    rcases horient u v huv with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · change source e = u at hs
      change target e = v at ht
      rw [hs] at hI hLP
      rw [hs, ht] at hinside
      have hRI : Rf e ∩ P u = L := (inter_comm _ _).trans hI
      exact ⟨hS, by rw [hRI]; exact ⟨a,b,hL⟩,
        hRI.symm ▸ hLP, hRI.symm ▸ hLS, hinside⟩
    · change source e = v at hs
      change target e = u at ht
      rw [ht] at hJ hKP
      rw [hs, ht, drawing.line_comm v u] at hinside
      have hU : P v ∪ Rf e ∪ P u = P u ∪ Rf e ∪ P v := by ac_rfl
      rw [hU] at hinside
      exact ⟨hS, by rw [hJ]; exact ⟨c,d,hK⟩,
        hJ.symm ▸ hKP, hJ.symm ▸ hKS, hinside⟩
  · intro u v huv z t hzt hne
    rw [hR u v huv, hR z t hzt]
    apply hsep
    exact fun he => hne (congrArg Subtype.val he)
  · intro u v huv z hzu hzv
    rw [hR u v huv]
    rcases horient u v huv with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact hnonincident ⟨s(u,v), huv⟩ z (hs.symm ▸ hzu) (ht.symm ▸ hzv)
    · exact hnonincident ⟨s(u,v), huv⟩ z (hs.symm ▸ hzv) (ht.symm ▸ hzu)
  · intro u v huv z t hzt hne
    rw [hR u v huv]
    apply hother ⟨s(u,v), huv⟩ z t hzt
    rw [hends]
    exact hne.symm

end GraphMinor.LRPlanarity
