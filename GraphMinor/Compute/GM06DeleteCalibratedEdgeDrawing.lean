module

public import GraphMinor.Compute.GM06DeleteCalibratedEdge
public import GraphMinor.GM06.Section5SignedRotationClockwise
public import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section5DeletedMaskGraph

/-!
# Correctness of a clockwise deletion at an initial vertex

The signed cuff and given path labels interpret the ordinary
rotation row. Their proved finite crossing criterion identifies
the calibrated scan with the corrected clockwise side condition.
Clearing a selected bit gives precisely the proper deleted drawing
and retains the supplied linkage. On failure every active edge
fails the clockwise test. This is the Reduction 1 branch of
VI (5.7), page 133, with its actual RAM execution and time bound.
-/

public section
namespace GraphMinor.Compute
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06 unitInterval

/-- The calibrated RAM deletion at a supplied initial vertex either
excludes all clockwise edges or performs an actual Reduction 1. -/
theorem gm06DeleteCalibratedEdgeProg_drawing
    {w n : ℕ} (rot active : ℕ)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
    (edge : Fin tagged.length → Set ClosedCylinder)
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (a b c : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)))
    (d : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)) → Circle)
    (hd : ∀ e, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d e)) ∈ range (spoke γ e.1))
    (ha : a.1.2 = true) (hc : c.1.2 = false)
    (haAngle : ∀ t, γ a.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k)))
    (hcAngle : ∀ t, γ c.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k)))
    (hb : b.1.1 ∈ (cylinderSphereDrawing (L.pathDrawing i)).E)
    (hinj : Set.InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun u v => circleStdCoord.angle (z u) < circleStdCoord.angle (z v)))
    (p q r : ℕ) (hpx : p ∈ xs) (hqx : q ∈ xs) (hrx : r ∈ xs)
    (hzp : z p = d a) (hzq : z q = d b) (hzr : z r = d c)
    (hlabel : ∀ (j : Fin tagged.length), tagged[j].2 = 1 → ∀ w : Circle,
      polarRimMap Φ w ∈ cylinderToSphere '' edge j ↔
        ∃ u ∈ xs, z u = w ∧ (u = 2 * j.val ∨ u = 2 * j.val + 1))
    (st : State) (hw : 2 < 2 ^ w) (hn : xs.length < 2 ^ w)
    (hx : ∀ u ∈ xs, u < 2 ^ w) (hnd : xs.Nodup)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ t ∈ tagged, t.2 ≤ 1)
    (hrot : st.arrs rot = xs) (hactive : st.arrs active = tagged.map Prod.snd)
    (h36 : st.regs 36 = p) (h37 : st.regs 37 = q) (h39 : st.regs 39 = r) :
    ∃ st' t, Exec w (gm06DeleteCalibratedEdgeProg rot active) st st' t ∧
      t ≤ 61 + 39 * xs.length + tagged.length * (120 + 104 * xs.length) ∧
      TwoPaths.Keeps [36, 37, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60] [active] st st' ∧
      ((st'.regs 60 = 0 ∧ st'.arrs active = tagged.map Prod.snd ∧
        ∀ e ∈ G.E, ¬ IsClockwiseInitialEdge L i e) ∨
       ∃ (j : Fin tagged.length) (M : CylinderLinkage k (G.deleteEdge (edge j))),
        st'.regs 60 = 1 ∧ st'.regs 55 = j.val ∧ tagged[j].2 = 1 ∧
        st'.arrs active = (tagged.map Prod.snd).set j.val 0 ∧
        IsCylinderSection5Drawing k (G.deleteEdge (edge j)) ∧
        Section5Reduction1Step k G L (G.deleteEdge (edge j)) M ∧
        M.pathDrawing = L.pathDrawing ∧ M.curve = L.curve ∧
        (∀ u : Fin tagged.length, (st'.arrs active)[u.val]? = some 1 →
          (G.deleteEdge (edge j)).toGraph.IsLink
            (edge u) (vertex tagged[u].1.1) (vertex tagged[u].1.2)) ∧
        (∀ e ∈ (G.deleteEdge (edge j)).E,
          ∃ u : Fin tagged.length, (st'.arrs active)[u.val]? = some 1 ∧ edge u = e) ∧
        (st'.arrs active).count 1 + 1 = (tagged.map Prod.snd).count 1) := by
  obtain ⟨_, _, _, htest⟩ := clockwise_edge_iff_calibrated_signed_rotation
    edge (fun j => tagged[j].2 = 1) L hG hGF hbdF hθ i hγ hp a b c d hd ha hc
      haAngle hcAngle hb (fun j hj => (hlinks j hj).edge_mem) xs z hz hs p q r
      hpx hqx hrx hzp hzq hzr hlabel
  obtain ⟨st', t, hex, ht, hframe, hout⟩ := gm06DeleteCalibratedEdgeProg_exec
    rot active xs (tagged.map Prod.snd) p q r st hw hn hx hnd hpx hqx hrx
      (by simpa only [List.length_map] using hm)
      (by simpa only [List.forall_mem_map] using hbits) hrot hactive h36 h37 h39
  refine ⟨st', t, hex, by simpa only [List.length_map] using ht, hframe, ?_⟩
  rcases hout with ⟨hflag, hmask, hnone⟩ | ⟨hflag, j, hj, hpos, hmask, hjactive, hsector, hprogress⟩
  · left
    refine ⟨hflag, hmask, ?_⟩
    intro e he hcw
    obtain ⟨j, hjactive, hje⟩ := hcover e he
    have hjbound : j.val < (tagged.map Prod.snd).length := by simpa using j.isLt
    apply hnone j.val hjbound
    refine ⟨by simpa using hjactive, ?_⟩
    exact (htest j hjactive).mp (hje.symm ▸ hcw)
  · have hj' : j < tagged.length := by simpa only [List.length_map] using hj
    let v : Fin tagged.length := ⟨j, hj'⟩
    have hvactive : tagged[v].2 = 1 := by simpa [v] using hjactive
    have hcw := (htest v hvactive).mpr hsector
    obtain ⟨M, hG', hRed, hpaths, hcurves⟩ :=
      exists_reduction1_on_deleted_drawing L hG (hlinks v hvactive).edge_mem hcw
    obtain ⟨hnewLinks, hnewCover⟩ :=
      deleted_mask_links_and_cover G tagged vertex edge hinj hlinks hcover v hvactive
    right
    refine ⟨v, M, hflag, hpos, hvactive, hmask, hG', hRed, hpaths, hcurves, ?_, ?_, hprogress⟩
    · intro u hu
      apply hnewLinks u
      rw [hmask] at hu
      have hbound : u.val < ((tagged.map Prod.snd).set j 0).length := by
        simpa only [List.length_set, List.length_map] using u.isLt
      rw [List.getElem?_eq_getElem hbound] at hu
      exact Option.some.inj hu
    · intro e he
      obtain ⟨u, hu, hue⟩ := hnewCover e he
      refine ⟨u, ?_, hue⟩
      rw [hmask]
      have hbound : u.val < ((tagged.map Prod.snd).set j 0).length := by
        simpa only [List.length_set, List.length_map] using u.isLt
      rw [List.getElem?_eq_getElem hbound, hu]

end GraphMinor.Compute
