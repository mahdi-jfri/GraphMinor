module

public import GraphMinor.GM12.Defs
import GraphMinor.GM12.Section2EntryUnique
import GraphMinor.GM12.Section2EntryIndependence
import GraphMinor.GM11.Regions

/-!
# Comparing entry intervals with different starting parameters

For XII (2.1), pages 243--244, an entry germ can be read on any
terminal interval of a region visit. Restrict two such intervals
to their common terminal part and apply entry-edge uniqueness.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Two entry descriptions at the same parameter agree even when
their region intervals start at different parameters. -/
theorem entersLike_edge_unique_overlapping_intervals
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {r e e' : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (he' : e' ∈ K.E)
    (hends : closure e ∩ K.V = {v, w}) (hends' : closure e' ∩ K.V = {v, w})
    {f : ℝ → S} (hf : Continuous f) {a b c : ℝ} (hac : a < c) (hbc : b < c)
    (hfc : f c = v) (hfr : ∀ z ∈ Ioo a c, f z ∈ r)
    (hfr' : ∀ z ∈ Ioo b c, f z ∈ r)
    (hentry : EntersLike f a c e r v w) (hentry' : EntersLike f b c e' r v w) : e = e' := by
  have hvE : v ∉ e := fun hz => (he.2.1 hz).2 (hK.2.1.2.1 hv)
  have hwE : w ∉ e := fun hz => (he.2.1 hz).2 hw.2
  have hvE' : v ∉ e' := fun hz => (he'.2.1 hz).2 (hK.2.1.2.1 hv)
  have hwE' : w ∉ e' := fun hz => (he'.2.1 hz).2 hw.2
  have hvw : v ≠ w := fun h => region_subset hr (h.symm ▸ hw.1) (Γ.V_subset_U hv)
  have hmax : max a b < c := max_lt hac hbc
  have hentry₀ := (entersLike_iff_tail_interval (hK.1.2 r hr) hw.1 hvE hwE hvw
    hf (le_max_left a b) hmax hfc hfr).mp hentry
  have hentry₁ := (entersLike_iff_tail_interval (hK.1.2 r hr) hw.1 hvE' hwE' hvw
    hf (le_max_right a b) hmax hfc hfr').mp hentry'
  exact entersLike_edge_unique hS hConn hK hr hv hw he he' hends hends' hf hfc
    (fun z hz => hfr z ⟨(le_max_left a b).trans_lt hz.1, hz.2⟩) hentry₀ hentry₁

end GraphMinor.GM12
