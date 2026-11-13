module

public import GraphMinor.GM12.Defs
import GraphMinor.GM12.Section2NormalEntryExistence
import GraphMinor.GM12.Section2EntryUnique
import GraphMinor.GM12.Section2EntryEnds
import GraphMinor.GM11.Section7b

/-!
# The omitted entry-edge existence and uniqueness lemma

XII, page 243, omits the proof that the entering edge exists and is
unique. The proved normal-approach construction supplies existence in
both the sector and leaf cases. The entry witness recovers the edge
ends, and the proved XI (7.2) makes the entry-uniqueness argument
unconditional. Reversing the real parameter supplies the exit edge.
The independence of the chosen starting point is included in that
uniqueness argument, whose two witnesses may start at different times.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- The omitted entry-edge lemma in the trace definition of Graph
Minors XII, page 243: an entering edge exists and is unique, independently
of the starting points chosen by its witnesses. -/
theorem existsUnique_entersLike
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R)
    {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃! e : Set S, e ∈ K.E ∧ EntersLike f a c e r v w := by
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  obtain ⟨e, he, hentry⟩ := exists_entersLike hS hrad hK.2.2 hE hv hr hw hwV hf hac hfc hinside
  refine ⟨e, ⟨he, hentry⟩, ?_⟩
  intro e' he'
  have hends := (entersLike_isLink hS hrad hr hv hw hwV he hfc hentry).2.2.2
  have hends' := (entersLike_isLink hS hrad hr hv hw hwV he'.1 hfc he'.2).2.2.2
  exact entersLike_edge_unique hS inferInstance hK hr hv ⟨hw, hwV⟩
    he'.1 he hends' hends hf hfc hinside he'.2 hentry

/-- The exit form of the omitted lemma of Graph Minors XII, page 243,
proved by reversing the real parameter in the entry form. -/
theorem existsUnique_leavesLike
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R)
    {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfa : f a = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃! e : Set S, e ∈ K.E ∧ LeavesLike f a c e r v w := by
  change ∃! e : Set S, e ∈ K.E ∧ EntersLike (fun t => f (-t)) (-c) (-a) e r v w
  apply existsUnique_entersLike hS hK hE hv hr hw hwV
    (hf.comp continuous_neg) (by linarith : -c < -a)
  · simpa only [Function.comp_apply, neg_neg] using hfa
  · intro t ht
    apply hinside
    constructor <;> linarith [ht.1, ht.2]

end GraphMinor.GM12
