module

public import GraphMinor.GM06.Alg57PersistentRotations
public import GraphMinor.Compute.GM06PruneRotations
import GraphMinor.GM11.EvenCircuit
import GraphMinor.GM11.NiceStatements
import GraphMinor.GM11.Walks

/-!
# Restricting rotation rows after deletions

In VI (5.7), page 133, deleting vertices or edges removes their
directed ends from the current rotations. Every old drawing atom
is contained in a new atom of a subdrawing. Therefore an old polar
chart stays polar after a deletion, with the same positive boundary
and the same directions on retained edges.

Filtering a row by its edge activity consequently gives exactly the
new geometric row. The permanent labels and both auxiliary cuffs
retain their indices. This justifies pruning inactive words after
the mask updates of Reductions 1 and 2.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Every old atom lies inside one atom of a subdrawing. A deleted
open edge is connected and wholly outside the smaller drawing, so
it lies in one of its regions. -/
theorem atom_subset_atom_of_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hHG : H.IsSubdrawing G) : ∀ a ∈ G.A, ∃ b ∈ H.A, a ⊆ b := by
  intro a ha
  rcases ha with (⟨v, hv, rfl⟩ | ha) | ha
  · obtain ⟨b, hb, hvb⟩ := exists_atom H v
    exact ⟨b, hb, singleton_subset_iff.mpr hvb⟩
  · by_cases haH : a ∈ H.E
    · exact ⟨a, Or.inl (Or.inr haH), subset_rfl⟩
    · have hdis : Disjoint a H.U := by
        apply disjoint_left.mpr
        intro x hx hxH
        have hxV : x ∉ H.V := fun hv => (ha.2.1 hx).2 (hHG.1 hv)
        obtain ⟨f, hf, hxf⟩ := H.exists_edge_of_mem hxH hxV
        have heq := G.edge_eq_of_mem ha (hHG.2 hf) hx hxf
        exact haH (heq.symm ▸ hf)
      obtain ⟨x, hx⟩ := ha.2.2.1.nonempty
      obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hx)
      exact ⟨r, Or.inr hr, subset_region hr ha.2.2.1.isConnected.isPreconnected hdis hx hxr⟩
  · obtain ⟨x, hx⟩ := region_nonempty ha
    have hdis : Disjoint a H.U := disjoint_left.mpr fun y hy hyH =>
      region_subset ha hy (hHG.U_subset hyH)
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hx)
    exact ⟨r, Or.inr hr, subset_region hr (region_isPreconnected ha) hdis hx hxr⟩

/-- Deleting drawing atoms merges them without changing the rays
of a polar chart. Its embedding, centre and neighbourhood are fixed. -/
theorem isPolar_of_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hHG : H.IsSubdrawing G) {v : S} {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar G v Φ) :
    IsPolar H v Φ := by
  refine ⟨hp.inj, hp.centre, hp.nhd, ?_⟩
  intro x hx c hc
  obtain ⟨a, ha, hxa, hca⟩ := hp.ray x hx c hc
  obtain ⟨b, hb, hab⟩ := atom_subset_atom_of_subdrawing hHG a ha
  exact ⟨b, hb, hab hxa, hab hca⟩

/-- A retained edge keeps its old parametrization and both old
ends. The subdrawing property retains those ends as vertices. -/
theorem edgePar_of_subdrawing
    {S : Type*} [TopologicalSpace S] [T2Space S] {G H : Drawing S}
    (hHG : H.IsSubdrawing G) {γ : Set S → I → S} (hγ : EdgePar G γ) : EdgePar H γ := by
  refine ⟨fun f hf => hγ.cont f (hHG.2 hf), ?_, ?_,
    fun f hf => hγ.inj f (hHG.2 hf), fun f hf => hγ.image f (hHG.2 hf)⟩
  · intro f hf
    exact (isLink_ends hγ hHG hf false).left_mem
  · intro f hf
    exact (isLink_ends hγ hHG hf false).right_mem

/-- Restricting permanent labels to retained actual edges preserves
the labels and their injectivity. -/
@[expose] def gm06RestrictEdgeLabels
    {S : Type*} [TopologicalSpace S] {G H : Drawing S} (hHG : H.IsSubdrawing G)
    (label : G.E ↪ ℕ) : H.E ↪ ℕ :=
  ⟨fun f => label ⟨f.val, hHG.2 f.property⟩, by
    intro a b hab
    have hh := label.injective hab
    exact Subtype.ext (congrArg (fun f : G.E => f.val) hh)⟩

/-- Removing exactly the inactive directed ends from a row gives
its actual positive rotation in the retained subdrawing. The keep
predicate specifies only the ordinary activity data for each edge. -/
theorem persistent_rotation_row_of_subdrawing
    {G H : Drawing (OnePoint EuclideanPlane)} (hHG : H.IsSubdrawing G)
    (label : G.E ↪ ℕ)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {v : OnePoint EuclideanPlane} {xs : List ℕ}
    (hrow : GM06PersistentRotationRowRep label γ v xs) (keep : ℕ → Bool)
    (hkeep : ∀ (f : G.E) (b : Bool),
      keep (2 * label f + b.toNat) = true ↔ f.val ∈ H.E) :
    GM06PersistentRotationRowRep (gm06RestrictEdgeLabels hHG label) γ v (xs.filter keep) := by
  let label' := gm06RestrictEdgeLabels hHG label
  let oldEnd : halfEdges H γ v → halfEdges G γ v := fun b =>
    ⟨b.val, hHG.2 b.property.1, b.property.2⟩
  have hcode : ∀ b : halfEdges H γ v, gm06PersistentHalfEdgeLabel label' b =
      gm06PersistentHalfEdgeLabel label (oldEnd b) := fun _ => rfl
  have hnewmem : ∀ r, r ∈ xs.filter keep ↔
      ∃ b : halfEdges H γ v, gm06PersistentHalfEdgeLabel label' b = r := by
    intro r
    constructor
    · intro hr
      obtain ⟨hr, hkr⟩ := List.mem_filter.mp hr
      obtain ⟨a, ha⟩ := (hrow.2.1 r).mp hr
      have hk : keep (gm06PersistentHalfEdgeLabel label a) = true := ha.symm ▸ hkr
      have haH : a.val.1 ∈ H.E := (hkeep ⟨a.val.1, a.property.1⟩ a.val.2).mp hk
      let b : halfEdges H γ v := ⟨a.val, haH, a.property.2⟩
      exact ⟨b, ha⟩
    · rintro ⟨b, hb⟩
      apply List.mem_filter.mpr
      have hcb : gm06PersistentHalfEdgeLabel label (oldEnd b) = r := (hcode b).symm.trans hb
      refine ⟨(hrow.2.1 r).mpr ⟨oldEnd b, hcb⟩, ?_⟩
      rw [← hcb]
      exact (hkeep ⟨b.val.1, hHG.2 b.property.1⟩ b.val.2).mpr b.property.1
  refine ⟨hrow.1.filter keep, hnewmem, ?_⟩
  rcases hrow.2.2 with hsmall | ⟨Φ, z, hp, hpos, hzi, hs, hspoke, hlabel⟩
  · exact Or.inl ((List.length_filter_le keep xs).trans hsmall)
  · refine Or.inr ⟨Φ, z, isPolar_of_subdrawing hHG hp, hpos,
      hzi.mono (fun r hr => (List.mem_filter.mp hr).1), hs.filter keep, ?_, ?_⟩
    · intro b t ht
      rw [hcode]
      exact hspoke (oldEnd b) t ht
    · intro f w
      let fOld : G.E := ⟨f.val, hHG.2 f.property⟩
      have hk0 : keep (2 * label fOld) = true := by
        simpa only [Bool.toNat_false, Nat.add_zero] using (hkeep fOld false).mpr f.property
      have hk1 : keep (2 * label fOld + 1) = true :=
        (hkeep fOld true).mpr f.property
      constructor
      · intro hw
        obtain ⟨r, hr, hzr, hcode⟩ := (hlabel fOld w).mp hw
        refine ⟨r, List.mem_filter.mpr ⟨hr, ?_⟩, hzr, hcode⟩
        rcases hcode with h0 | h1
        · exact h0.symm ▸ hk0
        · exact h1.symm ▸ hk1
      · rintro ⟨r, hr, hzr, hcode⟩
        exact (hlabel fOld w).mpr ⟨r, (List.mem_filter.mp hr).1, hzr, hcode⟩

/-- The complete RAM pruning operation produces exactly the positive
rotation rows of a retained subdrawing. Its supplied mask predicates
interpret only which actual edges were retained. -/
theorem gm06PruneCurrentRotationsProg_drawing
    {w : ℕ} {G H : Drawing (OnePoint EuclideanPlane)} (hHG : H.IsSubdrawing G)
    (label : G.E ↪ ℕ)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane} (hγ : EdgePar G γ)
    (mask cuff : List ℕ) (rows : List (List ℕ)) (vertex : Fin rows.length → OnePoint EuclideanPlane)
    (hrot : ∀ v : Fin rows.length, GM06PersistentRotationRowRep label γ (vertex v) rows[v.val])
    (hkeep : ∀ (f : G.E) (b : Bool),
      Compute.gm06KeepActiveDart (Compute.gm06AugmentedActivity mask cuff.length)
        (2 * label f + b.toNat) = true ↔ f.val ∈ H.E)
    (s : Compute.State) (hw : 2 < 2 ^ w)
    (hlen : 4 * (Compute.gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ Compute.gm06EncodeRows rows, x < 2 ^ w)
    (haLen : mask.length + 2 * cuff.length < 2 ^ w) (hbits : ∀ x ∈ mask, x ≤ 1)
    (hd : ∀ row ∈ rows, ∀ d ∈ row, d < 2 * (mask.length + 2 * cuff.length))
    (h4 : s.arrs 4 = Compute.gm06EncodeRows rows) (h12 : s.arrs 12 = mask) (h6 : s.arrs 6 = cuff) :
    ∃ s' t, Compute.Exec w Compute.gm06PruneCurrentRotationsProg s s' t ∧
      t ≤ 27 + 16 * mask.length + 30 * cuff.length +
        rows.length * (260 + 34 * rows.length + 300 * (Compute.gm06EncodeRows rows).length) ∧
      Compute.TwoPaths.Keeps
        [339, 330, 31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
        [30, 25, 27, 29, 4, 28] s s' ∧
      s'.arrs 4 = Compute.gm06EncodeRows
        (Compute.gm06PrunedRotationRows (Compute.gm06AugmentedActivity mask cuff.length) rows) ∧
      EdgePar H γ ∧ ∀ v : Fin rows.length,
        GM06PersistentRotationRowRep (gm06RestrictEdgeLabels hHG label) γ (vertex v)
          ((Compute.gm06PrunedRotationRows (Compute.gm06AugmentedActivity mask cuff.length) rows)[v.val]'
            (by simp only [Compute.gm06PrunedRotationRows, List.length_map]; exact v.isLt)) := by
  obtain ⟨s', t, hex, ht, hk, hout, _, _, _⟩ := Compute.gm06PruneCurrentRotationsProg_exec
    mask cuff rows s hw hlen hwords haLen hbits hd h4 h12 h6
  refine ⟨s', t, hex, ht, hk, hout, edgePar_of_subdrawing hHG hγ, ?_⟩
  intro v
  simpa only [Compute.gm06PrunedRotationRows, List.getElem_map] using
    persistent_rotation_row_of_subdrawing hHG label (hrot v)
      (Compute.gm06KeepActiveDart (Compute.gm06AugmentedActivity mask cuff.length)) hkeep

end GraphMinor.GM06
