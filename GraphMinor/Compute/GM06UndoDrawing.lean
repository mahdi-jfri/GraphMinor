module

public import GraphMinor.Compute.GM06EdgeMaskData
public import GraphMinor.Compute.GM06RecoverContractions
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import GraphMinor.Compute.GM06ExpandLinkageRows
import GraphMinor.Compute.GM06RestrictedLinkageRows
import GraphMinor.GM06.Alg57RowBounds

/-!
# Recovering output rows through the drawing history

UNDO in Section 18 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
changes output rows only at contractions. A deleted subdrawing is restored without changing the
paths' directed words. A contraction prepends its recorded initial word to its indexed
path. Rerouting the reference linkage changes none of the drawing
or output labels.

The states below contain only drawing and label data. Each inverse
operation is interpreted by its actual subdrawing or its continuous
edge collapse, with the literal endpoint-table update. Induction
through those operations proves output recovery. The existing RAM
history loop computes exactly that induction's row updates.
-/

public section
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 TwoPaths

/-- Drawing and ordinary labels at one recorded point of UNDO.
The geometric maps interpreting a RAM record are not RAM input. -/
structure GM06UndoState (n : ℕ) where
  drawing : Drawing ClosedCylinder
  tagged : List ((Fin n × Fin n) × ℕ)
  vertex : Fin n → ClosedCylinder
  edge : Fin tagged.length → Set ClosedCylinder

/-- An inverse operation is specified by actual drawing data and the
literal finite update. Only contractions contribute a stored pair. -/
inductive GM06UndoStep (n k : ℕ) :
    GM06UndoState n → GM06UndoState n → Option (ℕ × ℕ) → Prop
  | unchanged (X) : GM06UndoStep n k X X none
  | subdrawing {G H : Drawing ClosedCylinder} (hHG : H.IsSubdrawing G)
      (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → ClosedCylinder)
      (edge : Fin tagged.length → Set ClosedCylinder) (mask : List ℕ)
      (hlen : mask.length = tagged.length)
      (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
        G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
      (hmask : ∀ j : Fin tagged.length, mask[j.val]?.getD 0 = 1 → tagged[j].2 = 1) :
      GM06UndoStep n k ⟨G, tagged, vertex, edge⟩
        ⟨H, gm06RetagEdges tagged mask, vertex,
          fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)⟩ none
  | contraction {G G' : Drawing ClosedCylinder} (i : Fin k)
      (hG : IsCylinderSection5Drawing k G)
      (tagged : List ((Fin n × Fin n) × ℕ)) (vertex vertex' : Fin n → ClosedCylinder)
      (edge : Fin tagged.length → Set ClosedCylinder) (A : Finset (Fin n))
      (hinj : InjOn edge {j | tagged[j].2 = 1})
      (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
        G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
      (hLive : ∀ x, vertex x ∈ G.V → x ∈ A)
      (a b : Fin n) (ha : a ∈ A) (hab : a ≠ b)
      (hpoint : vertex a = cylinderM1Point k i)
      (d₀ : Fin tagged.length) (hd₀ : tagged[d₀].2 = 1)
      (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
      (hl : G.toGraph.IsLink (edge d₀) (cylinderM1Point k i) (vertex b))
      (hvs : vertex b ≠ cylinderM1Point k i)
      (π : C(ClosedCylinder, ClosedCylinder))
      (hfiber : π ⁻¹' {cylinderM1Point k i} = closure (edge d₀))
      (hi : InjOn π (closure (edge d₀))ᶜ) (hV : G'.V = π '' G.V)
      (hnew : ∀ x ∈ A.erase b, vertex' x = π (vertex x))
      (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
      (hH0 : ∀ x, H (0, x) = x) (hH1 : ∀ x, H (1, x) = π x)
      (hHbd : ∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x)
      (first : ℕ) (hfirst : first < 2 * tagged.length) (hfirstEdge : first / 2 = d₀.val)
      (hfirstTail : vertex (gm06DartTail tagged ⟨first, hfirst⟩) = cylinderM1Point k i)
      (hfirstHead : vertex (gm06DartHead tagged ⟨first, hfirst⟩) = vertex b) :
      GM06UndoStep n k ⟨G, tagged, vertex, edge⟩
        ⟨G', gm06ContractTaggedEdges tagged a b d₀.val, vertex',
          fun j => π '' edge (Fin.cast (gm06ContractTaggedEdges_length tagged a b d₀.val) j)⟩
        (some (i.val, first))

/-- One inverse record changes only the indexed row of a contraction. -/
@[expose] def gm06UndoRecordRows (record : Option (ℕ × ℕ)) (rows : List (List ℕ)) :
    List (List ℕ) :=
  match record with
  | none => rows
  | some p => rows.set p.1 (p.2 :: (rows[p.1]?.getD []))

/-- Each actual recorded inverse operation lifts every returned
encoded linkage, with precisely the stated row update and winding. -/
theorem GM06UndoStep.recover {n k : ℕ} {X Y : GM06UndoState n} {record : Option (ℕ × ℕ)}
    (h : GM06UndoStep n k X Y record) {θ : ℝ} (M : CylinderLinkage k Y.drawing)
    (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows) :
    ∃ N : CylinderLinkage k X.drawing, N.HasTheta θ ∧
      GM06LinkageRowsEncoding N X.tagged X.vertex X.edge (gm06UndoRecordRows record rows) := by
  cases h with
  | unchanged => exact ⟨M, hθ, hrows⟩
  | subdrawing hHG tagged vertex edge mask hlen hlinks hmask =>
    obtain ⟨N, hN, henc, _, _⟩ := gm06LinkageRowsEncoding_lift_subdrawing
      hHG tagged vertex edge mask hlen hlinks hmask M hθ rows hrows
    exact ⟨N, hN, henc⟩
  | contraction i hG tagged vertex vertex' edge A hinj hlinks hLive a b ha hab hpoint
      d₀ hd₀ hval hl hvs π hfiber hi hV hnew H hH0 hH1 hHbd first hfirst hfirstEdge hfirstTail hfirstHead =>
    exact gm06LinkageRowsEncoding_expand hG tagged vertex vertex' edge A hinj hlinks hLive
      a b ha hab hpoint d₀ hd₀ hval hl hvs π hfiber hi hV hnew H hH0 hH1 hHbd
      first hfirst hfirstEdge hfirstTail hfirstHead M hθ rows hrows

/-- A chronological drawing history. Optional numeric pairs record
only the contractions, since the other inverse operations do not
change output rows. -/
inductive GM06UndoTrace (n k : ℕ) :
    GM06UndoState n → GM06UndoState n → List (Option (ℕ × ℕ)) → Prop
  | nil (X) : GM06UndoTrace n k X X []
  | cons {X Y Z record records} (step : GM06UndoStep n k X Y record)
      (rest : GM06UndoTrace n k Y Z records) :
      GM06UndoTrace n k X Z (record :: records)

/-- The pure UNDO output ignores empty records and processes the
remaining contraction pairs from newest to oldest. -/
@[expose] def gm06UndoTraceRows (records : List (Option (ℕ × ℕ))) (rows : List (List ℕ)) :
    List (List ℕ) := gm06RecoverContractionRows (records.filterMap id) rows

/-- The pure chronological history has the inverse-record recurrence. -/
theorem gm06UndoTraceRows_cons (record : Option (ℕ × ℕ)) (records : List (Option (ℕ × ℕ)))
    (rows : List (List ℕ)) :
    gm06UndoTraceRows (record :: records) rows =
      gm06UndoRecordRows record (gm06UndoTraceRows records rows) := by
  cases record <;> rfl

/-- Lemma 17 and UNDO of our proof of VI (5.7): restoring the
actual recorded operations recovers a linkage in the input drawing
with the same winding and exactly the computed ordinary output rows. -/
theorem GM06UndoTrace.recover {n k : ℕ} {X Y : GM06UndoState n}
    {records : List (Option (ℕ × ℕ))} (h : GM06UndoTrace n k X Y records)
    {θ : ℝ} (M : CylinderLinkage k Y.drawing) (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows) :
    ∃ N : CylinderLinkage k X.drawing, N.HasTheta θ ∧
      GM06LinkageRowsEncoding N X.tagged X.vertex X.edge (gm06UndoTraceRows records rows) := by
  induction h with
  | nil => exact ⟨M, hθ, hrows⟩
  | cons step _ ih =>
    obtain ⟨N, hN, henc⟩ := ih M hθ hrows
    obtain ⟨P, hP, hencP⟩ := step.recover N hN _ henc
    exact ⟨P, hP, (gm06UndoTraceRows_cons _ _ rows).symm ▸ hencP⟩

/-- The actual RAM recovery program realizes the drawing-level UNDO
proof with its exact row output and polynomial time bound. The
history array contains only the numeric contraction pairs. -/
theorem gm06RecoverContractionsProg_drawing
    {n k w : ℕ} {X Y : GM06UndoState n} {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace n k X Y records) {θ : ℝ}
    (M : CylinderLinkage k Y.drawing) (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows)
    (tail : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length + (records.filterMap id).length < 2 ^ w)
    (hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hr : ∀ p ∈ records.filterMap id, p.1 < rows.length ∧ p.2 < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h309 : s.regs 309 = (records.filterMap id).length) :
    ∃ s' t, Exec w gm06RecoverContractionsProg s s' t ∧
      t ≤ 3 + (records.filterMap id).length *
        (400 + 300 * ((gm06EncodeRows rows).length + (records.filterMap id).length)) ∧
      Keeps [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s s' ∧
      s'.regs 309 = 0 ∧ s'.arrs 8 = gm06EncodeRows (gm06UndoTraceRows records rows) ∧
      (s'.arrs 8).length = (gm06EncodeRows rows).length + (records.filterMap id).length ∧
      ∃ N : CylinderLinkage k X.drawing, N.HasTheta θ ∧
        GM06LinkageRowsEncoding N X.tagged X.vertex X.edge (gm06UndoTraceRows records rows) := by
  obtain ⟨N, hN, henc⟩ := trace.recover M hθ rows hrows
  obtain ⟨s', t, hex, ht, hk, hzero, hout, hlen⟩ := gm06RecoverContractionsProg_exec
    (records.filterMap id) rows tail s hw hn hhist hx hr h8 h9 h309
  exact ⟨s', t, hex, ht, hk, hzero, hout, hlen, N, hN, henc⟩

private theorem contracted_vertex_ncard
    {G G' : Drawing ClosedCylinder} {e : Set ClosedCylinder} {s v : ClosedCylinder}
    (hl : G.toGraph.IsLink e s v) (hvs : v ≠ s) (π : ClosedCylinder → ClosedCylinder)
    (hfibre : π ⁻¹' {s} = closure e) (hi : InjOn π (closure e)ᶜ)
    (hV : G'.V = π '' G.V) : G'.V.ncard + 1 = G.V.ncard := by
  have hscl : s ∈ closure e :=
    (show s ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert s {v}).1
  have hvcl : v ∈ closure e :=
    (show v ∈ closure e ∩ G.V from hl.2.2.2.symm ▸ mem_insert_of_mem s rfl).1
  have hπs : π s = s := show s ∈ π ⁻¹' {s} from hfibre.symm ▸ hscl
  have hπv : π v = s := show v ∈ π ⁻¹' {s} from hfibre.symm ▸ hvcl
  have hends : ∀ x ∈ G.V \ {v}, x ∈ closure e → x = s := by
    intro x hx hxe
    have hh : x ∈ ({s, v} : Set ClosedCylinder) := hl.2.2.2 ▸ ⟨hxe, hx.1⟩
    rcases hh with hxs | hxv
    · exact hxs
    · exact False.elim (hx.2 hxv)
  have hinj : InjOn π (G.V \ {v}) := by
    intro x hx y hy hxy
    by_cases hxcl : x ∈ closure e
    · have hxs := hends x hx hxcl
      have hycl : y ∈ closure e := by
        rw [← hfibre]
        exact hxy.symm.trans (hxs ▸ hπs)
      exact hxs.trans (hends y hy hycl).symm
    · have hycl : y ∉ closure e := by
        intro hycl
        have hys := hends y hy hycl
        have hxcl' : x ∈ closure e := by
          rw [← hfibre]
          exact hxy.trans (hys ▸ hπs)
        exact hxcl hxcl'
      exact hi hxcl hycl hxy
  have himage : π '' G.V = π '' (G.V \ {v}) := by
    apply subset_antisymm
    · rintro y ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst x
        exact ⟨s, ⟨hl.left_mem, hvs.symm⟩, hπs.trans hπv.symm⟩
      · exact ⟨x, ⟨hx, hxv⟩, rfl⟩
    · exact image_mono sdiff_subset
  rw [hV, himage, hinj.ncard_image]
  exact ncard_sdiff_singleton_add_one hl.right_mem G.finite_V

/-- The original edge-label space is unchanged by every recorded
inverse operation, including deletions and contractions. -/
theorem GM06UndoStep.tagged_length {n k : ℕ} {X Y : GM06UndoState n} {record}
    (h : GM06UndoStep n k X Y record) : Y.tagged.length = X.tagged.length := by
  cases h with
  | unchanged => rfl
  | subdrawing => exact gm06RetagEdges_length _ _
  | contraction => exact gm06ContractTaggedEdges_length _ _ _ _

/-- Every actual contraction record contains an in-range path
index and an original ordinary directed word. -/
theorem GM06UndoStep.record_bounds {n k : ℕ} {X Y : GM06UndoState n} {record}
    (h : GM06UndoStep n k X Y record) {p : ℕ × ℕ} (hp : record = some p) :
    p.1 < k ∧ p.2 < 2 * X.tagged.length := by
  cases h with
  | unchanged => cases hp
  | subdrawing => cases hp
  | contraction i hG tagged vertex vertex' edge A hinj hlinks hLive a b ha hab hpoint
      d hd hval hl hvs π hfibre hi hV hnew H hH0 hH1 hHbd first hfirst hfirstEdge htail hhead =>
    cases hp
    exact ⟨i.isLt, hfirst⟩

/-- Every contraction consumes one distinct old vertex. Deletions
cannot increase the vertex set and unchanged operations use no slot. -/
theorem GM06UndoStep.vertex_credit {n k : ℕ} {X Y : GM06UndoState n} {record}
    (h : GM06UndoStep n k X Y record) :
    Y.drawing.V.ncard + record.isSome.toNat ≤ X.drawing.V.ncard := by
  cases h with
  | unchanged => simp
  | @subdrawing G H hHG =>
    simpa only [Option.isSome_none, Bool.toNat_false, Nat.add_zero] using
      ncard_le_ncard hHG.1 G.finite_V
  | contraction i hG tagged vertex vertex' edge A hinj hlinks hLive a b ha hab hpoint
      d hd hval hl hvs π hfibre hi hV hnew H hH0 hH1 hHbd first hfirst hfirstEdge htail hhead =>
    exact (contracted_vertex_ncard hl hvs π hfibre hi hV).le

/-- The full drawing history retains the original edge-index count. -/
theorem GM06UndoTrace.tagged_length {n k : ℕ} {X Y : GM06UndoState n} {records}
    (h : GM06UndoTrace n k X Y records) : Y.tagged.length = X.tagged.length := by
  induction h with
  | nil => rfl
  | cons step _ ih => exact ih.trans step.tagged_length

/-- All stored words throughout UNDO use the input path and ordinary
edge-label spaces, independent of how many reroutings occurred. -/
theorem GM06UndoTrace.record_bounds {n k : ℕ} {X Y : GM06UndoState n} {records}
    (h : GM06UndoTrace n k X Y records) :
    ∀ p ∈ records.filterMap id, p.1 < k ∧ p.2 < 2 * X.tagged.length := by
  induction h with
  | nil => simp
  | @cons X Y Z record records step rest ih =>
    intro p hp
    cases record with
    | none =>
      have hp' : p ∈ records.filterMap id := hp
      have hh := ih p hp'
      rw [step.tagged_length] at hh
      exact hh
    | some q =>
      rcases List.mem_cons.mp hp with hpq | hp'
      · subst p
        exact step.record_bounds rfl
      · have hh := ih p hp'
        rw [step.tagged_length] at hh
        exact hh

/-- The numeric contraction history has at most one record per
original vertex. This bounds the actual history allocation without
placing a reduction sequence in the algorithm's input. -/
theorem GM06UndoTrace.history_length_le {n k : ℕ} {X Y : GM06UndoState n} {records}
    (h : GM06UndoTrace n k X Y records) :
    Y.drawing.V.ncard + (records.filterMap id).length ≤ X.drawing.V.ncard := by
  induction h with
  | nil => simp
  | @cons X Y Z record records step rest ih =>
    have hc := step.vertex_credit
    cases record <;> simp only [List.filterMap_cons, id_eq, Option.isSome_none,
      Option.isSome_some, Bool.toNat_false, Bool.toNat_true,
      List.length_cons, Nat.add_zero] at hc ih ⊢ <;> omega

/-- A nonempty reached drawing leaves room for the next two-word
record in the history allocated from the original ordinary counts. -/
theorem GM06UndoTrace.history_free_slot {n k : ℕ} {X Y : GM06UndoState n} {records}
    (h : GM06UndoTrace n k X Y records) (hne : Y.drawing.V.Nonempty) :
    2 * (records.filterMap id).length + 1 <
      2 * (X.drawing.V.ncard + X.drawing.E.ncard) := by
  have hc := h.history_length_le
  have hv := (ncard_pos Y.drawing.finite_V).mpr hne
  omega

/-- The actual history supplies all record-index and word bounds
for RAM recovery. A uniform original-instance bound supplies the
current path-code and recovery growth bounds as well. -/
theorem gm06RecoverContractionsProg_drawing_of_trace
    {n k w : ℕ} {X Y : GM06UndoState n} {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace n k X Y records) {θ : ℝ}
    (M : CylinderLinkage k Y.drawing) (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows)
    (tail : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hcap : 1 + k + 2 * X.tagged.length + X.drawing.V.ncard < 2 ^ w)
    (hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h309 : s.regs 309 = (records.filterMap id).length) :
    ∃ sf t, Exec w gm06RecoverContractionsProg s sf t ∧
      t ≤ 3 + X.drawing.V.ncard *
        (400 + 300 * (1 + k + 2 * X.tagged.length + X.drawing.V.ncard)) ∧
      Keeps [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s sf ∧
      sf.regs 309 = 0 ∧ sf.arrs 8 = gm06EncodeRows (gm06UndoTraceRows records rows) ∧
      (sf.arrs 8).length = (gm06EncodeRows rows).length + (records.filterMap id).length ∧
      ∃ N : CylinderLinkage k X.drawing, N.HasTheta θ ∧
        GM06LinkageRowsEncoding N X.tagged X.vertex X.edge (gm06UndoTraceRows records rows) := by
  have hc : (records.filterMap id).length ≤ X.drawing.V.ncard := by
    have hh := trace.history_length_le
    omega
  have hcode := hrows.length_bounds.2.2
  rw [trace.tagged_length] at hcode
  have hsum : (gm06EncodeRows rows).length + (records.filterMap id).length ≤
      1 + k + 2 * X.tagged.length + X.drawing.V.ncard := by omega
  have hwords : ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w := by
    intro d hd
    have hb := hrows.code_words_le d hd
    rw [trace.tagged_length] at hb
    omega
  have hrecord : ∀ p ∈ records.filterMap id, p.1 < rows.length ∧ p.2 < 2 ^ w := by
    intro p hp
    have hb := trace.record_bounds p hp
    rw [hrows.1]
    exact ⟨hb.1, by omega⟩
  obtain ⟨sf, t, he, ht, hk, hzero, hout, hlen, N, hN, henc⟩ :=
    gm06RecoverContractionsProg_drawing trace M hθ rows hrows tail s hw
      (hsum.trans_lt hcap) hhist hwords hrecord h8 h9 h309
  have hcost := Nat.mul_le_mul hc
    (Nat.add_le_add_left (Nat.mul_le_mul_left 300 hsum) 400)
  exact ⟨sf, t, he, ht.trans (Nat.add_le_add_left hcost 3), hk, hzero, hout, hlen, N, hN, henc⟩

end GraphMinor.Compute
