module

public import GraphMinor.GM06.Alg57PersistentRotations
public import GraphMinor.Compute.GM06LinkageRowsEncoding
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Card

/-!
# Bounds on the current row encodings

The loop for VI (5.7), page 133, keeps the original edge labels.
Its rotation rows list actual directed ends, so rows at distinct
vertex labels are disjoint. Its path rows encode disjoint simple
walks, so their directed words also have no repetitions. These
facts bound both flattened tables by the fixed directed-label
space. Length prefixes then give uniform linear code bounds for
the repeated scans and the recovery procedure.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

private theorem nodup_length_le_of_words_lt {xs : List ℕ} (hnd : xs.Nodup) {B : ℕ}
    (hwords : ∀ r ∈ xs, r < B) : xs.length ≤ B := by
  classical
  rw [← List.toFinset_card_of_nodup hnd]
  calc
    xs.toFinset.card ≤ (Finset.range B).card := Finset.card_le_card (by
      intro r hr
      exact Finset.mem_range.mpr (hwords r (List.mem_toFinset.mp hr)))
    _ = B := Finset.card_range B

/-- Actual directed-end rows at injectively labelled vertices have
no repeated word, either within one row or between different rows. -/
theorem persistent_rotation_rows_flatten_nodup
    {n : ℕ} {G : Drawing (OnePoint EuclideanPlane)}
    (label : G.E ↪ ℕ) (γ : Set (OnePoint EuclideanPlane) → unitInterval → OnePoint EuclideanPlane)
    (vertex : Fin n ↪ OnePoint EuclideanPlane) (rows : List (List ℕ))
    (hlen : rows.length = n)
    (hrows : ∀ j : Fin n, GM06PersistentRotationRowRep label γ (vertex j)
      (rows[j.val]'(hlen.symm ▸ j.isLt))) : rows.flatten.Nodup := by
  apply List.nodup_flatten.mpr
  constructor
  · intro row hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    exact (hrows ⟨j, hlen ▸ hj⟩).1
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    let a : Fin n := ⟨i, hlen ▸ hi⟩
    let b : Fin n := ⟨j, hlen ▸ hj⟩
    intro r hr hs
    obtain ⟨x, hx⟩ := ((hrows a).2.1 r).mp hr
    obtain ⟨y, hy⟩ := ((hrows b).2.1 r).mp hs
    have hxy := gm06PersistentHalfEdgeLabel_data_eq label x y (hx.trans hy.symm)
    have hverts : vertex a = vertex b := x.property.2.symm.trans
      ((congrArg (fun p : Set (OnePoint EuclideanPlane) × Bool => γ p.1 (endOf p.2)) hxy).trans
        y.property.2)
    have hab := congrArg Fin.val (vertex.injective hverts)
    exact (Nat.ne_of_lt hij) hab

/-- The total rotation words fit in the original augmented dart
space. Deleted labels may leave gaps, so only an upper bound on
permanent edge labels is needed. -/
theorem persistent_rotation_rows_length_le
    {n B : ℕ} {G : Drawing (OnePoint EuclideanPlane)}
    (label : G.E ↪ ℕ) (γ : Set (OnePoint EuclideanPlane) → unitInterval → OnePoint EuclideanPlane)
    (vertex : Fin n ↪ OnePoint EuclideanPlane) (rows : List (List ℕ))
    (hlen : rows.length = n)
    (hrows : ∀ j : Fin n, GM06PersistentRotationRowRep label γ (vertex j)
      (rows[j.val]'(hlen.symm ▸ j.isLt)))
    (hlabel : ∀ f : G.E, label f < B) :
    rows.flatten.length ≤ 2 * B ∧ (gm06EncodeRows rows).length ≤ 1 + n + 2 * B := by
  have hnd := persistent_rotation_rows_flatten_nodup label γ vertex rows hlen hrows
  have hbound : rows.flatten.length ≤ 2 * B := by
    apply nodup_length_le_of_words_lt hnd
    intro r hr
    obtain ⟨row, hrow, hr⟩ := List.mem_flatten.mp hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hrow
    obtain ⟨a, ha⟩ := ((hrows ⟨j, hlen ▸ hj⟩).2.1 r).mp hr
    have hB := hlabel ⟨a.val.1, a.property.1⟩
    have hb : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
    change 2 * label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat = r at ha
    omega
  refine ⟨hbound, ?_⟩
  rw [gm06EncodeRows_length, hlen]
  omega

end GraphMinor.GM06

namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM06

/-- An encoding of a simple walk contains no repeated directed
word: such a repetition would repeat the corresponding actual edge. -/
theorem GM06WalkDartEncoding.nodup_of_simple
    {n : ℕ} {α β : Type*} {G : Graph α β}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → α}
    {edge : Fin tagged.length → β} {x y : α} {W : GraphWalk G x y} {row : List ℕ}
    (henc : GM06WalkDartEncoding G tagged vertex edge W row) (hW : W.IsSimple) : row.Nodup := by
  induction henc with
  | nil => exact List.nodup_nil
  | @cons x y z e hl R row d hd hactive hedge htail hhead hrest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih hW.of_cons⟩
    intro hdrow
    have he : e ∈ R.edges := (hrest.edge_mem_iff e).mpr ⟨d, hdrow, hd, hedge⟩
    exact (List.nodup_cons.mp hW.edges_nodup).1 he

/-- Different paths of an actual linkage have disjoint directed
word rows, since sharing any word would share its nonempty open edge. -/
theorem GM06LinkageRowsEncoding.rows_disjoint
    {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows)
    (i j : Fin k) (hij : i ≠ j) :
    List.Disjoint (rows[i.val]'(hrows.1.symm ▸ i.isLt))
      (rows[j.val]'(hrows.1.symm ▸ j.isLt)) := by
  intro r hri hrj
  obtain ⟨Wi, _, henci, hPi⟩ := hrows.path i
  obtain ⟨Wj, _, hencj, hPj⟩ := hrows.path j
  obtain ⟨hd, _⟩ := henci.active_words r hri
  let d : Fin tagged.length := ⟨r / 2, by omega⟩
  have hei : edge d ∈ (L.pathDrawing i).E := by
    rw [← hPi, walkDrawing_E]
    exact (henci.edge_mem_iff _).mpr ⟨r, hri, hd, rfl⟩
  have hej : edge d ∈ (L.pathDrawing j).E := by
    rw [← hPj, walkDrawing_E]
    exact (hencj.edge_mem_iff _).mpr ⟨r, hrj, hd, rfl⟩
  obtain ⟨p, hp⟩ := hei.1
  exact disjoint_left.mp (L.pairwise_disjoint hij) ((hei.2.1 hp).1) ((hej.2.1 hp).1)

/-- Every current linkage table has globally distinct directed
words, bounded by the fixed ordinary dart space. This remains true
after a rerouting, without a bound on its number of previous steps. -/
theorem GM06LinkageRowsEncoding.length_bounds
    {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows) :
    rows.flatten.Nodup ∧ rows.flatten.length ≤ 2 * tagged.length ∧
      (gm06EncodeRows rows).length ≤ 1 + k + 2 * tagged.length := by
  have hnd : rows.flatten.Nodup := by
    apply List.nodup_flatten.mpr
    constructor
    · intro row hr
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
      obtain ⟨W, hW, henc, _⟩ := hrows.path ⟨j, hrows.1 ▸ hj⟩
      exact henc.nodup_of_simple hW
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij
      exact hrows.rows_disjoint ⟨i, hrows.1 ▸ hi⟩ ⟨j, hrows.1 ▸ hj⟩
        (fun h => (Nat.ne_of_lt hij) (congrArg Fin.val h))
  have hbound : rows.flatten.length ≤ 2 * tagged.length := by
    apply nodup_length_le_of_words_lt hnd
    intro d hd
    obtain ⟨row, hr, hdrow⟩ := List.mem_flatten.mp hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨W, _, henc, _⟩ := hrows.path ⟨j, hrows.1 ▸ hj⟩
    exact (henc.active_words d hdrow).choose
  refine ⟨hnd, hbound, ?_⟩
  rw [gm06EncodeRows_length, hrows.1]
  omega

/-- The row count, row lengths and data words account for every
word in the length-prefixed row encoding. -/
theorem gm06EncodeRows_words_le (rows : List (List ℕ)) (B : ℕ)
    (hcount : rows.length ≤ B) (hflat : rows.flatten.length ≤ B)
    (hwords : ∀ d ∈ rows.flatten, d ≤ B) : ∀ d ∈ gm06EncodeRows rows, d ≤ B := by
  intro d hd
  rcases List.mem_cons.mp hd with h | h
  · exact h ▸ hcount
  · obtain ⟨row, hr, hd⟩ := List.mem_flatMap.mp h
    rcases List.mem_cons.mp hd with hlen | hdrow
    · have hsub := (List.sublist_flatten_of_mem hr).length_le
      exact hlen ▸ hsub.trans hflat
    · exact hwords d (List.mem_flatten.mpr ⟨row, hr, hdrow⟩)

/-- Every path-code word is bounded by the fixed row count plus
the original ordinary dart space. This includes all length headers. -/
theorem GM06LinkageRowsEncoding.code_words_le
    {n k : ℕ} {G : Drawing ClosedCylinder} {L : CylinderLinkage k G}
    {tagged : List ((Fin n × Fin n) × ℕ)} {vertex : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (hrows : GM06LinkageRowsEncoding L tagged vertex edge rows) :
    ∀ d ∈ gm06EncodeRows rows, d ≤ k + 2 * tagged.length := by
  apply gm06EncodeRows_words_le
  · rw [hrows.1]; omega
  · exact hrows.length_bounds.2.1.trans (by omega)
  · intro d hd
    obtain ⟨row, hr, hdrow⟩ := List.mem_flatten.mp hd
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨W, _, henc, _⟩ := hrows.path ⟨j, hrows.1 ▸ hj⟩
    have hh := (henc.active_words d hdrow).choose
    omega

end GraphMinor.Compute

namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- Every rotation-code word is bounded by the fixed vertex count
plus the original augmented dart space, including its length headers. -/
theorem persistent_rotation_rows_code_words_le
    {n B : ℕ} {G : Drawing (OnePoint EuclideanPlane)}
    (label : G.E ↪ ℕ) (γ : Set (OnePoint EuclideanPlane) → unitInterval → OnePoint EuclideanPlane)
    (vertex : Fin n ↪ OnePoint EuclideanPlane) (rows : List (List ℕ))
    (hlen : rows.length = n)
    (hrows : ∀ j : Fin n, GM06PersistentRotationRowRep label γ (vertex j)
      (rows[j.val]'(hlen.symm ▸ j.isLt)))
    (hlabel : ∀ f : G.E, label f < B) :
    ∀ d ∈ gm06EncodeRows rows, d ≤ n + 2 * B := by
  apply gm06EncodeRows_words_le
  · rw [hlen]; omega
  · exact (persistent_rotation_rows_length_le label γ vertex rows hlen hrows hlabel).1.trans (by omega)
  · intro r hr
    obtain ⟨row, hrow, hr⟩ := List.mem_flatten.mp hr
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hrow
    obtain ⟨a, ha⟩ := ((hrows ⟨j, hlen ▸ hj⟩).2.1 r).mp hr
    have hB := hlabel ⟨a.val.1, a.property.1⟩
    have hb : a.val.2.toNat ≤ 1 := by cases a.val.2 <;> decide
    change 2 * label ⟨a.val.1, a.property.1⟩ + a.val.2.toNat = r at ha
    omega

end GraphMinor.GM06

