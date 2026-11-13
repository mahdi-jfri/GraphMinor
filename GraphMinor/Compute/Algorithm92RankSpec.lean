module

public import GraphMinor.Compute.Algorithm92Rank

/-!
# Graph Minors XIII, (9.2): what the numbering computes (`Algorithm92RankSpec.lean`)

The numbering of `Algorithm92Rank.lean` is stated on plain functions. This file applies it to
the layout of `H ∪ F` (page 101 of Graph Minors XIII) and shows that it computes the objects of
the compression (`Algorithm92Compress.lean`, `Algorithm92Input.lean`):

* `repv_eq`: the vertex `repv y` is `cRep y`;
* `isV_eq`: the test `isV y` holds exactly for the vertices of `fVerts x segs`;
* `length_vlist_eq_fι`, `getD_vlist_eq_fE`, `length_vlist_eq_card`: the numbers and the list of
  the compressed vertices are `fι`, `fE` and the number of compressed vertices.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-! ### Facts on `vlist` -/

section Generic

variable {nd onp : ℕ → Bool} {rep : ℕ → ℕ}

theorem vlist_prefix {y : ℕ} : ∀ {m : ℕ}, y ≤ m → ∃ t, vlist nd onp rep m = vlist nd onp rep y ++ t
  | 0, h => ⟨[], by rw [Nat.le_zero.mp h]; simp⟩
  | m + 1, h => by
    rcases Nat.lt_or_ge y (m + 1) with hlt | hge
    · obtain ⟨t, ht⟩ := vlist_prefix (y := y) (m := m) (by omega)
      exact ⟨t ++ (if isV nd onp rep m then [m] else []), by rw [vlist_succ, ht, List.append_assoc]⟩
    · exact ⟨[], by rw [Nat.le_antisymm h hge]; simp⟩

theorem mem_vlist {m z : ℕ} : z ∈ vlist nd onp rep m ↔ z < m ∧ isV nd onp rep z = true := by
  simp [vlist]

theorem getD_vlist_length {y m : ℕ} (hy : y < m) (hV : isV nd onp rep y = true) :
    (vlist nd onp rep m).getD (vlist nd onp rep y).length 0 = y := by
  obtain ⟨t, ht⟩ := vlist_prefix (nd := nd) (onp := onp) (rep := rep) (show y + 1 ≤ m by omega)
  rw [ht, vlist_succ, if_pos hV, List.append_assoc, List.getD_append_right _ _ _ _ le_rfl,
    Nat.sub_self]
  rfl

theorem pairwise_vlist (m : ℕ) : (vlist nd onp rep m).Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem nodup_vlist (m : ℕ) : (vlist nd onp rep m).Nodup :=
  (pairwise_vlist m).imp (fun h => Nat.ne_of_lt h)

end Generic

/-! ### The numbering on the layout of `H ∪ F` -/

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

variable (x segs) in
/-- The test for a vertex on a path of `H ∪ F`. -/
noncomputable def onpB (v : ℕ) : Bool := by
  classical exact decide (v ∈ layout x segs)

variable (x segs) in
/-- The vertex that stands for the blob of `v`, as a number. -/
noncomputable def repF (v : ℕ) : ℕ := if hv : v < x.n then (cRep (fNodes x segs) (fPaths x segs)
  ⟨v, hv⟩).val else 0

theorem tab_pF (n : ℕ) : tab (n + 1) (pF (layout x segs) (layout x segs).length) =
    tab (n + 1) (fun v => if onpB x segs v then 1 else 0) := by
  refine tab_congr fun v _ => ?_
  simp only [pF, ind, onpB]
  congr 1
  apply propext
  constructor
  · rintro ⟨j, hj, hjv⟩
    rw [List.getD_eq_getElem _ _ hj] at hjv
    simpa [← hjv] using List.getElem_mem hj
  · intro hv
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp (by simpa using hv)
    exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, hjv]⟩

section FSystem

variable {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

/-- The run end of a vertex on a path, read through the two arrays of the pass, holds `cRep y`. -/
theorem hrep_layout : ∀ y < x.n, ndB x segs y = false → onpB x segs y = true →
    rsF (ndB x segs) (layout x segs) (layout x segs).length y < (layout x segs).length ∧
    enF (ndB x segs) (layout x segs) (layout x segs).length
        (rsF (ndB x segs) (layout x segs) (layout x segs).length y) < (layout x segs).length ∧
    (layout x segs).getD (enF (ndB x segs) (layout x segs) (layout x segs).length
        (rsF (ndB x segs) (layout x segs) (layout x segs).length y)) 0 = repF x segs y := by
  intro y hy hnd hop
  have hyS : (⟨y, hy⟩ : Fin x.n) ∉ fNodes x segs := by
    have := ndB_val (x := x) (segs := segs) ⟨y, hy⟩; simp_all
  have hyP : OnPath (fPaths x segs) ⟨y, hy⟩ := by
    apply mem_layout_iff.mp; simpa [onpB] using hop
  obtain ⟨h1, h2, h3, h4, -, -⟩ := sweep_spec hF
    (rsA := rsF (ndB x segs) (layout x segs) (layout x segs).length)
    (enA := enF (ndB x segs) (layout x segs) (layout x segs).length)
    (fun v hv hvn => by
      obtain ⟨j, hj, h1, h2⟩ := rsF_spec (layout x segs).length v hvn (by
        obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hv
        exact ⟨j, hj, by rw [List.getD_eq_getElem _ _ hj, hjv]⟩)
      exact ⟨j, hj, h1, h2⟩)
    (fun j hj hnd => enF_spec _ j hj hnd) hyS hyP
  simp only [Fin.val_mk] at h2 h3 h4
  refine ⟨by omega, h3, ?_⟩
  rw [h4, repF, dif_pos hy]

theorem repv_eq {y : ℕ} (hy : y < x.n) :
    repv (ndB x segs) (onpB x segs) (repF x segs) y =
      (cRep (fNodes x segs) (fPaths x segs) ⟨y, hy⟩).val := by
  unfold repv
  by_cases hnd : ndB x segs y = true
  · rw [if_pos hnd]
    have hyS : (⟨y, hy⟩ : Fin x.n) ∈ fNodes x segs := by
      have := ndB_val (x := x) (segs := segs) ⟨y, hy⟩; simp_all
    rw [cRep_of_mem_S hyS]
  · rw [if_neg hnd]
    by_cases hop : onpB x segs y = true
    · rw [if_pos hop, repF, dif_pos hy]
    · rw [if_neg hop]
      have hyP : ¬ OnPath (fPaths x segs) ⟨y, hy⟩ := fun h => hop (by
        have := mem_layout_iff.mpr h; simpa [onpB] using this)
      rw [cRep_of_not_onPath hyP]

theorem isV_eq {y : ℕ} (hy : y < x.n) :
    isV (ndB x segs) (onpB x segs) (repF x segs) y =
      decide ((⟨y, hy⟩ : Fin x.n) ∈ fVerts x segs) := by
  have e1 := ndB_val (x := x) (segs := segs) ⟨y, hy⟩
  have e2 : onpB x segs y = true ↔ OnPath (fPaths x segs) ⟨y, hy⟩ := by
    simp only [onpB, decide_eq_true_eq]; exact mem_layout_iff (y := ⟨y, hy⟩)
  simp only at e1
  unfold isV
  rw [e1, repv_eq hF hy]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, fVerts, mem_cVerts_iff, e2,
    Fin.ext_iff]

/-- The list of the compressed vertices is the sorted list of `fVerts`. -/
theorem vlist_eq_sort : vlist (ndB x segs) (onpB x segs) (repF x segs) x.n =
    ((fVerts x segs).sort (· ≤ ·)).map Fin.val := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact (pairwise_vlist _).imp le_of_lt
  · exact List.Pairwise.map _ (fun a b h => h) (Finset.pairwise_sort _ _)
  · rw [List.perm_ext_iff_of_nodup (nodup_vlist _)
      ((Finset.sort_nodup _ _).map Fin.val_injective)]
    intro z
    rw [mem_vlist, List.mem_map]
    constructor
    · rintro ⟨hz, hV⟩
      rw [isV_eq hF hz] at hV
      exact ⟨⟨z, hz⟩, (Finset.mem_sort _).mpr (by simpa using hV), rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [isV_eq hF y.2]
      simpa using (Finset.mem_sort _).mp hy

theorem length_vlist_eq_card :
    (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n).length = (fVerts x segs).card := by
  rw [vlist_eq_sort hF, List.length_map, Finset.length_sort]

theorem getD_vlist_eq_fE (c : Fin (fVerts x segs).card) :
    (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n).getD c.val 0 = (fE x segs c).val := by
  have hc : c.val < (((fVerts x segs).sort (· ≤ ·)).map Fin.val).length := by
    simp [Finset.length_sort]
  rw [vlist_eq_sort hF, List.getD_eq_getElem _ _ hc, List.getElem_map, fE,
    Finset.orderEmbOfFin_apply]
  rfl

omit hF in
theorem fE_fι {y : Fin x.n} (hy : y ∈ fVerts x segs) : fE x segs (fι x segs y) = y := by
  simp only [fE, fι, hy, dite_true, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem length_vlist_eq_fι {y : Fin x.n} (hy : y ∈ fVerts x segs) :
    (vlist (ndB x segs) (onpB x segs) (repF x segs) y.val).length = (fι x segs y).val := by
  have hV : isV (ndB x segs) (onpB x segs) (repF x segs) y.val = true := by
    rw [isV_eq hF y.2]; simpa using hy
  have h1 := getD_vlist_length (nd := ndB x segs) (onp := onpB x segs) (rep := repF x segs)
    y.2 hV
  have h2 := getD_vlist_eq_fE hF (fι x segs y)
  rw [fE_fι hy] at h2
  have hlen := length_vlist_eq_card hF
  have hl1 : (vlist (ndB x segs) (onpB x segs) (repF x segs) y.val).length <
      (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n).length := by
    obtain ⟨t, ht⟩ := vlist_prefix (nd := ndB x segs) (onp := onpB x segs) (rep := repF x segs)
      (show y.val + 1 ≤ x.n by have := y.2; omega)
    rw [ht, vlist_succ, if_pos hV]
    simp
  have hl2 : (fι x segs y).val < (vlist (ndB x segs) (onpB x segs) (repF x segs) x.n).length := by
    rw [hlen]; exact (fι x segs y).2
  rw [List.getD_eq_getElem _ _ hl1] at h1
  rw [List.getD_eq_getElem _ _ hl2] at h2
  exact ((nodup_vlist _).getElem_inj_iff).mp (h1.trans h2.symm)

end FSystem

end Alg92

end GraphMinor.Compute
