module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.Compute.GM06InitLinkageMasks
public import GraphMinor.Compute.GM06PruneRotations
public import GraphMinor.Compute.GM02BalancedSeparationInput
import GraphMinor.GM06.Section5ComputedLinkageMask
import GraphMinor.GM06.Alg57RowBounds

/-!
# Rebuilding the actual current linkage masks

Each round of VI (5.7), page 133, rebuilds the directed-edge and
vertex masks from the current ordinary endpoint and linkage arrays.
Every word is bounded by its original edge-slot space. Packing
these bounded words into finite labels lets the existing RAM mask
initializer run directly. Its vertex mask is exactly the union of
the current path vertices, by the actual walk and edge encodings.
No geometric membership mask is an extra input to the loop.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

private theorem pack_words {B : ℕ} (xs : List ℕ) (h : ∀ d ∈ xs, d < B) :
    ∃ ys : List (Fin B), ys.map Fin.val = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons x xs ih =>
    obtain ⟨ys, hy⟩ := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    exact ⟨⟨x, h x (List.mem_cons_self)⟩ :: ys, by simp only [List.map_cons, hy]⟩

private theorem pack_rows {B : ℕ} (xs : List (List ℕ))
    (h : ∀ d ∈ xs.flatten, d < B) :
    ∃ ys : List (List (Fin B)), ys.map (List.map Fin.val) = xs := by
  induction xs with
  | nil => exact ⟨[], rfl⟩
  | cons row xs ih =>
    obtain ⟨ys, hy⟩ := ih (fun d hd => h d (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hd))
    obtain ⟨r, hr⟩ := pack_words row (fun d hd => h d
      (by simp only [List.flatten_cons, List.mem_append]; exact Or.inl hd))
    exact ⟨r :: ys, by simp only [List.map_cons, hr, hy]⟩

/-- The current walk rows compute the exact protected vertex mask
and directed-label mask in linear time. All other arrays, the
history count and the control bit are preserved. -/
theorem gm06InitLinkageMasksProg_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (s : State) (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hm : 2 * rep.tagged.length < 2 ^ w) (hk : k < 2 ^ w)
    (hlen : (gm06EncodeRows x.linkage).length < 2 ^ w)
    (h100 : s.regs 100 = x.vertexCount)
    (h3 : s.arrs 3 = x.endpoints) (h8 : s.arrs 8 = gm06EncodeRows x.linkage) :
    ∃ (s' : State) (t : ℕ) (Q : Finset (Fin x.vertexCount))
      (D : Finset (Fin (2 * rep.tagged.length))),
      Exec w gm06InitLinkageMasksProg s s' t ∧
      t ≤ x.vertexCount + 36 * rep.tagged.length + 22 * k + 14 * x.linkage.flatten.length + 22 ∧
      Keeps [40, 280, 281, 282, 283, 285] [17, 19] s s' ∧
      s'.arrs 17 = gm02VertexBits Q ∧ s'.arrs 19 = bitSetList D ∧
      (∀ d : Fin (2 * rep.tagged.length), d ∈ D ↔ d.val ∈ x.linkage.flatten) ∧
      rep.vertex '' (Q : Set (Fin x.vertexCount)) = ⋃ i : Fin k, (L.pathDrawing i).V := by
  classical
  let es := rep.tagged.map Prod.fst
  have hes : es.length = rep.tagged.length := by simp only [es, List.length_map]
  have hwords (d : ℕ) (hd : d ∈ x.linkage.flatten) : d < 2 * es.length := by
    obtain ⟨row, hr, hdrow⟩ := List.mem_flatten.mp hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    obtain ⟨_, _, henc, _⟩ := rep.linkage.path ⟨i, rep.linkage.1 ▸ hi⟩
    rw [hes]
    exact (henc.active_words d hdrow).1
  obtain ⟨rows, hrows⟩ := pack_rows x.linkage hwords
  have hmap : rows.flatten.map Fin.val = x.linkage.flatten := by rw [List.map_flatten, hrows]
  let D := rows.flatten.toFinset
  let Q := (gm06UsedEndpointRows es D).flatten.toFinset
  let edge : Fin es.length → Set ClosedCylinder := fun j => rep.edge (Fin.cast hes j)
  have hD (d : Fin (2 * es.length)) : d ∈ D ↔ d.val ∈ x.linkage.flatten := by
    rw [← hmap, List.mem_map]
    constructor
    · intro hd
      exact ⟨d, List.mem_toFinset.mp hd, rfl⟩
    · rintro ⟨e, he, hed⟩
      exact List.mem_toFinset.mpr (Fin.ext hed ▸ he)
  have hused (j : Fin es.length) :
      ((⟨2 * j.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * j.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) ↔
        ∃ d ∈ x.linkage.flatten, d / 2 = j.val := by
    constructor
    · rintro (hd | hd)
      · exact ⟨2 * j.val, (hD _).mp hd, by omega⟩
      · exact ⟨2 * j.val + 1, (hD _).mp hd, by omega⟩
    · rintro ⟨d, hd, hdj⟩
      have heven : d = 2 * j.val ∨ d = 2 * j.val + 1 := by omega
      rcases heven with rfl | rfl
      · exact Or.inl ((hD _).mpr hd)
      · exact Or.inr ((hD _).mpr hd)
  have hpath (d : ℕ) (hd : d ∈ x.linkage.flatten) :
      ∃ (i : Fin k) (hbound : d < 2 * rep.tagged.length),
        rep.tagged[d / 2].2 = 1 ∧ rep.edge ⟨d / 2, by omega⟩ ∈ (L.pathDrawing i).E := by
    obtain ⟨row, hr, hdrow⟩ := List.mem_flatten.mp hd
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    let j : Fin k := ⟨i, rep.linkage.1 ▸ hi⟩
    obtain ⟨W, _, henc, hP⟩ := rep.linkage.path j
    obtain ⟨hbound, hactive⟩ := henc.active_words d hdrow
    refine ⟨j, hbound, hactive, ?_⟩
    rw [← hP, walkDrawing_E]
    exact (henc.edge_mem_iff _).mpr ⟨d, hdrow, hbound, rfl⟩
  have hlinks (j : Fin es.length)
      (hj : (⟨2 * j.val, by omega⟩ : Fin (2 * es.length)) ∈ D ∨
        (⟨2 * j.val + 1, by omega⟩ : Fin (2 * es.length)) ∈ D) :
      G.toGraph.IsLink (edge j) (rep.vertex es[j.val].1) (rep.vertex es[j.val].2) := by
    obtain ⟨d, hd, hdj⟩ := (hused j).mp hj
    obtain ⟨_, hbound, hactive, _⟩ := hpath d hd
    have heq : (⟨d / 2, by omega⟩ : Fin rep.tagged.length) = Fin.cast hes j := Fin.ext hdj
    have hactive' : rep.tagged[Fin.cast hes j].2 = 1 := by
      have hh := congrArg (fun q : Fin rep.tagged.length => rep.tagged[q].2) heq
      exact hh ▸ hactive
    simpa only [es, edge, List.getElem_map, Fin.getElem_fin, Fin.val_cast] using rep.links (Fin.cast hes j) hactive'
  have hQ : rep.vertex '' (Q : Set (Fin x.vertexCount)) = ⋃ i : Fin k, (L.pathDrawing i).V := by
    apply computed_endpoint_mask_eq_linkage_vertices L es rep.vertex edge D hlinks
    · intro i e he
      obtain ⟨W, _, henc, hP⟩ := rep.linkage.path i
      rw [← hP, walkDrawing_E] at he
      obtain ⟨d, hd, hbound, heq⟩ := (henc.edge_mem_iff e).mp he
      let j : Fin es.length := ⟨d / 2, by rw [hes]; omega⟩
      refine ⟨j, heq, (hused j).mpr ⟨d, ?_, rfl⟩⟩
      exact List.mem_flatten.mpr ⟨_, List.getElem_mem (rep.linkage.1.symm ▸ i.isLt), hd⟩
    · intro j hj
      obtain ⟨d, hd, hdj⟩ := (hused j).mp hj
      obtain ⟨i, hbound, _, hmem⟩ := hpath d hd
      refine ⟨i, ?_⟩
      have heq : (⟨d / 2, by omega⟩ : Fin rep.tagged.length) = Fin.cast hes j := Fin.ext hdj
      have hh := congrArg rep.edge heq
      exact (show rep.edge (Fin.cast hes j) ∈ (L.pathDrawing i).E from hh ▸ hmem)
  have hrowCount : rows.length = k := by
    have hh := congrArg List.length hrows
    simpa only [List.length_map, rep.linkage.1] using hh
  have hflatLen : rows.flatten.length = x.linkage.flatten.length := by
    have hh := congrArg List.length hmap
    simpa only [List.length_map] using hh
  have hends : gm06EndpointWords (es.map fun e => (e.1.val, e.2.val)) = x.endpoints := by
    simpa only [es, List.map_map, Function.comp_def] using rep.endpoints.symm
  obtain ⟨s', t, he, ht, hframe, h19, h17⟩ := gm06InitLinkageMasksProg_exec es rows hw hn
    (hes ▸ hm) (hrowCount ▸ hk) (by rw [hrows]; exact hlen) h100
    (h3.trans hends.symm) (by rw [hrows]; exact h8)
  let D' : Finset (Fin (2 * rep.tagged.length)) := D.map (finCongr (congrArg (2 * ·) hes)).toEmbedding
  have hbits : bitSetList D' = bitSetList D := by
    apply List.ext_getElem
    · simp only [bitSetList, List.length_ofFn, hes]
    · intro i hi hj
      simp only [bitSetList, List.getElem_ofFn, D', Finset.mem_map_equiv, finCongr_symm, finCongr_apply_mk]
      rfl
  refine ⟨s', t, Q, D', he, ?_, hframe, ?_, h19.trans hbits.symm, ?_, hQ⟩
  · simpa only [hes, hrowCount, hflatLen] using ht
  · exact h17
  · intro d
    rw [Finset.mem_map]
    constructor
    · rintro ⟨e, heD, hed⟩
      have hev : e.val = d.val := congrArg Fin.val hed
      exact hev ▸ (hD e).mp heD
    · intro hd
      let e : Fin (2 * es.length) := ⟨d.val, by rw [hes]; exact d.isLt⟩
      exact ⟨e, (hD e).mpr hd, Fin.ext rfl⟩

end GraphMinor.Compute
