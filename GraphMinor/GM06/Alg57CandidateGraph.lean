module

public import GraphMinor.GM06.Alg57Reduction4Complete
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction

/-!
# The candidate graph `A_{i,v}` of Reduction 4, in the drawing

Section 12 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`) searches for Reduction 4
with a breadth-first search in a graph `A_{i,j}`: the vertices incident with `Rᵢ` except the
opposite boundary and the strict tail, and the edges incident with `Rᵢ` whose ends remain. Here we
state this graph in the drawing `G` (`IsReduction4CandidateVertex`, `IsReduction4CandidateEdge`) for
`k ≥ 2`. We exclude the points of all other linkage paths, which is what a linkage needs; and we
exclude the tail `T` of `Pᵢ` from the contact `v`, except `v` itself.

The main results:
* `exists_candidate_walk_iff`: a path `Q` as in Lemma 13 exists exactly when `sᵢ` and `v` are
  joined by a walk of `G` inside the candidate graph. This is formula (12).
* `exists_reduction4Step_iff_candidate_walk`: Reduction 4 applies exactly when some contact `v`,
  with its prefix not in the closure of `Rᵢ`, is joined to `sᵢ` in its candidate graph. This is
  Lemma 13 for `k ≥ 2`, both directions, and is the drawing-level counterpart of
  `gm06Find4_sound` and `gm06Find4_none_iff`.

The key step is `walkDrawing_inter_U_subset`: if a simple walk meets a subdrawing `B` only in
vertices of a set with at most one point, then so does its drawing. Edges cannot add new contacts:
a shared edge would have both ends in that set, so it would be a loop of a simple walk.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A simple walk whose vertices in a subdrawing `B` lie in a set `Y` with at most one point has
its whole drawing meeting `B` inside `Y`. -/
theorem walkDrawing_inter_U_subset {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ B : Drawing S} (hB : B.IsSubdrawing Γ) {a b : S} (W : GraphWalk Γ.toGraph a b)
    (hW : W.support.Nodup) {Y : Set S} (hY : Y.Subsingleton)
    (h : ∀ x ∈ W.support, x ∈ B.U → x ∈ Y) : (walkDrawing Γ W).U ∩ B.U ⊆ Y := by
  rintro x ⟨hx, hxB⟩
  rw [mem_walkDrawing_U] at hx
  rcases hx with hx | ⟨e, he, hxe⟩
  · exact h x hx hxB
  obtain ⟨z, z', hz, hz', hl⟩ := walk_exists_isLink_of_mem_edges W he
  have hends : closure e ∩ Γ.V = {z, z'} := hl.2.2.2
  by_cases hxV : x ∈ Γ.V
  · have : x ∈ ({z, z'} : Set S) := hends ▸ ⟨hxe, hxV⟩
    rcases this with rfl | hxz
    · exact h x hz hxB
    · rw [mem_singleton_iff.mp hxz]
      exact h z' hz' (mem_singleton_iff.mp hxz ▸ hxB)
  · exfalso
    have heΓ : e ∈ Γ.E := hl.1
    have hxe' : x ∈ e := by rw [← Γ.closure_diff_V heΓ]; exact ⟨hxe, hxV⟩
    have hxBV : x ∉ B.V := fun h => hxV (hB.1 h)
    obtain ⟨e', he', hxe''⟩ := B.exists_edge_of_mem hxB hxBV
    have hee : e = e' := Γ.edge_eq_of_mem heΓ (hB.2 he') hxe' hxe''
    have hBends : closure e ∩ Γ.V ⊆ B.U := by
      rw [hee, ← hB.closure_inter_V he']
      exact fun y hy => B.V_subset_U hy.2
    have hzY : z ∈ Y := h z hz (hBends (hends ▸ mem_insert _ _))
    have hz'Y : z' ∈ Y := h z' hz' (hBends (hends ▸ mem_insert_of_mem _ (mem_singleton _)))
    have hzz : z = z' := hY hzY hz'Y
    rw [← hzz] at hl
    exact walk_not_isLink_self_of_nodup W hW he hl

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-- A vertex of the candidate graph `A_{i,v}`: a vertex of `G` in the closure of `Rᵢ`, off the
other linkage paths, and off the tail `T` except at the contact `v`. -/
@[expose] def IsReduction4CandidateVertex (L : CylinderLinkage k G) (i : Fin k) (T : Drawing ClosedCylinder)
    (v x : ClosedCylinder) : Prop :=
  x ∈ G.V ∧ x ∈ closure (cylinderRegion k G i) ∧ (∀ j, j ≠ i → x ∉ (L.pathDrawing j).U) ∧
    (x ∈ T.U → x = v)

/-- An edge of the candidate graph `A_{i,v}`: an edge of `G` in the closure of `Rᵢ` whose ends are
candidate vertices. -/
@[expose] def IsReduction4CandidateEdge (L : CylinderLinkage k G) (i : Fin k) (T : Drawing ClosedCylinder)
    (v : ClosedCylinder) (e : Set ClosedCylinder) : Prop :=
  e ∈ G.E ∧ e ⊆ closure (cylinderRegion k G i) ∧
    ∀ x ∈ closure e ∩ G.V, IsReduction4CandidateVertex L i T v x

/-- **Formula (12).** For a contact `v ≠ sᵢ` with tail `T`, a path `Q` of `G` from `sᵢ` to `v` in
the closure of `Rᵢ`, missing the other linkage paths and meeting `T` only at `v`, exists exactly
when `sᵢ` and `v` are joined by a walk of `G` in the candidate graph. -/
theorem exists_candidate_walk_iff (L : CylinderLinkage k G) (i : Fin k)
    {T : Drawing ClosedCylinder} (hTG : T.IsSubdrawing G) {v : ClosedCylinder}
    (hsv : cylinderM1Point k i ≠ v) :
    (∃ Q : Drawing ClosedCylinder, Q.IsSubdrawing G ∧
        IsPathDrawing Q (cylinderM1Point k i) v ∧ Q.U ⊆ closure (cylinderRegion k G i) ∧
        Q.U ∩ T.U ⊆ {v} ∧ ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U) ↔
      ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) v,
        (∀ x ∈ W.support, IsReduction4CandidateVertex L i T v x) ∧
        ∀ e ∈ W.edges, IsReduction4CandidateEdge L i T v e := by
  classical
  constructor
  · rintro ⟨Q, hQG, hQ, hQR, hQT, hQP⟩
    obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
    obtain ⟨W', hWS, hWE⟩ := hQG.exists_walk_up W
    have hvert : ∀ x ∈ Q.V, IsReduction4CandidateVertex L i T v x := by
      intro x hx
      have hxU := Q.V_subset_U hx
      refine ⟨hQG.1 hx, hQR hxU, fun j hj hxj => disjoint_left.mp (hQP j hj) hxU hxj,
        fun hxT => mem_singleton_iff.mp (hQT ⟨hxU, hxT⟩)⟩
    refine ⟨W', fun x hx => hvert x ?_, fun e he => ?_⟩
    · rw [hVQ, ← hWS]; exact hx
    · have heQ : e ∈ Q.E := by rw [hEQ, ← hWE]; exact he
      have hcl : closure e ⊆ Q.U := by
        rw [Q.U_eq]
        exact subset_union_of_subset_right (subset_biUnion_of_mem (u := fun e => closure e) heQ) _
      refine ⟨hQG.2 heQ, subset_closure.trans (hcl.trans hQR), fun x hx => hvert x ?_⟩
      have : x ∈ closure e ∩ Q.V := by rw [hQG.closure_inter_V heQ]; exact hx
      exact this.2
  · rintro ⟨W, hV, hE⟩
    obtain ⟨R, hR, hRV, hRE⟩ := GraphWalk.exists_isSimple W
    have hRs : R.support.Nodup := hR
    refine ⟨walkDrawing G R, walkDrawing_isSubdrawing G R,
      isPathDrawing_walkDrawing_of_isSimple G hR hsv, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_walkDrawing_U] at hx
      rcases hx with hx | ⟨e, he, hxe⟩
      · exact (hV x (hRV x hx)).2.1
      · exact closure_minimal (hE e (hRE e he)).2.1 isClosed_closure hxe
    · exact walkDrawing_inter_U_subset hTG R hRs subsingleton_singleton
        fun x hx hxT => (hV x (hRV x hx)).2.2.2 hxT
    · intro j hj
      rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
      exact walkDrawing_inter_U_subset (L.isSubdrawing j).1 R hRs subsingleton_empty
        fun x hx hxj => absurd hxj ((hV x (hRV x hx)).2.2.1 j hj)

/-- A Reduction 4 tail of a linkage path is a subdrawing of `G`. -/
theorem isSubdrawing_of_section5Tail (L : CylinderLinkage k G) (i : Fin k)
    {T : Drawing ClosedCylinder} {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing i).V)
    (hT : IsSection5Tail (L.pathDrawing i) T v (L.curve i 1)) : T.IsSubdrawing G := by
  have hPG := (L.isSubdrawing i).1
  rcases hT with ⟨-, hU, hV⟩ | ⟨hTP, -, -⟩
  · refine ⟨?_, ?_⟩
    · rw [hV]; exact singleton_subset_iff.mpr (hPG.1 hv)
    · intro e he
      exfalso
      obtain ⟨x, hx⟩ := (he.2.2.1 : IsPathConnected e).nonempty
      have hxU : x ∈ T.U := (he.2.1 hx).1
      have hxV : x ∉ T.V := (he.2.1 hx).2
      rw [hU] at hxU
      rw [hV] at hxV
      exact hxV hxU
  · exact hTP.trans hPG

/-- **Lemma 13 for `k ≥ 2`.** Reduction 4 applies exactly when, for some `i`, some vertex `v` of
`Pᵢ` in the closure of `Rᵢ`, whose prefix subpath from `sᵢ` is not in that closure, is joined to
`sᵢ` by a walk of `G` in its candidate graph. -/
theorem exists_reduction4Step_iff_candidate_walk (L : CylinderLinkage k G) (hk : 1 < k) :
    (∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L') ↔
      ∃ (i : Fin k) (v : ClosedCylinder) (P_sv T : Drawing ClosedCylinder),
        v ∈ (L.pathDrawing i).V ∧ v ∈ closure (cylinderRegion k G i) ∧
        IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) v ∧
        ¬ P_sv.U ⊆ closure (cylinderRegion k G i) ∧
        IsSection5Tail (L.pathDrawing i) T v (L.curve i 1) ∧
        ∃ W : GraphWalk G.toGraph (cylinderM1Point k i) v,
          (∀ x ∈ W.support, IsReduction4CandidateVertex L i T v x) ∧
          ∀ e ∈ W.edges, IsReduction4CandidateEdge L i T v e := by
  constructor
  · rintro ⟨L', h⟩
    obtain ⟨i, v, P_sv, T, Q, hv, hvR, hsv, hpre, hT, hQG, hQ, hQR, hQT, hQP⟩ :=
      exists_reduction4_path_of_step hk h
    refine ⟨i, v, P_sv, T, hv, hvR, hsv, hpre, hT, ?_⟩
    exact (exists_candidate_walk_iff L i (isSubdrawing_of_section5Tail L i hv hT)
      (isPathDrawing_start_ne_end hsv.2.2)).mp ⟨Q, hQG, hQ, hQR, hQT, hQP⟩
  · rintro ⟨i, v, P_sv, T, hv, hvR, hsv, hpre, hT, hW⟩
    obtain ⟨Q, hQG, hQ, hQR, hQT, hQP⟩ := (exists_candidate_walk_iff L i
      (isSubdrawing_of_section5Tail L i hv hT) (isPathDrawing_start_ne_end hsv.2.2)).mpr hW
    exact exists_reduction4Step_of_path L hk i hv hvR hsv hpre hT hQG hQ hQR hQT hQP

end GraphMinor.GM06
