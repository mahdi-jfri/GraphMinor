module

public import GraphMinor.GM06.Alg57Find4Link
import GraphMinor.GM06.Alg57CandidateGraph
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks

/-!
# `FIND_4` on any drawing

`Alg57Find4Link` links the search `FIND_4` of the Word RAM program (`gm06Find4`) to Reduction 4 for
`k ≥ 2`, in the cylinder. For `k = 1` the search runs in the cut disc, on the left copy of `P₁`,
with the right copy as the opposite boundary. The proofs are the same. So here we state them for any
drawing `Γ` in a Hausdorff space, with

* a path `P` of `Γ` from `s` to `t` (the copy of the linkage path that is searched),
* a closed set `Rc` (the closure of the region), containing `s`,
* a set `Up` (the opposite boundary), missing `P`,
* a set `Eok` of allowed edges (all edges for `k ≥ 2`; for `k = 1`, the edges over edges of `G`).

`GenReduction4At` is Reduction 4 at `P` in this setting, `Find4GenRep` says when the program's lists
represent it, and the two results are `genReduction4At_of_find4_some` and
`not_genReduction4At_of_find4_none`. The proofs follow `Alg57Find4Link` and
`Alg57CandidateGraph` step by step.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- A tail of `P` from `v` to `t`: the subpath from `v` to `t`, or the point `t` when `v = t`. -/
@[expose] def IsGenTail (P T : Drawing S) (v t : S) : Prop :=
  (v = t ∧ T.U = {v} ∧ T.V = {v}) ∨ IsSubpathOf P T v t

/-- A vertex of the candidate graph at contact `v` with tail `T`. -/
@[expose] def IsGenCandVertex (Γ : Drawing S) (Rc Up : Set S) (T : Drawing S) (v x : S) : Prop :=
  x ∈ Γ.V ∧ x ∈ Rc ∧ x ∉ Up ∧ (x ∈ T.U → x = v)

/-- An edge of the candidate graph at contact `v` with tail `T`. -/
@[expose] def IsGenCandEdge (Γ : Drawing S) (Rc Up : Set S) (Eok : Set (Set S)) (T : Drawing S)
    (v : S) (e : Set S) : Prop :=
  e ∈ Γ.E ∧ e ⊆ Rc ∧ e ∈ Eok ∧ ∀ x ∈ closure e ∩ Γ.V, IsGenCandVertex Γ Rc Up T v x

/-- One step of the candidate graph. -/
@[expose] def GenCandStep (Γ : Drawing S) (Rc Up : Set S) (Eok : Set (Set S)) (T : Drawing S)
    (v x y : S) : Prop :=
  ∃ e, IsGenCandEdge Γ Rc Up Eok T v e ∧ Γ.toGraph.IsLink e x y

/-- **Reduction 4 at the path `P`**: a contact `w` on `P` in `Rc` whose prefix is not in `Rc`, and
a path `Q` of `Γ` from `s` to `w` in `Rc`, with allowed edges, missing `Up` and meeting the tail
only at `w`. -/
@[expose] def GenReduction4At (Γ P : Drawing S) (s t : S) (Rc : Set S) (B : Drawing S)
    (Eok : Set (Set S)) : Prop :=
  ∃ (w : S) (P_sw T Q : Drawing S), w ∈ P.V ∧ w ∈ Rc ∧ IsSubpathOf P P_sw s w ∧
    ¬ P_sw.U ⊆ Rc ∧ IsGenTail P T w t ∧ Q.IsSubdrawing Γ ∧ IsPathDrawing Q s w ∧ Q.U ⊆ Rc ∧
    Q.U ∩ T.U ⊆ {w} ∧ Disjoint Q.U B.U ∧ ∀ e ∈ Q.E, e ∈ Eok

theorem GenCandStep.vertices {Γ : Drawing S} {Rc Up : Set S} {Eok : Set (Set S)} {T : Drawing S}
    {v x y : S} (h : GenCandStep Γ Rc Up Eok T v x y) :
    IsGenCandVertex Γ Rc Up T v x ∧ IsGenCandVertex Γ Rc Up T v y := by
  obtain ⟨e, he, hl⟩ := h
  have hends : closure e ∩ Γ.V = {x, y} := hl.2.2.2
  exact ⟨he.2.2.2 x (hends ▸ mem_insert _ _),
    he.2.2.2 y (hends ▸ mem_insert_of_mem _ (mem_singleton _))⟩

/-- A walk in the candidate graph is a chain of candidate steps from a candidate vertex. -/
theorem exists_genCand_walk_iff_reflTransGen (Γ : Drawing S) (Rc Up : Set S)
    (Eok : Set (Set S)) (T : Drawing S) (v a b : S) :
    (∃ W : GraphWalk Γ.toGraph a b,
        (∀ x ∈ W.support, IsGenCandVertex Γ Rc Up T v x) ∧
        ∀ e ∈ W.edges, IsGenCandEdge Γ Rc Up Eok T v e) ↔
      IsGenCandVertex Γ Rc Up T v a ∧
        Relation.ReflTransGen (GenCandStep Γ Rc Up Eok T v) a b := by
  constructor
  · rintro ⟨W, hV, hE⟩
    refine ⟨hV a W.start_mem_support, ?_⟩
    clear hV
    induction W with
    | nil _ => exact Relation.ReflTransGen.refl
    | @cons u x w e hlink rest ih =>
      refine Relation.ReflTransGen.head ⟨e, hE e (List.mem_cons_self), hlink⟩ ?_
      exact ih fun e he => hE e (List.mem_cons_of_mem _ he)
  · rintro ⟨ha, h⟩
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      refine ⟨GraphWalk.nil ha.1, fun x hx => ?_, by simp [GraphWalk.edges]⟩
      rw [List.mem_singleton.mp hx]
      exact ha
    | head hstep _ ih =>
      obtain ⟨e, he, hl⟩ := hstep
      obtain ⟨W, hV, hE⟩ := ih (GenCandStep.vertices ⟨e, he, hl⟩).2
      refine ⟨GraphWalk.cons hl W, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (GenCandStep.vertices ⟨e, he, hl⟩).1
        · exact hV x hx
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact he
        · exact hE e' he'

/-- **Formula (12).** A path `Q` of `Γ` from `s` to `v ≠ s` in `Rc`, with allowed edges, missing
`Up` and meeting the tail `T` only at `v`, exists exactly when `s` and `v` are joined by a walk in
the candidate graph. -/
theorem exists_genCand_walk_iff (Γ : Drawing S) (Rc : Set S) {B : Drawing S}
    (hB : B.IsSubdrawing Γ) (Eok : Set (Set S))
    (hRc : IsClosed Rc) {T : Drawing S} (hTG : T.IsSubdrawing Γ) {s v : S} (hsv : s ≠ v) :
    (∃ Q : Drawing S, Q.IsSubdrawing Γ ∧ IsPathDrawing Q s v ∧ Q.U ⊆ Rc ∧
        Q.U ∩ T.U ⊆ {v} ∧ Disjoint Q.U B.U ∧ ∀ e ∈ Q.E, e ∈ Eok) ↔
      ∃ W : GraphWalk Γ.toGraph s v,
        (∀ x ∈ W.support, IsGenCandVertex Γ Rc B.U T v x) ∧
        ∀ e ∈ W.edges, IsGenCandEdge Γ Rc B.U Eok T v e := by
  classical
  constructor
  · rintro ⟨Q, hQG, hQ, hQR, hQT, hQP, hQE⟩
    obtain ⟨W, hW, hVQ, hEQ⟩ := hQ.1
    obtain ⟨W', hWS, hWE⟩ := hQG.exists_walk_up W
    have hvert : ∀ x ∈ Q.V, IsGenCandVertex Γ Rc B.U T v x := by
      intro x hx
      have hxU := Q.V_subset_U hx
      exact ⟨hQG.1 hx, hQR hxU, fun hxj => disjoint_left.mp hQP hxU hxj,
        fun hxT => mem_singleton_iff.mp (hQT ⟨hxU, hxT⟩)⟩
    refine ⟨W', fun x hx => hvert x ?_, fun e he => ?_⟩
    · rw [hVQ, ← hWS]; exact hx
    · have heQ : e ∈ Q.E := by rw [hEQ, ← hWE]; exact he
      refine ⟨hQG.2 heQ, subset_closure.trans ((Q.closure_subset_U heQ).trans hQR), hQE e heQ,
        fun x hx => hvert x ?_⟩
      have : x ∈ closure e ∩ Q.V := by rw [hQG.closure_inter_V heQ]; exact hx
      exact this.2
  · rintro ⟨W, hV, hE⟩
    obtain ⟨R, hR, hRV, hRE⟩ := GraphWalk.exists_isSimple W
    have hRs : R.support.Nodup := hR
    refine ⟨walkDrawing Γ R, walkDrawing_isSubdrawing Γ R,
      isPathDrawing_walkDrawing_of_isSimple Γ hR hsv, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_walkDrawing_U] at hx
      rcases hx with hx | ⟨e, he, hxe⟩
      · exact (hV x (hRV x hx)).2.1
      · exact closure_minimal (hE e (hRE e he)).2.1 hRc hxe
    · exact walkDrawing_inter_U_subset hTG R hRs subsingleton_singleton
        fun x hx hxT => (hV x (hRV x hx)).2.2.2 hxT
    · rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
      exact walkDrawing_inter_U_subset hB R hRs subsingleton_empty
        fun x hx hxB => absurd hxB ((hV x (hRV x hx)).2.2.1)
    · intro e he
      rw [walkDrawing_E] at he
      exact (hE e (hRE e he)).2.2.1

/-- Reachability in a labelled graph is a chain of steps, when adjacency gives a step and each step
from a good label is matched by a good label. -/
theorem reachable_iff_reflTransGen_of_match' {n : ℕ} (H : SimpleGraph (Fin n))
    {lab : Fin n → S} (good : Fin n → Prop) (step : S → S → Prop)
    (hadj : ∀ u w, H.Adj u w → step (lab u) (lab w))
    (hmatch : ∀ x y, step x y → ∀ u, good u → lab u = x →
      ∃ w, good w ∧ lab w = y ∧ (u = w ∨ H.Adj u w))
    (hinj : ∀ u w, good u → good w → lab u = lab w → u = w)
    {a b : Fin n} (ha : good a) (hb : good b) :
    H.Reachable a b ↔ Relation.ReflTransGen step (lab a) (lab b) := by
  constructor
  · intro h
    clear hb
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ huw ih => exact ih.tail (hadj _ _ huw)
  · intro h
    have key : ∀ z, Relation.ReflTransGen step (lab a) z →
        ∃ w, good w ∧ lab w = z ∧ H.Reachable a w := by
      intro z hz
      induction hz with
      | refl => exact ⟨a, ha, rfl, SimpleGraph.Reachable.refl a⟩
      | tail _ hstep ih =>
        obtain ⟨w, hw, hwz, hr⟩ := ih
        obtain ⟨w', hw', hw'z, hor⟩ := hmatch _ _ hstep w hw hwz
        refine ⟨w', hw', hw'z, ?_⟩
        rcases hor with rfl | hadj'
        · exact hr
        · exact hr.trans hadj'.reachable
    obtain ⟨w, hw, hwb, hr⟩ := key _ h
    rwa [hinj w b hw hb hwb] at hr

/-- Any two subpaths of a parametrized path with the same ends have the same points. -/
theorem gen_subpath_U_eq {P : Drawing S} {f : Curve S} {s t : S} (hf : ParametrizesSet f P.U s t)
    {A A' : Drawing S} {x y : S} (hA : IsPathDrawing A x y) (hAP : A.U ⊆ P.U)
    (hA' : IsPathDrawing A' x y) (hA'P : A'.U ⊆ P.U) (hx : x ∈ P.U) (hy : y ∈ P.U) :
    A.U = A'.U := by
  obtain ⟨hfi, hfr, -, -⟩ := hf
  rw [← hfr] at hx hy hAP hA'P
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨g, hgi, hgr, hg0, hg1⟩ := hA.2
  obtain ⟨g', hgi', hgr', hg0', hg1'⟩ := hA'.2
  rw [← hgr, ← hgr', range_eq_image_uIcc_of_subarc hfi hgi (hgr ▸ hAP) (hg0.trans ha.symm)
    (hg1.trans hb.symm), range_eq_image_uIcc_of_subarc hfi hgi' (hgr' ▸ hA'P)
    (hg0'.trans ha.symm) (hg1'.trans hb.symm)]

/-! ### The representation -/

section Rep

variable {Γ P B : Drawing S} {s t : S} {Rc : Set S} {Eok : Set (Set S)} {n : ℕ}
  {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
  {start : Fin n} {steps : List (ℕ × Fin n)}
  {lab : Fin n → S} {edgeLab : ℕ → Set S}

/-- **The lists of `FIND_4` represent the setting** `(Γ, P, Rc, B, Eok)`. The fields are those of
`Find4Rep`, with `closure Rᵢ` replaced by `Rc`, the next path by `B`, and edges restricted to
`Eok`. -/
structure Find4GenRep (Γ P : Drawing S) (s t : S) (Rc : Set S) (B : Drawing S)
    (Eok : Set (Set S)) {n : ℕ}
    (ends : List (ℕ × ℕ)) (ordinary : List Bool) (incV incE upper : List ℕ)
    (start : Fin n) (steps : List (ℕ × Fin n))
    (lab : Fin n → S) (edgeLab : ℕ → Set S) : Prop where
  vertex_sound : ∀ u : Fin n, incV[u.val]?.getD 0 ≠ 0 → lab u ∈ Γ.V ∧ lab u ∈ Rc
  vertex_cover : ∀ x ∈ Γ.V, x ∈ Rc → ∃ u : Fin n, incV[u.val]?.getD 0 ≠ 0 ∧ lab u = x
  inj : ∀ u w : Fin n, (incV[u.val]?.getD 0 ≠ 0 ∨ u ∈ find4PathLabels start steps) →
    (incV[w.val]?.getD 0 ≠ 0 ∨ w ∈ find4PathLabels start steps) → lab u = lab w → u = w
  upper_iff : ∀ u : Fin n, incV[u.val]?.getD 0 ≠ 0 → (u.val ∈ upper ↔ lab u ∈ B.U)
  edge_sound : ∀ e, ordinary[e]?.getD false = true → incE[e]?.getD 0 ≠ 0 →
    ∃ u w : Fin n, ends[e]?.getD (0, 0) = (u.val, w.val) ∧ edgeLab e ⊆ Rc ∧ edgeLab e ∈ Eok ∧
      Γ.toGraph.IsLink (edgeLab e) (lab u) (lab w)
  edge_cover : ∀ f x y, Γ.toGraph.IsLink f x y → x ≠ y → f ⊆ Rc → f ∈ Eok →
    ∃ e < ends.length, ordinary[e]?.getD false = true ∧ incE[e]?.getD 0 ≠ 0 ∧ edgeLab e = f ∧
      ∃ u w : Fin n, ends[e]?.getD (0, 0) = (u.val, w.val) ∧ incV[u.val]?.getD 0 ≠ 0 ∧
        incV[w.val]?.getD 0 ≠ 0 ∧ ((lab u = x ∧ lab w = y) ∨ (lab u = y ∧ lab w = x))
  path_walk : ∃ W : GraphWalk P.toGraph s t,
    W.IsSimple ∧ P.V = {x | x ∈ W.support} ∧
    W.support = (find4PathLabels start steps).map lab ∧ W.edges = steps.map (fun st => edgeLab st.1)
  path_incV : ∀ u ∈ find4PathLabels start steps, (incV[u.val]?.getD 0 ≠ 0 ↔ lab u ∈ Rc)
  path_incE : ∀ st ∈ steps, (incE[st.1]?.getD 0 ≠ 0 ↔ edgeLab st.1 ⊆ Rc)

/-- The program's candidate vertex test at contact `q` is the candidate vertex of the setting. -/
theorem gen_candidateVertex_iff
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) {W : GraphWalk P.toGraph s t}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : S} {W₂ : GraphWalk P.toGraph v t}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q)
    (u : Fin n) (hu : incV[u.val]?.getD 0 ≠ 0) :
    gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true ↔
      IsGenCandVertex Γ Rc B.U (walkDrawing P W₂) v (lab u) := by
  rw [gm06CandidateVertex_iff, mem_drop_pathVertices_iff]
  have hsound := rep.vertex_sound u hu
  have hdrop : W.support.drop q = v :: W.support.drop (q + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hv).1]
    rw [(List.getElem?_eq_some_iff.mp hv).2]
  have hvnot : v ∉ W.support.drop (q + 1) := by
    have hnd : (W.support.drop q).Nodup := hWs.sublist (List.drop_sublist _ _)
    rw [hdrop] at hnd
    exact (List.nodup_cons.mp hnd).1
  have htail : lab u ∈ (walkDrawing P W₂).U ∧ lab u ≠ v ↔
      u ∈ (find4PathLabels start steps).drop (q + 1) := by
    constructor
    · rintro ⟨hU, hne⟩
      have hs := mem_support_of_mem_walkDrawing_U hPΓ W₂ hU hsound.1
      rw [h2, hdrop] at hs
      rcases List.mem_cons.mp hs with h | h
      · exact absurd h hne
      · rw [hWsupp, ← List.map_drop] at h
        obtain ⟨w, hw, hwu⟩ := List.mem_map.mp h
        have hwP : w ∈ find4PathLabels start steps := List.mem_of_mem_drop hw
        rwa [rep.inj u w (Or.inl hu) (Or.inr hwP) hwu.symm]
    · intro h
      have hmem : lab u ∈ W.support.drop (q + 1) := by
        rw [hWsupp, ← List.map_drop]
        exact List.mem_map.mpr ⟨u, h, rfl⟩
      refine ⟨(mem_walkDrawing_U _ W₂).mpr (Or.inl ?_), ?_⟩
      · rw [h2, hdrop]; exact List.mem_cons_of_mem _ hmem
      · rintro rfl; exact hvnot hmem
  have hupper := rep.upper_iff u hu
  constructor
  · rintro ⟨-, hup, hdr⟩
    refine ⟨hsound.1, hsound.2, fun h => hup (hupper.mpr h), ?_⟩
    intro hT
    by_contra hne
    exact hdr (htail.mp ⟨hT, hne⟩)
  · rintro ⟨-, -, hP, hT⟩
    refine ⟨hu, fun h => hP (hupper.mp h), fun h => ?_⟩
    obtain ⟨hU, hne⟩ := htail.mpr h
    exact hne (hT hU)

/-- Adjacency in the program's candidate graph at contact `q` is a candidate step of the setting. -/
theorem gen_find4Graph_adj_step
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) {W : GraphWalk P.toGraph s t}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : S} {W₂ : GraphWalk P.toGraph v t}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q) (u w : Fin n)
    (h : (gm06Find4Graph ends ordinary incV incE upper start steps q).Adj u w) :
    GenCandStep Γ Rc B.U Eok (walkDrawing P W₂) v (lab u) (lab w) := by
  obtain ⟨-, e, he, hends⟩ := h
  rw [gm06CandidateEdges_mem_iff] at he
  obtain ⟨-, hord, hinc, hc1, hc2⟩ := he
  obtain ⟨u', w', hends', hsub, hok, hl⟩ := rep.edge_sound e hord hinc
  have hcand : ∀ z : Fin n, gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q
      z.val = true → IsGenCandVertex Γ Rc B.U (walkDrawing P W₂) v (lab z) := by
    intro z hz
    have hzi : incV[z.val]?.getD 0 ≠ 0 := ((gm06CandidateVertex_iff _ _ _ _ _).mp hz).1
    exact (gen_candidateVertex_iff rep hPΓ hWs hWsupp hv h2 z hzi).mp hz
  rw [hends'] at hc1 hc2
  have hcu := hcand u' hc1
  have hcw := hcand w' hc2
  have hedge : IsGenCandEdge Γ Rc B.U Eok (walkDrawing P W₂) v (edgeLab e) := by
    refine ⟨hl.1, hsub, hok, fun x hx => ?_⟩
    have hx' : x ∈ ({lab u', lab w'} : Set S) := hl.2.2.2 ▸ hx
    rcases hx' with rfl | hx'
    · exact hcu
    · rw [mem_singleton_iff.mp hx']; exact hcw
  rcases hends with hends | hends
  · rw [hends'] at hends
    obtain ⟨h1, h2⟩ := Prod.mk.inj hends
    rw [Fin.ext h1, Fin.ext h2] at hl
    exact ⟨edgeLab e, hedge, hl⟩
  · rw [hends'] at hends
    obtain ⟨h1, h2⟩ := Prod.mk.inj hends
    rw [Fin.ext h1, Fin.ext h2] at hl
    exact ⟨edgeLab e, hedge, hl.symm⟩

/-- A candidate step of the setting from a good label is matched in the program's candidate
graph. -/
theorem gen_find4Graph_match
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) {W : GraphWalk P.toGraph s t}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : S} {W₂ : GraphWalk P.toGraph v t}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q) (x y : S)
    (hxy : GenCandStep Γ Rc B.U Eok (walkDrawing P W₂) v x y) (u : Fin n)
    (hu : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true)
    (hux : lab u = x) :
    ∃ w : Fin n, gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q w.val = true ∧
      lab w = y ∧ (u = w ∨ (gm06Find4Graph ends ordinary incV incE upper start steps q).Adj u w) := by
  obtain ⟨f, ⟨hfE, hfR, hfok, hfc⟩, hl⟩ := hxy
  by_cases hxy : x = y
  · exact ⟨u, hu, hux.trans hxy, Or.inl rfl⟩
  have hui : incV[u.val]?.getD 0 ≠ 0 := ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1
  have hcy : IsGenCandVertex Γ Rc B.U (walkDrawing P W₂) v y :=
    hfc y (by rw [hl.2.2.2]; exact mem_insert_of_mem _ (mem_singleton _))
  obtain ⟨e, helen, hord, hinc, hfe, u', w', hends, hu'i, hw'i, hor⟩ :=
    rep.edge_cover f x y hl hxy hfR hfok
  have hgood : ∀ z : Fin n, incV[z.val]?.getD 0 ≠ 0 → lab z = y →
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q z.val = true := by
    intro z hz hzy
    rw [gen_candidateVertex_iff rep hPΓ hWs hWsupp hv h2 z hz, hzy]
    exact hcy
  have hmemE : ∀ a b : Fin n, ends[e]?.getD (0, 0) = (a.val, b.val) →
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q a.val = true →
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q b.val = true →
      e ∈ gm06CandidateEdges ends ordinary incV incE upper (gm06Find4PathVertices start steps) q := by
    intro a b hab ha hb
    rw [gm06CandidateEdges_mem_iff, hab]
    exact ⟨helen, hord, hinc, ha, hb⟩
  rcases hor with ⟨hu'x, hw'y⟩ | ⟨hu'y, hw'x⟩
  · have huu : u = u' := rep.inj u u' (Or.inl hui) (Or.inl hu'i) (hux.trans hu'x.symm)
    subst huu
    have hw' := hgood w' hw'i hw'y
    refine ⟨w', hw', hw'y, ?_⟩
    by_cases huw : u = w'
    · exact Or.inl huw
    · exact Or.inr ⟨huw, e, hmemE u w' hends hu hw', Or.inl hends⟩
  · have huu : u = w' := rep.inj u w' (Or.inl hui) (Or.inl hw'i) (hux.trans hw'x.symm)
    subst huu
    have hu' := hgood u' hu'i hu'y
    refine ⟨u', hu', hu'y, ?_⟩
    by_cases huw : u = u'
    · exact Or.inl huw
    · exact Or.inr ⟨huw, e, hmemE u' u hends hu' hu, Or.inr hends⟩

/-- **The setup at one contact**, as in `find4_contact`. -/
theorem gen_find4_contact
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) {f : Curve S} (hf : ParametrizesSet f P.U s t)
    (hRc : IsClosed Rc) (hsR : s ∈ Rc) (hPB : Disjoint P.U B.U)
    {W : GraphWalk P.toGraph s t}
    (hWs : W.IsSimple) (hWV : P.V = {x | x ∈ W.support})
    (hWsupp : W.support = (find4PathLabels start steps).map lab)
    (hWedges : W.edges = steps.map (fun st => edgeLab st.1))
    {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ steps.length) :
    ∃ (P_sv T : Drawing S),
      W.support[q]? = some (lab (gm06Find4Target start steps q)) ∧
      IsSubpathOf P P_sv s (lab (gm06Find4Target start steps q)) ∧
      IsGenTail P T (lab (gm06Find4Target start steps q)) t ∧
      (P_sv.U ⊆ Rc ↔ gm06PrefixOK incV incE start.val
        ((steps.map (fun step => (step.1, step.2.val))).take q) = true) ∧
      (∀ P', IsSubpathOf P P' s (lab (gm06Find4Target start steps q)) → P'.U = P_sv.U) ∧
      (∀ T', IsGenTail P T' (lab (gm06Find4Target start steps q)) t → T'.U = T.U) ∧
      (incV[(gm06Find4Target start steps q).val]?.getD 0 ≠ 0 →
        ((gm06Find4Graph ends ordinary incV incE upper start steps q).Reachable start
            (gm06Find4Target start steps q) ↔
          ∃ Wc : GraphWalk Γ.toGraph s (lab (gm06Find4Target start steps q)),
            (∀ x ∈ Wc.support, IsGenCandVertex Γ Rc B.U T
              (lab (gm06Find4Target start steps q)) x) ∧
            ∀ e ∈ Wc.edges, IsGenCandEdge Γ Rc B.U Eok T (lab (gm06Find4Target start steps q)) e)) := by
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  obtain ⟨x, W₁, W₂, hx, h1, h2, h3, h4⟩ := GraphWalk.exists_split_take_drop W q (hlen ▸ hq)
  have hxt : x = lab (gm06Find4Target start steps q) := by
    rw [hWsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hq1 hq] at hx
    exact (Option.some.inj hx).symm
  subst hxt
  have hnd : W.support.Nodup := hWs
  have hs0 := GraphWalk.support_getElem?_zero W
  have hsx : s ≠ lab (gm06Find4Target start steps q) := by
    intro h
    have := nodup_index_eq_of_getElem? hnd (hs0.trans (congrArg some h)) hx
    omega
  have hxP : lab (gm06Find4Target start steps q) ∈ P.V := by
    rw [hWV]; exact List.mem_of_getElem? hx
  have hW₁s : W₁.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h1]; exact hnd.sublist (List.take_sublist _ _)
  have hW₂s : W₂.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h2]; exact hnd.sublist (List.drop_sublist _ _)
  have hsub₁ : IsSubpathOf P (walkDrawing P W₁) s (lab (gm06Find4Target start steps q)) :=
    ⟨walkDrawing_isSubdrawing P W₁, walkDrawing_U_subset P W₁,
      isPathDrawing_walkDrawing_of_isSimple P hW₁s hsx⟩
  have hsuppLen : W.support.length = steps.length + 1 := by
    rw [GraphWalk.support_length W, hlen]
  have htail : IsGenTail P (walkDrawing P W₂) (lab (gm06Find4Target start steps q)) t := by
    by_cases hqr : q = steps.length
    · have hl1 : W₂.support.length = 1 := by rw [h2, List.length_drop]; omega
      have hxt : lab (gm06Find4Target start steps q) = t := GraphWalk.eq_of_support_length_one W₂ hl1
      have hsupp : W₂.support = [lab (gm06Find4Target start steps q)] := by
        rw [W₂.support_eq_cons] at hl1 ⊢
        simp only [List.length_cons, add_eq_right, List.length_eq_zero_iff] at hl1
        rw [hl1]
      have hedges : W₂.edges = [] := by
        rw [h4, List.drop_eq_nil_iff, hWedges, List.length_map]; omega
      refine Or.inl ⟨hxt, ?_, ?_⟩
      · ext y
        rw [mem_walkDrawing_U, hsupp, hedges]
        simp
      · rw [walkDrawing_V, hsupp]
        ext y; simp
    · have hne : lab (gm06Find4Target start steps q) ≠ t := by
        intro h
        have ht := GraphWalk.support_getElem?_length W
        have ht' : W.support[steps.length]? = some (lab (gm06Find4Target start steps q)) := by
          rw [← hlen]; exact ht.trans (congrArg some h.symm)
        exact hqr (nodup_index_eq_of_getElem? hnd hx ht')
      exact Or.inr ⟨walkDrawing_isSubdrawing P W₂, walkDrawing_U_subset P W₂,
        isPathDrawing_walkDrawing_of_isSimple P hW₂s hne⟩
  have hsPV : s ∈ P.V := by rw [hWV]; exact W.start_mem_support
  have hsP : s ∈ P.U := P.V_subset_U hsPV
  have hxPU : lab (gm06Find4Target start steps q) ∈ P.U := P.V_subset_U hxP
  have htP : t ∈ P.U := P.V_subset_U (by rw [hWV]; exact W.end_mem_support)
  refine ⟨walkDrawing P W₁, walkDrawing P W₂, hx, hsub₁, htail, ?_, ?_, ?_, ?_⟩
  · -- the prefix test
    rw [walkDrawing_U_subset_iff _ W₁ hRc, gm06PrefixOK_iff, h1, h3, hWsupp, hWedges]
    have hpv := rep.path_incV
    have hpe := rep.path_incE
    have hmemT : ∀ st ∈ steps.take q, ((st.1, st.2.val) : ℕ × ℕ) ∈
        (steps.map (fun step => (step.1, step.2.val))).take q := by
      intro st hst
      rw [← List.map_take]; exact List.mem_map.mpr ⟨st, hst, rfl⟩
    have hlabT : ∀ st ∈ steps.take q,
        lab st.2 ∈ ((find4PathLabels start steps).map lab).take (q + 1) := by
      intro st hst
      rw [← List.map_take]
      refine List.mem_map.mpr ⟨st.2, ?_, rfl⟩
      simp only [find4PathLabels, List.take_succ_cons]
      refine List.mem_cons_of_mem _ ?_
      rw [← List.map_take]; exact List.mem_map.mpr ⟨st, hst, rfl⟩
    have hpathT : ∀ st ∈ steps.take q, st.2 ∈ find4PathLabels start steps := fun st hst =>
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨st, List.mem_of_mem_take hst, rfl⟩)
    constructor
    · rintro ⟨hV, hE⟩
      refine ⟨(hpv start List.mem_cons_self).mpr (hV _ ?_), fun st hst => ?_⟩
      · rw [← List.map_take]; exact List.mem_map.mpr ⟨start, by simp [find4PathLabels], rfl⟩
      rw [← List.map_take] at hst
      obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hst
      refine ⟨(hpe st' (List.mem_of_mem_take hst')).mpr (hE _ ?_),
        (hpv st'.2 (hpathT st' hst')).mpr (hV _ (hlabT st' hst'))⟩
      rw [← List.map_take]; exact List.mem_map.mpr ⟨st', hst', rfl⟩
    · rintro ⟨hs, hst⟩
      refine ⟨fun y hy => ?_, fun e he => ?_⟩
      · rw [← List.map_take] at hy
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hy
        simp only [find4PathLabels, List.take_succ_cons] at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact (hpv _ List.mem_cons_self).mp hs
        · rw [← List.map_take] at hu
          obtain ⟨st', hst', rfl⟩ := List.mem_map.mp hu
          exact (hpv st'.2 (hpathT st' hst')).mp (hst _ (hmemT st' hst')).2
      · rw [← List.map_take] at he
        obtain ⟨st', hst', rfl⟩ := List.mem_map.mp he
        exact (hpe st' (List.mem_of_mem_take hst')).mp (hst _ (hmemT st' hst')).1
  · intro P' hP'
    exact gen_subpath_U_eq hf hP'.2.2 hP'.2.1 hsub₁.2.2 hsub₁.2.1 hsP hxPU
  · intro T' hT'
    rcases hT' with ⟨hxt, hTU, -⟩ | hT'
    · rcases htail with ⟨-, hTU', -⟩ | htail
      · rw [hTU, hTU']
      · exact absurd hxt (isPathDrawing_start_ne_end htail.2.2)
    · rcases htail with ⟨hxt, -, -⟩ | htail
      · exact absurd hxt (isPathDrawing_start_ne_end hT'.2.2)
      · exact gen_subpath_U_eq hf hT'.2.2 hT'.2.1 htail.2.2 htail.2.1 hxPU htP
  · intro hinc
    have hcandV := fun z hz => gen_candidateVertex_iff rep hPΓ hWs hWsupp hx h2 z hz
    have hsG : s ∈ Γ.V := hPΓ.1 hsPV
    have hcs : IsGenCandVertex Γ Rc B.U (walkDrawing P W₂) (lab (gm06Find4Target start steps q)) s := by
      refine ⟨hsG, hsR, fun hsB => disjoint_left.mp hPB hsP hsB, ?_⟩
      intro hsT
      exfalso
      have hs2 := mem_support_of_mem_walkDrawing_U hPΓ W₂ hsT hsG
      rw [h2] at hs2
      rw [W.support_eq_cons] at hs2 hnd
      have hsub : (s :: W.support.tail).drop q ⊆ W.support.tail := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        rw [List.drop_succ_cons]
        exact fun y hy => List.mem_of_mem_drop hy
      exact (List.nodup_cons.mp hnd).1 (hsub hs2)
    have hlabs : lab start = s := by
      have := hWsupp ▸ hs0
      simpa [find4PathLabels] using this
    have hstartInc : incV[start.val]?.getD 0 ≠ 0 :=
      (rep.path_incV start List.mem_cons_self).mpr (hlabs ▸ hsR)
    have hgoodS : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q start.val =
        true := (hcandV start hstartInc).mpr (hlabs ▸ hcs)
    have hgoodT : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q
        (gm06Find4Target start steps q).val = true := by
      refine (hcandV (gm06Find4Target start steps q) hinc).mpr
        ⟨(rep.vertex_sound (gm06Find4Target start steps q) hinc).1,
          (rep.vertex_sound (gm06Find4Target start steps q) hinc).2,
          fun h => disjoint_left.mp hPB hxPU h, fun _ => rfl⟩
    rw [reachable_iff_reflTransGen_of_match' _
      (fun z => gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q z.val = true)
      (GenCandStep Γ Rc B.U Eok (walkDrawing P W₂) (lab (gm06Find4Target start steps q)))
      (gen_find4Graph_adj_step rep hPΓ hWs hWsupp hx h2)
      (gen_find4Graph_match rep hPΓ hWs hWsupp hx h2)
      (fun u w hu hw huw => rep.inj u w
        (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1)
        (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hw).1) huw) hgoodS hgoodT,
      exists_genCand_walk_iff_reflTransGen, hlabs]
    exact ⟨fun h => ⟨hcs, h⟩, fun h => h.2⟩

/-- A tail of a subdrawing `P` of `Γ` from a vertex of `P` is a subdrawing of `Γ`. -/
theorem isSubdrawing_of_genTail (hPΓ : P.IsSubdrawing Γ) {T : Drawing S} {v : S}
    (hv : v ∈ P.V) (hT : IsGenTail P T v t) : T.IsSubdrawing Γ := by
  rcases hT with ⟨-, hU, hV⟩ | ⟨hTP, -, -⟩
  · refine ⟨?_, ?_⟩
    · rw [hV]; exact singleton_subset_iff.mpr (hPΓ.1 hv)
    · intro e he
      exfalso
      obtain ⟨x, hx⟩ := (he.2.2.1 : IsPathConnected e).nonempty
      have hxU : x ∈ T.U := (he.2.1 hx).1
      have hxV : x ∉ T.V := (he.2.1 hx).2
      rw [hU] at hxU
      rw [hV] at hxV
      exact hxV hxU
  · exact hTP.trans hPΓ

/-- **`FIND_4` is sound**, in any setting. -/
theorem genReduction4At_of_find4_some
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) (hB : B.IsSubdrawing Γ) {f : Curve S}
    (hf : ParametrizesSet f P.U s t) (hRc : IsClosed Rc) (hsR : s ∈ Rc) (hPB : Disjoint P.U B.U)
    {j : ℕ} {path : List ℕ}
    (h : gm06Find4 ends ordinary incV incE upper start steps = some (j, path)) :
    GenReduction4At Γ P s t Rc B Eok := by
  obtain ⟨hj, p, -, -⟩ := gm06Find4_sound ends ordinary incV incE upper start steps j path h
  rw [mem_gm06Reduction4Contacts_iff] at hj
  obtain ⟨q, hq, rfl, hinc, hpre⟩ := hj
  simp only [List.length_map] at hq
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  obtain ⟨P_sv, T, hx, hsub, htail, hpreIff, -, -, hreach⟩ :=
    gen_find4_contact rep hPΓ hf hRc hsR hPB hWs hWV hWsupp hWedges (q := q + 1) (by omega)
      (by omega)
  have htgt : gm06Find4Target start steps (q + 1) = steps[q].2 := by
    simp [gm06Find4Target, List.getElem?_eq_getElem hq]
  have hinc' : incV[(gm06Find4Target start steps (q + 1)).val]?.getD 0 ≠ 0 := by
    rw [htgt]; simpa [List.getElem?_eq_getElem hq] using hinc
  obtain ⟨Wc, hWcV, hWcE⟩ := (hreach hinc').mp p.reachable
  have hvP : lab (gm06Find4Target start steps (q + 1)) ∈ P.V := by
    rw [hWV]; exact List.mem_of_getElem? hx
  have hsv : s ≠ lab (gm06Find4Target start steps (q + 1)) :=
    isPathDrawing_start_ne_end hsub.2.2
  have hTG := isSubdrawing_of_genTail hPΓ hvP htail
  obtain ⟨Q, hQG, hQ, hQR, hQT, hQP, hQE⟩ :=
    (exists_genCand_walk_iff Γ Rc hB Eok hRc hTG hsv).mpr ⟨Wc, hWcV, hWcE⟩
  refine ⟨_, P_sv, T, Q, hvP, (rep.vertex_sound _ hinc').2, hsub, ?_, htail,
    hQG, hQ, hQR, hQT, hQP, hQE⟩
  rw [hpreIff]
  simpa using hpre

/-- **`FIND_4` is complete**, in any setting. -/
theorem not_genReduction4At_of_find4_none
    (rep : Find4GenRep Γ P s t Rc B Eok ends ordinary incV incE upper start steps lab edgeLab)
    (hPΓ : P.IsSubdrawing Γ) (hB : B.IsSubdrawing Γ) {f : Curve S}
    (hf : ParametrizesSet f P.U s t) (hRc : IsClosed Rc) (hsR : s ∈ Rc) (hPB : Disjoint P.U B.U)
    (h : gm06Find4 ends ordinary incV incE upper start steps = none) :
    ¬ GenReduction4At Γ P s t Rc B Eok := by
  rintro ⟨w, P_sw, T', Q, hw, hwR, hsw, hpre, hT', hQG, hQ, hQR, hQT, hQP, hQE⟩
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  rw [hWV] at hw
  obtain ⟨q, hqw⟩ := List.mem_iff_getElem?.mp hw
  have hqlt : q < W.support.length := (List.getElem?_eq_some_iff.mp hqw).1
  rw [GraphWalk.support_length W, hlen] at hqlt
  have hsw_ne : s ≠ w := isPathDrawing_start_ne_end hsw.2.2
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [GraphWalk.support_getElem?_zero W] at hqw
    exact hsw_ne (Option.some.inj hqw)
  obtain ⟨P_sv, T, hx, hsub, htail, hpreIff, huniqP, huniqT, hreach⟩ :=
    gen_find4_contact rep hPΓ hf hRc hsR hPB hWs hWV hWsupp hWedges (q := q) (by omega) (by omega)
  have hwv : lab (gm06Find4Target start steps q) = w := Option.some.inj (hx.symm.trans hqw)
  have htgtP : gm06Find4Target start steps q ∈ find4PathLabels start steps :=
    List.mem_of_getElem? (find4PathLabels_getElem?_target start steps (by omega) (by omega))
  have hinc : incV[(gm06Find4Target start steps q).val]?.getD 0 ≠ 0 :=
    (rep.path_incV _ htgtP).mpr (hwv ▸ hwR)
  have hcontact : q ∈ gm06Reduction4Contacts incV incE start.val
      (steps.map (fun step => (step.1, step.2.val))) := by
    rw [mem_gm06Reduction4Contacts_iff]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have hq' : q' < steps.length := by omega
    refine ⟨q', by simpa using hq', rfl, ?_, ?_⟩
    · have htgt : gm06Find4Target start steps (q' + 1) = steps[q'].2 := by
        simp [gm06Find4Target, List.getElem?_eq_getElem hq']
      rw [htgt] at hinc
      simpa [List.getElem?_eq_getElem hq'] using hinc
    · by_contra hok
      rw [Bool.not_eq_false] at hok
      apply hpre
      rw [huniqP P_sw (hwv ▸ hsw)]
      exact hpreIff.mpr hok
  have hnot := (gm06Find4_none_iff ends ordinary incV incE upper start steps).mp h q hcontact
  have hTU : T'.U = T.U := huniqT T' (hwv ▸ hT')
  have hvP : lab (gm06Find4Target start steps q) ∈ P.V := by
    rw [hWV]; exact List.mem_of_getElem? hx
  have hTG := isSubdrawing_of_genTail hPΓ hvP htail
  have hQT' : Q.U ∩ T.U ⊆ {lab (gm06Find4Target start steps q)} := by
    rw [← hTU, hwv]; exact hQT
  obtain ⟨Wc, hWcV, hWcE⟩ := (exists_genCand_walk_iff Γ Rc hB Eok hRc hTG (hwv ▸ hsw_ne)).mp
    ⟨Q, hQG, hwv ▸ hQ, hQR, hQT', hQP, hQE⟩
  exact hnot ((hreach hinc).mpr ⟨Wc, hWcV, hWcE⟩)

end Rep


end GraphMinor.GM06
