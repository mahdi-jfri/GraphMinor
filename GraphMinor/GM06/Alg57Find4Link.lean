module

public import GraphMinor.GM06.Alg57CandidateGraph
public import GraphMinor.GM06.Alg57CandidateLabels
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
public import GraphMinor.Compute.GM06Find4
import GraphMinor.GM06.Alg57StripPathContact
import GraphMinor.GM06.Section5Red
import GraphMinor.GM11.Walks

/-!
# `FIND_4` and Reduction 4, for `k ≥ 2`

The search `FIND_4` of the Word RAM program, for one cut component (`gm06Find4`), works on lists:
vertex labels `Fin n`, the ends of each edge label (`ends`), the flags `ordinary`, the incidence
bits `incV` and `incE` of the selected face, the labels `upper` of the opposite boundary, and the
path `Pᵢ` as a start label and a list of steps (edge label, arrival vertex label). Here we say when
these lists represent the drawing (`Find4Rep`) and prove, for `k ≥ 2`:

* `exists_reduction4Step_of_find4_some`: if `FIND_4` returns a witness, a Reduction 4 step exists;
* `not_reduction4_at_of_find4_none`: if `FIND_4` returns none, there is no Reduction 4 at `Pᵢ`;
* `not_exists_reduction4Step_of_find4_none`: if `FIND_4` returns none for every `i`, no
  Reduction 4 applies.

`Find4Rep` asks that the incident labels represent the vertices of `G` in `closure Rᵢ`
injectively, that the incident ordinary edge labels represent the edges of `G` in `closure Rᵢ`,
that `upper` marks the vertices of `Pᵢ₊₁`, and that the path data list the vertices and edges of
`Pᵢ` in order. The incidence bits are read from the face orbit of `c̄ᵢ` in the cut graph `Kᵢ`; for
`k ≥ 2`, `region_incidence_of_no_reduction` reads the same incidence from the cuffed drawing.

The link between the two candidate graphs uses `not_mem_other_paths_iff_of_mem_closure_region`:
the program removes only `Pᵢ₊₁`, and the other paths do not meet `closure Rᵢ`.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-! ### Splitting a walk -/

/-- A walk splits at each position `q` into a prefix with the first `q` edges and a suffix with
the rest. -/
theorem GraphWalk.exists_split_take_drop {α β : Type*} {Gr : Graph α β} {u v : α}
    (W : GraphWalk Gr u v) (q : ℕ) (hq : q ≤ W.length) :
    ∃ (x : α) (W₁ : GraphWalk Gr u x) (W₂ : GraphWalk Gr x v), W.support[q]? = some x ∧
      W₁.support = W.support.take (q + 1) ∧ W₂.support = W.support.drop q ∧
      W₁.edges = W.edges.take q ∧ W₂.edges = W.edges.drop q := by
  induction W generalizing q with
  | nil h =>
    have hq0 : q = 0 := by simpa [GraphWalk.length, GraphWalk.edges] using hq
    subst hq0
    exact ⟨_, .nil h, .nil h, rfl, rfl, rfl, rfl, rfl⟩
  | @cons a y b e hl rest ih =>
    cases q with
    | zero =>
      exact ⟨a, .nil hl.left_mem, .cons hl rest, rfl, rfl, rfl, rfl, rfl⟩
    | succ q =>
      have hq' : q ≤ rest.length := by
        simpa [GraphWalk.length, GraphWalk.edges] using hq
      obtain ⟨x, W₁, W₂, hx, h1, h2, h3, h4⟩ := ih q hq'
      refine ⟨x, .cons hl W₁, W₂, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [GraphWalk.support] using hx
      · simp [GraphWalk.support, h1]
      · simp [GraphWalk.support, h2]
      · simp [GraphWalk.edges, h3]
      · simp [GraphWalk.edges, h4]

/-- A walk whose support has one point is closed. -/
theorem GraphWalk.eq_of_support_length_one {α β : Type*} {Gr : Graph α β} {u v : α}
    (W : GraphWalk Gr u v) (h : W.support.length = 1) : u = v := by
  cases W with
  | nil _ => rfl
  | cons hl rest =>
    exfalso
    rw [GraphWalk.support, rest.support_eq_cons] at h
    simp at h

theorem GraphWalk.support_length {α β : Type*} {Gr : Graph α β} {u v : α}
    (W : GraphWalk Gr u v) : W.support.length = W.length + 1 := by
  induction W with
  | nil _ => rfl
  | cons hl rest ih => simp [GraphWalk.support, GraphWalk.length, GraphWalk.edges, ih,
      GraphWalk.length] at *

/-- A vertex of `G` in the drawing of a walk of a subdrawing `P` is on the walk. -/
theorem mem_support_of_mem_walkDrawing_U {S : Type*} [TopologicalSpace S] [T1Space S] {P Γ : Drawing S}
    (hP : P.IsSubdrawing Γ) {a b : S} (W : GraphWalk P.toGraph a b) {y : S}
    (hy : y ∈ (walkDrawing P W).U) (hyV : y ∈ Γ.V) : y ∈ W.support := by
  rcases (mem_walkDrawing_U P W).mp hy with hy | ⟨e, he, hye⟩
  · exact hy
  obtain ⟨z, z', hz, hz', hl⟩ := walk_exists_isLink_of_mem_edges W he
  have hends : closure e ∩ P.V = {z, z'} := hl.2.2.2
  have hyP : y ∈ closure e ∩ P.V := by
    rw [hP.closure_inter_V hl.1]
    exact ⟨hye, hyV⟩
  rw [hends] at hyP
  rcases hyP with rfl | hy
  · exact hz
  · rw [mem_singleton_iff.mp hy]; exact hz'

/-- The drawing of a walk of a subdrawing lies in that subdrawing. -/
theorem walkDrawing_U_subset {S : Type*} [TopologicalSpace S] [T1Space S] (P : Drawing S) {a b : S}
    (W : GraphWalk P.toGraph a b) : (walkDrawing P W).U ⊆ P.U :=
  (walkDrawing_isSubdrawing P W).U_subset

/-- The drawing of a walk lies in a closed set exactly when its vertices and edges do. -/
theorem walkDrawing_U_subset_iff {S : Type*} [TopologicalSpace S] [T1Space S] (P : Drawing S) {a b : S}
    (W : GraphWalk P.toGraph a b) {C : Set S} (hC : IsClosed C) :
    (walkDrawing P W).U ⊆ C ↔ (∀ y ∈ W.support, y ∈ C) ∧ ∀ e ∈ W.edges, e ⊆ C := by
  constructor
  · intro h
    refine ⟨fun y hy => h ((mem_walkDrawing_U P W).mpr (Or.inl hy)), fun e he y hye => ?_⟩
    exact h ((mem_walkDrawing_U P W).mpr (Or.inr ⟨e, he, subset_closure hye⟩))
  · rintro ⟨hV, hE⟩ y hy
    rcases (mem_walkDrawing_U P W).mp hy with hy | ⟨e, he, hye⟩
    · exact hV y hy
    · exact closure_minimal (hE e he) hC hye

theorem GraphWalk.support_getElem?_length {α β : Type*} {Gr : Graph α β} {u v : α}
    (W : GraphWalk Gr u v) : W.support[W.length]? = some v := by
  induction W with
  | nil _ => rfl
  | cons hl rest ih =>
    simpa [GraphWalk.support, GraphWalk.length, GraphWalk.edges] using ih

theorem GraphWalk.support_getElem?_zero {α β : Type*} {Gr : Graph α β} {u v : α}
    (W : GraphWalk Gr u v) : W.support[0]? = some u := by
  rw [W.support_eq_cons]; rfl

theorem nodup_index_eq_of_getElem? {α : Type*} {l : List α} (hl : l.Nodup) {a b : ℕ} {x : α}
    (ha : l[a]? = some x) (hb : l[b]? = some x) : a = b := by
  obtain ⟨ha', hax⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hb', hbx⟩ := List.getElem?_eq_some_iff.mp hb
  exact (hl.getElem_inj_iff (hi := ha') (hj := hb')).mp (hax.trans hbx.symm)

variable {k : ℕ} {G : Drawing ClosedCylinder}

/-! ### The representation -/

/-- The vertex labels of the path, in order, as the program lists them. -/
abbrev find4PathLabels {n : ℕ} (start : Fin n) (steps : List (ℕ × Fin n)) : List (Fin n) :=
  start :: steps.map Prod.snd

/-- **The lists of `FIND_4` represent the drawing** at the path `Pᵢ`.

* `vertex_sound`, `vertex_cover`, `inj`: labels with `incV` set are vertices of `G` in
  `closure Rᵢ`, every such vertex has one, and labels with `incV` set or on the path are
  distinct points.
* `upper_iff`: an incident label is in `upper` exactly when its vertex is on `Pᵢ₊₁`.
* `edge_sound`, `edge_cover`: an ordinary incident edge label is an edge of `G` in `closure Rᵢ`
  joining its listed ends; every edge of `G` in `closure Rᵢ` with distinct ends has such a label,
  with incident end labels.
* `path_walk`, `path_incV`, `path_incE`: the path data list the vertices and edges of a simple walk
  tracing `Pᵢ`, and their incidence bits are the incidence with `closure Rᵢ`. -/
structure Find4Rep (L : CylinderLinkage k G) (i : Fin k) {n : ℕ}
    (ends : List (ℕ × ℕ)) (ordinary : List Bool) (incV incE upper : List ℕ)
    (start : Fin n) (steps : List (ℕ × Fin n))
    (lab : Fin n → ClosedCylinder) (edgeLab : ℕ → Set ClosedCylinder) : Prop where
  vertex_sound : ∀ u : Fin n, incV[u.val]?.getD 0 ≠ 0 →
    lab u ∈ G.V ∧ lab u ∈ closure (cylinderRegion k G i)
  vertex_cover : ∀ x ∈ G.V, x ∈ closure (cylinderRegion k G i) →
    ∃ u : Fin n, incV[u.val]?.getD 0 ≠ 0 ∧ lab u = x
  inj : ∀ u w : Fin n, (incV[u.val]?.getD 0 ≠ 0 ∨ u ∈ find4PathLabels start steps) →
    (incV[w.val]?.getD 0 ≠ 0 ∨ w ∈ find4PathLabels start steps) → lab u = lab w → u = w
  upper_iff : ∀ u : Fin n, incV[u.val]?.getD 0 ≠ 0 →
    (u.val ∈ upper ↔ lab u ∈ (L.pathDrawing (finSuccCycle i)).U)
  edge_sound : ∀ e, ordinary[e]?.getD false = true → incE[e]?.getD 0 ≠ 0 →
    ∃ u w : Fin n, ends[e]?.getD (0, 0) = (u.val, w.val) ∧ edgeLab e ⊆ closure (cylinderRegion k G i) ∧
      G.toGraph.IsLink (edgeLab e) (lab u) (lab w)
  edge_cover : ∀ f x y, G.toGraph.IsLink f x y → x ≠ y → f ⊆ closure (cylinderRegion k G i) →
    ∃ e < ends.length, ordinary[e]?.getD false = true ∧ incE[e]?.getD 0 ≠ 0 ∧ edgeLab e = f ∧
      ∃ u w : Fin n, ends[e]?.getD (0, 0) = (u.val, w.val) ∧ incV[u.val]?.getD 0 ≠ 0 ∧
        incV[w.val]?.getD 0 ≠ 0 ∧ ((lab u = x ∧ lab w = y) ∨ (lab u = y ∧ lab w = x))
  path_walk : ∃ W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1),
    W.IsSimple ∧ (L.pathDrawing i).V = {x | x ∈ W.support} ∧
    W.support = (find4PathLabels start steps).map lab ∧ W.edges = steps.map (fun st => edgeLab st.1)
  path_incV : ∀ u ∈ find4PathLabels start steps,
    (incV[u.val]?.getD 0 ≠ 0 ↔ lab u ∈ closure (cylinderRegion k G i))
  path_incE : ∀ st ∈ steps,
    (incE[st.1]?.getD 0 ≠ 0 ↔ edgeLab st.1 ⊆ closure (cylinderRegion k G i))

/-! ### Labelled reachability -/

/-- Reachability in a labelled graph is a chain of steps, when adjacency gives a step and each step
from a good label is matched by a good label. -/
theorem reachable_iff_reflTransGen_of_match {n : ℕ} (H : SimpleGraph (Fin n))
    {lab : Fin n → ClosedCylinder} (good : Fin n → Prop) (step : ClosedCylinder → ClosedCylinder → Prop)
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

/-! ### The candidate graph at one contact -/

section Contact

variable {L : CylinderLinkage k G} {i : Fin k} {n : ℕ}
  {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
  {start : Fin n} {steps : List (ℕ × Fin n)}
  {lab : Fin n → ClosedCylinder} {edgeLab : ℕ → Set ClosedCylinder}

theorem find4PathVertices_eq (start : Fin n) (steps : List (ℕ × Fin n)) :
    gm06Find4PathVertices start steps = (find4PathLabels start steps).map Fin.val := by
  simp [gm06Find4PathVertices, find4PathLabels]

theorem mem_drop_pathVertices_iff (start : Fin n) (steps : List (ℕ × Fin n)) (u : Fin n) (m : ℕ) :
    u.val ∈ (gm06Find4PathVertices start steps).drop m ↔
      u ∈ (find4PathLabels start steps).drop m := by
  rw [find4PathVertices_eq, ← List.map_drop]
  constructor
  · intro h
    obtain ⟨w, hw, hwu⟩ := List.mem_map.mp h
    rwa [Fin.ext hwu] at hw
  · intro h
    exact List.mem_map.mpr ⟨u, h, rfl⟩

/-- The candidate vertex test of the program at contact `q` agrees with the candidate vertex of the
drawing, for an incident label, when `T` is the tail drawn from the walk. -/
theorem candidateVertex_iff (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1)}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : ClosedCylinder} {W₂ : GraphWalk (L.pathDrawing i).toGraph v (L.curve i 1)}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q)
    (u : Fin n) (hu : incV[u.val]?.getD 0 ≠ 0) :
    gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true ↔
      IsReduction4CandidateVertex L i (walkDrawing (L.pathDrawing i) W₂) v (lab u) := by
  rw [gm06CandidateVertex_iff, mem_drop_pathVertices_iff]
  have hsound := rep.vertex_sound u hu
  have hPG : (L.pathDrawing i).IsSubdrawing G := (L.isSubdrawing i).1
  have hdrop : W.support.drop q = v :: W.support.drop (q + 1) := by
    rw [List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hv).1]
    rw [(List.getElem?_eq_some_iff.mp hv).2]
  have hvnot : v ∉ W.support.drop (q + 1) := by
    have hnd : (W.support.drop q).Nodup := hWs.sublist (List.drop_sublist _ _)
    rw [hdrop] at hnd
    exact (List.nodup_cons.mp hnd).1
  -- membership of `lab u` in the tail
  have htail : lab u ∈ (walkDrawing (L.pathDrawing i) W₂).U ∧ lab u ≠ v ↔
      u ∈ (find4PathLabels start steps).drop (q + 1) := by
    constructor
    · rintro ⟨hU, hne⟩
      have hs := mem_support_of_mem_walkDrawing_U hPG W₂ hU hsound.1
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
  have hother := not_mem_other_paths_iff_of_mem_closure_region L hk hG hθ i hsound.2
  have hupper := rep.upper_iff u hu
  constructor
  · rintro ⟨-, hup, hdr⟩
    refine ⟨hsound.1, hsound.2, hother.mpr (fun h => hup (hupper.mpr h)), ?_⟩
    intro hT
    by_contra hne
    exact hdr (htail.mp ⟨hT, hne⟩)
  · rintro ⟨-, -, hP, hT⟩
    refine ⟨hu, fun h => hother.mp hP (hupper.mp h), fun h => ?_⟩
    obtain ⟨hU, hne⟩ := htail.mpr h
    exact hne (hT hU)

/-- Adjacency in the program's candidate graph at contact `q` is a candidate step of the drawing. -/
theorem find4Graph_adj_step (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1)}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : ClosedCylinder} {W₂ : GraphWalk (L.pathDrawing i).toGraph v (L.curve i 1)}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q) (u w : Fin n)
    (h : (gm06Find4Graph ends ordinary incV incE upper start steps q).Adj u w) :
    Reduction4CandidateStep L i (walkDrawing (L.pathDrawing i) W₂) v (lab u) (lab w) := by
  obtain ⟨-, e, he, hends⟩ := h
  rw [gm06CandidateEdges_mem_iff] at he
  obtain ⟨-, hord, hinc, hc1, hc2⟩ := he
  obtain ⟨u', w', hends', hsub, hl⟩ := rep.edge_sound e hord hinc
  have hcand : ∀ z : Fin n, gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q
      z.val = true → IsReduction4CandidateVertex L i (walkDrawing (L.pathDrawing i) W₂) v (lab z) := by
    intro z hz
    have hzi : incV[z.val]?.getD 0 ≠ 0 := ((gm06CandidateVertex_iff _ _ _ _ _).mp hz).1
    exact (candidateVertex_iff rep hk hG hθ hWs hWsupp hv h2 z hzi).mp hz
  rw [hends'] at hc1 hc2
  have hcu := hcand u' hc1
  have hcw := hcand w' hc2
  have hedge : IsReduction4CandidateEdge L i (walkDrawing (L.pathDrawing i) W₂) v (edgeLab e) := by
    refine ⟨hl.1, hsub, fun x hx => ?_⟩
    have hx' : x ∈ ({lab u', lab w'} : Set ClosedCylinder) := hl.2.2.2 ▸ hx
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

/-- A candidate step of the drawing from a good label is matched in the program's candidate
graph. -/
theorem find4Graph_match (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1)}
    (hWs : W.IsSimple) (hWsupp : W.support = (find4PathLabels start steps).map lab)
    {q : ℕ} {v : ClosedCylinder} {W₂ : GraphWalk (L.pathDrawing i).toGraph v (L.curve i 1)}
    (hv : W.support[q]? = some v) (h2 : W₂.support = W.support.drop q) (x y : ClosedCylinder)
    (hxy : Reduction4CandidateStep L i (walkDrawing (L.pathDrawing i) W₂) v x y) (u : Fin n)
    (hu : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q u.val = true)
    (hux : lab u = x) :
    ∃ w : Fin n, gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q w.val = true ∧
      lab w = y ∧ (u = w ∨ (gm06Find4Graph ends ordinary incV incE upper start steps q).Adj u w) := by
  obtain ⟨f, ⟨hfE, hfR, hfc⟩, hl⟩ := hxy
  by_cases hxy : x = y
  · exact ⟨u, hu, hux.trans hxy, Or.inl rfl⟩
  have hui : incV[u.val]?.getD 0 ≠ 0 := ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1
  have hcy : IsReduction4CandidateVertex L i (walkDrawing (L.pathDrawing i) W₂) v y :=
    hfc y (by rw [hl.2.2.2]; exact mem_insert_of_mem _ (mem_singleton _))
  obtain ⟨e, helen, hord, hinc, hfe, u', w', hends, hu'i, hw'i, hor⟩ :=
    rep.edge_cover f x y hl hxy hfR
  have hgood : ∀ z : Fin n, incV[z.val]?.getD 0 ≠ 0 → lab z = y →
      gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q z.val = true := by
    intro z hz hzy
    rw [candidateVertex_iff rep hk hG hθ hWs hWsupp hv h2 z hz, hzy]
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

/-- The path label at position `q ≥ 1` is the target of `FIND_4` at `q`. -/
theorem find4PathLabels_getElem?_target (start : Fin n) (steps : List (ℕ × Fin n)) {q : ℕ}
    (hq1 : 1 ≤ q) (hq : q ≤ steps.length) :
    (find4PathLabels start steps)[q]? = some (gm06Find4Target start steps q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hlt : q < steps.length := by omega
  simp [find4PathLabels, gm06Find4Target, List.getElem?_eq_getElem hlt]

/-- Any two subpaths of `Pᵢ` with the same ends have the same points. -/
theorem subpath_U_eq (L : CylinderLinkage k G) (i : Fin k) {A A' : Drawing ClosedCylinder}
    {x y : ClosedCylinder} (hA : IsPathDrawing A x y) (hAP : A.U ⊆ (L.pathDrawing i).U)
    (hA' : IsPathDrawing A' x y) (hA'P : A'.U ⊆ (L.pathDrawing i).U)
    (hx : x ∈ (L.pathDrawing i).U) (hy : y ∈ (L.pathDrawing i).U) : A.U = A'.U := by
  obtain ⟨hfi, hfr, -, -⟩ := L.curve_parametrizes i
  rw [← hfr] at hx hy hAP hA'P
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  obtain ⟨g, hgi, hgr, hg0, hg1⟩ := hA.2
  obtain ⟨g', hgi', hgr', hg0', hg1'⟩ := hA'.2
  rw [← hgr, ← hgr', range_eq_image_uIcc_of_subarc hfi hgi (hgr ▸ hAP) (hg0.trans ha.symm)
    (hg1.trans hb.symm), range_eq_image_uIcc_of_subarc hfi hgi' (hgr' ▸ hA'P)
    (hg0'.trans ha.symm) (hg1'.trans hb.symm)]

/-- **The setup at one contact.** For a position `1 ≤ q ≤ r` of the path, with contact `v`, the
prefix and tail drawn from the walk are a subpath and a tail of `Pᵢ` (unique up to their points);
the prefix test of the program is the prefix condition; and, when the contact is incident,
reachability in the program's candidate graph is a walk of `G` in the candidate graph of the
drawing. -/
theorem find4_contact (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {W : GraphWalk (L.pathDrawing i).toGraph (cylinderM1Point k i) (L.curve i 1)}
    (hWs : W.IsSimple) (hWV : (L.pathDrawing i).V = {x | x ∈ W.support})
    (hWsupp : W.support = (find4PathLabels start steps).map lab)
    (hWedges : W.edges = steps.map (fun st => edgeLab st.1))
    {q : ℕ} (hq1 : 1 ≤ q) (hq : q ≤ steps.length) :
    ∃ (P_sv T : Drawing ClosedCylinder),
      W.support[q]? = some (lab (gm06Find4Target start steps q)) ∧
      IsSubpathOf (L.pathDrawing i) P_sv (cylinderM1Point k i) (lab (gm06Find4Target start steps q)) ∧
      IsSection5Tail (L.pathDrawing i) T (lab (gm06Find4Target start steps q)) (L.curve i 1) ∧
      (P_sv.U ⊆ closure (cylinderRegion k G i) ↔ gm06PrefixOK incV incE start.val
        ((steps.map (fun step => (step.1, step.2.val))).take q) = true) ∧
      (∀ P', IsSubpathOf (L.pathDrawing i) P' (cylinderM1Point k i)
        (lab (gm06Find4Target start steps q)) → P'.U = P_sv.U) ∧
      (∀ T', IsSection5Tail (L.pathDrawing i) T' (lab (gm06Find4Target start steps q))
        (L.curve i 1) → T'.U = T.U) ∧
      (incV[(gm06Find4Target start steps q).val]?.getD 0 ≠ 0 →
        ((gm06Find4Graph ends ordinary incV incE upper start steps q).Reachable start
            (gm06Find4Target start steps q) ↔
          ∃ Wc : GraphWalk G.toGraph (cylinderM1Point k i) (lab (gm06Find4Target start steps q)),
            (∀ x ∈ Wc.support, IsReduction4CandidateVertex L i T
              (lab (gm06Find4Target start steps q)) x) ∧
            ∀ e ∈ Wc.edges, IsReduction4CandidateEdge L i T (lab (gm06Find4Target start steps q)) e)) := by
  have hPG : (L.pathDrawing i).IsSubdrawing G := (L.isSubdrawing i).1
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  obtain ⟨x, W₁, W₂, hx, h1, h2, h3, h4⟩ := GraphWalk.exists_split_take_drop W q (hlen ▸ hq)
  have hxt : x = lab (gm06Find4Target start steps q) := by
    rw [hWsupp, List.getElem?_map, find4PathLabels_getElem?_target start steps hq1 hq] at hx
    exact (Option.some.inj hx).symm
  subst hxt
  have hnd : W.support.Nodup := hWs
  have hs0 := GraphWalk.support_getElem?_zero W
  have hsx : (cylinderM1Point k i) ≠ lab (gm06Find4Target start steps q) := by
    intro h
    have := nodup_index_eq_of_getElem? hnd (hs0.trans (congrArg some h)) hx
    omega
  have hxP : lab (gm06Find4Target start steps q) ∈ (L.pathDrawing i).V := by rw [hWV]; exact List.mem_of_getElem? hx
  have hW₁s : W₁.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h1]; exact hnd.sublist (List.take_sublist _ _)
  have hW₂s : W₂.IsSimple := by
    unfold GraphWalk.IsSimple; rw [h2]; exact hnd.sublist (List.drop_sublist _ _)
  have hsub₁ : IsSubpathOf (L.pathDrawing i) (walkDrawing (L.pathDrawing i) W₁) (cylinderM1Point k i) (lab (gm06Find4Target start steps q)) :=
    ⟨walkDrawing_isSubdrawing (L.pathDrawing i) W₁, walkDrawing_U_subset (L.pathDrawing i) W₁,
      isPathDrawing_walkDrawing_of_isSimple (L.pathDrawing i) hW₁s hsx⟩
  have hsuppLen : W.support.length = steps.length + 1 := by rw [GraphWalk.support_length W, hlen]
  have htail : IsSection5Tail (L.pathDrawing i) (walkDrawing (L.pathDrawing i) W₂) (lab (gm06Find4Target start steps q)) (L.curve i 1) := by
    by_cases hqr : q = steps.length
    · have hl1 : W₂.support.length = 1 := by rw [h2, List.length_drop]; omega
      have hxt : lab (gm06Find4Target start steps q) = (L.curve i 1) := GraphWalk.eq_of_support_length_one W₂ hl1
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
    · have hne : lab (gm06Find4Target start steps q) ≠ (L.curve i 1) := by
        intro h
        have ht := GraphWalk.support_getElem?_length W
        have ht' : W.support[steps.length]? = some (lab (gm06Find4Target start steps q)) := by
          rw [← hlen]; exact ht.trans (congrArg some h.symm)
        exact hqr (nodup_index_eq_of_getElem? hnd hx ht')
      exact Or.inr ⟨walkDrawing_isSubdrawing (L.pathDrawing i) W₂, walkDrawing_U_subset (L.pathDrawing i) W₂,
        isPathDrawing_walkDrawing_of_isSimple (L.pathDrawing i) hW₂s hne⟩
  have hsP : (cylinderM1Point k i) ∈ (L.pathDrawing i).U := (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hxPU : lab (gm06Find4Target start steps q) ∈ (L.pathDrawing i).U := (L.pathDrawing i).V_subset_U hxP
  have htP : (L.curve i 1) ∈ (L.pathDrawing i).U := (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).2
  refine ⟨walkDrawing (L.pathDrawing i) W₁, walkDrawing (L.pathDrawing i) W₂, hx, hsub₁, htail, ?_, ?_, ?_, ?_⟩
  · -- the prefix test
    rw [walkDrawing_U_subset_iff _ W₁ isClosed_closure, gm06PrefixOK_iff, h1, h3, hWsupp, hWedges]
    have hpv := rep.path_incV
    have hpe := rep.path_incE
    have hmemT : ∀ st ∈ steps.take q, ((st.1, st.2.val) : ℕ × ℕ) ∈
        (steps.map (fun step => (step.1, step.2.val))).take q := by
      intro st hst
      rw [← List.map_take]; exact List.mem_map.mpr ⟨st, hst, rfl⟩
    have hlabT : ∀ st ∈ steps.take q, lab st.2 ∈ ((find4PathLabels start steps).map lab).take (q + 1) := by
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
    exact subpath_U_eq L i hP'.2.2 hP'.2.1 hsub₁.2.2 hsub₁.2.1 hsP hxPU
  · intro T' hT'
    rcases hT' with ⟨hxt, hTU, -⟩ | hT'
    · rcases htail with ⟨-, hTU', -⟩ | htail
      · rw [hTU, hTU']
      · exact absurd hxt (isPathDrawing_start_ne_end htail.2.2)
    · rcases htail with ⟨hxt, -, -⟩ | htail
      · exact absurd hxt (isPathDrawing_start_ne_end hT'.2.2)
      · exact subpath_U_eq L i hT'.2.2 hT'.2.1 htail.2.2 htail.2.1 hxPU htP
  · intro hinc
    have hcandV := fun z hz => candidateVertex_iff rep hk hG hθ hWs hWsupp hx h2 z hz
    -- the start is a candidate vertex
    have hsG : (cylinderM1Point k i) ∈ G.V := hPG.1 (isPathDrawing_end_vertices (L.isPath i)).1
    have hsR : (cylinderM1Point k i) ∈ closure (cylinderRegion k G i) := (initial_vertices_mem_closure_cylinderRegion hG i).1
    have hcs : IsReduction4CandidateVertex L i (walkDrawing (L.pathDrawing i) W₂) (lab (gm06Find4Target start steps q)) (cylinderM1Point k i) := by
      refine ⟨hsG, hsR, fun j hj hsj => disjoint_left.mp (L.pairwise_disjoint hj) hsj hsP, ?_⟩
      intro hsT
      exfalso
      have hs2 := mem_support_of_mem_walkDrawing_U hPG W₂ hsT hsG
      rw [h2] at hs2
      rw [W.support_eq_cons] at hs2 hnd
      have hsub : ((cylinderM1Point k i) :: W.support.tail).drop q ⊆ W.support.tail := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        rw [List.drop_succ_cons]
        exact fun y hy => List.mem_of_mem_drop hy
      exact (List.nodup_cons.mp hnd).1 (hsub hs2)
    have hlabs : lab start = (cylinderM1Point k i) := by
      have := hWsupp ▸ hs0
      simpa [find4PathLabels] using this
    have hstartInc : incV[start.val]?.getD 0 ≠ 0 :=
      (rep.path_incV start List.mem_cons_self).mpr (hlabs ▸ hsR)
    have hgoodS : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q start.val =
        true := (hcandV start hstartInc).mpr (hlabs ▸ hcs)
    have hgoodT : gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q (gm06Find4Target start steps q).val =
        true := by
      refine (hcandV (gm06Find4Target start steps q) hinc).mpr ⟨(rep.vertex_sound (gm06Find4Target start steps q) hinc).1, (rep.vertex_sound (gm06Find4Target start steps q) hinc).2,
        fun j hj h => disjoint_left.mp (L.pairwise_disjoint hj) h hxPU, fun _ => rfl⟩
    rw [reachable_iff_reflTransGen_of_match _
      (fun z => gm06CandidateVertex incV upper (gm06Find4PathVertices start steps) q z.val = true)
      (Reduction4CandidateStep L i (walkDrawing (L.pathDrawing i) W₂) (lab (gm06Find4Target start steps q)))
      (find4Graph_adj_step rep hk hG hθ hWs hWsupp hx h2)
      (find4Graph_match rep hk hG hθ hWs hWsupp hx h2)
      (fun u w hu hw huw => rep.inj u w
        (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hu).1)
        (Or.inl ((gm06CandidateVertex_iff _ _ _ _ _).mp hw).1) huw) hgoodS hgoodT,
      exists_candidate_walk_iff_reflTransGen, hlabs]
    exact ⟨fun h => ⟨hcs, h⟩, fun h => h.2⟩

/-- Membership in the program's contact list. -/
theorem mem_gm06Reduction4Contacts_iff (incV incE : List ℕ) (start : ℕ) (steps : List (ℕ × ℕ))
    (j : ℕ) : j ∈ gm06Reduction4Contacts incV incE start steps ↔
      ∃ q < steps.length, j = q + 1 ∧ incV[(steps[q]?.getD (0, 0)).2]?.getD 0 ≠ 0 ∧
        gm06PrefixOK incV incE start (steps.take (q + 1)) = false := by
  simp only [gm06Reduction4Contacts, List.mem_map, List.mem_filter, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true', gm06Incident, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨q, ⟨hq, hinc, hpre⟩, rfl⟩
    exact ⟨q, hq, rfl, hinc, hpre⟩
  · rintro ⟨q, hq, rfl, hinc, hpre⟩
    exact ⟨q, ⟨hq, hinc, hpre⟩, rfl⟩

end Contact

/-- **Reduction 4 at the path `Pᵢ`**, in the form of Lemma 13: a contact `w` on `Pᵢ` in
`closure Rᵢ` whose prefix is not in `closure Rᵢ`, and a path `Q` from `sᵢ` to `w` in `closure Rᵢ`
meeting the tail only at `w` and missing the other paths. -/
def Reduction4At (L : CylinderLinkage k G) (i : Fin k) : Prop :=
  ∃ (w : ClosedCylinder) (P_sw T Q : Drawing ClosedCylinder),
    w ∈ (L.pathDrawing i).V ∧ w ∈ closure (cylinderRegion k G i) ∧
    IsSubpathOf (L.pathDrawing i) P_sw (cylinderM1Point k i) w ∧
    ¬ P_sw.U ⊆ closure (cylinderRegion k G i) ∧
    IsSection5Tail (L.pathDrawing i) T w (L.curve i 1) ∧
    Q.IsSubdrawing G ∧ IsPathDrawing Q (cylinderM1Point k i) w ∧
    Q.U ⊆ closure (cylinderRegion k G i) ∧ Q.U ∩ T.U ⊆ {w} ∧
    ∀ j, j ≠ i → Disjoint Q.U (L.pathDrawing j).U

/-- For `k ≥ 2`, a Reduction 4 step exists exactly when Reduction 4 applies at some path. -/
theorem exists_reduction4Step_iff_exists_reduction4At (L : CylinderLinkage k G) (hk : 1 < k) :
    (∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L') ↔ ∃ i, Reduction4At L i := by
  constructor
  · rintro ⟨L', h⟩
    obtain ⟨i, w, P_sw, T, Q, h⟩ := exists_reduction4_path_of_step hk h
    exact ⟨i, w, P_sw, T, Q, h⟩
  · rintro ⟨i, w, P_sw, T, Q, hw, hwR, hsw, hpre, hT, hQG, hQ, hQR, hQT, hQP⟩
    exact exists_reduction4Step_of_path L hk i hw hwR hsw hpre hT hQG hQ hQR hQT hQP

section Main

variable {L : CylinderLinkage k G} {i : Fin k} {n : ℕ}
  {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
  {start : Fin n} {steps : List (ℕ × Fin n)}
  {lab : Fin n → ClosedCylinder} {edgeLab : ℕ → Set ClosedCylinder}

/-- **`FIND_4` is sound** (`k ≥ 2`). If `FIND_4` returns a contact and a path at `Pᵢ`, and
its lists represent the drawing, then Reduction 4 applies at `Pᵢ`. -/
theorem reduction4At_of_find4_some
    (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {j : ℕ} {path : List ℕ}
    (h : gm06Find4 ends ordinary incV incE upper start steps = some (j, path)) :
    Reduction4At L i := by
  obtain ⟨hj, p, -, -⟩ := gm06Find4_sound ends ordinary incV incE upper start steps j path h
  rw [mem_gm06Reduction4Contacts_iff] at hj
  obtain ⟨q, hq, rfl, hinc, hpre⟩ := hj
  simp only [List.length_map] at hq
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  obtain ⟨P_sv, T, hx, hsub, htail, hpreIff, -, -, hreach⟩ :=
    find4_contact rep hk hG hθ hWs hWV hWsupp hWedges (q := q + 1) (by omega) (by omega)
  have htgt : gm06Find4Target start steps (q + 1) = steps[q].2 := by
    simp [gm06Find4Target, List.getElem?_eq_getElem hq]
  have hinc' : incV[(gm06Find4Target start steps (q + 1)).val]?.getD 0 ≠ 0 := by
    rw [htgt]; simpa [List.getElem?_eq_getElem hq] using hinc
  obtain ⟨Wc, hWcV, hWcE⟩ := (hreach hinc').mp p.reachable
  have hvP : lab (gm06Find4Target start steps (q + 1)) ∈ (L.pathDrawing i).V := by rw [hWV]; exact List.mem_of_getElem? hx
  have hsv : cylinderM1Point k i ≠ lab (gm06Find4Target start steps (q + 1)) :=
    isPathDrawing_start_ne_end hsub.2.2
  have hTG := isSubdrawing_of_section5Tail L i hvP htail
  obtain ⟨Q, hQG, hQ, hQR, hQT, hQP⟩ :=
    (exists_candidate_walk_iff L i hTG hsv).mpr ⟨Wc, hWcV, hWcE⟩
  refine ⟨_, P_sv, T, Q, hvP, (rep.vertex_sound _ hinc').2, hsub, ?_, htail,
    hQG, hQ, hQR, hQT, hQP⟩
  rw [hpreIff]
  simpa using hpre

/-- **`FIND_4` is complete** (`k ≥ 2`). If `FIND_4` returns none at `Pᵢ`, and its lists
represent the drawing, then Reduction 4 does not apply at `Pᵢ`. -/
theorem not_reduction4At_of_find4_none
    (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    (h : gm06Find4 ends ordinary incV incE upper start steps = none) :
    ¬ Reduction4At L i := by
  rintro ⟨w, P_sw, T', Q, hw, hwR, hsw, hpre, hT', hQG, hQ, hQR, hQT, hQP⟩
  obtain ⟨W, hWs, hWV, hWsupp, hWedges⟩ := rep.path_walk
  have hlen : W.length = steps.length := by
    rw [GraphWalk.length, hWedges, List.length_map]
  rw [hWV] at hw
  obtain ⟨q, hqw⟩ := List.mem_iff_getElem?.mp hw
  have hqlt : q < W.support.length := (List.getElem?_eq_some_iff.mp hqw).1
  rw [GraphWalk.support_length W, hlen] at hqlt
  have hsw_ne : cylinderM1Point k i ≠ w := isPathDrawing_start_ne_end hsw.2.2
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [GraphWalk.support_getElem?_zero W] at hqw
    exact hsw_ne (Option.some.inj hqw)
  obtain ⟨P_sv, T, hx, hsub, htail, hpreIff, huniqP, huniqT, hreach⟩ :=
    find4_contact rep hk hG hθ hWs hWV hWsupp hWedges (q := q) (by omega) (by omega)
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
  have hvP : lab (gm06Find4Target start steps q) ∈ (L.pathDrawing i).V := by
    rw [hWV]; exact List.mem_of_getElem? hx
  have hTG := isSubdrawing_of_section5Tail L i hvP htail
  have hQT' : Q.U ∩ T.U ⊆ {lab (gm06Find4Target start steps q)} := by
    rw [← hTU, hwv]; exact hQT
  obtain ⟨Wc, hWcV, hWcE⟩ := (exists_candidate_walk_iff L i hTG (hwv ▸ hsw_ne)).mp
    ⟨Q, hQG, hwv ▸ hQ, hQR, hQT', hQP⟩
  exact hnot ((hreach hinc).mpr ⟨Wc, hWcV, hWcE⟩)

end Main

/-- **No Reduction 4** (`k ≥ 2`): if Reduction 4 applies at no path, no Reduction 4 step exists.
With `not_reduction4At_of_find4_none` this turns `FIND_4` returning none for every component into
the absence of Reduction 4. -/
theorem not_exists_reduction4Step_of_forall (L : CylinderLinkage k G) (hk : 1 < k)
    (h : ∀ i, ¬ Reduction4At L i) :
    ¬ ∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L' := by
  rw [exists_reduction4Step_iff_exists_reduction4At L hk]
  rintro ⟨i, hi⟩
  exact h i hi

/-- **`FIND_4` returns a witness ⇒ a Reduction 4 step exists** (`k ≥ 2`). -/
theorem exists_reduction4Step_of_find4_some {L : CylinderLinkage k G} {i : Fin k} {n : ℕ}
    {ends : List (ℕ × ℕ)} {ordinary : List Bool} {incV incE upper : List ℕ}
    {start : Fin n} {steps : List (ℕ × Fin n)}
    {lab : Fin n → ClosedCylinder} {edgeLab : ℕ → Set ClosedCylinder}
    (rep : Find4Rep L i ends ordinary incV incE upper start steps lab edgeLab)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {θ : ℝ} (hθ : L.HasTheta θ)
    {j : ℕ} {path : List ℕ}
    (h : gm06Find4 ends ordinary incV incE upper start steps = some (j, path)) :
    ∃ L' : CylinderLinkage k G, Section5Reduction4Step k G L G L' :=
  (exists_reduction4Step_iff_exists_reduction4At L hk).mpr
    ⟨i, reduction4At_of_find4_some rep hk hG hθ h⟩

end GraphMinor.GM06
