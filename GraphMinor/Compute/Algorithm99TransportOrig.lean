module

public import GraphMinor.Compute.Algorithm99TransportRural
public import GraphMinor.Compute.Algorithm99State

/-!
# The renaming along `orig`, from `G_i` to `G`

A state of Algorithm (9.9) (`Alg99Iter`, step (2) of Graph Minors XIII, page 104) stores `G_i`
on `Fin v_i` with an injective map `orig : Fin v_i → Fin n` to the vertices of `G`, and the edges
of `G_i` from `u` to `w` are none or all of the edges of `G` from `orig u` to `orig w`.

Here we turn `orig` into embeddings of labels, `origVertexEmb` on `ℕ` (equal to `orig` below
`v_i`, and `n + x` above it, so that it is injective) and `origEdgeEmb` on edge triples
`(u, w, k) ↦ (orig u, orig w, k)`. With these maps the results of `Algorithm99Transport*.lean`
apply. We prove:

* `relabelGraph_toGMGraph_le`: the renamed `G_i` is a subgraph of `G`;
* `relabelGraph_toGMGraph_closed`: an edge of `G` at a renamed vertex outside `Z_i` is a renamed
  edge of `G_i`. This is the hypothesis `hclosed` of `GM13.wallCompass_eq_of_closed_outside_Z` and
  of `GM13.step8_closed_outside_Z`, and it comes from conditions (ii) and (iii) of step (2),
  `Alg99Iter.IsValid.closed_out` and `closed_in`.

We also show that the compass, flatness, the wall society and the interior members of a wall
depend only on its corners, its vertex set and the vertex sets of its perimeter
(`wallCompass_congr`, `isFlatWallIn_congr`, `wallCornerCyclicPerm_congr`,
`isInteriorMember_congr`). The walls written by the program in the labels of `G` choose, between
two adjacent vertices, the edge `(u, w, 0)` or `(w, u, 0)` by the multiplicities of `G`
(`WallOfHeight.adjEdgeTriple`), while the renamed walls of `G_i` choose by those of `G_i`. The two
walls have the same vertices, so these lemmas carry flatness and the society from one to the other.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function Set GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport

/-! ### The embeddings -/

/-- The vertex renaming of `orig`: `x ↦ orig x` for `x < v`, and `x ↦ n + x` otherwise. -/
def origVertexEmb {v n : ℕ} (orig : Fin v → Fin n) (hinj : Injective orig) : ℕ ↪ ℕ where
  toFun x := if hx : x < v then (orig ⟨x, hx⟩).1 else n + x
  inj' := by
    intro x y hxy
    simp only at hxy
    by_cases hx : x < v <;> by_cases hy : y < v
    · simp only [hx, hy, ↓reduceDIte] at hxy
      have := hinj (Fin.ext hxy)
      simpa using this
    · simp only [hx, hy, ↓reduceDIte] at hxy
      have := (orig ⟨x, hx⟩).2
      omega
    · simp only [hx, hy, ↓reduceDIte] at hxy
      have := (orig ⟨y, hy⟩).2
      omega
    · simp only [hx, hy, ↓reduceDIte] at hxy
      omega

@[simp]
theorem origVertexEmb_apply_val {v n : ℕ} (orig : Fin v → Fin n) (hinj : Injective orig)
    (u : Fin v) : origVertexEmb orig hinj u.1 = (orig u).1 := by
  change (if hx : u.1 < v then (orig ⟨u.1, hx⟩).1 else n + u.1) = _
  simp only [u.2, ↓reduceDIte]

/-- The edge renaming of `orig`: `(u, w, k) ↦ (orig u, orig w, k)`. -/
def origEdgeEmb {v n : ℕ} (orig : Fin v → Fin n) (hinj : Injective orig) :
    ℕ × ℕ × ℕ ↪ ℕ × ℕ × ℕ where
  toFun e := (origVertexEmb orig hinj e.1, origVertexEmb orig hinj e.2.1, e.2.2)
  inj' := by
    rintro ⟨a, b, k⟩ ⟨a', b', k'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, h₂, rfl⟩ := h
    rw [(origVertexEmb orig hinj).injective h₁, (origVertexEmb orig hinj).injective h₂]

@[simp]
theorem origEdgeEmb_apply {v n : ℕ} (orig : Fin v → Fin n) (hinj : Injective orig)
    (e : ℕ × ℕ × ℕ) : origEdgeEmb orig hinj e =
      (origVertexEmb orig hinj e.1, origVertexEmb orig hinj e.2.1, e.2.2) := rfl

/-! ### The renamed `G_i` in `G` -/

variable {v n : ℕ} {Gi : MultiDigraph v} {G : MultiDigraph n} {orig : Fin v → Fin n}

/-- If the edges of `G_i` from `u` to `w` are none or all of those of `G` from `orig u` to
`orig w`, then `G_i` renamed along `orig` is a subgraph of `G`. -/
theorem relabelGraph_toGMGraph_le (hinj : Injective orig)
    (hmult : ∀ u w, Gi.edgeMult u w = 0 ∨ Gi.edgeMult u w = G.edgeMult (orig u) (orig w)) :
    relabelGraph (origVertexEmb orig hinj) (origEdgeEmb orig hinj) Gi.toGMDigraph.toGraph ≤
      G.toGMDigraph.toGraph where
  vertexSet_mono := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x < v := hx
    have := origVertexEmb_apply_val orig hinj ⟨x, hx'⟩
    change origVertexEmb orig hinj x < n
    rw [this]
    exact (orig _).2
  isLink_mono := by
    rintro _ _ _ ⟨⟨a, b, k⟩, x, y, ⟨⟨ha, hb, hk⟩, hxy⟩, rfl, rfl, rfl⟩
    have hk' : k < G.edgeMult (orig ⟨a, ha⟩) (orig ⟨b, hb⟩) := by
      rcases hmult ⟨a, ha⟩ ⟨b, hb⟩ with h0 | heq
      · simp only at hk
        omega
      · simp only at hk
        omega
    have hfa := origVertexEmb_apply_val orig hinj ⟨a, ha⟩
    have hfb := origVertexEmb_apply_val orig hinj ⟨b, hb⟩
    simp only at hfa hfb
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · change origVertexEmb orig hinj a < n
      rw [hfa]
      exact (orig _).2
    · change origVertexEmb orig hinj b < n
      rw [hfb]
      exact (orig _).2
    · change k < G.edgeMult ⟨origVertexEmb orig hinj a, _⟩ ⟨origVertexEmb orig hinj b, _⟩
      simp only [hfa, hfb]
      exact hk'
    · change ((origVertexEmb orig hinj b = _ ∧ origVertexEmb orig hinj a = _) ∨
        (origVertexEmb orig hinj b = _ ∧ origVertexEmb orig hinj a = _))
      change ((b = x ∧ a = y) ∨ (b = y ∧ a = x)) at hxy
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩

/-- For a valid state, the renamed `G_i` is a subgraph of `G`. -/
theorem Alg99Iter.IsValid.relabelGraph_le {h' : ℕ} {st : Alg99Iter h' G} {s : ℕ}
    (hst : st.IsValid s) :
    relabelGraph (origVertexEmb st.orig hst.orig_injective) (origEdgeEmb st.orig hst.orig_injective)
      st.Gi.toGMDigraph.toGraph ≤ G.toGMDigraph.toGraph :=
  relabelGraph_toGMGraph_le hst.orig_injective hst.edgeMult_eq

/-- For a valid state, an edge of `G` at `orig u` with `u ∉ Z_i` is a renamed edge of `G_i`
(conditions (ii) and (iii) of step (2) of (9.9), page 104). -/
theorem Alg99Iter.IsValid.relabelGraph_closed {h' : ℕ} {st : Alg99Iter h' G} {s : ℕ}
    (hst : st.IsValid s) (u : Fin st.v) (hu : u ∉ st.Z) (e : ℕ × ℕ × ℕ)
    (he : e ∈ E(G.toGMDigraph.toGraph)) (hinc : G.toGMDigraph.toGraph.Inc e (st.orig u).1) :
    e ∈ E(relabelGraph (origVertexEmb st.orig hst.orig_injective)
      (origEdgeEmb st.orig hst.orig_injective) st.Gi.toGMDigraph.toGraph) := by
  obtain ⟨a, b, k⟩ := e
  obtain ⟨ha, hb, hk⟩ := he
  simp only at ha hb hk
  obtain ⟨y, -, hends⟩ := hinc
  change (b = (st.orig u).1 ∧ a = y) ∨ (b = y ∧ a = (st.orig u).1) at hends
  have hF := origVertexEmb_apply_val st.orig hst.orig_injective
  rcases hends with ⟨hbu, -⟩ | ⟨-, hau⟩
  · -- `e` has head `orig u`
    have hpos : 0 < G.edgeMult ⟨a, ha⟩ (st.orig u) := by
      have : (⟨b, hb⟩ : Fin n) = st.orig u := Fin.ext hbu
      rw [← this]
      omega
    obtain ⟨w, hw, hmult⟩ := hst.closed_in u hu ⟨a, ha⟩ hpos
    refine ⟨(w.1, u.1, k), ⟨w.2, u.2, ?_⟩, ?_⟩
    · change k < st.Gi.edgeMult w u
      rw [hmult]
      have : (⟨b, hb⟩ : Fin n) = st.orig u := Fin.ext hbu
      rw [← this]
      exact hk
    · rw [origEdgeEmb_apply]
      simp only [hF, hw, hbu]
  · -- `e` has tail `orig u`
    have hpos : 0 < G.edgeMult (st.orig u) ⟨b, hb⟩ := by
      have : (⟨a, ha⟩ : Fin n) = st.orig u := Fin.ext hau
      rw [← this]
      omega
    obtain ⟨w, hw, hmult⟩ := hst.closed_out u hu ⟨b, hb⟩ hpos
    refine ⟨(u.1, w.1, k), ⟨u.2, w.2, ?_⟩, ?_⟩
    · change k < st.Gi.edgeMult u w
      rw [hmult]
      have : (⟨a, ha⟩ : Fin n) = st.orig u := Fin.ext hau
      rw [← this]
      exact hk
    · rw [origEdgeEmb_apply]
      simp only [hF, hw, hau]

/-! ### Walls with the same vertices -/

section SameVertices

variable {α : Type*} {β : Type*}

/-- The compass of a wall depends only on the vertex set of its perimeter and its inside
vertices. -/
theorem wallCompass_congr {K : Graph α β} {W₁ W₂ : Wall α β}
    (hC : V(W₁.perimeter) = V(W₂.perimeter)) (hI : W₁.insideVerts = W₂.insideVerts) :
    wallCompass K W₁ = wallCompass K W₂ := by
  unfold wallCompass wallCompassVerts
  rw [hC, hI]

/-- Flatness of a wall depends only on its graph being a subgraph, its corners, the vertex set
of its perimeter and its inside vertices. -/
theorem isFlatWallIn_congr {K : Graph α β} {W₁ W₂ : Wall α β} (hle : W₂.graph ≤ K)
    (hcorner : W₁.corner = W₂.corner) (hC : V(W₁.perimeter) = V(W₂.perimeter))
    (hI : W₁.insideVerts = W₂.insideVerts) (h : IsFlatWallIn K W₁) : IsFlatWallIn K W₂ := by
  refine ⟨hle, fun ⟨P, Q, hPQ⟩ => h.2 ⟨P, Q, ?_⟩⟩
  rw [wallCompass_congr hC hI]
  unfold IsCrossOverWall at hPQ ⊢
  rw [hcorner]
  exact hPQ

open Classical in
/-- The corner order of a wall depends only on its corners. -/
theorem wallCornerCyclicPerm_congr {W₁ W₂ : Wall α β} (hcorner : W₁.corner = W₂.corner) :
    wallCornerCyclicPerm W₁ = wallCornerCyclicPerm W₂ := by
  refine cyclicPerm_ext ?_ ?_
  · change Set.range W₁.corner = Set.range W₂.corner
    rw [hcorner]
  · funext x
    change (if x = W₁.corner 0 then W₁.corner 1 else if x = W₁.corner 1 then W₁.corner 2
      else if x = W₁.corner 2 then W₁.corner 3 else if x = W₁.corner 3 then W₁.corner 0 else x) =
      (if x = W₂.corner 0 then W₂.corner 1 else if x = W₂.corner 1 then W₂.corner 2
      else if x = W₂.corner 2 then W₂.corner 3 else if x = W₂.corner 3 then W₂.corner 0 else x)
    rw [hcorner]

theorem isWallSociety_congr {K : Graph α β} {W₁ W₂ : Wall α β} {S : Society α β}
    (hcorner : W₁.corner = W₂.corner) (hC : V(W₁.perimeter) = V(W₂.perimeter))
    (hI : W₁.insideVerts = W₂.insideVerts) (h : IsWallSociety K W₁ S) : IsWallSociety K W₂ S :=
  ⟨h.1.trans (wallCompass_congr hC hI), h.2.trans (wallCornerCyclicPerm_congr hcorner)⟩

theorem isInteriorMember_congr {W₁ W₂ : Wall α β} {𝒜 : Set (Graph α β)} {A : Graph α β}
    (hC : V(W₁.perimeter) = V(W₂.perimeter)) :
    IsInteriorMember W₁ 𝒜 A ↔ IsInteriorMember W₂ 𝒜 A := by
  unfold IsInteriorMember
  rw [hC]

end SameVertices

end GraphMinor.Compute
