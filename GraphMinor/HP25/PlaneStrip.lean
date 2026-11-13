module

public import GraphMinor.HP25.PlaneCut
import GraphMinor.HP25.Link
import GraphMinor.HP25.Prop23
import GraphMinor.HP25.RibEdges
import GraphMinor.Surface.SurfaceGraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# A strip of triangles along a cut

Let `φ` be a rib embedding with frame `C`, cut by the image of a path `l` of the rib into two sides
(`IsTheta`, `PlaneCut.lean`), and let `M` be a set of vertices of `l` off the frame. In the strip
argument of Lemma 5.4 (`Sec5Strip.lean`), `M` is the set of rib vertices strictly between `y_j` and
`y_s`, and we need a connected set on the side `F₂` that runs along `l` from the first edge of `l` at
`M` to the last one, made of faces of triangles and of open lines of edges at `M`.

The *strip graph* (`stripGraph`) has the pairs `s(u, v)` as vertices; `s(σ, w)` and `s(σ, w')` are
adjacent when `σ ∈ M` and the face of the triangle `σ w w'` lies on the side `F₂`. We count the
neighbours of an edge `uv` with `u ∈ M` (`degree_stripGraph`). The edge `uv` lies on two triangles
(`IsRibEmbedding.common_neighbours`, since `u` is off the frame). If `uv` is not an edge of `l`, the
two triangles are on the same side (`tri_side_eq`), so the number of triangles at `uv` on the side
`F₂` is even. If `uv` is an edge of `l`, one triangle is on each side (`exists_tri_at_cut`). So an
edge has an odd number of neighbours exactly when it is an edge of `l` with one end in `M`. There are
two such edges, and by the handshake lemma they are in the same component of the strip graph
(`reachable_stripGraph`). Along a walk of the strip graph, consecutive edges share a triangle; the
face of a triangle together with any part of its frontier is path-connected
(`isPathConnected_inner_union`). This gives `joinedIn_strip`.
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*} {G : SimpleGraph V} {R : Set V}

/-- Three distinct elements of a set with at most two elements cannot exist. -/
theorem eq_or_eq_of_encard_le_two {s : Set V} (hs : s.encard ≤ 2) {a b x : V} (ha : a ∈ s)
    (hb : b ∈ s) (hab : a ≠ b) (hx : x ∈ s) : x = a ∨ x = b := by
  by_contra h
  push Not at h
  have hsub : ({x, a, b} : Set V) ⊆ s := by
    rintro y (rfl | rfl | rfl) <;> assumption
  have h3 : ({x, a, b} : Set V).encard = 3 := by
    rw [Set.encard_insert_of_notMem (by simp [h.1, h.2]), Set.encard_pair hab]
    rfl
  have := (Set.encard_le_encard hsub).trans hs
  rw [h3] at this
  exact absurd this (by norm_num)

theorem IsTriangleOn.swap₁₂ {a b c : V} (h : IsTriangleOn G R a b c) : IsTriangleOn G R b a c :=
  ⟨h.2.1, h.1, h.2.2.1, h.2.2.2.1.symm, h.2.2.2.2.2, h.2.2.2.2.1⟩

theorem IsTriangleOn.swap₂₃ {a b c : V} (h : IsTriangleOn G R a b c) : IsTriangleOn G R a c b :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.2.2, h.2.2.2.2.1.symm, h.2.2.2.1⟩

namespace PlaneEmbedding

variable (φ : PlaneEmbedding G R)

theorem cycleImage_swap₁₂ (a b c : V) : φ.cycleImage [a, b, c] = φ.cycleImage [b, a, c] := by
  rw [φ.cycleImage_three, φ.cycleImage_three, φ.line_comm b a, φ.line_comm a c, φ.line_comm c b]
  ext z; simp only [mem_union]; tauto

theorem cycleImage_swap₂₃ (a b c : V) : φ.cycleImage [a, b, c] = φ.cycleImage [a, c, b] := by
  rw [φ.cycleImage_three, φ.cycleImage_three, φ.line_comm a c, φ.line_comm c b, φ.line_comm b a]
  ext z; simp only [mem_union]; tauto

/-- A step of the strip graph: `σ ∈ M` and `σ w w'` is a triangle whose face lies in the inner
domain of `F₂`. -/
@[expose] def StripStep (M : Set V) (F₂ : Set ℂ) (e e' : Sym2 V) : Prop :=
  ∃ σ w w', σ ∈ M ∧ e = s(σ, w) ∧ e' = s(σ, w') ∧ IsTriangleOn G R σ w w' ∧
    Surface.inner (φ.cycleImage [σ, w, w']) ⊆ Surface.inner F₂

theorem StripStep.symm {M : Set V} {F₂ : Set ℂ} {e e' : Sym2 V} (h : φ.StripStep M F₂ e e') :
    φ.StripStep M F₂ e' e := by
  obtain ⟨σ, w, w', hσ, rfl, rfl, hT, hF⟩ := h
  exact ⟨σ, w', w, hσ, rfl, rfl, hT.swap₂₃, by rwa [← φ.cycleImage_swap₂₃]⟩

/-- **The strip graph.** Its vertices are the pairs of vertices; `s(σ, w)` and `s(σ, w')` are
adjacent when `σ ∈ M` and `σ w w'` is a triangle whose face lies in the inner domain of `F₂`. -/
@[expose] def stripGraph (M : Set V) (F₂ : Set ℂ) : SimpleGraph (Sym2 V) :=
  SimpleGraph.fromRel (φ.StripStep M F₂)

theorem stripGraph_adj {M : Set V} {F₂ : Set ℂ} {e e' : Sym2 V} :
    (φ.stripGraph M F₂).Adj e e' ↔ e ≠ e' ∧ φ.StripStep M F₂ e e' := by
  simp only [stripGraph, fromRel_adj]
  exact ⟨fun ⟨h, h'⟩ => ⟨h, h'.elim id (StripStep.symm φ)⟩, fun ⟨h, h'⟩ => ⟨h, Or.inl h'⟩⟩

/-- The triangles at `uv` whose face lies in the inner domain of `F₂`, by their third vertex. -/
@[expose] def sideTris (F₂ : Set ℂ) (u v : V) : Set V :=
  {x | IsTriangleOn G R u v x ∧ Surface.inner (φ.cycleImage [u, v, x]) ⊆ Surface.inner F₂}

theorem sideTris_comm (F₂ : Set ℂ) (u v : V) : φ.sideTris F₂ u v = φ.sideTris F₂ v u := by
  ext x
  simp only [sideTris, mem_ofPred_eq]
  rw [φ.cycleImage_swap₁₂ u v x]
  exact ⟨fun h => ⟨h.1.swap₁₂, h.2⟩, fun h => ⟨h.1.swap₁₂, h.2⟩⟩

theorem finite_sideTris (F₂ : Set ℂ) (u v : V) : (φ.sideTris F₂ u v).Finite :=
  φ.finite.subset fun _ hx => hx.1.2.2.1

/-- The neighbours of `s(u, v)` in the strip graph. -/
theorem neighborSet_stripGraph (M : Set V) (F₂ : Set ℂ) {u v : V} (huv : u ≠ v) :
    (φ.stripGraph M F₂).neighborSet s(u, v) =
      {e | u ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(u, x)} ∪
        {e | v ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(v, x)} := by
  ext e
  rw [mem_neighborSet, stripGraph_adj]
  simp only [mem_union, mem_ofPred_eq]
  constructor
  · rintro ⟨-, σ, w, w', hσ, he, rfl, hT, hF⟩
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hσ, w', ⟨hT, hF⟩, rfl⟩
    · refine Or.inr ⟨hσ, w', ?_, rfl⟩
      rw [φ.sideTris_comm]
      exact ⟨hT, hF⟩
  · rintro (⟨hu, x, ⟨hT, hF⟩, rfl⟩ | ⟨hv, x, hx, rfl⟩)
    · refine ⟨fun h => ?_, u, v, x, hu, rfl, rfl, hT, hF⟩
      rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
      · exact hT.2.2.2.2.1.ne h
      · exact hT.2.2.2.2.2.ne h
    · rw [φ.sideTris_comm] at hx
      refine ⟨fun h => ?_, v, u, x, hv, Sym2.eq_swap, rfl, hx.1, hx.2⟩
      rcases Sym2.eq_iff.mp h with ⟨h, -⟩ | ⟨h, -⟩
      · exact huv h
      · exact hx.1.2.2.2.2.1.ne h

/-- **The degree of an edge in the strip graph**: the number of triangles at `uv` on the side `F₂`,
counted once for each end in `M`. -/
theorem degree_stripGraph [Fintype V] [DecidableEq V] (M : Set V) [DecidablePred (· ∈ M)]
    (F₂ : Set ℂ) [DecidableRel (φ.stripGraph M F₂).Adj] {u v : V} (huv : u ≠ v) :
    (φ.stripGraph M F₂).degree s(u, v) =
      (if u ∈ M then (φ.sideTris F₂ u v).ncard else 0) +
        (if v ∈ M then (φ.sideTris F₂ u v).ncard else 0) := by
  classical
  rw [← ncard_neighborSet, φ.neighborSet_stripGraph M F₂ huv]
  have hfin := φ.finite_sideTris F₂ u v
  have himg : ∀ w : V, {e | ∃ x ∈ φ.sideTris F₂ u v, e = s(w, x)} =
      (fun x => s(w, x)) '' φ.sideTris F₂ u v := by
    intro w; ext e; simp [eq_comm]
  have hinj : ∀ w : V, Function.Injective fun x : V => s(w, x) := fun w x y h => by
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h1, h2⟩
    · exact h
    · rw [h2, h1]
  have hcard : ∀ w : V, ({e | ∃ x ∈ φ.sideTris F₂ u v, e = s(w, x)}).ncard =
      (φ.sideTris F₂ u v).ncard := fun w => by
    rw [himg w, Set.ncard_image_of_injective _ (hinj w)]
  have hdisj : Disjoint {e | u ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(u, x)}
      {e | v ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(v, x)} := by
    refine Set.disjoint_left.mpr ?_
    rintro e ⟨-, x, hx, rfl⟩ ⟨-, y, hy, he⟩
    rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨rfl, rfl⟩
    · exact huv h
    · exact hx.1.2.2.2.2.1.ne rfl
  have hf1 : ({e | u ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(u, x)}).Finite := by
    refine ((hfin.image fun x => s(u, x))).subset ?_
    rintro e ⟨-, x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  have hf2 : ({e | v ∈ M ∧ ∃ x ∈ φ.sideTris F₂ u v, e = s(v, x)}).Finite := by
    refine ((hfin.image fun x => s(v, x))).subset ?_
    rintro e ⟨-, x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  rw [Set.ncard_union_eq hdisj hf1 hf2]
  congr 1
  · by_cases hu : u ∈ M
    · simp only [hu, true_and, ↓reduceIte]; exact hcard u
    · simp [hu]
  · by_cases hv : v ∈ M
    · simp only [hv, true_and, ↓reduceIte]; exact hcard v
    · simp [hv]


variable {φ} {C : List V} {F₁ F₂ A₁ A₂ : Set ℂ} {l : List V} {p q : ℂ}

/-- The two triangles at an edge `uv` off the frame. -/
theorem IsRibEmbedding.two_tris (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) {u v : V} (hu : u ∈ R) (hv : v ∈ R) (huv : G.Adj u v) (huC : u ∉ C) :
    ∃ z₁ z₂, z₁ ≠ z₂ ∧ IsTriangleOn G R u v z₁ ∧ IsTriangleOn G R u v z₂ ∧
      ∀ x, IsTriangleOn G R u v x → x = z₁ ∨ x = z₂ := by
  obtain ⟨hle, -, htwo⟩ := hφ.common_neighbours hC hR hu hv huv
  obtain ⟨z₁, z₂, hne, h₁, h₂⟩ := htwo fun h => huC h.mem_left
  refine ⟨z₁, z₂, hne, ⟨hu, hv, h₁.1, huv, h₁.2.2, h₁.2.1⟩,
    ⟨hu, hv, h₂.1, huv, h₂.2.2, h₂.2.1⟩, fun x hx => ?_⟩
  exact eq_or_eq_of_encard_le_two hle h₁ h₂ hne ⟨hx.2.2.1, hx.2.2.2.2.2, hx.2.2.2.2.1⟩

/-- **Off the cut, the triangles at an edge on the side `F₂` come in pairs.** -/
theorem IsRibEmbedding.even_sideTris (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {u v : V} (huC : u ∉ C) (huv : ¬ IsListEdge l u v) :
    Even (φ.sideTris F₂ u v).ncard := by
  by_cases hadj : u ∈ R ∧ v ∈ R ∧ G.Adj u v
  swap
  · have : φ.sideTris F₂ u v = ∅ := by
      ext x
      simp only [sideTris, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hT => absurd ⟨hT.1, hT.2.1, hT.2.2.2.1⟩ hadj
    rw [this, Set.ncard_empty]; exact ⟨0, rfl⟩
  obtain ⟨z₁, z₂, hne, hT₁, hT₂, hall⟩ := hφ.two_tris hC hR hadj.1 hadj.2.1 hadj.2.2 huC
  have hsame : ∀ {w w'}, IsTriangleOn G R u v w → IsTriangleOn G R u v w' →
      w ∈ φ.sideTris F₂ u v → w' ∈ φ.sideTris F₂ u v := by
    intro w w' hw hw' hws
    refine ⟨hw', ?_⟩
    rcases hφ.tri_side hC hR hθ hl hw' with h | h
    · exact absurd (tri_side_eq hθ hl hw' hw huv h hws.2) id
    · exact h
  by_cases h₁ : z₁ ∈ φ.sideTris F₂ u v
  · have h₂ := hsame hT₁ hT₂ h₁
    have : φ.sideTris F₂ u v = {z₁, z₂} := by
      ext x
      refine ⟨fun hx => hall x hx.1, ?_⟩
      rintro (rfl | rfl)
      · exact h₁
      · exact h₂
    rw [this, Set.ncard_pair hne]; exact even_two
  · have : φ.sideTris F₂ u v = ∅ := by
      ext x
      simp only [mem_empty_iff_false, iff_false]
      intro hx
      rcases hall x hx.1 with rfl | rfl
      · exact h₁ hx
      · exact h₁ (hsame hT₂ hT₁ hx)
    rw [this, Set.ncard_empty]; exact ⟨0, rfl⟩

/-- **At an edge of the cut, one triangle lies on the side `F₂`.** -/
theorem IsRibEmbedding.sideTris_eq_one (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {u v : V} (huC : u ∉ C) (huv : IsListEdge l u v) :
    ∃ z, φ.sideTris F₂ u v = {z} := by
  have hnC : ¬ IsCycleEdge C u v := fun h => huC h.mem_left
  obtain ⟨hu, hv, hadj⟩ := hl.adj_of_isListEdge huv
  obtain ⟨z, hz, huz, hvz, hz1⟩ := hφ.exists_tri_at_cut hC hR hθ hl huv hnC
  obtain ⟨z', hz', huz', hvz', hz2⟩ := hφ.exists_tri_at_cut hC hR hθ.symm hl huv hnC
  obtain ⟨-, -, -, hall⟩ := hφ.two_tris hC hR hu hv hadj huC
  have hT : IsTriangleOn G R u v z := ⟨hu, hv, hz, hadj, hvz, huz⟩
  have hT' : IsTriangleOn G R u v z' := ⟨hu, hv, hz', hadj, hvz', huz'⟩
  have hJ := isJordanParts (φ.isOArc_cycleImage hT.isCycleList hT.mem).some
  have hne : z ≠ z' := by
    rintro rfl
    exact hθ.not_both hJ.isConnected_inner.nonempty hz1 hz2
  refine ⟨z', Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hT', hz2⟩, fun x hx => ?_⟩⟩
  obtain ⟨z₁, z₂, hne₁₂, hT₁, hT₂, hall'⟩ := hφ.two_tris hC hR hu hv hadj huC
  rcases hall' z hT with rfl | rfl <;> rcases hall' z' hT' with rfl | rfl <;>
    rcases hall' x hx.1 with rfl | rfl
  all_goals first
    | rfl
    | exact absurd rfl hne
    | exact absurd (hθ.not_both hJ.isConnected_inner.nonempty hz1 hx.2) id


/-- **Parity in the strip graph.** An edge with an odd number of neighbours is an edge of the cut
with exactly one end in `M`. -/
theorem IsRibEmbedding.odd_degree_stripGraph [Fintype V] [DecidableEq V] {M : Set V}
    [DecidablePred (· ∈ M)] [DecidableRel (φ.stripGraph M F₂).Adj] (hφ : φ.IsRibEmbedding C)
    (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q) (hl : IsPathList G R l)
    (hMC : ∀ u ∈ M, u ∉ C) {u v : V} (h : Odd ((φ.stripGraph M F₂).degree s(u, v))) :
    ((u ∈ M ∧ v ∉ M) ∨ (v ∈ M ∧ u ∉ M)) ∧ IsListEdge l u v := by
  by_cases huv : u = v
  · subst huv
    have : (φ.stripGraph M F₂).neighborSet s(u, u) = ∅ := by
      ext e
      simp only [mem_neighborSet, stripGraph_adj, mem_empty_iff_false, iff_false, not_and]
      rintro - ⟨σ, w, w', -, he, -, hT, -⟩
      rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hT.2.2.2.1.ne (h1.symm.trans h2)
      · exact hT.2.2.2.1.ne (h2.symm.trans h1)
    rw [← ncard_neighborSet, this, Set.ncard_empty] at h
    exact absurd h (by decide)
  rw [degree_stripGraph φ M F₂ huv] at h
  by_cases hu : u ∈ M <;> by_cases hv : v ∈ M <;> simp only [hu, hv, ↓reduceIte] at h
  · exact absurd h (Nat.not_odd_iff_even.mpr ⟨_, rfl⟩)
  · refine ⟨Or.inl ⟨hu, hv⟩, ?_⟩
    by_contra hne
    exact Nat.not_even_iff_odd.mpr (by simpa using h) (hφ.even_sideTris hC hR hθ hl (hMC u hu) hne)
  · refine ⟨Or.inr ⟨hv, hu⟩, ?_⟩
    by_contra hne
    rw [φ.sideTris_comm] at h
    exact Nat.not_even_iff_odd.mpr (by simpa using h)
      (hφ.even_sideTris hC hR hθ hl (hMC v hv) fun h' => hne h'.symm)
  · exact absurd h (by decide)

/-- An edge of the cut with exactly one end in `M` has one neighbour in the strip graph. -/
theorem IsRibEmbedding.odd_degree_of_cut [Fintype V] [DecidableEq V] {M : Set V}
    [DecidablePred (· ∈ M)] [DecidableRel (φ.stripGraph M F₂).Adj] (hφ : φ.IsRibEmbedding C)
    (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q) (hl : IsPathList G R l)
    (hMC : ∀ u ∈ M, u ∉ C) {u v : V} (hu : u ∈ M) (hv : v ∉ M) (huv : IsListEdge l u v) :
    Odd ((φ.stripGraph M F₂).degree s(u, v)) := by
  have hne : u ≠ v := (hl.adj_of_isListEdge huv).2.2.ne
  obtain ⟨z, hz⟩ := hφ.sideTris_eq_one hC hR hθ hl (hMC u hu) huv
  rw [degree_stripGraph φ M F₂ hne]
  simp [hu, hv, hz]

/-- **The two ends of the strip are joined in the strip graph** (the handshake lemma, in the
component of the first end). -/
theorem IsRibEmbedding.reachable_stripGraph [Finite V] (hφ : φ.IsRibEmbedding C)
    (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q) (hl : IsPathList G R l)
    {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {σ₀ σ₁ τ₀ τ₁ : V} (hσ : IsListEdge l σ₁ σ₀)
    (hσ₁ : σ₁ ∈ M) (hσ₀ : σ₀ ∉ M)
    (honly : ∀ u v, IsListEdge l u v → u ∈ M → v ∉ M → s(u, v) = s(σ₁, σ₀) ∨ s(u, v) = s(τ₀, τ₁)) :
    (φ.stripGraph M F₂).Reachable s(σ₁, σ₀) s(τ₀, τ₁) := by
  classical
  have := Fintype.ofFinite V
  set Γ := φ.stripGraph M F₂ with hΓ
  set e₀ := s(σ₁, σ₀)
  let Γc : SimpleGraph (Sym2 V) := SimpleGraph.fromRel fun e e' => Γ.Adj e e' ∧ Γ.Reachable e₀ e
  have hadj : ∀ e e', Γc.Adj e e' ↔ Γ.Adj e e' ∧ Γ.Reachable e₀ e := by
    intro e e'
    simp only [Γc, fromRel_adj]
    constructor
    · rintro ⟨-, h | h⟩
      · exact h
      · exact ⟨h.1.symm, h.2.trans h.1.reachable⟩
    · intro h
      exact ⟨h.1.ne, Or.inl h⟩
  have hdeg : ∀ e, Γc.degree e = if Γ.Reachable e₀ e then Γ.degree e else 0 := by
    intro e
    rw [← ncard_neighborSet, ← ncard_neighborSet]
    split_ifs with hr
    · congr 1
      ext e'
      simp only [mem_neighborSet, hadj, hr, and_true]
    · rw [← Set.ncard_empty (Sym2 V)]
      congr 1
      ext e'
      simp only [mem_neighborSet, hadj, hr, and_false, mem_empty_iff_false]
  have h₀ : Odd (Γc.degree e₀) := by
    rw [hdeg, ite_eq_left_of_eq_true _ _ (eq_true (Reachable.refl _))]
    exact hφ.odd_degree_of_cut hC hR hθ hl hMC hσ₁ hσ₀ hσ
  obtain ⟨e, hne, hodd⟩ := Γc.exists_ne_odd_degree_of_exists_odd_degree e₀ h₀
  rw [hdeg] at hodd
  split_ifs at hodd with hr
  · induction e using Sym2.ind with
    | h u v =>
      obtain ⟨hM, huv⟩ := hφ.odd_degree_stripGraph hC hR hθ hl hMC hodd
      have key : s(u, v) = e₀ ∨ s(u, v) = s(τ₀, τ₁) := by
        rcases hM with ⟨hu, hv⟩ | ⟨hv, hu⟩
        · exact honly u v huv hu hv
        · rw [Sym2.eq_swap]; exact honly v u huv.symm hv hu
      rcases key with h | h
      · exact absurd h hne
      · rw [← h]; exact hr
  · exact absurd hodd (by decide)


variable (φ) in
/-- **The strip set**: the faces of the triangles whose face lies in the inner domain of `F₂`,
together with the points of their frontiers off `Z`. -/
@[expose] def stripSet (F₂ Z : Set ℂ) : Set ℂ :=
  {z | ∃ a b c, IsTriangleOn G R a b c ∧
    Surface.inner (φ.cycleImage [a, b, c]) ⊆ Surface.inner F₂ ∧
    z ∈ Surface.inner (φ.cycleImage [a, b, c]) ∪ (φ.cycleImage [a, b, c] \ Z)}

/-- One triangle of the strip set is path-connected. -/
theorem joinedIn_stripSet_of_tri {Z : Set ℂ} {a b c : V} (hT : IsTriangleOn G R a b c)
    (hF : Surface.inner (φ.cycleImage [a, b, c]) ⊆ Surface.inner F₂) {z z' : ℂ}
    (hz : z ∈ Surface.inner (φ.cycleImage [a, b, c]) ∪ (φ.cycleImage [a, b, c] \ Z))
    (hz' : z' ∈ Surface.inner (φ.cycleImage [a, b, c]) ∪ (φ.cycleImage [a, b, c] \ Z)) :
    JoinedIn (φ.stripSet F₂ Z) z z' := by
  have hpc := isPathConnected_inner_union (φ.isOArc_cycleImage hT.isCycleList hT.mem)
    (S := φ.cycleImage [a, b, c] \ Z) sdiff_subset
  exact (hpc.joinedIn z hz z' hz').mono fun y hy => ⟨a, b, c, hT, hF, hy⟩

variable (φ) in
/-- `z` lies on every triangle of the strip graph at `e`. -/
@[expose] def StripGood (M : Set V) (F₂ Z : Set ℂ) (e : Sym2 V) (z : ℂ) : Prop :=
  ∀ σ w w', σ ∈ M → e = s(σ, w) → IsTriangleOn G R σ w w' →
    Surface.inner (φ.cycleImage [σ, w, w']) ⊆ Surface.inner F₂ →
      z ∈ Surface.inner (φ.cycleImage [σ, w, w']) ∪ (φ.cycleImage [σ, w, w'] \ Z)

/-- At an edge of the cut with an end in `M`, a point of the triangle on the side `F₂` lies on
every triangle of the strip graph at the edge. -/
theorem IsRibEmbedding.stripGood_of_cut (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {Z : Set ℂ} {u v x : V}
    (huv : IsListEdge l u v) (hx : x ∈ φ.sideTris F₂ u v) {z : ℂ}
    (hz : z ∈ Surface.inner (φ.cycleImage [u, v, x]) ∪ (φ.cycleImage [u, v, x] \ Z)) :
    StripGood φ M F₂ Z s(u, v) z := by
  intro σ w w' hσ he hT hF
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst σ w
    obtain ⟨y, hy⟩ := hφ.sideTris_eq_one hC hR hθ hl (hMC u hσ) huv
    have h1 : x = y := by rw [hy] at hx; exact hx
    have h2 : w' = y := by
      have : w' ∈ φ.sideTris F₂ u v := ⟨hT, hF⟩
      rw [hy] at this; exact this
    rw [h2, ← h1]; exact hz
  · subst σ w
    obtain ⟨y, hy⟩ := hφ.sideTris_eq_one hC hR hθ hl (hMC v hσ) huv.symm
    rw [φ.sideTris_comm] at hy
    have h1 : x = y := by rw [hy] at hx; exact hx
    have h2 : w' = y := by
      have : w' ∈ φ.sideTris F₂ u v := by rw [φ.sideTris_comm]; exact ⟨hT, hF⟩
      rw [hy] at this; exact this
    rw [h2, ← h1, ← φ.cycleImage_swap₁₂]; exact hz

/-- At an edge with a neighbour in the strip graph, some point lies on every triangle of the strip
graph at the edge. Off the cut, both triangles at the edge are on the side `F₂`, and a point of the
line of the edge away from its ends works, when the edge is not an edge of `r`. -/
theorem IsRibEmbedding.exists_stripGood (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {r : List V}
    (hr : IsPathList G R r)
    (hZ : ∀ σ ∈ M, ∀ w, w ∈ R → G.Adj σ w → ¬ IsListEdge l σ w →
      (∀ x, IsTriangleOn G R σ w x → Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂) →
      ¬ IsListEdge r σ w)
    {e e' : Sym2 V} (h : (φ.stripGraph M F₂).Adj e e') :
    ∃ z, StripGood φ M F₂ (φ.pathImage r) e z := by
  obtain ⟨-, σ₀, w₀, w₀', hσ₀, rfl, -, hT₀, hF₀⟩ := (φ.stripGraph_adj).mp h
  by_cases hcut : IsListEdge l σ₀ w₀
  · obtain ⟨z, hz⟩ := (isJordanParts (φ.isOArc_cycleImage hT₀.isCycleList hT₀.mem).some).isConnected_inner.nonempty
    exact ⟨z, hφ.stripGood_of_cut hC hR hθ hl hMC hcut ⟨hT₀, hF₀⟩ (Or.inl hz)⟩
  -- off the cut: both triangles are on the side `F₂`
  have hboth : ∀ x, IsTriangleOn G R σ₀ w₀ x →
      Surface.inner (φ.cycleImage [σ₀, w₀, x]) ⊆ Surface.inner F₂ := by
    intro x hx
    rcases hφ.tri_side hC hR hθ hl hx with h1 | h2
    · exact absurd (tri_side_eq hθ hl hx hT₀ hcut h1 hF₀) id
    · exact h2
  have hnr := hZ σ₀ hσ₀ w₀ hT₀.2.1 hT₀.2.2.2.1 hcut hboth
  obtain ⟨z, hzL, hz1, hz2⟩ := exists_inner_point (φ.isLine σ₀ hT₀.1 w₀ hT₀.2.1 hT₀.2.2.2.1)
  have hzr : z ∉ φ.pathImage r := by
    intro hz
    have hne : ∀ pr ∈ r.zip r.tail, s(σ₀, w₀) ≠ s(pr.1, pr.2) := fun pr hpr he => hnr ⟨pr, hpr, he⟩
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ :=
      φ.line_inter_pathImage_sub hT₀.1 hT₀.2.1 hT₀.2.2.2.1 hr hne ⟨hzL, hz⟩
    rcases hy with rfl | rfl
    · exact hz1 rfl
    · exact hz2 rfl
  refine ⟨z, fun σ w w' hσ he hT hF => Or.inr ⟨?_, hzr⟩⟩
  rw [φ.cycleImage_three]
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl (Or.inl hzL)
  · rw [φ.line_comm] at hzL
    exact Or.inl (Or.inl hzL)

/-- Along a walk of the strip graph, good points are joined in the strip set. -/
theorem IsRibEmbedding.joinedIn_of_walk (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q)
    (hl : IsPathList G R l) {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {r : List V}
    (hr : IsPathList G R r)
    (hZ : ∀ σ ∈ M, ∀ w, w ∈ R → G.Adj σ w → ¬ IsListEdge l σ w →
      (∀ x, IsTriangleOn G R σ w x → Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂) →
      ¬ IsListEdge r σ w) :
    ∀ {e e' : Sym2 V} (_ : (φ.stripGraph M F₂).Walk e e') {e'' : Sym2 V},
      (φ.stripGraph M F₂).Adj e e'' → ∀ {z z' : ℂ}, StripGood φ M F₂ (φ.pathImage r) e z →
        StripGood φ M F₂ (φ.pathImage r) e' z' → JoinedIn (φ.stripSet F₂ (φ.pathImage r)) z z'
  | _, _, .nil, e'', h, z, z', hz, hz' => by
    obtain ⟨-, σ, w, w', hσ, he, -, hT, hF⟩ := (φ.stripGraph_adj).mp h
    exact joinedIn_stripSet_of_tri hT hF (hz σ w w' hσ he hT hF) (hz' σ w w' hσ he hT hF)
  | _, _, .cons h p', e'', _, z, z', hz, hz' => by
    obtain ⟨-, σ, w, w', hσ, he, he₂, hT, hF⟩ := (φ.stripGraph_adj).mp h
    obtain ⟨z₂, hz₂⟩ := hφ.exists_stripGood hC hR hθ hl hMC hr hZ h.symm
    have h1 := hz σ w w' hσ he hT hF
    have h2 := hz₂ σ w' w hσ he₂ hT.swap₂₃ (by rwa [← φ.cycleImage_swap₂₃])
    rw [← φ.cycleImage_swap₂₃] at h2
    exact (joinedIn_stripSet_of_tri hT hF h1 h2).trans
      (hφ.joinedIn_of_walk hC hR hθ hl hMC hr hZ p' h.symm hz₂ hz')


/-- **The strip.** The points of the triangles on the side `F₂` at the two edges of the cut with
one end in `M` are joined in the strip set, when no edge of `r` at `M` runs between two triangles on
the side `F₂` (`hZ`). -/
theorem IsRibEmbedding.joinedIn_strip [Finite V] (hφ : φ.IsRibEmbedding C)
    (hC : IsCycleList G C) (hR : ∀ x ∈ C, x ∈ R)
    (hθ : IsTheta (φ.cycleImage C) F₁ F₂ A₁ A₂ (φ.pathImage l) p q) (hl : IsPathList G R l)
    {M : Set V} (hMC : ∀ u ∈ M, u ∉ C) {r : List V} (hr : IsPathList G R r)
    (hZ : ∀ σ ∈ M, ∀ w, w ∈ R → G.Adj σ w → ¬ IsListEdge l σ w →
      (∀ x, IsTriangleOn G R σ w x → Surface.inner (φ.cycleImage [σ, w, x]) ⊆ Surface.inner F₂) →
      ¬ IsListEdge r σ w)
    {σ₀ σ₁ τ₀ τ₁ : V} (hσ : IsListEdge l σ₁ σ₀) (hσ₁ : σ₁ ∈ M) (hσ₀ : σ₀ ∉ M)
    (hτ : IsListEdge l τ₀ τ₁)
    (honly : ∀ u v, IsListEdge l u v → u ∈ M → v ∉ M → s(u, v) = s(σ₁, σ₀) ∨ s(u, v) = s(τ₀, τ₁))
    {x₀ x₁ : V} (hx₀ : x₀ ∈ φ.sideTris F₂ σ₁ σ₀) (hx₁ : x₁ ∈ φ.sideTris F₂ τ₀ τ₁) {z₀ z₁ : ℂ}
    (hz₀ : z₀ ∈ Surface.inner (φ.cycleImage [σ₁, σ₀, x₀]) ∪
      (φ.cycleImage [σ₁, σ₀, x₀] \ φ.pathImage r))
    (hz₁ : z₁ ∈ Surface.inner (φ.cycleImage [τ₀, τ₁, x₁]) ∪
      (φ.cycleImage [τ₀, τ₁, x₁] \ φ.pathImage r)) :
    JoinedIn (φ.stripSet F₂ (φ.pathImage r)) z₀ z₁ := by
  obtain ⟨w⟩ := hφ.reachable_stripGraph hC hR hθ hl hMC hσ hσ₁ hσ₀ honly (F₂ := F₂)
  have hadj : (φ.stripGraph M F₂).Adj s(σ₁, σ₀) s(σ₁, x₀) := by
    refine (φ.stripGraph_adj).mpr ⟨fun h => ?_, σ₁, σ₀, x₀, hσ₁, rfl, rfl, hx₀.1, hx₀.2⟩
    rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨h, -⟩
    · exact hx₀.1.2.2.2.2.1.ne h
    · exact hx₀.1.2.2.2.2.2.ne h
  exact hφ.joinedIn_of_walk hC hR hθ hl hMC hr hZ w hadj
    (hφ.stripGood_of_cut hC hR hθ hl hMC hσ hx₀ hz₀)
    (hφ.stripGood_of_cut hC hR hθ hl hMC hτ hx₁ hz₁)

/-- The strip set lies in the closed disc bounded by the image of the frame. -/
theorem IsRibEmbedding.stripSet_subset (hφ : φ.IsRibEmbedding C) (hC : IsCycleList G C)
    (hR : ∀ x ∈ C, x ∈ R) (hUF : φ.U ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C)
    (Z : Set ℂ) :
    φ.stripSet F₂ Z ⊆ Surface.inner (φ.cycleImage C) ∪ φ.cycleImage C := by
  rintro z ⟨a, b, c, hT, -, hz | hz⟩
  · exact Or.inl (hφ.tri_inner hC hR hT hz)
  · exact hUF (φ.cycleImage_subset_U hT.isCycleList hT.mem hz.1)

/-- The strip set misses every part `Z` of the drawing. -/
theorem IsRibEmbedding.disjoint_stripSet (hφ : φ.IsRibEmbedding C) {Z : Set ℂ} (hZ : Z ⊆ φ.U) :
    Disjoint (φ.stripSet F₂ Z) Z := by
  refine Set.disjoint_left.mpr ?_
  rintro z ⟨a, b, c, hT, -, hz | hz⟩ hzZ
  · exact Set.disjoint_left.mp (hφ.inner_mem_faces hT).2 (hZ hzZ) hz
  · exact hz.2 hzZ

end PlaneEmbedding

end GraphMinor.HP25
