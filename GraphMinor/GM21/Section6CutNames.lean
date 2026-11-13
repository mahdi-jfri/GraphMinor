module

public import GraphMinor.GM21.Section6SplitPresentation

/-!
# Graph Minors XXI, (6.3), claim (2): splitting twice

Claim (2) of the proof of (6.3) (page 28 of the preprint) says: "Let $\Gamma'$ be the drawing
in $\Sigma'$ obtained from $\Gamma$ by splitting appropriately the vertices of $\Gamma$ in $F$. ...
By splitting $v$ according to $\delta_1(v), \delta_2(v)$, for each $v \in V(\mu(a))$, and similarly
splitting each $v \in V(\mu(b))$, we obtain a graph $G'$ which has a presentation in $\Sigma'$
(using the drawing $\Gamma'$) of depth $\le q$ and defect $\le r + 2$." When one
support holds both ends `a, b` of the line and `μ(a)` and `μ(b)` share a vertex, that vertex lies in
three pieces of the support, so it needs three copies. We split twice: first the set `Xa` with the
edges `Ea` going to the second copies, then the set `Xb` of the new graph with the edges `Eb`.

* `split2 G Xa Ea Xb Eb` is the graph split twice, and `nm2 Xa Xb c v` is the copy of `v` on the
  sides `c = (c₁, c₂)`.
* `isoImage_nm2_le`: a subgraph whose edges are on the sides `c` is copied into the split graph.
* `exists_nm2_of_mem`: each vertex of the split graph is a copy of a vertex of `G`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Split

open Set Function Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- Each vertex of the split graph is the copy on some side of a vertex of `G`. -/
theorem exists_splitName_of_mem {G : Hypergraph α β} {X : Set α} {E₂ : Set β} {w : α ⊕ α ⊕ α}
    (hw : w ∈ (splitAlong G X E₂).vertexSet) :
    ∃ c v, v ∈ G.vertexSet ∧ splitName X c v = w := by
  rcases hw with (⟨v, ⟨hv, hvX⟩, rfl⟩ | ⟨v, ⟨hv, hvX⟩, rfl⟩) | ⟨v, ⟨hv, hvX⟩, rfl⟩
  · exact ⟨false, v, hv, splitName_of_notMem hvX⟩
  · exact ⟨false, v, hv, splitName_false_of_mem hvX⟩
  · exact ⟨true, v, hv, splitName_true_of_mem hvX⟩

/-- The vertex names of a graph split twice. -/
abbrev Name2 (α : Type u) : Type u := (α ⊕ α ⊕ α) ⊕ (α ⊕ α ⊕ α) ⊕ (α ⊕ α ⊕ α)

/-- The name of the copy of `v` on the sides `c = (c₁, c₂)` in a graph split twice. -/
noncomputable def nm2 (Xa : Set α) (Xb : Set (α ⊕ α ⊕ α)) (c : Bool × Bool) (v : α) : Name2 α :=
  splitName Xb c.2 (splitName Xa c.1 v)

/-- The graph `G` split first along `Xa`, with the edges `Ea` on the second copies, and then along
`Xb`, with the edges `Eb` on the second copies. -/
def split2 (G : Hypergraph α β) (Xa : Set α) (Ea : Set β) (Xb : Set (α ⊕ α ⊕ α)) (Eb : Set β) :
    Hypergraph (Name2 α) β :=
  splitAlong (splitAlong G Xa Ea) Xb Eb

variable {G : Hypergraph α β} {Xa : Set α} {Ea : Set β} {Xb : Set (α ⊕ α ⊕ α)} {Eb : Set β}

/-- Two copies are equal only for the same vertex. -/
theorem eq_of_nm2_eq {c c' : Bool × Bool} {v w : α} (h : nm2 Xa Xb c v = nm2 Xa Xb c' w) :
    v = w :=
  eq_of_splitName_eq (eq_of_splitName_eq h)

theorem nm2_injective (c : Bool × Bool) : Injective (nm2 Xa Xb c) :=
  fun _ _ h => eq_of_nm2_eq h

@[simp] theorem split2_edgeSet : (split2 G Xa Ea Xb Eb).edgeSet = G.edgeSet := rfl

/-- The copy of a vertex of `G` is a vertex of the split graph. -/
theorem nm2_mem (c : Bool × Bool) {v : α} (hv : v ∈ G.vertexSet) :
    nm2 Xa Xb c v ∈ (split2 G Xa Ea Xb Eb).vertexSet :=
  splitName_mem c.2 (splitName_mem c.1 hv)

/-- An edge on the sides `c` is incident in the split graph with the copy on the sides `c` of each
of its ends. -/
theorem split2_inc_nm2_iff {c : Bool × Bool} {e : β} (ha : e ∈ Ea ↔ c.1 = true)
    (hb : e ∈ Eb ↔ c.2 = true) {v : α} :
    (split2 G Xa Ea Xb Eb).Inc e (nm2 Xa Xb c v) ↔ G.Inc e v :=
  (splitAlong_inc_splitName_iff hb).trans (splitAlong_inc_splitName_iff ha)

/-- An edge on the sides `c` is incident in the split graph only with copies on the sides `c`. -/
theorem eq_nm2_of_inc {c : Bool × Bool} {e : β} (ha : e ∈ Ea ↔ c.1 = true)
    (hb : e ∈ Eb ↔ c.2 = true) {x : Name2 α} (hx : (split2 G Xa Ea Xb Eb).Inc e x) :
    ∃ v, G.Inc e v ∧ nm2 Xa Xb c v = x := by
  obtain ⟨w, hw, rfl⟩ := eq_splitName_of_splitAlong_inc hb hx
  obtain ⟨v, hv, rfl⟩ := eq_splitName_of_splitAlong_inc ha hw
  exact ⟨v, hv, rfl⟩

/-- An incidence of the split graph comes from an incidence of `G`. -/
theorem inc_of_split2_inc {e : β} {c : Bool × Bool} {v : α}
    (h : (split2 G Xa Ea Xb Eb).Inc e (nm2 Xa Xb c v)) : G.Inc e v := by
  classical
  have ha : e ∈ Ea ↔ decide (e ∈ Ea) = true := decide_eq_true_iff.symm
  have hb : e ∈ Eb ↔ decide (e ∈ Eb) = true := decide_eq_true_iff.symm
  obtain ⟨w, hw, hwx⟩ := eq_nm2_of_inc (c := (decide (e ∈ Ea), decide (e ∈ Eb))) ha hb h
  rwa [← eq_of_nm2_eq hwx]

/-- **A subgraph on the sides `c` is copied into the split graph.** -/
theorem isoImage_nm2_le {A : Hypergraph α β} {c : Bool × Bool} (hA : A ≤ G)
    (hc : ∀ e ∈ A.edgeSet, (e ∈ Ea ↔ c.1 = true) ∧ (e ∈ Eb ↔ c.2 = true)) :
    isoImage (nm2 Xa Xb c) id A ≤ split2 G Xa Ea Xb Eb where
  vertexSet_subset := by
    rintro _ ⟨v, hv, rfl⟩
    exact nm2_mem c (hA.vertexSet_subset hv)
  edgeSet_subset := by
    rintro _ ⟨e, he, rfl⟩
    exact hA.edgeSet_subset he
  ends_eq := by
    rintro _ ⟨e, he, rfl⟩
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, isoImage, id_eq]
    constructor
    · intro hx
      obtain ⟨v, hv, rfl⟩ := eq_nm2_of_inc (hc e he).1 (hc e he).2 hx
      exact ⟨e, v, (GM10.inc_iff_of_le hA he).mpr hv, rfl, rfl⟩
    · rintro ⟨e₀, v, hv, rfl, rfl⟩
      exact (split2_inc_nm2_iff (hc e₀ he).1 (hc e₀ he).2).mpr (GM10.inc_of_le hA hv)

/-- Each vertex of the split graph is the copy on some sides of a vertex of `G`. -/
theorem exists_nm2_of_mem {w : Name2 α} (hw : w ∈ (split2 G Xa Ea Xb Eb).vertexSet) :
    ∃ c v, v ∈ G.vertexSet ∧ nm2 Xa Xb c v = w := by
  obtain ⟨c₂, w', hw', rfl⟩ := exists_splitName_of_mem hw
  obtain ⟨c₁, v, hv, rfl⟩ := exists_splitName_of_mem hw'
  exact ⟨(c₁, c₂), v, hv, rfl⟩

/-- The first side does not matter for a vertex outside `Xa`. -/
theorem nm2_eq_of_notMem_left {c c' : Bool × Bool} (h2 : c.2 = c'.2) {v : α} (hv : v ∉ Xa) :
    nm2 Xa Xb c v = nm2 Xa Xb c' v := by
  unfold nm2
  rw [splitName_of_notMem hv, splitName_of_notMem hv, h2]

/-- The second side does not matter for a vertex whose first copy is outside `Xb`. -/
theorem nm2_eq_of_notMem_right {c c' : Bool × Bool} (h1 : c.1 = c'.1) {v : α}
    (hv : splitName Xa c.1 v ∉ Xb) : nm2 Xa Xb c v = nm2 Xa Xb c' v := by
  unfold nm2
  rw [← h1, splitName_of_notMem hv, splitName_of_notMem hv]

/-- Both sides do not matter for a vertex outside both split sets. -/
theorem nm2_eq_of_notMem {c c' : Bool × Bool} {v : α} (ha : v ∉ Xa)
    (hb : ∀ d, splitName Xa d v ∉ Xb) : nm2 Xa Xb c v = nm2 Xa Xb c' v :=
  (nm2_eq_of_notMem_right (c := c) (c' := (c.1, c'.2)) rfl (hb _)).trans
    (nm2_eq_of_notMem_left (c := (c.1, c'.2)) (c' := c') rfl ha)

/-- Copies of a vertex of `Xa` on different first sides differ. -/
theorem nm2_ne_of_mem_left {c c' : Bool × Bool} (hc : c.1 ≠ c'.1) {v w : α} (hv : v ∈ Xa) :
    nm2 Xa Xb c v ≠ nm2 Xa Xb c' w := by
  intro h
  have h1 := eq_of_splitName_eq h
  exact notMem_of_splitName_eq hc h1 hv

/-- Copies of a vertex whose first copy is in `Xb` on different second sides differ. -/
theorem nm2_ne_of_mem_right {c c' : Bool × Bool} (h1 : c.1 = c'.1) (hc : c.2 ≠ c'.2) {v : α}
    (hv : splitName Xa c.1 v ∈ Xb) : nm2 Xa Xb c v ≠ nm2 Xa Xb c' v := by
  intro h
  unfold nm2 at h
  rw [← h1] at h
  exact notMem_of_splitName_eq hc h hv

/-- Equal copies of a vertex of `Xa` are on the same first side. -/
theorem fst_eq_of_nm2_eq {c c' : Bool × Bool} {v w : α} (hv : v ∈ Xa)
    (h : nm2 Xa Xb c v = nm2 Xa Xb c' w) : c.1 = c'.1 := by
  by_contra hc
  exact nm2_ne_of_mem_left hc hv h

/-- Equal copies of a vertex whose first copy is in `Xb` are on the same second side. -/
theorem snd_eq_of_nm2_eq {c c' : Bool × Bool} {v w : α} (hv : splitName Xa c.1 v ∈ Xb)
    (h : nm2 Xa Xb c v = nm2 Xa Xb c' w) : c.2 = c'.2 := by
  by_contra hc
  exact notMem_of_splitName_eq hc h hv

/-- A graph split twice is a graph. -/
theorem isGraph_split2 (hG : G.IsGraph) : (split2 G Xa Ea Xb Eb).IsGraph :=
  isGraph_splitAlong (isGraph_splitAlong hG _ _) _ _

end Split
end GM21
end GraphMinor
