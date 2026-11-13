module

public import GraphMinor.GM06.Defs
import Mathlib.Data.List.FinRange

/-!
# Finite drawing data for the disc feasibility algorithm

The input consists of vertex labels, edge ends, region boundaries, cuff
orders, and division blocks. All fields are finite data. In particular,
parallel edges retain their separate positions in the edge list. Cuffs are
stored separately so that the same drawing data can also describe a cylinder.

The representation relation records bijections to an actual drawing. Its
order condition compares crossings with the supplied cyclic lists. It does
not ask for a realization or for any of the reductions of VI (3.4).
-/

@[expose] public section
namespace GraphMinor.Compute

open Set GraphMinor.Surface GraphMinor.GM06

/-- A boundary is recorded by its incident vertex and edge labels. -/
structure GM06RegionBoundary (n m : ℕ) where
  vertices : List (Fin n)
  edges : List (Fin m)
  deriving DecidableEq

/-- Plain finite drawing data for VI, Section 3, pages 120–121. The edge
list includes both ends even for a loop. Region boundaries are incidence
lists, and cuff lists give cyclic orders. Division blocks are lists of
vertex labels, as in VI, Section 1, page 116. -/
structure GM06DrawingData where
  n : ℕ
  ends : List (Fin n × Fin n)
  regions : List (GM06RegionBoundary n ends.length)
  cuffs : List (List (Fin n))
  division : List (List (Fin n))
  deriving DecidableEq

namespace GM06DrawingData

/-- Membership strictly between two positions in the positive cyclic order. -/
def cyclicBetween (p q t : ℕ) : Bool :=
  if p < q then decide (p < t ∧ t < q) else decide (p < t ∨ t < q)

/-- Two pairs alternate on a cuff when exactly one end of the second pair
lies strictly between the ends of the first pair. All four ends must occur
and must be distinct. This is the crossing test of VI, Section 2, page 117. -/
def crossesOnList {n : ℕ} (L : List (Fin n)) (a c b d : Fin n) : Bool :=
  decide (a ∈ L ∧ c ∈ L ∧ b ∈ L ∧ d ∈ L ∧
    a ≠ c ∧ b ≠ d ∧ a ≠ b ∧ a ≠ d ∧ c ≠ b ∧ c ≠ d) &&
    (cyclicBetween (L.idxOf a) (L.idxOf c) (L.idxOf b) !=
      cyclicBetween (L.idxOf a) (L.idxOf c) (L.idxOf d))

/-- The finite crossing test over all cuffs. -/
def crosses (x : GM06DrawingData) (a c b d : Fin x.n) : Bool :=
  x.cuffs.any (fun L => crossesOnList L a c b d)

/-- A list block as a set of labels. -/
def block {n : ℕ} (L : List (Fin n)) : Set (Fin n) := {v | v ∈ L}

/-- The division described by the supplied blocks. -/
def divisionSet (x : GM06DrawingData) : Set (Set (Fin x.n)) :=
  block '' {L | L ∈ x.division}

/-- A finite check for the cross-free condition of VI, Section 2, page 117.
It compares blocks as sets, so reordering a block does not change the test. -/
def crossFree (x : GM06DrawingData) : Bool :=
  x.division.all fun A => x.division.all fun B =>
    A.toFinset == B.toFinset || A.all fun a => A.all fun c =>
      B.all fun b => B.all fun d => !(x.crosses a c b d)

/-- The words occupied by a length-prefixed list. -/
def listWords (L : List ℕ) : List ℕ := L.length :: L

/-- A list of lists, each preceded by its length. -/
def listsWords (L : List (List ℕ)) : List ℕ :=
  L.length :: L.flatMap listWords

/-- Flatten the supplied data into words. Each variable-length section has
a count, including both incidence lists for each region. No mathematical
search is performed by this encoding. -/
def words (x : GM06DrawingData) : List ℕ :=
  [x.n, x.ends.length, x.regions.length] ++
    x.ends.flatMap (fun e => [e.1.val, e.2.val]) ++
    x.regions.flatMap (fun r =>
      listWords (r.vertices.map Fin.val) ++ listWords (r.edges.map Fin.val)) ++
    listsWords (x.cuffs.map (List.map Fin.val)) ++
    listsWords (x.division.map (List.map Fin.val))

/-- The size counts all vertices as well as input words. Isolated vertices
are represented by the vertex count and still contribute to the size. -/
def size (x : GM06DrawingData) : ℕ := x.n + x.words.length

/-- The crossing test is a finite condition on the supplied lists. -/
theorem crossFree_eq_true_iff (x : GM06DrawingData) :
    x.crossFree = true ↔
      ∀ A ∈ x.division, ∀ B ∈ x.division, A.toFinset ≠ B.toFinset →
        ∀ a ∈ A, ∀ c ∈ A, ∀ b ∈ B, ∀ d ∈ B, x.crosses a c b d = false := by
  simp only [crossFree, List.all_eq_true, Bool.or_eq_true, beq_iff_eq,
    Bool.not_eq_true']
  constructor
  · intro h A hA B hB hne
    exact (h A hA B hB).resolve_left hne
  · intro h A hA B hB
    by_cases heq : A.toFinset = B.toFinset
    · exact Or.inl heq
    · exact Or.inr (h A hA B hB heq)

/-- Empty division blocks never produce a crossing. -/
theorem crossFree_empty_division (x : GM06DrawingData) (h : x.division = []) :
    x.crossFree = true := by
  simp [crossFree, h]

end GM06DrawingData

/-- The finite data describe a drawing and its division through bijections.
For regions, the lists describe the boundary relative to the surface,
namely `closure r \ r`. Cuff order is specified by its crossing relation,
so the starting point and orientation of a cyclic list do not matter.
Every field concerns input data or its interpretation, rather than a step
or the answer of VI (3.4). -/
structure GM06DrawingRep (x : GM06DrawingData) {S : Type*} [TopologicalSpace S]
    (G : Drawing S) (Δ : Set (Set S)) where
  vertex : Fin x.n ≃ G.V
  edge : Fin x.ends.length ≃ G.E
  region : Fin x.regions.length ≃ G.R
  ends : ∀ e : Fin x.ends.length,
    closure (edge e).val ∩ G.V =
      {(vertex (x.ends[e].1)).val, (vertex (x.ends[e].2)).val}
  boundary : ∀ r : Fin x.regions.length,
    closure (region r).val \ (region r).val =
      {p | ∃ v ∈ x.regions[r].vertices, (vertex v).val = p} ∪
      ⋃ e ∈ x.regions[r].edges, (edge e).val
  cuff : Fin x.cuffs.length ≃ Surface.cuffs S
  cuff_vertices : ∀ i : Fin x.cuffs.length,
    (fun v => (vertex v).val) '' GM06DrawingData.block x.cuffs[i] =
      G.V ∩ (cuff i).val
  cuff_nodup : ∀ L ∈ x.cuffs, L.Nodup
  order : ∀ a c b d : Fin x.n,
    x.crosses a c b d = true ↔
      ∃ C ∈ Surface.cuffs S,
        CrossesOn C (vertex a).val (vertex c).val (vertex b).val (vertex d).val
  division : Δ =
    (fun L => (fun v => (vertex v).val) '' GM06DrawingData.block L) ''
      {L | L ∈ x.division}

namespace GM06DrawingRep

private theorem image_block_eq_iff {n : ℕ} {S : Type*} (f : Fin n → S)
    (hf : Function.Injective f) (A B : List (Fin n)) :
    f '' GM06DrawingData.block A = f '' GM06DrawingData.block B ↔
      A.toFinset = B.toFinset := by
  constructor
  · intro h
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro hv
      obtain ⟨w, hw, heq⟩ := h ▸ (show f v ∈ f '' GM06DrawingData.block A from ⟨v, hv, rfl⟩)
      exact hf heq ▸ hw
    · intro hv
      obtain ⟨w, hw, heq⟩ := h.symm ▸
        (show f v ∈ f '' GM06DrawingData.block B from ⟨v, hv, rfl⟩)
      exact hf heq ▸ hw
  · intro h
    have hb : GM06DrawingData.block A = GM06DrawingData.block B := by
      ext v
      change v ∈ A ↔ v ∈ B
      simpa only [List.mem_toFinset] using
        (show v ∈ A.toFinset ↔ v ∈ B.toFinset from h ▸ Iff.rfl)
    rw [hb]

/-- Correctness of the finite crossing check: it accepts exactly when no
cuff has crossing division blocks, as defined in VI, Section 2, page 117.
The only hypothesis is that the supplied data describe the drawing and
its division. This theorem does not use a feasibility decision. -/
theorem crossFree_iff {x : GM06DrawingData} {S : Type*} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) :
    x.crossFree = true ↔ ∀ C ∈ Surface.cuffs S, IsCrossFree C Δ := by
  have hinj : Function.Injective (fun v => (h.vertex v).val) :=
    Subtype.val_injective.comp h.vertex.injective
  rw [GM06DrawingData.crossFree_eq_true_iff]
  constructor
  · intro ht C hC
    rintro ⟨δ, hδ, ε, hε, hne, a, ha, c, hc, b, hb, d, hd, hcross⟩
    rw [h.division] at hδ hε
    obtain ⟨A, hA, rfl⟩ := hδ
    obtain ⟨B, hB, rfl⟩ := hε
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨c, hc, rfl⟩ := hc
    obtain ⟨b, hb, rfl⟩ := hb
    obtain ⟨d, hd, rfl⟩ := hd
    have hAB : A.toFinset ≠ B.toFinset := fun heq =>
      hne ((image_block_eq_iff _ hinj A B).mpr heq)
    have hf := ht A hA B hB hAB a ha c hc b hb d hd
    have ht := (h.order a c b d).mpr ⟨C, hC, hcross⟩
    exact Bool.noConfusion (hf.symm.trans ht)
  · intro ht A hA B hB hne a ha c hc b hb d hd
    cases heq : x.crosses a c b d with
    | false => rfl
    | true =>
      obtain ⟨C, hC, hcross⟩ := (h.order a c b d).mp heq
      apply False.elim
      apply ht C hC
      refine ⟨(fun v => (h.vertex v).val) '' GM06DrawingData.block A, ?_,
        (fun v => (h.vertex v).val) '' GM06DrawingData.block B, ?_, ?_,
        (h.vertex a).val, ⟨a, ha, rfl⟩, (h.vertex c).val, ⟨c, hc, rfl⟩,
        (h.vertex b).val, ⟨b, hb, rfl⟩, (h.vertex d).val, ⟨d, hd, rfl⟩, hcross⟩
      · exact h.division.symm.subset ⟨A, hA, rfl⟩
      · exact h.division.symm.subset ⟨B, hB, rfl⟩
      · exact fun he => hne ((image_block_eq_iff _ hinj A B).mp he)

end GM06DrawingRep

end GraphMinor.Compute
