module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15GraftIsoEmbedding

/-!
# The classes of Section 18 and the statements of (18.3) and (6.1)

Page 286 defines `𝒞(Σ, k)`, the grafts of index at most `k` that embed in
`Σ`, and `𝒞(h, k)`, the union of `𝒞(Σ, k)` over all surfaces with
`g(Σ) ≤ h`. The proof of (18.3) on page 287 also uses `𝒞(Σ; k₁, …, k_c)`,
the grafts with a drawing in `Σ` that has `kᵢ` vertices on the cuff `Cᵢ`. We
index the cuff counts by the cuffs themselves, so no order of the cuffs is
needed.

The surfaces in `𝒞(h, k)` live in a fixed universe `w`. The surfaces made in
the proof (cut surfaces and pieces of surfaces) stay in the universe of the
surface they come from.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v w u' v'

/-- `𝒞(Σ, k)`: the grafts of index at most `k` which embed in `Σ`
(VIII Section 18, page 286). -/
def classCSurface {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S] (k : ℕ) :
    Set (Graft α β) :=
  {X | X.index ≤ k ∧ EmbedsGraft S X}

/-- `𝒞(Σ; k₁, …, k_c)`: the grafts with a drawing in `Σ` that has exactly
`κ C` vertices on each cuff `C` (VIII Section 18, page 287). -/
def classCCuffs {α : Type u} {β : Type v} (S : Type w) [TopologicalSpace S]
    (κ : Set S → ℕ) : Set (Graft α β) :=
  {X | ∃ gd : GraftDrawing X.G X.T S, ∀ C ∈ cuffs S, (gd.drawing.V ∩ C).ncard = κ C}

/-- `𝒞(h, k)`: the union of `𝒞(Σ, k)` over all surfaces `Σ` with
`g(Σ) ≤ h` (VIII Section 18, page 286). A surface need not be connected, and
`g` of a surface is the maximum over its components (`surfaceComplexity`). -/
def classC {α : Type u} {β : Type v} (h k : ℕ) : Set (Graft α β) :=
  {X | ∃ (S : Type w) (_ : TopologicalSpace S), IsSurface S ∧ surfaceComplexity S ≤ h ∧
    X ∈ classCSurface S k}

/-- **VIII (18.3)**, page 286: for any integers `h, k ≥ 0`, `𝒞(h, k)` is
well-rooted. -/
def Theorem183Statement : Prop :=
  ∀ (α : Type u) (β : Type v) (h k : ℕ),
    IsWellRootedGraftClass (classC.{u, v, w} (α := α) (β := β) h k)

/-- **VIII (6.1)**, page 263: if `𝒜` is a class of grafts with bounded index,
and some surface `Σ` embeds `𝒜`, then `𝒜` is well-rooted. The paper writes
"class of graphs"; the index and the simulation make sense only for grafts. -/
def Theorem61Statement : Prop :=
  ∀ (α : Type u) (β : Type v) (𝒜 : Set (Graft α β)), HasGraftClassIndex 𝒜 →
    (∃ (S : Type w) (_ : TopologicalSpace S), IsSurface S ∧ EmbedsGraftClass S 𝒜) →
    IsWellRootedGraftClass 𝒜

/-! ## Basic facts -/

/-- Isomorphic grafts have the same index. -/
theorem IsGraftIso.index_eq {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {Y : Graft α' β'} {X : Graft α β} (h : IsGraftIso Y X) : X.index = Y.index := by
  obtain ⟨φ, hT⟩ := h
  unfold Graft.index
  refine (Set.ncard_congr (fun t ht => (φ.vertexEquiv ⟨t, Y.T_subset ht⟩).1) ?_ ?_ ?_).symm
  · intro t ht
    exact (hT _).mp ht
  · intro a ha b hb hab
    have := φ.vertexEquiv.injective (Subtype.ext hab)
    simpa using congrArg Subtype.val this
  · intro x hx
    refine ⟨(φ.vertexEquiv.symm ⟨x, X.T_subset hx⟩).1, (hT _).mpr (by simpa using hx), by simp⟩

/-- `𝒞(Σ, k)` is closed under isomorphism. -/
theorem mem_classCSurface_of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'}
    {β' : Type v'} {S : Type w} [TopologicalSpace S] {k : ℕ} {Y : Graft α' β'}
    {X : Graft α β} (h : IsGraftIso Y X) (hY : Y ∈ classCSurface S k) :
    X ∈ classCSurface S k :=
  ⟨h.index_eq ▸ hY.1, embedsGraft_of_isGraftIso h hY.2⟩

/-- `𝒞(h, k)` is closed under isomorphism. -/
theorem mem_classC_of_isGraftIso {α : Type u} {β : Type v} {α' : Type u'}
    {β' : Type v'} {h k : ℕ} {Y : Graft α' β'} {X : Graft α β} (hi : IsGraftIso Y X)
    (hY : Y ∈ classC.{u', v', w} h k) : X ∈ classC.{u, v, w} h k := by
  obtain ⟨S, tS, hS, hg, hYS⟩ := hY
  exact ⟨S, tS, hS, hg, mem_classCSurface_of_isGraftIso hi hYS⟩

/-- `𝒞(h, k)` grows with `h` and `k`. -/
theorem classC_mono {α : Type u} {β : Type v} {h h' k k' : ℕ} (hh : h ≤ h') (hk : k ≤ k') :
    classC.{u, v, w} (α := α) (β := β) h k ⊆ classC.{u, v, w} h' k' := by
  rintro X ⟨S, tS, hS, hg, hi, he⟩
  exact ⟨S, tS, hS, hg.trans hh, hi.trans hk, he⟩

/-- `𝒞(Σ, k)` lies in `𝒞(h, k)` when `g(Σ) ≤ h`. -/
theorem classCSurface_subset_classC {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] (hS : IsSurface S) {h k : ℕ} (hg : surfaceComplexity S ≤ h) :
    classCSurface (α := α) (β := β) S k ⊆ classC.{u, v, w} h k :=
  fun _ hX => ⟨S, inferInstance, hS, hg, hX⟩

end GraphMinor.GM08
