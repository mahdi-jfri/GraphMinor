module

public import GraphMinor.GM08.Section15PrintedPinch
public import GraphMinor.GM07.Section9DiscSphere
public import GraphMinor.GM07.CuffCells
public import GraphMinor.Surface.DiscArcs
public import GraphMinor.Surface.DiscUnion
public import GraphMinor.GM06.Section4Subarc
public import GraphMinor.GM06.Section4OpenSubarc
public import GraphMinor.GM08.Section18NestedCap
public import GraphMinor.GM08.Section12Subspace
public import GraphMinor.GM07.Matched
public import GraphMinor.GM19.FeatureOrient
public import GraphMinor.Surface.DiscMerge
public import GraphMinor.GM12.Section3SubspaceArcs
public import GraphMinor.GM08.Section17CollarDrawing

/-!
# A pinched framing built from a disc

This file builds the framings needed for the pieces of our proof of the printed
(15.1) (`Section15PrintedFinal.lean`).

Start from a closed disc `B` in a sphere and two points `p ≠ q` on its boundary.
They cut `bd B` into two open arcs `A₁` and `A₂`. Outside `B`, a chord `C` of the
closed complement joins `p` to `q`, and it cuts that complement into two discs
`K₁` and `K₂`, with boundaries `A₁ ∪ C` and `A₂ ∪ C` (`exists_theta_discs`).
So the sphere is the union of the three discs `B`, `K₁`, `K₂`, which meet pairwise
in `C` and in the closures of `A₁`, `A₂`. Both `B ∪ K₁` and `B ∪ K₂` are discs.

Then `A₁ ∪ C` and `A₂ ∪ C` are the two hoops of a tube, once small discs are cut
out of the interiors of `K₁` and `K₂`; the region between them is `B ∪ C`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

section Components

variable {Z : Type u} [TopologicalSpace Z]

/-- A component of a set lies in it. -/
theorem subset_of_mem_componentsIn {Y A : Set Z} (hA : A ∈ componentsIn Y) : A ⊆ Y := by
  obtain ⟨x, -, rfl⟩ := hA
  exact connectedComponentIn_subset Y x

/-- If a set has exactly two components, they cover it. -/
theorem union_eq_of_componentsIn_eq_pair {Y A₁ A₂ : Set Z}
    (h : componentsIn Y = {A₁, A₂}) : A₁ ∪ A₂ = Y := by
  refine Subset.antisymm (union_subset (subset_of_mem_componentsIn (h ▸ .inl rfl))
    (subset_of_mem_componentsIn (h ▸ .inr rfl))) fun y hy => ?_
  have hmem : connectedComponentIn Y y ∈ componentsIn Y := ⟨y, hy, rfl⟩
  rw [h] at hmem
  rcases hmem with h1 | h1
  · exact .inl (h1 ▸ mem_connectedComponentIn hy)
  · exact .inr (h1 ▸ mem_connectedComponentIn hy)

/-- Two different components are disjoint. -/
theorem disjoint_of_mem_componentsIn {Y A₁ A₂ : Set Z} (h₁ : A₁ ∈ componentsIn Y)
    (h₂ : A₂ ∈ componentsIn Y) (hne : A₁ ≠ A₂) : Disjoint A₁ A₂ := by
  obtain ⟨x, hx, rfl⟩ := h₁
  obtain ⟨y, hy, rfl⟩ := h₂
  rw [disjoint_iff_inter_eq_empty]
  by_contra hne'
  obtain ⟨z, hz₁, hz₂⟩ := nonempty_iff_ne_empty.mpr hne'
  exact hne ((connectedComponentIn_eq hz₁).trans (connectedComponentIn_eq hz₂).symm)

end Components

section Theta

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z]

/-- **Three discs of a sphere meeting in a theta.** Let `B` be a closed disc of a
sphere and `p ≠ q` two points of its boundary, which cut it into the open arcs `A₁`
and `A₂`. Then there are a line `C` from `p` to `q` that meets `B` only at its ends,
and two closed discs `K₁`, `K₂` with boundaries `A₁ ∪ C` and `A₂ ∪ C`, such that
`B`, `K₁`, `K₂` cover the sphere and meet pairwise only in `C`, `A₁ ∪ {p, q}` and
`A₂ ∪ {p, q}`. Moreover `B ∪ K₁` and `B ∪ K₂` are closed discs, with boundaries
`A₂ ∪ C` and `A₁ ∪ C`.

The closure of the complement of `B` is a closed disc with the same boundary
(`GM07.exists_compl_disc_in_sphere`). A chord of it from `p` to `q`
(`GM07.exists_chord_any`) splits it into `K₁` and `K₂` (`disc_iArc`). Each of
`K₁`, `K₂` meets `B` in the closure of one arc, which is a line, so its union with
`B` is a disc (`disc_union`). -/
theorem exists_theta_discs (hsph : IsSphere Z) {B : Set Z} (hB : IsClosedDisc B) {p q : Z}
    (hp : p ∈ discBd B) (hq : q ∈ discBd B) (hpq : p ≠ q) :
    ∃ A₁ A₂ C K₁ K₂ : Set Z,
      componentsIn (discBd B \ {p, q}) = {A₁, A₂} ∧ A₁ ≠ A₂ ∧
      IsLineWithEnds C p q ∧ C ∩ B = {p, q} ∧
      IsClosedDisc K₁ ∧ IsClosedDisc K₂ ∧ discBd K₁ = A₁ ∪ C ∧ discBd K₂ = A₂ ∪ C ∧
      K₁ ∩ K₂ = C ∧ K₁ ∪ K₂ ∪ B = univ ∧
      K₁ ∩ B = A₁ ∪ {p, q} ∧ K₂ ∩ B = A₂ ∪ {p, q} ∧
      IsClosedDisc (B ∪ K₁) ∧ discBd (B ∪ K₁) = A₂ ∪ C ∧
      IsClosedDisc (B ∪ K₂) ∧ discBd (B ∪ K₂) = A₁ ∪ C := by
  obtain ⟨E, hE, hbE, hEeq, -⟩ := GM07.exists_compl_disc_in_sphere hsph hB
  obtain ⟨C, hC, hCE, hCbd⟩ :=
    GM07.exists_chord_any hE (hbE ▸ hp) (hbE ▸ hq) hpq
  obtain ⟨A₁, A₂, K₁, K₂, hne, hcomp, hK₁, hK₂, hun, hint, hb₁, hb₂, -⟩ :=
    disc_iArc.{u} E C p q hE hCE hpq hC hCbd
  rw [hbE] at hcomp hCbd
  have hcup := union_eq_of_componentsIn_eq_pair hcomp
  have hA₁m : A₁ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inl rfl
  have hA₂m : A₂ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inr rfl
  have hA₁ : A₁ ⊆ discBd B \ {p, q} := subset_of_mem_componentsIn hA₁m
  have hA₂ : A₂ ⊆ discBd B \ {p, q} := subset_of_mem_componentsIn hA₂m
  have hdA : Disjoint A₁ A₂ :=
    disjoint_of_mem_componentsIn hA₁m hA₂m hne
  have hbB : discBd B ⊆ B := discBd_subset B
  -- points of `E` in `B` lie on `bd B`
  have hEB : E ∩ B = discBd B := by
    rw [hEeq]
    ext x
    refine ⟨fun ⟨h1, h2⟩ => by_contra fun h3 => h1 ⟨h2, h3⟩, fun hx => ⟨fun h => h.2 hx, hbB hx⟩⟩
  -- the arcs miss the chord
  have hAC : ∀ {A : Set Z}, A ⊆ discBd B \ {p, q} → Disjoint A C := by
    intro A hA
    rw [disjoint_left]
    intro x hxA hxC
    have hx := hA hxA
    have : x ∈ C ∩ discBd B := ⟨hxC, hx.1⟩
    rw [hCbd] at this
    exact hx.2 this
  have hdA₁C := hAC hA₁
  have hdA₂C := hAC hA₂
  have hpqC : ({p, q} : Set Z) ⊆ C := by
    rintro x (rfl | rfl)
    · exact hC.left_mem
    · exact hC.right_mem
  have hpqB : ({p, q} : Set Z) ⊆ discBd B := by
    rintro x (rfl | rfl)
    · exact hp
    · exact hq
  -- `C` meets `B` only at its ends
  have hCB : C ∩ B = {p, q} := by
    refine Subset.antisymm ?_ fun x hx => ⟨hpqC hx, hbB (hpqB hx)⟩
    rintro x ⟨hxC, hxB⟩
    rw [← hCbd]
    exact ⟨hxC, hEB ▸ ⟨hCE hxC, hxB⟩⟩
  -- each `Kᵢ` meets `B` in the closure of `Aᵢ`
  have hKB : ∀ {K K' A A' : Set Z}, K ⊆ E → discBd K = A ∪ C → discBd K' = A' ∪ C →
      K ∩ K' = C → A ⊆ discBd B \ {p, q} → A' ⊆ discBd B \ {p, q} → Disjoint A A' →
      A ∪ A' = discBd B \ {p, q} → K ∩ B = A ∪ {p, q} := by
    intro K K' A A' hKE hbK hbK' hKK' hA hA' hdAA' hAA'
    apply Subset.antisymm
    · rintro x ⟨hxK, hxB⟩
      have hxb : x ∈ discBd B := hEB ▸ ⟨hKE hxK, hxB⟩
      by_cases hxpq : x ∈ ({p, q} : Set Z)
      · exact .inr hxpq
      · have hx' : x ∈ A ∪ A' := hAA' ▸ ⟨hxb, hxpq⟩
        rcases hx' with h | h
        · exact .inl h
        · have hxK' : x ∈ K' := discBd_subset K' (hbK' ▸ .inl h)
          have hxC : x ∈ C := hKK' ▸ ⟨hxK, hxK'⟩
          exact absurd hxC (disjoint_left.mp (hAC hA') h)
    · rintro x (hx | hx)
      · exact ⟨discBd_subset K (hbK ▸ .inl hx), hbB (hA hx).1⟩
      · refine ⟨?_, hbB (hpqB hx)⟩
        have : x ∈ C := hpqC hx
        exact (hKK' ▸ this : x ∈ K ∩ K').1
  have hK₁E : K₁ ⊆ E := hun ▸ subset_union_left
  have hK₂E : K₂ ⊆ E := hun ▸ subset_union_right
  have hK₁B := hKB hK₁E hb₁ hb₂ hint hA₁ hA₂ hdA hcup
  have hK₂B := hKB hK₂E hb₂ hb₁ (by rw [inter_comm]; exact hint) hA₂ hA₁ hdA.symm
    (by rw [union_comm]; exact hcup)
  -- the closures of the arcs are lines from `p` to `q`
  have hline : ∀ {A : Set Z}, A ∈ componentsIn (discBd B \ {p, q}) →
      IsLineWithEnds (A ∪ {p, q}) p q := by
    intro A hA
    have h := GM06.isLineWithEnds_closure_component_of_oArc hB.isOArc_discBd hp hq hpq hA
    rwa [GM06.closure_component_eq_union_pair hA h] at h
  -- the covering
  have hcov : K₁ ∪ K₂ ∪ B = univ := by
    rw [hun]
    refine eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ B
    · exact .inr hx
    · exact .inl (hEeq ▸ fun h => hx h.1)
  -- the two unions with `B`
  have hunion : ∀ {K A A' : Set Z}, IsClosedDisc K → A ∈ componentsIn (discBd B \ {p, q}) →
      A' ⊆ discBd B \ {p, q} → Disjoint A A' → A ∪ A' = discBd B \ {p, q} →
      discBd K = A ∪ C → K ∩ B = A ∪ {p, q} →
      IsClosedDisc (B ∪ K) ∧ discBd (B ∪ K) = A' ∪ C := by
    intro K A A' hK hA hA' hdAA' hAA' hbK hKB'
    have hAs := subset_of_mem_componentsIn hA
    obtain ⟨hd, hbd⟩ := disc_union.{u} B K (A ∪ {p, q}) p q hB hK (hline hA)
      (by rw [inter_comm]; exact hKB')
      (union_subset (fun x hx => (hAs hx).1) hpqB)
      (by rw [hbK]; exact union_subset_union_right A hpqC)
    refine ⟨hd, ?_⟩
    rw [hbd, hbK]
    have hdiff : (A ∪ {p, q}) \ {p, q} = A := by
      ext x
      exact ⟨fun h => h.1.resolve_right h.2, fun h => ⟨.inl h, (hAs h).2⟩⟩
    rw [hdiff]
    ext x
    constructor
    · rintro ⟨hx | hx | hx, hxA⟩
      · by_cases hxpq : x ∈ ({p, q} : Set Z)
        · exact .inr (hpqC hxpq)
        · have : x ∈ A ∪ A' := hAA' ▸ ⟨hx, hxpq⟩
          exact .inl (this.resolve_left hxA)
      · exact absurd hx hxA
      · exact .inr hx
    · rintro (hx | hx)
      · exact ⟨.inl (hA' hx).1, disjoint_right.mp hdAA' hx⟩
      · exact ⟨.inr (.inr hx), disjoint_right.mp (hAC hAs) hx⟩
  obtain ⟨hBK₁, hbBK₁⟩ := hunion hK₁ hA₁m hA₂ hdA hcup hb₁ hK₁B
  obtain ⟨hBK₂, hbBK₂⟩ := hunion hK₂ hA₂m hA₁ hdA.symm
    (by rw [union_comm]; exact hcup) hb₂ hK₂B
  exact ⟨A₁, A₂, C, K₁, K₂, hcomp, hne, hC, hCB, hK₁, hK₂, hb₁, hb₂, hint, hcov, hK₁B, hK₂B,
    hBK₁, hbBK₁, hBK₂, hbBK₂⟩

end Theta

section Tube

/-- A line minus its ends is infinite. -/
theorem IsLineWithEnds.infinite_diff_ends {Z : Type u} [TopologicalSpace Z] {C : Set Z} {p q : Z}
    (hC : IsLineWithEnds C p q) : (C \ {p, q}).Infinite := by
  obtain ⟨f, hf0, hf1⟩ := hC
  have hI : (univ \ {(0 : unitInterval), 1}).Infinite := by
    have : Infinite unitInterval := Set.infinite_coe_iff.mpr (Set.Icc_infinite zero_lt_one)
    exact (Set.infinite_univ (α := unitInterval)).sdiff (toFinite _)
  have hinj : Function.Injective (fun t : unitInterval => (f t).1) :=
    Subtype.val_injective.comp f.injective
  refine (hI.image hinj.injOn).mono ?_
  rintro _ ⟨t, ⟨-, ht⟩, rfl⟩
  refine ⟨(f t).2, ?_⟩
  rintro (h | h)
  · exact ht (.inl (f.injective (Subtype.ext (h.trans hf0.symm))))
  · exact ht (.inr (f.injective (Subtype.ext (h.trans hf1.symm))))

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]

/-- **A tube built from a disc.** Let `Γ₀` be a drawing in a closed disc `B` of a
sphere, which meets `bd B` only at vertices, and let `p ≠ q` be two points of `bd B`;
they cut `bd B` into the open arcs `A₁`, `A₂`. For every `m` there are a set `M` of `m`
points outside `B`, and a tube `τ` in a cylinder `Q ⊆ Z`, whose drawing is `Γ₀` with
the points of `M` added as isolated vertices, such that a vertex lies on `F₁` exactly
when it is in `M` or in `A₁ ∪ {p, q}`, and on `F₂` exactly when it is in `M` or in
`A₂ ∪ {p, q}`.

Take the three discs `B`, `K₁`, `K₂` of `exists_theta_discs`, and `M` on the line
`C = K₁ ∩ K₂`. Cut small discs `P₁`, `P₂` out of the interiors of `K₁`, `K₂`
(`exists_nestedCap`). The boundaries of `K₁` and `K₂` are hoops of `Q`, with discs
`K₁`, `B ∪ K₂` and `B ∪ K₁`, `K₂` (`CylinderSphereCap.isHoop_of_discs`). They are
laminar since `K₁ ⊆ B ∪ K₁`, and the region between them is `B ∪ C`. -/
theorem exists_tube_of_disc (hZ : IsClosedSurface Z) (hsph : IsSphere Z) {B : Set Z}
    (hB : IsClosedDisc B) {p q : Z} (hp : p ∈ discBd B) (hq : q ∈ discBd B) (hpq : p ≠ q)
    (Γ₀ : Drawing Z) (hU : Γ₀.U ⊆ B) (hbd : Γ₀.U ∩ discBd B ⊆ Γ₀.V) (m : ℕ) :
    ∃ (A₁ A₂ M Q : Set Z) (hM : M.Finite) (hMU : Disjoint M Γ₀.U)
      (hQ : (GM07.addIsolated Γ₀ M hM hMU).U ⊆ Q) (τ : Tube Q),
      componentsIn (discBd B \ {p, q}) = {A₁, A₂} ∧ M.ncard = m ∧ Disjoint M B ∧
      IsClosed Q ∧ τ.Γ = GM12.drawingInSubspace (GM07.addIsolated Γ₀ M hM hMU) Q hQ ∧
      (∀ x : Q, x.1 ∈ Γ₀.V ∪ M → (x ∈ τ.F₁ ↔ x.1 ∈ M ∪ (A₁ ∪ {p, q}))) ∧
      (∀ x : Q, x.1 ∈ Γ₀.V ∪ M → (x ∈ τ.F₂ ↔ x.1 ∈ M ∪ (A₂ ∪ {p, q}))) := by
  have hman : ∀ x : Z, IsManifoldPoint x := fun x => (hZ.2.2 x).isManifoldPoint
  obtain ⟨A₁, A₂, C, K₁, K₂, hcomp, hne, hC, hCB, hK₁, hK₂, hb₁, hb₂, hint, hcov, hK₁B, hK₂B,
    hBK₁, hbBK₁, hBK₂, hbBK₂⟩ := exists_theta_discs hsph hB hp hq hpq
  have hpqC : ({p, q} : Set Z) ⊆ C := by
    rintro x (rfl | rfl)
    · exact hC.left_mem
    · exact hC.right_mem
  have hCb₁ : C ⊆ discBd K₁ := hb₁ ▸ subset_union_right
  have hCb₂ : C ⊆ discBd K₂ := hb₂ ▸ subset_union_right
  -- the extra points
  obtain ⟨M', hMsub, hMcard⟩ := (IsLineWithEnds.infinite_diff_ends hC).exists_subset_card_eq m
  set M : Set Z := (M' : Set Z) with hMdef
  have hMfin : M.Finite := M'.finite_toSet
  have hMC : M ⊆ C \ {p, q} := hMsub
  have hMB : Disjoint M B := by
    rw [disjoint_left]
    intro x hxM hxB
    have hx := hMC hxM
    have : x ∈ C ∩ B := ⟨hx.1, hxB⟩
    rw [hCB] at this
    exact hx.2 this
  have hMU : Disjoint M Γ₀.U := hMB.mono_right hU
  have hA₁m : A₁ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inl rfl
  have hA₂m : A₂ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inr rfl
  have hA₁bd : A₁ ⊆ discBd B := fun x hx => (subset_of_mem_componentsIn hA₁m hx).1
  have hA₂bd : A₂ ⊆ discBd B := fun x hx => (subset_of_mem_componentsIn hA₂m hx).1
  have hpqbd : ({p, q} : Set Z) ⊆ discBd B := by
    rintro x (rfl | rfl)
    · exact hp
    · exact hq
  -- the interiors of `K₁`, `K₂` miss the rest
  have hK₁Bbd : K₁ ∩ B ⊆ discBd K₁ := by
    rw [hK₁B, hb₁]
    exact union_subset subset_union_left (hpqC.trans subset_union_right)
  have hK₂Bbd : K₂ ∩ B ⊆ discBd K₂ := by
    rw [hK₂B, hb₂]
    exact union_subset subset_union_left (hpqC.trans subset_union_right)
  have hI₁ : Disjoint (discInt K₁) (B ∪ K₂) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨hxK, hxb⟩ := hx
    rcases hx' with hxB | hxK₂
    · exact hxb (hK₁Bbd ⟨hxK, hxB⟩)
    · exact hxb (hCb₁ (hint ▸ ⟨hxK, hxK₂⟩))
  have hI₂ : Disjoint (discInt K₂) (B ∪ K₁) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨hxK, hxb⟩ := hx
    rcases hx' with hxB | hxK₁
    · exact hxb (hK₂Bbd ⟨hxK, hxB⟩)
    · exact hxb (hCb₂ (hint ▸ ⟨hxK₁, hxK⟩))
  -- the small discs
  obtain ⟨x₁, hx₁⟩ := hK₁.nonempty_discInt
  obtain ⟨P₁, hP₁, hP₁K, -⟩ := GM19.exists_disc_around_interior
    (isInteriorPoint_of_mem_discInt hman hK₁ hx₁) (hK₁.isOpen_discInt hman) hx₁
  obtain ⟨x₂, hx₂⟩ := hK₂.nonempty_discInt
  obtain ⟨P₂, hP₂, hP₂K, -⟩ := GM19.exists_disc_around_interior
    (isInteriorPoint_of_mem_discInt hman hK₂ hx₂) (hK₂.isOpen_discInt hman) hx₂
  have hP₂BK₂ : P₂ ⊆ B ∪ K₂ := fun x hx => .inr (discInt_subset K₂ (hP₂K hx))
  have hP₁BK₁ : P₁ ⊆ B ∪ K₁ := fun x hx => .inr (discInt_subset K₁ (hP₁K hx))
  have hdisj : Disjoint P₁ P₂ := (hI₁.mono_left hP₁K).mono_right hP₂BK₂
  set Q := GM12.discComplement ![P₁, P₂] with hQdef
  obtain ⟨hcyl, cap, e, hje, hcD₁, hcD₂⟩ := exists_nestedCap hZ hsph hP₁ hP₂ hdisj
  have hmemQ := GM07.mem_discComplement_iff hZ (![P₁, P₂] : Fin 2 → Set Z)
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i k hik
      fin_cases i <;> fin_cases k
      · exact (hik rfl).elim
      · exact hdisj
      · exact hdisj.symm
      · exact (hik rfl).elim)
  have hQc : IsClosed Q := isClosed_closure
  have hinQ : ∀ x, x ∉ discInt K₁ → x ∉ discInt K₂ → x ∈ Q := by
    intro x h1 h2
    refine (hmemQ x).mpr fun i hi => ?_
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      exact h1 (hP₁K (discInt_subset P₁ hi))
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi
      exact h2 (hP₂K (discInt_subset P₂ hi))
  have hBQ : B ⊆ Q := fun x hx =>
    hinQ x (fun h => disjoint_left.mp hI₁ h (.inl hx)) (fun h => disjoint_left.mp hI₂ h (.inl hx))
  have hsub₁ : discBd K₁ ⊆ Q := fun x hx =>
    hinQ x (fun h => h.2 hx) (fun h => disjoint_left.mp hI₂ h (.inr (discBd_subset K₁ hx)))
  have hsub₂ : discBd K₂ ⊆ Q := fun x hx =>
    hinQ x (fun h => disjoint_left.mp hI₁ h (.inr (discBd_subset K₂ hx))) (fun h => h.2 hx)
  -- the two hoops
  set H₁ : Set Q := Subtype.val ⁻¹' discBd K₁ with hH₁def
  set H₂ : Set Q := Subtype.val ⁻¹' discBd K₂ with hH₂def
  have him₁ : (Subtype.val : Q → Z) '' H₁ = discBd K₁ :=
    image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub₁)
  have him₂ : (Subtype.val : Q → Z) '' H₂ = discBd K₂ :=
    image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub₂)
  have hcov' : ∀ x, x ∈ K₁ ∨ x ∈ K₂ ∨ x ∈ B := by
    intro x
    have hx : x ∈ K₁ ∪ K₂ ∪ B := hcov ▸ mem_univ x
    rcases hx with (h | h) | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  have hcap₁ : K₁ ∩ (B ∪ K₂) = A₁ ∪ C := by
    rw [inter_union_distrib_left, hK₁B, hint, union_assoc,
      union_eq_self_of_subset_left hpqC]
  have hcap₂ : (B ∪ K₁) ∩ K₂ = A₂ ∪ C := by
    rw [union_inter_distrib_right, inter_comm, hK₂B, hint, union_assoc,
      union_eq_self_of_subset_left hpqC]
  obtain ⟨hH₁, hd₁₁, hd₂₁⟩ := cap.isHoop_of_discs hcyl.1 e hje hcD₁ hcD₂
    (GM12.isOArc_subtype_preimage hsub₁ hK₁.isOArc_discBd) hK₁ hBK₂ him₁.symm
    (by rw [hbBK₂, ← hb₁]; exact him₁.symm)
    (eq_univ_of_forall fun x => by
      rcases hcov' x with h | h | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr (.inl h))
    (by rw [hcap₁, ← hb₁]; exact him₁.symm)
    (hP₁K.trans (discInt_subset K₁)) hP₂BK₂
  obtain ⟨hH₂, hd₁₂, hd₂₂⟩ := cap.isHoop_of_discs hcyl.1 e hje hcD₁ hcD₂
    (GM12.isOArc_subtype_preimage hsub₂ hK₂.isOArc_discBd) hBK₁ hK₂
    (by rw [hbBK₁, ← hb₂]; exact him₂.symm) him₂.symm
    (eq_univ_of_forall fun x => by
      rcases hcov' x with h | h | h
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl h))
    (by rw [hcap₂, ← hb₂]; exact him₂.symm)
    hP₁BK₁ (hP₂K.trans (discInt_subset K₂))
  have hle : cap.disc₁ hcyl.1 hH₁ ⊆ cap.disc₁ hcyl.1 hH₂ := by
    rw [hd₁₁, hd₁₂]
    exact image_mono subset_union_right
  have hlam : AreLaminarHoops H₁ H₂ := (cap.areLaminarHoops_iff hcyl hH₁ hH₂).mpr (.inl hle)
  have hbetween := cap.cylinderBetween_eq_of_disc₁_subset hcyl hH₁ hH₂ hle
  -- the drawing
  set Γ := GM07.addIsolated Γ₀ M hMfin hMU with hΓdef
  have hΓU : Γ.U = Γ₀.U ∪ M := rfl
  have hΓV : Γ.V = Γ₀.V ∪ M := rfl
  have hMbd₁ : M ⊆ discBd K₁ := fun x hx => hCb₁ (hMC hx).1
  have hΓQ : Γ.U ⊆ Q := by
    rw [hΓU]
    exact union_subset (hU.trans hBQ) (hMbd₁.trans hsub₁)
  set D := GM12.drawingInSubspace Γ Q hΓQ with hDdef
  have hnormal : ∀ {K A : Set Z}, discBd K = A ∪ C → A ⊆ discBd B →
      ∀ x : Q, x.1 ∈ discBd K → x ∈ D.U → x ∈ D.V := by
    intro K A hbK hA x hxK hxU
    rw [hDdef, GM12.drawingInSubspace_U, mem_preimage, hΓU] at hxU
    rw [hDdef, GM12.drawingInSubspace_V, mem_preimage, hΓV]
    rcases hxU with h | h
    · refine .inl (hbd ⟨h, ?_⟩)
      rw [hbK] at hxK
      rcases hxK with h' | h'
      · exact hA h'
      · have : x.1 ∈ C ∩ B := ⟨h', hU h⟩
        rw [hCB] at this
        exact hpqbd this
    · exact .inr h
  let τ : Tube Q := {
    Γ := D
    F₁ := H₁
    F₂ := H₂
    isCylinder := hcyl
    laminar := hlam
    isNormal_F₁ := fun x hx => hnormal hb₁ hA₁bd x hx.1 hx.2
    isNormal_F₂ := fun x hx => hnormal hb₂ hA₂bd x hx.1 hx.2
    U_subset := by
      rw [hbetween, hd₁₂, hd₂₁]
      intro x hx
      rw [hDdef, GM12.drawingInSubspace_U, mem_preimage, hΓU] at hx
      rw [mem_preimage, hje]
      have hx' : x.1 ∈ B ∪ K₁ ∧ x.1 ∈ B ∪ K₂ := by
        rcases hx with h | h
        · exact ⟨.inl (hU h), .inl (hU h)⟩
        · have hC' : x.1 ∈ K₁ ∩ K₂ := hint ▸ (hMC h).1
          exact ⟨.inr hC'.1, .inr hC'.2⟩
      exact ⟨mem_image_of_mem e hx'.1, mem_image_of_mem e hx'.2⟩ }
  -- which vertices lie on the hoops
  have hside : ∀ {K A : Set Z}, discBd K = A ∪ C → ∀ x : Q, x.1 ∈ Γ₀.V ∪ M →
      (x.1 ∈ discBd K ↔ x.1 ∈ M ∪ (A ∪ {p, q})) := by
    intro K A hbK x hx
    rw [hbK]
    constructor
    · rintro (h | h)
      · exact .inr (.inl h)
      · rcases hx with hV | hM
        · have : x.1 ∈ C ∩ B := ⟨h, hU (Γ₀.V_subset_U hV)⟩
          rw [hCB] at this
          exact .inr (.inr this)
        · exact .inl hM
    · rintro (h | h | h)
      · exact .inr (hMC h).1
      · exact .inl h
      · exact .inr (hpqC h)
  refine ⟨A₁, A₂, M, Q, hMfin, hMU, hΓQ, τ, hcomp, ?_, hMB, hQc, rfl,
    fun x hx => hside hb₁ x hx, fun x hx => hside hb₂ x hx⟩
  rw [hMdef, ncard_coe_finset]
  exact hMcard

/-- The tube of `exists_tube_of_disc` is pinched when the drawing has no vertex on the
boundary of the disc other than `p` and `q`. Both hoops then meet the vertices in the new
isolated vertices and in those of `p`, `q` that are vertices. The reason is that a vertex
in `A₁` or `A₂` would be a vertex on the boundary of the disc other than `p` and `q`. -/
theorem exists_pinched_tube_of_disc (hZ : IsClosedSurface Z) (hsph : IsSphere Z) {B : Set Z}
    (hB : IsClosedDisc B) {p q : Z} (hp : p ∈ discBd B) (hq : q ∈ discBd B) (hpq : p ≠ q)
    (Γ₀ : Drawing Z) (hU : Γ₀.U ⊆ B) (hbd : Γ₀.U ∩ discBd B ⊆ Γ₀.V)
    (hVbd : Γ₀.V ∩ discBd B ⊆ {p, q}) (m : ℕ) :
    ∃ (M Q : Set Z) (hM : M.Finite) (hMU : Disjoint M Γ₀.U)
      (hQ : (GM07.addIsolated Γ₀ M hM hMU).U ⊆ Q) (τ : Tube Q),
      M.ncard = m ∧ Disjoint M B ∧ IsClosed Q ∧
      τ.Γ = GM12.drawingInSubspace (GM07.addIsolated Γ₀ M hM hMU) Q hQ ∧
      τ.F₁ ∩ τ.Γ.V = (Subtype.val : Q → Z) ⁻¹' (M ∪ (Γ₀.V ∩ {p, q})) ∧
      τ.F₂ ∩ τ.Γ.V = (Subtype.val : Q → Z) ⁻¹' (M ∪ (Γ₀.V ∩ {p, q})) := by
  obtain ⟨A₁, A₂, M, Q, hM, hMU, hQ, τ, hcomp, hcard, hMB, hQc, hτ, h₁, h₂⟩ :=
    exists_tube_of_disc hZ hsph hB hp hq hpq Γ₀ hU hbd m
  have hV : τ.Γ.V = (Subtype.val : Q → Z) ⁻¹' (Γ₀.V ∪ M) := by
    rw [hτ, GM12.drawingInSubspace_V]; rfl
  -- the common computation for both hoops
  have key : ∀ (A : Set Z) (F : Set Q), A ∈ componentsIn (discBd B \ {p, q}) →
      (∀ x : Q, x.1 ∈ Γ₀.V ∪ M → (x ∈ F ↔ x.1 ∈ M ∪ (A ∪ {p, q}))) →
      F ∩ τ.Γ.V = (Subtype.val : Q → Z) ⁻¹' (M ∪ (Γ₀.V ∩ {p, q})) := by
    intro A F hA hF
    ext x
    rw [mem_inter_iff, hV, mem_preimage, mem_preimage]
    constructor
    · rintro ⟨hxF, hxV⟩
      rcases (hF x hxV).mp hxF with hxM | hxA | hxpq
      · exact .inl hxM
      · rcases hxV with hx₀ | hxM
        · have hx := subset_of_mem_componentsIn hA hxA
          exact absurd (hVbd ⟨hx₀, hx.1⟩) hx.2
        · exact .inl hxM
      · rcases hxV with hx₀ | hxM
        · exact .inr ⟨hx₀, hxpq⟩
        · exact .inl hxM
    · rintro (hxM | ⟨hx₀, hxpq⟩)
      · exact ⟨(hF x (.inr hxM)).mpr (.inl hxM), .inr hxM⟩
      · exact ⟨(hF x (.inl hx₀)).mpr (.inr (.inr hxpq)), .inl hx₀⟩
  have hA₁ : A₁ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inl rfl
  have hA₂ : A₂ ∈ componentsIn (discBd B \ {p, q}) := by rw [hcomp]; exact .inr rfl
  exact ⟨M, Q, hM, hMU, hQ, τ, hcard, hMB, hQc, hτ, key A₁ τ.F₁ hA₁ h₁, key A₂ τ.F₂ hA₂ h₂⟩

/-- A tube whose drawing is a drawing `Γ` of the larger space, read in a closed subspace,
frames every graft whose graph is isomorphic to the graph of `Γ`, provided the root vertices
are the vertices drawn on the two hoops. -/
theorem isFraming_of_drawingInSubspace {S : Type u} [TopologicalSpace S]
    {α : Type v} {β : Type w} (X : Graft α β) (Γ : Drawing S) {Q : Set S}
    (hQc : IsClosed Q) (hQ : Γ.U ⊆ Q) (τ : Tube Q)
    (hτ : τ.Γ = GM12.drawingInSubspace Γ Q hQ) (i : GraphMinor.Iso X.G Γ.toGraph)
    (hT : ∀ (v : V(X.G)) (y : Q), y.1 = (i.vertexEquiv v).1 →
      (y ∈ τ.F₁ ∪ τ.F₂ ↔ v.1 ∈ X.T)) :
    τ.IsFraming X := by
  have hb : IsGraphBij τ.Γ.toGraph Γ.toGraph (Subtype.val : Q → S)
      (image (Subtype.val : Q → S)) := hτ ▸ isGraphBij_drawingInSubspace Γ hQc hQ
  let i₃ := hb.toIso
  have hinv : ∀ (g : E(Γ.toGraph)) (y z : V(Γ.toGraph)),
      Γ.toGraph.IsLink g.1 y.1 z.1 ↔
        τ.Γ.toGraph.IsLink (i₃.edgeEquiv.symm g).1 (i₃.vertexEquiv.symm y).1
          (i₃.vertexEquiv.symm z).1 := by
    intro g y z
    have h := i₃.isLink_iff (i₃.edgeEquiv.symm g) (i₃.vertexEquiv.symm y)
      (i₃.vertexEquiv.symm z)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let a : GraphMinor.Iso X.G τ.Γ.toGraph :=
    { vertexEquiv := i.vertexEquiv.trans i₃.vertexEquiv.symm
      edgeEquiv := i.edgeEquiv.trans i₃.edgeEquiv.symm
      isLink_iff := fun g y z => (i.isLink_iff g y z).trans (hinv _ _ _) }
  refine ⟨⟨a, fun v => hT v _ ?_⟩⟩
  have h1 : ((i₃.vertexEquiv (i₃.vertexEquiv.symm (i.vertexEquiv v))).1 : S) =
      (i.vertexEquiv v).1 := by rw [Equiv.apply_symm_apply]
  exact h1

/-- Adding isolated vertices to a drawing does not change which edges join which vertices.
The closure of an edge lies in the drawing, so it misses the new vertices. -/
theorem isLink_addIsolated_iff {S : Type u} [TopologicalSpace S] [T1Space S] (Γ : Drawing S)
    (M : Set S) (hM : M.Finite) (hMU : Disjoint M Γ.U) (e : Set S) (x y : S) :
    (GM07.addIsolated Γ M hM hMU).toGraph.IsLink e x y ↔ Γ.toGraph.IsLink e x y := by
  have hE := addIsolated_E Γ M hM hMU
  change e ∈ (GM07.addIsolated Γ M hM hMU).E ∧ x ∈ Γ.V ∪ M ∧ y ∈ Γ.V ∪ M ∧
      closure e ∩ (Γ.V ∪ M) = {x, y} ↔
    e ∈ Γ.E ∧ x ∈ Γ.V ∧ y ∈ Γ.V ∧ closure e ∩ Γ.V = {x, y}
  rw [hE]
  -- for an edge, meeting `Γ.V ∪ M` in the closure is the same as meeting `Γ.V`
  have hcl : ∀ e ∈ Γ.E, closure e ∩ (Γ.V ∪ M) = closure e ∩ Γ.V := by
    intro e he
    have hsub : closure e ⊆ Γ.U :=
      closure_minimal (fun z hz => (he.2.1 hz).1) Γ.isClosed_U
    rw [inter_union_distrib_left]
    have : closure e ∩ M = ∅ := by
      rw [← disjoint_iff_inter_eq_empty]
      exact (hMU.mono_right hsub).symm
    rw [this, union_empty]
  constructor
  · rintro ⟨he, -, -, hxy⟩
    rw [hcl e he] at hxy
    have hx : x ∈ closure e ∩ Γ.V := hxy ▸ (mem_insert x {y})
    have hy : y ∈ closure e ∩ Γ.V := hxy ▸ (mem_insert_of_mem x rfl)
    exact ⟨he, hx.2, hy.2, hxy⟩
  · rintro ⟨he, hx, hy, hxy⟩
    exact ⟨he, .inl hx, .inl hy, (hcl e he).trans hxy⟩

/-- A graph with a set `W` of isolated vertices, whose other part is drawn by `Γ`, is drawn by
`Γ` with as many new isolated vertices. The map sends `W` onto the new vertices by any
bijection `h`, and the other vertices as before. -/
theorem isGraphBij_addIsolated {S : Type u} [TopologicalSpace S] [T1Space S]
    {α : Type v} {β : Type w} {G : Graph α β} {W : Set α} [∀ a, Decidable (a ∈ W)]
    (hWV : W ⊆ V(G)) (hWiso : ∀ e x y, G.IsLink e x y → x ∉ W) (Γ : Drawing S) (M : Set S)
    (hM : M.Finite) (hMU : Disjoint M Γ.U) {f h : α → S} {g : β → Set S}
    (hb : IsGraphBij (G.deleteVerts W) Γ.toGraph f g) (hh : BijOn h W M) :
    IsGraphBij G (GM07.addIsolated Γ M hM hMU).toGraph (W.piecewise h f) g := by
  have hMV : Disjoint M Γ.V := hMU.mono_right Γ.V_subset_U
  have hEdel : E(G.deleteVerts W) = E(G) := by
    ext e
    rw [edgeSet_deleteVerts, mem_ofPred_eq]
    constructor
    · rintro ⟨x, y, hl, -, -⟩
      exact hl.edge_mem
    · intro he
      obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
      exact ⟨x, y, hl, hWiso e x y hl, hWiso e y x hl.symm⟩
  have hoff : ∀ x, x ∉ W → W.piecewise h f x = f x := fun x hx => piecewise_eq_of_notMem _ _ _ hx
  have hon : ∀ x, x ∈ W → W.piecewise h f x = h x := fun x hx => piecewise_eq_of_mem _ _ _ hx
  refine ⟨?_, ?_, ?_⟩
  · have h₁ : BijOn (W.piecewise h f) (V(G) \ W) Γ.V := by
      have := hb.bijV
      rw [vertexSet_deleteVerts] at this
      exact this.congr fun x hx => (hoff x hx.2).symm
    have h₂ : BijOn (W.piecewise h f) W M := hh.congr fun x hx => (hon x hx).symm
    have hinj : InjOn (W.piecewise h f) ((V(G) \ W) ∪ W) := by
      rw [injOn_union disjoint_sdiff_left]
      refine ⟨h₁.injOn, h₂.injOn, fun x hx y hy hxy => ?_⟩
      have hxV : W.piecewise h f x ∈ Γ.V := h₁.mapsTo hx
      have hyM : W.piecewise h f y ∈ M := h₂.mapsTo hy
      exact disjoint_left.mp hMV hyM (hxy ▸ hxV)
    have := h₁.union h₂ hinj
    rwa [sdiff_union_of_subset hWV] at this
  · have := hb.bijE
    rw [hEdel] at this
    change BijOn g E(G) (GM07.addIsolated Γ M hM hMU).E
    rw [addIsolated_E]
    exact this
  · intro e he x hx y hy
    rw [isLink_addIsolated_iff]
    have hed : e ∈ E(G.deleteVerts W) := hEdel ▸ he
    have hmem : ∀ z, z ∈ V(G) → z ∉ W → z ∈ V(G.deleteVerts W) := fun z hz hzW => by
      rw [vertexSet_deleteVerts]; exact ⟨hz, hzW⟩
    constructor
    · intro hl
      have hxW := hWiso e x y hl
      have hyW := hWiso e y x hl.symm
      rw [hoff x hxW, hoff y hyW]
      exact (hb.isLink e hed x (hmem x hx hxW) y (hmem y hy hyW)).mp
        ((deleteVerts_isLink G W).mpr ⟨hl, hxW, hyW⟩)
    · intro hl
      have hnot : ∀ z, W.piecewise h f z ∈ Γ.V → z ∉ W := fun z hz hzW =>
        disjoint_left.mp hMV (hon z hzW ▸ hh.mapsTo hzW) hz
      have hxW := hnot x hl.left_mem
      have hyW := hnot y hl.right_mem
      rw [hoff x hxW, hoff y hyW] at hl
      exact ((deleteVerts_isLink G W).mp
        ((hb.isLink e hed x (hmem x hx hxW) y (hmem y hy hyW)).mpr hl)).1

end Tube

section Lens

variable {Z : Type} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]

/-- A lens graft has printed width more than its index. Let `B` be a disc of a sphere with
two points `p`, `q` on its boundary. Suppose the graph of `X`, without a set `W` of isolated
vertices, is drawn in `B` with no vertex on the boundary other than `p` and `q`. Suppose the
roots are `W` and the vertices drawn at `p` or `q`. Then `X` is tubular and its printed width
is at least `|T| + 1`.

The framing is `exists_pinched_tube_of_disc`, with the vertices of `W` drawn as the new
isolated vertices. Both hoops meet the vertices exactly in the roots, so
`Tube.printedWidth_ge_of_pinched` applies. -/
theorem le_tubularPrintedWidth_of_disc (hZ : IsClosedSurface Z) (hsph : IsSphere Z)
    {B : Set Z} (hB : IsClosedDisc B) {p q : Z} (hp : p ∈ discBd B) (hq : q ∈ discBd B)
    (hpq : p ≠ q) {α : Type v} {β : Type w} (X : Graft α β) {W : Set α}
    (hWV : W ⊆ V(X.G)) (hWiso : ∀ e x y, X.G.IsLink e x y → x ∉ W)
    (Γ₀ : Drawing Z) (hU : Γ₀.U ⊆ B) (hbd : Γ₀.U ∩ discBd B ⊆ Γ₀.V)
    (hVbd : Γ₀.V ∩ discBd B ⊆ {p, q}) {f : α → Z} {g : β → Set Z}
    (hb : IsGraphBij (X.G.deleteVerts W) Γ₀.toGraph f g)
    (hT : ∀ v ∈ V(X.G), v ∈ X.T ↔ v ∈ W ∨ f v ∈ ({p, q} : Set Z)) :
    IsTubularGraft X ∧ ((X.T.ncard + 1 : ℕ) : ℕ∞) ≤ tubularPrintedWidth X := by
  classical
  have : Nonempty Z := ⟨p⟩
  obtain ⟨M, Q, hM, hMU, hQ, τ, hcard, -, hQc, hτ, h₁, h₂⟩ :=
    exists_pinched_tube_of_disc hZ hsph hB hp hq hpq Γ₀ hU hbd hVbd W.ncard
  have hWfin : W.Finite := X.finite_G.1.subset hWV
  obtain ⟨h, hh⟩ := hWfin.exists_bijOn_of_encard_eq (t := M)
    (by rw [← hWfin.cast_ncard_eq, ← hM.cast_ncard_eq, hcard])
  have hgb := isGraphBij_addIsolated hWV hWiso Γ₀ M hM hMU hb hh
  set φ := W.piecewise h f with hφ
  have hMV : Disjoint M Γ₀.V := hMU.mono_right Γ₀.V_subset_U
  -- the image of the roots
  set P : Set Z := M ∪ (Γ₀.V ∩ {p, q}) with hPdef
  have hroot : ∀ v ∈ V(X.G), φ v ∈ P ↔ v ∈ X.T := by
    intro v hv
    rw [hT v hv]
    by_cases hvW : v ∈ W
    · rw [hφ, piecewise_eq_of_mem _ _ _ hvW]
      exact ⟨fun _ => .inl hvW, fun _ => .inl (hh.mapsTo hvW)⟩
    · rw [hφ, piecewise_eq_of_notMem _ _ _ hvW]
      have hfv : f v ∈ Γ₀.V := hb.bijV.mapsTo (by rw [vertexSet_deleteVerts]; exact ⟨hv, hvW⟩)
      constructor
      · rintro (hM' | ⟨-, hpq'⟩)
        · exact absurd hfv (disjoint_left.mp hMV hM')
        · exact .inr hpq'
      · rintro (h' | hpq')
        · exact absurd h' hvW
        · exact .inr ⟨hfv, hpq'⟩
  -- the framing
  have hV : τ.Γ.V = (Subtype.val : Q → Z) ⁻¹' (Γ₀.V ∪ M) := by
    rw [hτ, GM12.drawingInSubspace_V]; rfl
  have hfr : τ.IsFraming X := by
    refine isFraming_of_drawingInSubspace X _ hQc hQ τ hτ hgb.toIso fun v y hy => ?_
    have hy' : y.1 = φ v.1 := hy
    have hyV : y ∈ τ.Γ.V := by
      rw [hV, mem_preimage, hy']
      exact hgb.bijV.mapsTo v.2
    have hFV : y ∈ τ.F₁ ∪ τ.F₂ ↔ y.1 ∈ P := by
      constructor
      · rintro (hy₁ | hy₂)
        · have : y ∈ τ.F₁ ∩ τ.Γ.V := ⟨hy₁, hyV⟩
          rw [h₁] at this
          exact this
        · have : y ∈ τ.F₂ ∩ τ.Γ.V := ⟨hy₂, hyV⟩
          rw [h₂] at this
          exact this
      · intro hyP
        have : y ∈ τ.F₁ ∩ τ.Γ.V := by rw [h₁]; exact hyP
        exact .inl this.1
    rw [hFV, hy']
    exact hroot v.1 v.2
  refine ⟨IsTubularGraft.of_framing hfr, ?_⟩
  -- count the roots
  have himg : φ '' X.T = P := by
    ext z
    constructor
    · rintro ⟨v, hvT, rfl⟩
      exact (hroot v (X.T_subset hvT)).mpr hvT
    · intro hz
      have hzV : z ∈ Γ₀.V ∪ M := by
        rcases hz with hzM | hzV
        · exact .inr hzM
        · exact .inl hzV.1
      obtain ⟨v, hv, rfl⟩ := hgb.bijV.surjOn hzV
      exact ⟨v, (hroot v hv).mp hz, rfl⟩
  have hTcard : X.T.ncard = P.ncard := by
    rw [← himg, (hgb.bijV.injOn.mono X.T_subset).ncard_image]
  have hPQ : P ⊆ range (Subtype.val : Q → Z) := by
    rw [Subtype.range_coe]
    intro z hz
    apply hQ
    rcases hz with hzM | hzV
    · exact .inr hzM
    · exact .inl (Γ₀.V_subset_U hzV.1)
  have hFcard : (τ.F₁ ∩ τ.Γ.V).ncard = X.T.ncard := by
    rw [h₁, ncard_preimage_of_injective_subset_range Subtype.val_injective hPQ, hTcard]
  calc ((X.T.ncard + 1 : ℕ) : ℕ∞) = (((τ.F₁ ∩ τ.Γ.V).ncard + 1 : ℕ) : ℕ∞) := by rw [hFcard]
    _ ≤ τ.printedWidth := τ.printedWidth_ge_of_pinched (h₁.trans h₂.symm)
    _ ≤ tubularPrintedWidth X := le_sSup ⟨Q, inferInstance, τ, hfr, rfl⟩

end Lens

end GraphMinor.GM08
