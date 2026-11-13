module

public import GraphMinor.GM21.Section6CutPieceSystem
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6SidePieces

/-!
# Graph Minors XXI, (6.3), claim (2): a system of pieces in `Σ`

Claim (2) of the proof of (6.3) (page 28 of the preprint) cuts `Σ` along a line `F` with ends
`a ∈ F_1*`, `b ∈ F_2*` and splits the supports at `a` and at `b`: "let $I_i \subseteq F_1^*$ be the
support with ends $u_1, a$. For each $v \in V(\mu(a))$, let $\delta_i(v)$ be the set of edges of
$\mu(I_i)$ incident with $v$ $(i = 1, 2)$. By splitting $v$ according to $\delta_1(v), \delta_2(v)$
…". The print's $u_1$ is a misprint for $u_i$ (see the correction to the proof of (6.3) in
`corrections/GM21.md`). This file
states, in `Σ` alone, what a list of pieces of the supports must satisfy (`IsPieceSystem`), and
proves that such a list gives the presentation of the split graph in the cut surface
(`isPresentation_of_system`).

* `IsPieceSystem`: the pieces are supports inside the old supports, meeting only in `a` or `b`; the
  two pieces through `a` are on the two sides at `a` (and the same at `b`); the pieces of `F_j*` hold
  its vertices and spaces; the edges of `μ(P_i)` lie in `μ(A₊)` exactly when `P_i` is on the plus
  side at `a` (and the same at `b`); and the copies of the graphs `μ(P_i)` are disjoint and cover the
  copies of the vertices of `μ(a)` and `μ(b)`.
* `exists_sides_of_system`: the points `a₋, a₊` over `a` can be named so that the lift of each piece
  meets them only in the point on its side.
* `isPresentation_of_system`: the presentation.
* `IsPieceSystem.comp_equiv`: a system indexed by any finite type gives one indexed by `Fin r₂`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

/-! ## Copies in the twice split graph -/

/-- Two copies of `v` agree when their sides agree wherever `v` is split. -/
theorem nm2_eq_of_sides {Xa : Set α} {Xb : Set (α ⊕ α ⊕ α)} {c c' : Bool × Bool} {v : α}
    (h1 : v ∈ Xa → c.1 = c'.1) (h2 : splitName Xa c.1 v ∈ Xb → c.2 = c'.2) :
    nm2 Xa Xb c v = nm2 Xa Xb c' v := by
  have e1 : nm2 Xa Xb c v = nm2 Xa Xb (c.1, c'.2) v := by
    by_cases hb : splitName Xa c.1 v ∈ Xb
    · congr 1
      exact Prod.ext rfl (h2 hb)
    · exact nm2_eq_of_notMem_right (c := c) (c' := (c.1, c'.2)) rfl hb
  rw [e1]
  by_cases ha : v ∈ Xa
  · congr 1
    exact Prod.ext (h1 ha) rfl
  · exact nm2_eq_of_notMem_left (c := (c.1, c'.2)) (c' := c') rfl ha

omit [TopologicalSpace S] in
/-- The first copies of `v` that are split in the second step. -/
theorem splitName_mem_splitB_iff' {μ : BoundaryUnit S → Hypergraph α β} {cb d : Bool} {v : α} :
    splitName (μ (.vertex a)).vertexSet d v ∈ splitB μ a b cb ↔
      v ∈ (μ (.vertex b)).vertexSet ∧ (v ∈ (μ (.vertex a)).vertexSet → d = cb) := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' := eq_of_splitName_eq hwv
    subst hwv'
    refine ⟨hw, fun hva => ?_⟩
    by_contra hd
    exact notMem_of_splitName_eq (Ne.symm hd) hwv hva
  · rintro ⟨hv, hva⟩
    refine ⟨v, hv, ?_⟩
    by_cases h : v ∈ (μ (.vertex a)).vertexSet
    · rw [hva h]
    · rw [splitName_of_notMem h, splitName_of_notMem h]

/-! ## Systems of pieces -/

/-- **A system of pieces** of the supports `F_j*` for claim (2), with sides `col i` at `a` and at
`b`. `Apf` and `Bpf` are the parts of the supports on the plus sides at `a` and at `b`, and `cb` is
the first side of the copies of `V(μ(b))` that are split in the second step. -/
structure IsPieceSystem {r : ℕ} {ι : Type*} (G : Hypergraph α β) (Γ : Drawing S)
    (Γ_sub : Hypergraph α β) (μ : BoundaryUnit S → Hypergraph α β) (F_star : Fin r → Set S)
    (a b : S) (cb : Bool) (Apf Bpf : Set S) (P : ι → Set S) (τ : ι → Fin r)
    (col : ι → Bool × Bool) : Prop where
  sup : ∀ i, ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ {a, b} ⊆ {u, w}
  sub : ∀ i, P i ⊆ F_star (τ i)
  inter : ∀ i i', i ≠ i' → P i ∩ P i' ⊆ {a, b}
  notBoth : ∀ i i', i ≠ i' → a ∈ P i → a ∈ P i' → b ∈ P i → b ∉ P i'
  diffA : ∀ i i', i ≠ i' → a ∈ P i → a ∈ P i' → (col i).1 ≠ (col i').1
  diffB : ∀ i i', i ≠ i' → b ∈ P i → b ∈ P i' → (col i).2 ≠ (col i').2
  bothA : ∀ c, ∃ i, a ∈ P i ∧ (col i).1 = c
  bothB : ∀ c, ∃ i, b ∈ P i ∧ (col i).2 = c
  coverV : ∀ j, ∀ u ∈ Γ.V ∩ F_star j, ∃ i, τ i = j ∧ u ∈ P i
  coverS : ∀ j, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j → ∃ i, τ i = j ∧ s ⊆ P i
  colA : ∀ i, ∀ e ∈ (supportGraph G Γ μ (P i)).edgeSet,
    e ∈ (supportGraph G Γ μ Apf).edgeSet ↔ (col i).1 = true
  colB : ∀ i, ∀ e ∈ (supportGraph G Γ μ (P i)).edgeSet,
    e ∈ (supportGraph G Γ μ Bpf).edgeSet ↔ (col i).2 = true
  cover : ∀ c : Bool × Bool, ∀ v ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet,
    v ∉ Γ_sub.vertexSet → ∃ i, v ∈ (supportGraph G Γ μ (P i)).vertexSet ∧
      nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i) v =
        nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) c v
  disj : ∀ i i', i ≠ i' → ∀ v, v ∈ (supportGraph G Γ μ (P i)).vertexSet →
    v ∈ (supportGraph G Γ μ (P i')).vertexSet →
    nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i) v ≠
      nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i') v

/-- A system of pieces read through a bijection of the index sets. -/
theorem IsPieceSystem.comp_equiv {r : ℕ} {ι κ : Type*} {G : Hypergraph α β} {Γ : Drawing S}
    {Γ_sub : Hypergraph α β} {μ : BoundaryUnit S → Hypergraph α β} {F_star : Fin r → Set S}
    {cb : Bool} {Apf Bpf : Set S} {P : ι → Set S} {τ : ι → Fin r} {col : ι → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) (e : κ ≃ ι) :
    IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf (P ∘ e) (τ ∘ e) (col ∘ e) where
  sup i := hsys.sup (e i)
  sub i := hsys.sub (e i)
  inter i i' h := hsys.inter (e i) (e i') (e.injective.ne h)
  notBoth i i' h := hsys.notBoth (e i) (e i') (e.injective.ne h)
  diffA i i' h := hsys.diffA (e i) (e i') (e.injective.ne h)
  diffB i i' h := hsys.diffB (e i) (e i') (e.injective.ne h)
  bothA c := by
    obtain ⟨i, hi, hc⟩ := hsys.bothA c
    exact ⟨e.symm i, by simpa using hi, by simpa using hc⟩
  bothB c := by
    obtain ⟨i, hi, hc⟩ := hsys.bothB c
    exact ⟨e.symm i, by simpa using hi, by simpa using hc⟩
  coverV j u hu := by
    obtain ⟨i, hi, hc⟩ := hsys.coverV j u hu
    exact ⟨e.symm i, by simpa using hi, by simpa using hc⟩
  coverS j s hs hsj := by
    obtain ⟨i, hi, hc⟩ := hsys.coverS j s hs hsj
    exact ⟨e.symm i, by simpa using hi, by simpa using hc⟩
  colA i := hsys.colA (e i)
  colB i := hsys.colB (e i)
  cover c v hv hvΓ := by
    obtain ⟨i, hi, hc⟩ := hsys.cover c v hv hvΓ
    exact ⟨e.symm i, by simpa using hi, by simpa using hc⟩
  disj i i' h := hsys.disj (e i) (e i') (e.injective.ne h)

/-- **The two sides at an end `x` of `F`.** If exactly two pieces hold `x`, on the two sides
`sel`, and they meet only in `x`, then the points over `x` can be named so that the lift of each
piece meets them only in the point on its side. -/
theorem exists_sides_gen {x y : S} (hS : IsSurface S) (h : IsLineCut ψ F x y X Y a₁ b₁ a₂ b₂)
    (hF : IsProperLineInSurface F x y) {Γ : Drawing S} {ι : Type*} {P : ι → Set S}
    (sel : ι → Bool) (hsup : ∀ i, ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ F ⊆ {u, w})
    (hboth : ∀ c, ∃ i, x ∈ P i ∧ sel i = c)
    (hdiff : ∀ i i', i ≠ i' → x ∈ P i → x ∈ P i' → sel i ≠ sel i')
    (hint : ∀ i i', i ≠ i' → x ∈ P i → x ∈ P i' → P i ∩ P i' ⊆ {x}) :
    ∃ m p : S', ψ ⁻¹' {x} = {m, p} ∧ m ≠ p ∧
      ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {x} ⊆ {cond (sel i) p m} := by
  have hxF : x ∈ F := hF.1.left_mem
  -- A piece through `x` has `x` as an end.
  have hends : ∀ i, x ∈ P i → ∃ u', SupportHasEnds Γ (P i) x u' ∧ P i ∩ F ⊆ {x, u'} := by
    intro i hxi
    obtain ⟨u, w, hs, hPF⟩ := hsup i
    rcases hPF ⟨hxi, hxF⟩ with hxu | hxw
    · subst hxu
      exact ⟨w, hs, hPF⟩
    · subst hxw
      exact ⟨u, supportHasEnds_swap hs, by rw [pair_comm]; exact hPF⟩
  obtain ⟨i₁, hx₁, hc₁⟩ := hboth false
  obtain ⟨i₂, hx₂, hc₂⟩ := hboth true
  have h12 : i₁ ≠ i₂ := fun he => by rw [he, hc₂] at hc₁; exact Bool.noConfusion hc₁
  obtain ⟨u₁, hs₁, hF₁⟩ := hends i₁ hx₁
  obtain ⟨u₂, hs₂, hF₂⟩ := hends i₂ hx₂
  have hint' : P i₁ ∩ P i₂ = {x} :=
    Subset.antisymm (hint i₁ i₂ h12 hx₁ hx₂) (singleton_subset_iff.mpr ⟨hx₁, hx₂⟩)
  obtain ⟨m, p, hmp, hne, hm, hp⟩ := h.exists_sides_at hS hF hs₁ hs₂ hF₁ hF₂ hint'
  refine ⟨m, p, hmp, hne, fun i => ?_⟩
  by_cases hxi : x ∈ P i
  · by_cases hi₁ : i = i₁
    · subst hi₁
      rw [hc₁]
      exact hm
    by_cases hi₂ : i = i₂
    · subst hi₂
      rw [hc₂]
      exact hp
    exfalso
    have d1 := hdiff i i₁ hi₁ hxi hx₁
    have d2 := hdiff i i₂ hi₂ hxi hx₂
    rw [hc₁] at d1
    rw [hc₂] at d2
    cases hs : sel i
    · exact d1 hs
    · exact d2 hs
  · rintro z ⟨hz, hzx⟩
    exfalso
    obtain ⟨u, w, hs, hPF⟩ := hsup i
    have hzP : ψ z ∈ P i := (h.lift_piece hS hs hPF).2.1 hz
    rw [show ψ z = x from hzx] at hzP
    exact hxi hzP

section presentation

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- An edge of `μ(P)` is in `cutEdges … A p` exactly when it is an edge of `μ(A)`: it is not an
edge of `Γ`. -/
theorem mem_cutEdges_iff_of_mem (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {j : Fin r}
    {P A : Set S} (hPj : P ⊆ F_star j) {e : β} (he : e ∈ (supportGraph G Γ μ P).edgeSet)
    (p : S') : e ∈ cutEdges G Γ μ ψ ιE A p ↔ e ∈ (supportGraph G Γ μ A).edgeSet := by
  unfold cutEdges
  refine ⟨?_, Or.inl⟩
  rintro (h' | ⟨e', he', rfl⟩)
  · exact h'
  · exact absurd (hP.ιE_image ▸ mem_image_of_mem ιE he'.1)
      (disjoint_left.mp (GM21.supportGraph_edgeSet_disjoint hP j hPj) he)

/-- The pieces of a system meet `F` only in their ends. -/
theorem IsPieceSystem.inter_line (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hF : IsProperLineInSurface F a b) {ι : Type*} {cb : Bool} {Apf Bpf : Set S} {P : ι → Set S}
    {τ : ι → Fin r} {col : ι → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) (i : ι) :
    ∃ u w, SupportHasEnds Γ (P i) u w ∧ P i ∩ F ⊆ {u, w} := by
  obtain ⟨u, w, hsup, hab⟩ := hsys.sup i
  refine ⟨u, w, hsup, fun x hx => hab ⟨hx.1, ?_⟩⟩
  have hx' : x ∈ F ∩ bd S := ⟨hx.2, GM21.Supports.subset_bd_of_isSupportOfDrawing
    (hP.supports_isSupport (τ i)) (hsys.sub i hx.1)⟩
  rw [hF.inter_bd_eq] at hx'
  exact hx'

/-- **The points over `a` and over `b` named by sides** for a system of pieces. -/
theorem exists_sides_of_system (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b) {ι : Type*}
    {cb : Bool} {Apf Bpf : Set S} {P : ι → Set S} {τ : ι → Fin r} {col : ι → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col) :
    ∃ am ap bm bp : S', ψ ⁻¹' {a} = {am, ap} ∧ am ≠ ap ∧ ψ ⁻¹' {b} = {bm, bp} ∧ bm ≠ bp ∧
      (∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {a} ⊆ {cond (col i).1 ap am}) ∧
      (∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {b} ⊆ {cond (col i).2 bp bm}) := by
  have hS := hP.is_surface
  have hsup := hsys.inter_line hP hF
  obtain ⟨am, ap, hpa, hamp, hA⟩ := exists_sides_gen hS h hF (fun i => (col i).1) hsup
    hsys.bothA hsys.diffA fun i i' hii hai hai' z hz => by
      rcases hsys.inter i i' hii hz with hza | hzb
      · exact hza
      · subst hzb
        exact absurd hz.2 (hsys.notBoth i i' hii hai hai' hz.1)
  obtain ⟨bm, bp, hpb, hbmp, hB⟩ := exists_sides_gen hS h.symm (IsProperLineInSurface.swap hF) (fun i => (col i).2) hsup
    hsys.bothB hsys.diffB fun i i' hii hbi hbi' z hz => by
      rcases hsys.inter i i' hii hz with hza | hzb
      · subst hza
        exact absurd hbi' (hsys.notBoth i i' hii hz.1 hz.2 hbi)
      · exact hzb
  exact ⟨am, ap, bm, bp, hpa, hamp, hpb, hbmp, hA, hB⟩

open Classical in
/-- The copy of a vertex of `Γ_sub` on any sides is the name of a vertex of `Γ'`. -/
theorem nm2_ιV_mem_image_cutName (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) {Γ' : Drawing S'} (hV : Γ'.V = ψ ⁻¹' Γ.V) {am ap bm bp : S'}
    (hpa : ψ ⁻¹' {a} = {am, ap}) (hamp : am ≠ ap) (hpb : ψ ⁻¹' {b} = {bm, bp}) (hbmp : bm ≠ bp)
    (cb : Bool) (c : Bool × Bool) {u : S} (hu : u ∈ Γ.V) :
    nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) c (ιV u) ∈
      cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V := by
  have hab := hF.ne
  have key : ∀ x, ψ x = u → (ψ x = a → c.1 = decide (x = ap)) →
      (ψ x = b → c.2 = decide (x = bp)) →
      nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) c (ιV u) ∈
        cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V := by
    intro x hx h1 h2
    have hxV : x ∈ Γ'.V := by rw [hV]; show ψ x ∈ Γ.V; rw [hx]; exact hu
    refine ⟨x, hxV, ?_⟩
    rw [cutName_eq hP hF habV hV cb hxV c h1 h2, hx]
  have hψpa : ψ (cond c.1 ap am) = a := by
    cases c.1
    · exact show am ∈ ψ ⁻¹' {a} from hpa ▸ Or.inl rfl
    · exact show ap ∈ ψ ⁻¹' {a} from hpa ▸ Or.inr rfl
  have hψpb : ψ (cond c.2 bp bm) = b := by
    cases c.2
    · exact show bm ∈ ψ ⁻¹' {b} from hpb ▸ Or.inl rfl
    · exact show bp ∈ ψ ⁻¹' {b} from hpb ▸ Or.inr rfl
  by_cases hua : u = a
  · subst hua
    exact key _ hψpa (fun _ => decide_cond_eq hamp _) fun hb => absurd (hψpa.symm.trans hb) hab
  by_cases hub : u = b
  · subst hub
    exact key _ hψpb (fun ha => absurd (hψpb.symm.trans ha) (Ne.symm hab))
      (fun _ => decide_cond_eq hbmp _)
  obtain ⟨x, hx⟩ := h.cutting.2.1 u
  exact key x hx (fun ha => absurd (hx.symm.trans ha) hua) fun hb => absurd (hx.symm.trans hb) hub

open Classical in
/-- **The presentation of claim (2) from a system of pieces.** -/
theorem isPresentation_of_system (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) [ConnectedSpace S'] {Γ' : Drawing S'}
    (hU : Γ'.U = ψ ⁻¹' Γ.U) (hV : Γ'.V = ψ ⁻¹' Γ.V)
    (hE : ∀ e' ∈ Γ'.E, ∃ e ∈ Γ.E, e' = ψ ⁻¹' e)
    (hΓ' : Γ'.IsProper) (hcuff : ∀ C ∈ cuffs S', 2 ≤ (Γ'.V ∩ C).ncard) {am ap bm bp : S'}
    (hpa : ψ ⁻¹' {a} = {am, ap}) (hamp : am ≠ ap) (hpb : ψ ⁻¹' {b} = {bm, bp}) (hbmp : bm ≠ bp)
    {cb : Bool} {Apf Bpf : Set S}
    (hlink : ∀ e ∈ Γ.E, ∃ u w, u ≠ w ∧ closure e ∩ Γ.V = {u, w})
    (hApf : ∃ j, Apf ⊆ F_star j) (hBpf : ∃ j, Bpf ⊆ F_star j) {r₂ : ℕ} {P : Fin r₂ → Set S}
    {τ : Fin r₂ → Fin r} {col : Fin r₂ → Bool × Bool}
    (hsys : IsPieceSystem G Γ Γ_sub μ F_star a b cb Apf Bpf P τ col)
    (hsideA : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {a} ⊆ {cond (col i).1 ap am})
    (hsideB : ∀ i, lift ψ F (P i) ∩ ψ ⁻¹' {b} ⊆ {cond (col i).2 bp bm}) :
    IsPresentation (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap)
        (splitB μ a b cb) (cutEdges G Γ μ ψ ιE Bpf bp)) Γ'
      (subOn (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap)
        (splitB μ a b cb) (cutEdges G Γ μ ψ ιE Bpf bp))
        (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V) (ιE '' Γ.E))
      (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp)
      (fun e' => ιE (ψ '' e')) r₂
      (fun i => cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm))
      (fun i => isoImage (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (col i)) id
        (supportGraph G Γ μ (P i)))
      (fun x => isoImage (nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb)
          (pieceColor (fun i => cutPiece ψ F (P i) (cond (col i).1 ap am) (cond (col i).2 bp bm))
            col x)) id (μ (unitMap ψ x))) (q ∘ τ) := by
  refine isPresentation_of_pieces hP h hF habV hFU hU hV hE hΓ' hcuff hpa hamp hpb hbmp cb hlink
    hApf hBpf (hsys.inter_line hP hF) hsys.sub hsys.inter hsideA hsideB hsys.diffA hsys.diffB
    hsys.bothA hsys.bothB ?_ ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered hv)
    obtain ⟨i, -, hi⟩ := hsys.coverV j v ⟨hv.1, hj⟩
    exact ⟨i, hi⟩
  · intro j s hs hsj
    obtain ⟨i, -, hi⟩ := hsys.coverS j s hs hsj
    exact ⟨i, hi⟩
  · intro i e he
    exact ⟨(mem_cutEdges_iff_of_mem hP (hsys.sub i) he ap).trans (hsys.colA i e he),
      (mem_cutEdges_iff_of_mem hP (hsys.sub i) he bp).trans (hsys.colB i e he)⟩
  · intro w hw
    obtain ⟨c, v, hvG, rfl⟩ := exists_nm2_of_mem hw
    by_cases hvΓ : v ∈ Γ_sub.vertexSet
    · rw [← hP.ιV_image] at hvΓ
      obtain ⟨u, hu, rfl⟩ := hvΓ
      exact Or.inl (nm2_ιV_mem_image_cutName hP h hF habV hV hpa hamp hpb hbmp cb c hu)
    right
    by_cases hvab : v ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet
    · obtain ⟨i, hi, hc⟩ := hsys.cover c v hvab hvΓ
      exact mem_iUnion.mpr ⟨i, v, hi, hc⟩
    have hvH : v ∈ ⋃ j, (H j).vertexSet := by
      rw [hP.v1_union_V] at hvG
      exact hvG.resolve_right hvΓ
    obtain ⟨j, hj⟩ := mem_iUnion.mp hvH
    rw [hP.v2_eq j] at hj
    obtain ⟨i, hi⟩ := mem_iUnion.mp
      ((Side.supportGraph_subset_iUnion (hsys.coverV j) (hsys.coverS j)).1 hj)
    refine mem_iUnion.mpr ⟨i, v, hi, ?_⟩
    exact nm2_eq_of_notMem (fun h' => hvab (Or.inl h'))
      fun d hd => hvab (Or.inr (splitName_mem_splitB_iff'.mp hd).1)
  · intro i i' hii
    refine disjoint_left.mpr ?_
    rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
    have hwv := eq_of_nm2_eq hvw
    subst hwv
    exact hsys.disj i i' hii w hv hw hvw.symm

end presentation

end CutLine
end GM21
end GraphMinor
