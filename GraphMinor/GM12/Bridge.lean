module

public import GraphMinor.GM15.Cited
public import GraphMinor.GM12.Cited
public import GraphMinor.GM16.Cited
public import GraphMinor.GM19.Cited
public import GraphMinor.GM12.Section4Theorem43
public import GraphMinor.GM12.Section4Theorem44
public import GraphMinor.GM12.Section4Theorem45
import GraphMinor.GM12.Section3Theorem
import GraphMinor.GM11.Section6
import GraphMinor.GM12.Section4
import GraphMinor.GM12.Section4Monotone
import GraphMinor.GM12.Section4DrawnGraph
import GraphMinor.GM12.Section4MetricExistence
import GraphMinor.GM12.Section4SpanControl
import GraphMinor.Minor.Basic
import Mathlib.Data.Fintype.EquivFin

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# Graph Minors XII results in later papers

This file matches XII's proved results to the statements used by later
papers. No other XII file imports it.
-/

public section

namespace GraphMinor.GM12

universe u v w

/-- Graph Minors XII, (3.2), pages 245--248, in the exact form used
by XIX. The boundary conventions agree for each prescribed closed disc. -/
theorem gm19_theorem32
    : GM19.GM12Theorem32Statement.{u} := by
  intro S _ _ hS hConn t z
  let : T2Space S := hS.2.1
  let : ConnectedSpace S := hConn
  obtain ⟨η, hηpos, hmain⟩ := theorem_3_2_proof hS t z
  refine ⟨η, hηpos, ?_⟩
  intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeasible horder hm hsep hfree
  have hb : ∀ i, Surface.subBd (Δ i) = Surface.discBd (Δ i) := fun i =>
    (GM11.subBd_eq_frontier (Δ i)).trans (GM11.IsClosedDisc.frontier_eq_discBd hS (hΔ i).1)
  have hZeq : (⋃ i, Γ.V ∩ Surface.subBd (Δ i)) = discBoundaryVertices Γ Δ := by
    simp_rw [hb]
    rfl
  have hΔ' : ∀ i, Surface.IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ Surface.discBd (Δ i) := by
    intro i
    exact ⟨(hΔ i).1, by simpa only [hb i] using (hΔ i).2⟩
  have hfree' : ∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ Surface.discBd (Δ i)) := by
    intro i
    simpa only [hb i] using hfree i
  have hresult := hmain Δ Γ θ T d p Zs hΔ' hdis (by simpa only [hZeq] using hcount)
    (hcover.trans hZeq) hdisZ hfeasible horder hm hsep hfree'
  rwa [← hZeq] at hresult

/-- Graph Minors XII, (4.1), page 248, in the exact form used by XV. -/
theorem gm15_theorem41 : GM15.GM12Theorem41Statement.{u} := by
  exact @theorem_4_1_proof

open Set Graph Hypergraph

private theorem clique_inc {p : ℕ} {x y z : Fin p} (hxy : x ≠ y) :
    (GM16.completeGraph p).Inc s(x, y) z ↔ z = x ∨ z = y := by
  constructor
  · rintro ⟨w, _, heq⟩
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨_, h⟩
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact ⟨y, hxy, rfl⟩
    · exact ⟨x, hxy.symm, Sym2.eq_swap⟩

/-- Explicit clique size containing any graph with at most `vB` vertices and `eB` edges as a minor. -/
@[expose] def gm16_theorem42_bound (vB eB : ℕ) : ℕ :=
  vB + 2 * eB + 1

/-- Every finite multigraph with at most `vB` vertices and `eB` edges is a minor of
`completeGraph (vB + 2 * eB + 1)`. -/
private theorem isIsoMinor_completeGraph_of_le {γ δ : Type*} (L : Graph γ δ)
    (hV : L.vertexSet.Finite) (hE : L.edgeSet.Finite) {vB eB : ℕ}
    (hvB : L.vertexSet.ncard ≤ vB) (heB : L.edgeSet.ncard ≤ eB) :
    IsIsoMinor L (GM16.completeGraph (gm16_theorem42_bound vB eB)) := by
  classical
  let : Fintype L.vertexSet := hV.fintype
  let : Fintype L.edgeSet := hE.fintype
  let I := L.vertexSet ⊕ (L.edgeSet × Bool)
  let p := gm16_theorem42_bound vB eB
  have hcardV : Fintype.card L.vertexSet = L.vertexSet.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcardE : Fintype.card L.edgeSet = L.edgeSet.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hcardI : Fintype.card I < p := by
    have h1 : Fintype.card I = Fintype.card L.vertexSet + Fintype.card L.edgeSet * 2 := by
      simp [I]
    dsimp only [p, gm16_theorem42_bound]
    omega
  let tag : I → Fin p := fun z => ⟨(Fintype.equivFin I z).val,
    (Fintype.equivFin I z).isLt.trans hcardI⟩
  have htag : Function.Injective tag := by
    intro x y h
    have hval : (Fintype.equivFin I x).val = (Fintype.equivFin I y).val :=
      congrArg (fun z : Fin p => z.val) h
    exact (Fintype.equivFin I).injective (Fin.ext hval)
  have hend : ∀ e : L.edgeSet, ∃ x y, L.IsLink e.val x y := fun e =>
    L.exists_isLink_of_mem_edgeSet e.property
  choose left right hlink using hend
  let owner : I → γ := Sum.elim Subtype.val (fun t => if t.2 then right t.1 else left t.1)
  let core (v : L.vertexSet) : Fin p := tag (Sum.inl v)
  let port (e : L.edgeSet) (b : Bool) : Fin p := tag (Sum.inr (e, b))
  let a : γ → Set (Fin p) := fun v => tag '' {z | owner z = v}
  let b : δ → Sym2 (Fin p) := fun e => if he : e ∈ L.edgeSet then
    s(port ⟨e, he⟩ false, port ⟨e, he⟩ true) else s(⟨0, Nat.zero_lt_succ _⟩, ⟨0, Nat.zero_lt_succ _⟩)
  have hmem : ∀ z v, tag z ∈ a v ↔ owner z = v := by
    intro z v
    constructor
    · rintro ⟨w, hw, heq⟩
      exact htag heq ▸ hw
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hport : ∀ e : L.edgeSet, port e false ≠ port e true := by
    intro e heq
    have := htag heq
    exact Bool.false_ne_true (congrArg (fun z : I => match z with | .inl _ => false | .inr t => t.2) this)
  have hcore : ∀ v : L.vertexSet, ∀ e : L.edgeSet, ∀ k, core v ≠ port e k := by
    intro v e k heq
    exact Sum.inl_ne_inr (htag heq)
  have hdisj : ∀ u ∈ L.vertexSet, ∀ v ∈ L.vertexSet, u ≠ v → Disjoint (a u) (a v) := by
    intro u _ v _ huv
    apply Set.disjoint_left.mpr
    rintro x ⟨z, hz, rfl⟩ hx
    exact huv (hz.symm.trans ((hmem z v).mp hx))
  have hb : ∀ e (he : e ∈ L.edgeSet), b e = s(port ⟨e, he⟩ false, port ⟨e, he⟩ true) :=
    fun e he => dite_eq_left he
  have hinc : ∀ e (he : e ∈ L.edgeSet) v,
      (∃ x ∈ a v, (GM16.completeGraph p).Inc (b e) x) ↔
        v = left ⟨e, he⟩ ∨ v = right ⟨e, he⟩ := by
    intro e he v
    rw [hb e he]
    simp only [clique_inc (hport ⟨e, he⟩)]
    constructor
    · rintro ⟨x, hx, rfl | rfl⟩
      · exact Or.inl ((hmem _ v).mp hx).symm
      · exact Or.inr ((hmem _ v).mp hx).symm
    · rintro (rfl | rfl)
      · exact ⟨port ⟨e, he⟩ false, (hmem _ _).mpr rfl, Or.inl rfl⟩
      · exact ⟨port ⟨e, he⟩ true, (hmem _ _).mpr rfl, Or.inr rfl⟩
  have hm : IsMinorModel L (GM16.completeGraph p) a b := by
    refine {
      vertex_nonempty := ?_
      vertex_subset := fun _ _ _ _ => mem_univ _
      edge_mem := ?_
      vertex_disjoint := hdisj
      edge_injOn := ?_
      inc_iff := ?_
      isLoopAt_iff := ?_
      connected := ?_ }
    · intro v hv
      exact ⟨core ⟨v, hv⟩, (hmem _ _).mpr rfl⟩
    · intro e he
      rw [hb e he]
      exact ⟨_, _, hport ⟨e, he⟩, rfl⟩
    · intro e he f hf hef
      rw [hb e he, hb f hf] at hef
      rcases Sym2.eq_iff.mp hef with ⟨h, _⟩ | ⟨h, _⟩
      · have h' := htag h
        exact congrArg (fun z : I => match z with | .inl _ => e | .inr t => t.1.val) h'
      · have h' := htag h
        exact congrArg (fun z : I => match z with | .inl _ => e | .inr t => t.1.val) h'
    · intro v _ e he
      rw [hinc e he]
      constructor
      · intro hv
        exact hv.eq_or_eq_of_isLink (hlink ⟨e, he⟩)
      · rintro (rfl | rfl)
        · exact (hlink ⟨e, he⟩).inc_left
        · exact (hlink ⟨e, he⟩).inc_right
    · intro v _ e he
      rw [hb e he]
      constructor
      · intro hl x hx
        have hl' := hlink ⟨e, he⟩
        have hlv := hl.eq_of_inc hl'.inc_left
        have hrv := hl.eq_of_inc hl'.inc_right
        rcases (clique_inc (hport ⟨e, he⟩)).mp hx with rfl | rfl
        · exact (hmem _ _).mpr hlv.symm
        · exact (hmem _ _).mpr hrv.symm
      · intro hall
        have hlv := (hmem _ v).mp (hall _ ((clique_inc (hport ⟨e, he⟩)).mpr (Or.inl rfl)))
        have hrv := (hmem _ v).mp (hall _ ((clique_inc (hport ⟨e, he⟩)).mpr (Or.inr rfl)))
        change left ⟨e, he⟩ = v at hlv
        change right ⟨e, he⟩ = v at hrv
        have hl := hlink ⟨e, he⟩
        rw [hlv, hrv] at hl
        exact hl
    · intro v hv
      let K := ((GM16.completeGraph p).induce (a v)).deleteEdges (b '' L.edgeSet)
      have hcm : core ⟨v, hv⟩ ∈ a v := (hmem _ _).mpr rfl
      have hreach : ∀ x ∈ a v, Relation.ReflTransGen K.Adj x (core ⟨v, hv⟩) ∧
          Relation.ReflTransGen K.Adj (core ⟨v, hv⟩) x := by
        intro x hx
        by_cases hxc : x = core ⟨v, hv⟩
        · subst x
          exact ⟨.refl, .refl⟩
        have hn : s(x, core ⟨v, hv⟩) ∉ b '' L.edgeSet := by
          rintro ⟨e, he, heq⟩
          rw [hb e he] at heq
          rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h, _⟩
          · exact hcore ⟨v, hv⟩ ⟨e, he⟩ true h.symm
          · exact hcore ⟨v, hv⟩ ⟨e, he⟩ false h.symm
        have hadj : K.Adj x (core ⟨v, hv⟩) := ⟨s(x, core ⟨v, hv⟩), ⟨⟨hxc, rfl⟩, hx, hcm⟩, hn⟩
        exact ⟨.single hadj, .single hadj.symm⟩
      refine ⟨K, ?_, rfl, ⟨core ⟨v, hv⟩, hcm⟩, ?_⟩
      · exact ⟨subset_univ _, fun _ _ _ h => ⟨h.1.1, h.2⟩⟩
      · intro x hx y hy
        exact (hreach x hx).1.trans (hreach y hy).2
  exact isIsoMinor_of_isMinorModel L (GM16.completeGraph p) hV hE
    (Set.toFinite _) (Set.toFinite _) a b hm

/-- Explicit form of `gm16_theorem42`: a tangle controlling `K_{vB + 2*eB + 1}` controls
every finite graph with at most `vB` vertices and `eB` edges. -/
theorem gm16_theorem42_explicit {γ δ : Type*} (L : Graph γ δ)
    (hV : L.vertexSet.Finite) (hE : L.edgeSet.Finite) {vB eB : ℕ}
    (hvB : L.vertexSet.ncard ≤ vB) (heB : L.edgeSet.ncard ≤ eB)
    {α β : Type*} (G : Graph α β) (θ : ℕ) (T : Set (Hypergraph α β × Hypergraph α β))
    (hT : GM15.IsGraphTangle G θ T)
    (hc : ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ T
      (GM16.completeGraph (gm16_theorem42_bound vB eB))) :
    ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ T L := by
  have hminor := isIsoMinor_completeGraph_of_le L hV hE hvB heB
  have hp : 1 ≤ gm16_theorem42_bound vB eB := Nat.succ_le_succ (Nat.zero_le _)
  have : NeZero (gm16_theorem42_bound vB eB) := ⟨Nat.ne_zero_of_lt hp⟩
  have : Nonempty (Fin (gm16_theorem42_bound vB eB)) := ⟨⟨0, hp⟩⟩
  have hc' := hc
  obtain ⟨_, b, _⟩ := hc'
  let : Nonempty β := ⟨b s((0 : Fin (gm16_theorem42_bound vB eB)), 0)⟩
  exact theorem_4_2_proof hT.finite_V hT.finite_E (Set.toFinite _) (Set.toFinite _) hminor hc

/-- The finite-graph consequence of XII (4.2) used by XVI, with exactly
the cited conclusion. A sufficiently large complete graph contains the
given finite multigraph as a minor. -/
theorem gm16_theorem42 : GM16.GM12Theorem42Statement.{u, v} := by
  intro γ δ L hV hE
  exact ⟨gm16_theorem42_bound L.vertexSet.ncard L.edgeSet.ncard,
    fun G θ T hT hc => gm16_theorem42_explicit L hV hE le_rfl le_rfl G θ T hT hc⟩

/-- Explicit form of `gm16_theorem43`, with threshold `theorem_4_3_bound V a b vB eB`. -/
theorem gm16_theorem43_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {α' β' : Type*} (L : Graph α' β')
    (hS : Surface.IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ Surface.SurfaceModel a b 0))
    (hVL : L.vertexSet.Finite) (hEL : L.edgeSet.Finite)
    {vB eB : ℕ} (hvB : L.vertexSet.ncard ≤ vB) (heB : L.edgeSet.ncard ≤ eB)
    (hdraw : GM16.CanBeDrawnIn S L) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Surface.Drawing S) (η : GM14.SpanEmbedding H G) (θ_span : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (hT : GM15.IsGraphTangle G θ_star T_star),
      ¬ ControlsMinor (Hypergraph.ofGraph G hT.finite_V hT.finite_E) θ_star T_star L →
      theorem_4_3_bound V a b vB eB ≤ θ_span →
      ¬ GM15.IsSigmaSpan G H η θ_star θ_span T_star T := by
  let : ConnectedSpace S := hConn
  obtain ⟨ν, edgeOf, hν, hline, hloop, hmeet, hon⟩ := hdraw
  obtain ⟨D, _, _⟩ := exists_graphDrawing_of_edge_curves L hVL hEL ν edgeOf hν hline hloop hmeet hon
  have hmain := theorem_4_3_drawing_explicit V hV hS he D hvB heB
  intro α β G θstar Tstar H η θ T hTstar hNo hθ hSpan
  obtain ⟨d, hd⟩ := exists_metric_of_respectful_drawing_tangle hS hSpan.isRespectful
  have hc := hmain H θ T d hd hθ
  exact hNo (controlsMinor_of_controlling_drawing_tangle η hSpan.isControlling hc)

/-- XII (4.3), pages 249--251, with exactly the span conclusion
cited by XVI. The drawing embedding transfers every branch and
joining edge, and the controlling-tangle condition transfers the
small-side exclusion. The cited hypotheses are VII (7.5), (5.1),
and (5.5). -/
theorem gm16_theorem43
    : GM16.GM12Theorem43Statement.{u, v, w} := by
  intro S _ _ α' β' L hS hConn hVL hEL hdraw
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_3_bound GM07.vModel a b L.vertexSet.ncard L.edgeSet.ncard,
    one_le_theorem_4_3_bound _ a b _ _,
    gm16_theorem43_explicit GM07.vModel (fun _ _ _ _ => le_rfl) L hS hConn he hVL hEL le_rfl le_rfl hdraw⟩

/-- Explicit form of `gm16_theorem44`, with threshold `theorem_4_4_bound V a b p`. -/
theorem gm16_theorem44_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (hS : Surface.IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ Surface.SurfaceModel a b 0)) (p : ℕ) :
    let μ := p * (p - 1) / 2
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star θ_span : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Surface.Drawing S) (η : GM14.SpanEmbedding H G)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ)
      (s t : Fin μ → S) (Q : Fin μ → Graph α β)
      (hSpan : GM15.IsSigmaSpan G H η θ_star θ_span T_star T),
      GM14.HasTangleMetric H θ_span T d →
      theorem_4_4_bound V a b p ≤ θ_span →
      (∀ i : Fin μ, s i ∈ H.V ∧ t i ∈ H.V ∧ s i ≠ t i) →
      Function.Injective s → Function.Injective t → Disjoint (range s) (range t) →
      (∀ u ∈ range s ∪ range t, ∀ v ∈ range s ∪ range t, u ≠ v →
        theorem_4_4_bound V a b p ≤ d {u} {v}) →
      (∀ i : Fin μ, GM14.IsHPathWithEnds G η.imageGraph (Q i) (η.vMap (s i)) (η.vMap (t i))) →
      Pairwise (fun i j => Disjoint (Q i).vertexSet (Q j).vertexSet) →
      ControlsMinor
        (Hypergraph.ofGraph G hSpan.isControlling.isTangle_star.finite_V
          hSpan.isControlling.isTangle_star.finite_E)
        θ_star T_star (GM16.completeGraph p) := by
  let : ConnectedSpace S := hConn
  dsimp only
  intro α β G θstar θ Tstar H η T d s t P hSpan hm hθ hends hs ht hdisj hfar hP hPP
  exact theorem_4_4_span_explicit V hV hS he p G θstar θ Tstar H η T d s t P
    hSpan.isControlling hm hθ hends hs ht hdisj hfar hP hPP

/-- XII (4.4), pages 251--252, with exactly the span conclusion
cited by XVI. All branch, path, feasibility, and control steps are
proved; the statement hypotheses are VII (7.5), (5.1), and (5.5). -/
theorem gm16_theorem44
    : GM16.GM12Theorem44Statement.{u, v, w} := by
  intro S _ _ hS hConn p
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_4_bound GM07.vModel a b p, one_le_theorem_4_4_bound _ a b p,
    gm16_theorem44_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS hConn he p⟩

/-- Explicit form of `gm15_theorem45`, with eye count `theorem_4_5_kBound p` and order
threshold `theorem_4_5_NBound V a b p`. -/
theorem gm15_theorem45_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (S : Type w) [TopologicalSpace S] [T2Space S]
    (hS : Surface.IsClosedSurface S) (hConn : ConnectedSpace S)
    {a b : ℕ} (he : Nonempty (S ≃ₜ Surface.SurfaceModel a b 0)) (p : ℕ) :
    ∀ {α : Type u} {β : Type v} (G : Graph α β) (θ_star : ℕ)
      (T_star : Set (Hypergraph α β × Hypergraph α β))
      (H : Surface.Drawing S) (η : GM14.SpanEmbedding H G) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ)
      (hSpan : GM15.IsSigmaSpan G H η θ_star θ T_star T),
      GM14.HasTangleMetric H θ T d →
      p ≤ θ_star → theorem_4_5_NBound V a b p ≤ θ →
      GM15.HasIndependentEyes G H η θ T d (theorem_4_5_kBound p) →
      ControlsMinor
        (Hypergraph.ofGraph G hSpan.isControlling.isTangle_star.finite_V
          hSpan.isControlling.isTangle_star.finite_E)
        θ_star T_star (GM15.completeGraph p) := by
  let : ConnectedSpace S := hConn
  intro α β G θstar Tstar H η θ T d hSpan hm _ hNθ heyes
  obtain ⟨r, P, Q, hri, heye, hdist, hdisj⟩ := heyes
  have hfar : ∀ i j, i ≠ j → theorem_4_5_NBound V a b p ≤ d (r i) (r j) := by
    intro i j hij
    rw [hdist i j hij]
    exact hNθ
  exact theorem_4_5_span_explicit V hV hS he p G θstar θ Tstar H η T d hSpan.isControlling hm hNθ
    r P Q hri heye hfar hdisj

/-- Graph Minors XII (4.5), pages 252--253, in the exact independent-eye
span form used by XV. The only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem gm15_theorem45
    : GM15.GM12Theorem45Statement.{u, v, w} := by
  intro S _ _ hS hConn p
  let : ConnectedSpace S := hConn
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_5_kBound p, theorem_4_5_NBound GM07.vModel a b p,
    gm15_theorem45_explicit GM07.vModel (fun _ _ _ _ => le_rfl) S hS hConn he p⟩

/-- Unconditional proof of `GM19.GM12Theorem32Statement`. -/
theorem gm19_theorem32_proved : GM19.GM12Theorem32Statement.{u} :=
  gm19_theorem32

/-- Unconditional proof of `GM16.GM12Theorem43Statement`. -/
theorem gm16_theorem43_proved : GM16.GM12Theorem43Statement.{u, v, w} :=
  gm16_theorem43

/-- Unconditional proof of `GM16.GM12Theorem44Statement`. -/
theorem gm16_theorem44_proved : GM16.GM12Theorem44Statement.{u, v, w} :=
  gm16_theorem44

/-- Unconditional proof of `GM15.GM12Theorem45Statement`. -/
theorem gm15_theorem45_proved : GM15.GM12Theorem45Statement.{u, v, w} :=
  gm15_theorem45

end GraphMinor.GM12
