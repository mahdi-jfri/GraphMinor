module

public import GraphMinor.GM21.Section6CutPresentation
public import GraphMinor.GM21.Section6CutPieces
public import GraphMinor.GM21.Section6CutCuffs
public import GraphMinor.GM21.Section6CutDrawing
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6SidePieces
import GraphMinor.GM11.Defs
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, (6.3), claim (2): the names on the cut surface

Claim (2) of the proof of (6.3) (page 28 of the preprint): "Let $\Gamma'$ be the drawing in
$\Sigma'$ obtained from $\Gamma$ by splitting appropriately the vertices of $\Gamma$ in $F$. ...
By splitting $v$ according to $\delta_1(v), \delta_2(v)$, for each $v \in V(\mu(a))$, and similarly
splitting each $v \in V(\mu(b))$, we obtain a graph $G'$ which has a presentation in $\Sigma'$
(using the drawing $\Gamma'$) of depth $\le q$ and defect $\le r + 2$."

The two points over `a` are named `a₋, a₊`, and the two over `b` are named `b₋, b₊`. The graph is
split first along `Xa = V(μ(a))`, with the edges `Ea` on the side `a₊` going to the second copies,
and then along the copies `Xb` of `V(μ(b))`, with the edges `Eb` on the side `b₊`. Here `Ea` is
the set of edges of `μ(A₊)` for a piece `A₊` of the support at `a`, together with the edges of `Γ`
whose lift ends at `a₊` (`cutEdges`). A vertex `u` of `Γ'` is named by the copy of `ιV(ψ(u))` on the
sides (`u = a₊` and `u = b₊`, `cutName`).

* `split2_inc_nm2_iff'`: when a copy is incident with an edge.
* `cutName_injOn`, `inc_cutName_iff`, `mem_image_cutName_of_inc`: `cutName` draws `Γ'` as a
  subgraph of the split graph.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

namespace Split

variable {α : Type u} {β : Type v}

/-- When a copy in a split graph is incident with an edge. -/
theorem splitAlong_inc_splitName_iff' {G : Hypergraph α β} {X : Set α} {E₂ : Set β} {c : Bool}
    {e : β} {v : α} :
    (splitAlong G X E₂).Inc e (splitName X c v) ↔ G.Inc e v ∧ (v ∈ X → (e ∈ E₂ ↔ c = true)) := by
  by_cases hvX : v ∈ X
  · cases c
    · rw [splitName_false_of_mem hvX, splitAlong_inc_inr_inl]
      simp [hvX]
    · rw [splitName_true_of_mem hvX, splitAlong_inc_inr_inr]
      simp [hvX]
  · rw [splitName_of_notMem hvX, splitAlong_inc_inl]
    simp [hvX]

/-- When a copy in a graph split twice is incident with an edge. -/
theorem split2_inc_nm2_iff' {G : Hypergraph α β} {Xa : Set α} {Ea : Set β}
    {Xb : Set (α ⊕ α ⊕ α)} {Eb : Set β} {c : Bool × Bool} {e : β} {v : α} :
    (split2 G Xa Ea Xb Eb).Inc e (nm2 Xa Xb c v) ↔ G.Inc e v ∧ (v ∈ Xa → (e ∈ Ea ↔ c.1 = true)) ∧
      (splitName Xa c.1 v ∈ Xb → (e ∈ Eb ↔ c.2 = true)) := by
  unfold split2 nm2
  rw [splitAlong_inc_splitName_iff', splitAlong_inc_splitName_iff', and_assoc]

end Split

namespace CutLine

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

/-- The edges on the side `p` of the end of `F` over which `p` lies: the edges of `μ(A)` and the
edges of `Γ` whose lift ends at `p`. -/
def cutEdges (G : Hypergraph α β) (Γ : Drawing S) (μ : BoundaryUnit S → Hypergraph α β)
    (ψ : S' → S) (ιE : Set S → β) (A : Set S) (p : S') : Set β :=
  (supportGraph G Γ μ A).edgeSet ∪ ιE '' {e ∈ Γ.E | p ∈ closure (ψ ⁻¹' e)}

/-- The copies of `V(μ(b))` split in the second step, on the first side `cb`. -/
def splitB (μ : BoundaryUnit S → Hypergraph α β) (a b : S) (cb : Bool) : Set (α ⊕ α ⊕ α) :=
  splitName (μ (.vertex a)).vertexSet cb '' (μ (.vertex b)).vertexSet

open Classical in
/-- The name of a vertex `u` of `Γ'`: the copy of `ιV(ψ(u))` on the sides "`u = a₊`" and
"`u = b₊`". -/
noncomputable def cutName (ψ : S' → S) (ιV : S → α) (Xa : Set α) (Xb : Set (α ⊕ α ⊕ α))
    (ap bp : S') (u : S') : Name2 α :=
  nm2 Xa Xb (decide (u = ap), decide (u = bp)) (ιV (ψ u))

section names

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- `ιV(u)` is a vertex of `μ(a)` only for `u = a`. -/
theorem ιV_mem_μ_iff (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {a : S}
    (ha : a ∈ Γ.V ∩ bd S) {u : S} (hu : u ∈ Γ.V) :
    ιV u ∈ (μ (.vertex a)).vertexSet ↔ u = a := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered ha)
  have hint := (hP.μ_vertex_sub j a ⟨ha.1, hj⟩).2.2.2
  constructor
  · intro h
    have h1 : ιV u ∈ (μ (.vertex a)).vertexSet ∩ Γ_sub.vertexSet :=
      ⟨h, hP.ιV_image ▸ mem_image_of_mem ιV hu⟩
    rw [hint] at h1
    exact hP.ιV_injOn hu ha.1 h1
  · rintro rfl
    exact GM21.ιV_mem_μ_vertex hP j ⟨ha.1, hj⟩

/-- The first copy of `ιV(u)` is in `Xb` only for `u = b`. -/
theorem splitName_mem_splitB_iff (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) {a b : S}
    (ha : a ∈ Γ.V ∩ bd S) (hb : b ∈ Γ.V ∩ bd S) (hab : a ≠ b) (cb c : Bool) {u : S}
    (hu : u ∈ Γ.V) :
    splitName (μ (.vertex a)).vertexSet c (ιV u) ∈ splitB μ a b cb ↔ u = b := by
  constructor
  · rintro ⟨w, hw, hwu⟩
    have := eq_of_splitName_eq hwu
    subst this
    exact (ιV_mem_μ_iff hP hb hu).mp hw
  · rintro rfl
    have hnot : ιV u ∉ (μ (.vertex a)).vertexSet := fun h =>
      hab ((ιV_mem_μ_iff hP ha hu).mp h).symm
    refine ⟨ιV u, (ιV_mem_μ_iff hP hb hu).mpr rfl, ?_⟩
    rw [splitName_of_notMem hnot, splitName_of_notMem hnot]

end names

omit [TopologicalSpace S] [TopologicalSpace S'] in
/-- A point over `a` is one of the two points over `a`. -/
theorem eq_or_eq_of_map {x : S} {am ap z : S'} (hpa : ψ ⁻¹' {x} = {am, ap}) (hz : ψ z = x) :
    z = am ∨ z = ap := by
  have : z ∈ ψ ⁻¹' {x} := hz
  rw [hpa] at this
  exact this

/-! ## The names draw `Γ'` as a subgraph -/

section drawing

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
  (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
  (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) {Γ' : Drawing S'}
  (hV : Γ'.V = ψ ⁻¹' Γ.V) {am ap bm bp : S'} (hpa : ψ ⁻¹' {a} = {am, ap}) (hamp : am ≠ ap)
  (hpb : ψ ⁻¹' {b} = {bm, bp}) (hbmp : bm ≠ bp) (cb : Bool)
include hP h hF habV hFU hV hpa hamp hpb hbmp

omit h hFU hpa hamp hpb hbmp in
open Classical in
/-- The name of a vertex of `Γ'` is its copy on any sides that agree with it at `a` and at `b`. -/
theorem cutName_eq {u : S'} (hu : u ∈ Γ'.V) (c : Bool × Bool)
    (h1 : ψ u = a → c.1 = decide (u = ap)) (h2 : ψ u = b → c.2 = decide (u = bp)) :
    cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp u =
      nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) c (ιV (ψ u)) := by
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  have huV : ψ u ∈ Γ.V := by rw [hV] at hu; exact hu
  unfold cutName
  have e1 : nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (decide (u = ap), decide (u = bp))
      (ιV (ψ u)) = nm2 (μ (.vertex a)).vertexSet (splitB μ a b cb) (c.1, decide (u = bp))
      (ιV (ψ u)) := by
    by_cases hua : ψ u = a
    · rw [h1 hua]
    · exact nm2_eq_of_notMem_left (c := (decide (u = ap), decide (u = bp)))
        (c' := (c.1, decide (u = bp))) rfl fun hm => hua ((ιV_mem_μ_iff hP ha huV).mp hm)
  rw [e1]
  by_cases hub : ψ u = b
  · rw [← h2 hub]
  · exact nm2_eq_of_notMem_right (c := (c.1, decide (u = bp))) (c' := c) rfl fun hm =>
      hub ((splitName_mem_splitB_iff hP ha hb hF.ne cb _ huV).mp hm)

omit hP h hF habV hV hpa hamp hpb hbmp in
/-- A vertex of `V(Γ)` on `F` is an end of `F`. -/
theorem mem_ends_of_mem_line {x : S} (hxF : x ∈ F) (hxV : x ∈ Γ.V) : x = a ∨ x = b :=
  hFU ⟨hxF, Γ.V_subset_U hxV⟩

/-- **The names are one to one** on the vertices of `Γ'`. -/
theorem cutName_injOn :
    InjOn (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp) Γ'.V := by
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  intro u hu w hw huw
  have huV : ψ u ∈ Γ.V := by rw [hV] at hu; exact hu
  have hwV : ψ w ∈ Γ.V := by rw [hV] at hw; exact hw
  unfold cutName at huw
  have hψ : ψ u = ψ w := hP.ιV_injOn huV hwV (eq_of_nm2_eq huw)
  by_cases hF' : ψ u ∈ F
  · rcases mem_ends_of_mem_line hFU hF' huV with hua | hub
    · have h1 := fst_eq_of_nm2_eq ((ιV_mem_μ_iff hP ha huV).mpr hua) huw
      simp only [decide_eq_decide] at h1
      rcases eq_or_eq_of_map hpa hua with hu1 | hu1 <;>
        rcases eq_or_eq_of_map hpa (hψ ▸ hua) with hw1 | hw1
      · rw [hu1, hw1]
      · exact absurd (h1.mpr hw1) (by rw [hu1]; exact hamp)
      · exact absurd (h1.mp hu1) (by rw [hw1]; exact hamp)
      · rw [hu1, hw1]
    · have h1 := snd_eq_of_nm2_eq ((splitName_mem_splitB_iff hP ha hb hF.ne cb _ huV).mpr hub)
        huw
      simp only [decide_eq_decide] at h1
      rcases eq_or_eq_of_map hpb hub with hu1 | hu1 <;>
        rcases eq_or_eq_of_map hpb (hψ ▸ hub) with hw1 | hw1
      · rw [hu1, hw1]
      · exact absurd (h1.mpr hw1) (by rw [hu1]; exact hbmp)
      · exact absurd (h1.mp hu1) (by rw [hw1]; exact hbmp)
      · rw [hu1, hw1]
  · exact h.injOn_compl hF' (show ψ w ∉ F from hψ ▸ hF') hψ

omit h hF habV hFU hV hpa hamp hpb hbmp in
/-- An edge of `Γ` is not an edge of `μ(A)` for a set `A` inside a support. -/
theorem ιE_notMem_supportGraph {A : Set S} (hA : ∃ j, A ⊆ F_star j) {e : Set S}
    (he : e ∈ Γ.E) : ιE e ∉ (supportGraph G Γ μ A).edgeSet := by
  obtain ⟨j, hj⟩ := hA
  intro h1
  have h2 : supportGraph G Γ μ A ≤ H j := by
    rw [hP.v2_eq j]
    exact GM21.supportGraph_mono hP j subset_rfl hj
  exact disjoint_left.mp (hP.v1_inter_E j) (h2.edgeSet_subset h1)
    (hP.ιE_image ▸ mem_image_of_mem ιE he)

omit h hF habV hFU hV hpa hamp hpb hbmp in
/-- An edge of `Γ` is on the side `p` exactly when its lift ends at `p`. -/
theorem ιE_mem_cutEdges_iff {A : Set S} (hA : ∃ j, A ⊆ F_star j) {e : Set S} (he : e ∈ Γ.E)
    {p : S'} : ιE e ∈ cutEdges G Γ μ ψ ιE A p ↔ p ∈ closure (ψ ⁻¹' e) := by
  constructor
  · rintro (h1 | ⟨e', ⟨he', hp⟩, heq⟩)
    · exact absurd h1 (ιE_notMem_supportGraph hP hA he)
    · rwa [← hP.ιE_injOn he' he heq]
  · intro hp
    exact Or.inr ⟨e, ⟨he, hp⟩, rfl⟩

variable {Apf Bpf : Set S}

open Classical in
/-- **The edge `ιE(e)` is incident with the name of `u` exactly when `u` is an end of the lift of
`e`.** -/
theorem inc_cutName_iff (hlink : ∀ e ∈ Γ.E, ∃ u w, u ≠ w ∧ closure e ∩ Γ.V = {u, w})
    (hApf : ∃ j, Apf ⊆ F_star j) (hBpf : ∃ j, Bpf ⊆ F_star j) {e : Set S} (he : e ∈ Γ.E)
    {u : S'} (hu : u ∈ Γ'.V) :
    (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap) (splitB μ a b cb)
        (cutEdges G Γ μ ψ ιE Bpf bp)).Inc (ιE e)
        (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp u) ↔
      u ∈ closure (ψ ⁻¹' e) := by
  have hS := hP.is_surface
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  have huV : ψ u ∈ Γ.V := by rw [hV] at hu; exact hu
  have hFU' : F ∩ Γ.U ⊆ Γ.V := fun x hx => by
    rcases hFU hx with rfl | rfl
    exacts [habV.1, habV.2]
  have hψap : ψ ap = a := show ap ∈ ψ ⁻¹' {a} from hpa ▸ Or.inr rfl
  have hψbp : ψ bp = b := show bp ∈ ψ ⁻¹' {b} from hpb ▸ Or.inr rfl
  obtain ⟨u₀, w₀, hne, hcl⟩ := hlink e he
  obtain ⟨-, -, -, -, -, hinj, himg⟩ := h.closure_preimage_edge hS hFU' he hcl hne
  have heΓ : ιE e ∈ Γ_sub.edgeSet := hP.ιE_image ▸ mem_image_of_mem ιE he
  unfold cutName
  rw [split2_inc_nm2_iff', ιE_mem_cutEdges_iff hP hApf he, ιE_mem_cutEdges_iff hP hBpf he,
    ← GM10.inc_iff_of_le hP.drawing_subgraph heΓ, hP.inc_iff e he _ huV,
    ιV_mem_μ_iff hP ha huV, splitName_mem_splitB_iff hP ha hb hF.ne cb _ huV]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hcle, hA, hB⟩
    obtain ⟨l, hl, hlu⟩ : ψ u ∈ ψ '' closure (ψ ⁻¹' e) := himg ▸ hcle
    by_cases hF' : ψ u ∈ F
    · rcases mem_ends_of_mem_line hFU hF' huV with hua | hub
      · rcases eq_or_eq_of_map hpa (hlu.trans hua) with hl1 | hl1
        · have hapL : ap ∉ closure (ψ ⁻¹' e) := fun hap =>
            hamp (hinj (hl1 ▸ hl) hap (by rw [← hl1, hlu, hua, hψap]))
          have hu1 : u ≠ ap := fun h1 => hapL ((hA hua).mpr h1)
          rcases eq_or_eq_of_map hpa hua with hu2 | hu2
          · rw [hu2, ← hl1]
            exact hl
          · exact absurd hu2 hu1
        · rw [(hA hua).mp (hl1 ▸ hl)]
          exact hl1 ▸ hl
      · rcases eq_or_eq_of_map hpb (hlu.trans hub) with hl1 | hl1
        · have hbpL : bp ∉ closure (ψ ⁻¹' e) := fun hbp =>
            hbmp (hinj (hl1 ▸ hl) hbp (by rw [← hl1, hlu, hub, hψbp]))
          have hu1 : u ≠ bp := fun h1 => hbpL ((hB hub).mpr h1)
          rcases eq_or_eq_of_map hpb hub with hu2 | hu2
          · rw [hu2, ← hl1]
            exact hl
          · exact absurd hu2 hu1
        · rw [(hB hub).mp (hl1 ▸ hl)]
          exact hl1 ▸ hl
    · have hlF : ψ l ∉ F := hlu ▸ hF'
      rwa [← h.injOn_compl hlF hF' hlu]
  · intro huL
    refine ⟨himg ▸ mem_image_of_mem ψ huL, fun hua => ⟨fun hap => ?_, fun h1 => h1 ▸ huL⟩,
      fun hub => ⟨fun hbp => ?_, fun h1 => h1 ▸ huL⟩⟩
    · exact (hinj hap huL (by rw [hψap, hua])).symm
    · exact (hinj hbp huL (by rw [hψbp, hub])).symm

open Classical in
/-- **Every end of `ιE(e)` in the split graph is the name of a vertex of `Γ'`.** -/
theorem mem_image_cutName_of_inc (hlink : ∀ e ∈ Γ.E, ∃ u w, u ≠ w ∧ closure e ∩ Γ.V = {u, w})
    (hApf : ∃ j, Apf ⊆ F_star j) (hBpf : ∃ j, Bpf ⊆ F_star j) {e : Set S} (he : e ∈ Γ.E)
    {w : Name2 α}
    (hw : (split2 G (μ (.vertex a)).vertexSet (cutEdges G Γ μ ψ ιE Apf ap) (splitB μ a b cb)
        (cutEdges G Γ μ ψ ιE Bpf bp)).Inc (ιE e) w) :
    w ∈ cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V := by
  have hS := hP.is_surface
  have hFU' : F ∩ Γ.U ⊆ Γ.V := fun x hx => by
    rcases hFU hx with rfl | rfl
    exacts [habV.1, habV.2]
  obtain ⟨u₀, w₀, hne, hcl⟩ := hlink e he
  obtain ⟨-, -, -, -, -, -, himg⟩ := h.closure_preimage_edge hS hFU' he hcl hne
  have heΓ : ιE e ∈ Γ_sub.edgeSet := hP.ιE_image ▸ mem_image_of_mem ιE he
  obtain ⟨v, hv, rfl⟩ := eq_nm2_of_inc
    (c := (decide (ιE e ∈ cutEdges G Γ μ ψ ιE Apf ap), decide (ιE e ∈ cutEdges G Γ μ ψ ιE Bpf bp)))
    decide_eq_true_iff.symm decide_eq_true_iff.symm hw
  have hvΓ : Γ_sub.Inc (ιE e) v := (GM10.inc_iff_of_le hP.drawing_subgraph heΓ).mpr hv
  obtain ⟨u₁, hu₁, rfl⟩ : v ∈ ιV '' Γ.V := hP.ιV_image ▸ Γ_sub.vertex_mem_of_inc hvΓ
  have hcl₁ : u₁ ∈ closure e := (hP.inc_iff e he u₁ hu₁).mp hvΓ
  obtain ⟨l, hl, hlu⟩ : u₁ ∈ ψ '' closure (ψ ⁻¹' e) := himg ▸ hcl₁
  have hlV : l ∈ Γ'.V := by
    rw [hV]
    show ψ l ∈ Γ.V
    rw [hlu]
    exact hu₁
  have hinc := (inc_cutName_iff hP h hF habV hFU hV hpa hamp hpb hbmp cb hlink hApf hBpf he
    hlV).mpr hl
  obtain ⟨v', -, hv'⟩ := eq_nm2_of_inc
    (c := (decide (ιE e ∈ cutEdges G Γ μ ψ ιE Apf ap), decide (ιE e ∈ cutEdges G Γ μ ψ ιE Bpf bp)))
    decide_eq_true_iff.symm decide_eq_true_iff.symm hinc
  have hv'l : v' = ιV (ψ l) := eq_of_nm2_eq (hv'.trans rfl)
  refine ⟨l, hlV, ?_⟩
  rw [← hv', hv'l, hlu]

end drawing

end CutLine
end GM21
end GraphMinor
