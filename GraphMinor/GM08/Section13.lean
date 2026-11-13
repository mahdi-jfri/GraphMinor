module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section3
public import GraphMinor.GM08.Section4
import Mathlib.Data.Set.Card

/-!
# Graph Minors VIII, Section 13: Vertex Identification (pages 274–275)

This file formalizes Section 13 of N. Robertson and P. D. Seymour,
*Graph Minors. VIII. A Kuratowski Theorem for General Surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288:

- `isGraftSimulatedIn_of_isGraftDirectSum`: simulations on direct summands $A_1 \le A_2$ and
  $B_1 \le B_2$ combine to a simulation on $A_1 \oplus B_1 \le A_2 \oplus B_2$.
- `theorem_13_1`: (13.1) (page 274), if $\mathscr{A}, \mathscr{B}$ are well-rooted then so is
  $\mathscr{A} \oplus \mathscr{B}$.
- `isGraftSimulatedIn_of_rootedGraphSimulation_identify`: a rooted graph simulation preserving the
  two identified roots at positions $0$ and $1$ induces a graft simulation after vertex
  identification.
- `theorem_13_2`: (13.2) (page 274), if $\mathscr{A}$ is well-rooted, then $W^1(\mathscr{A})$ is
  well-rooted.
- `theorem_13_3`: (13.3) (page 275), if $\mathscr{A}$ is well-rooted, then $W(\mathscr{A})$ is
  well-rooted.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Function Relation Graph

universe u v

/-! ## Direct sums of grafts and (13.1) -/

/-- Basic structural properties of a graft direct sum $C = A \oplus B$. -/
theorem isGraftDirectSum_props {α : Type u} {β : Type v} {C A B : Graft α β}
    (h : IsGraftDirectSum C A B) :
    V(A.G) ⊆ V(C.G) ∧
    V(B.G) = V(C.G) \ V(A.G) ∧
    Disjoint V(A.G) V(B.G) ∧
    V(A.G) ∪ V(B.G) = V(C.G) ∧
    A.G ≤ C.G ∧
    B.G ≤ C.G ∧
    Disjoint E(A.G) E(B.G) ∧
    E(A.G) ∪ E(B.G) = E(C.G) ∧
    A.T = C.T ∩ V(A.G) ∧
    B.T = C.T \ V(A.G) ∧
    Disjoint A.T B.T ∧
    A.T ∪ B.T = C.T := by
  obtain ⟨X, hX, hlink, hAG, hBG, hAT, hBT⟩ := h
  have hVA : V(A.G) = X := by rw [hAG, vertexSet_induce]
  have hVB : V(B.G) = V(C.G) \ X := by rw [hBG, vertexSet_induce]
  have hVA_sub : V(A.G) ⊆ V(C.G) := hVA ▸ hX
  have hVB_eq : V(B.G) = V(C.G) \ V(A.G) := by rw [hVB, hVA]
  have hdisj_V : Disjoint V(A.G) V(B.G) := by
    rw [hVB_eq]
    exact disjoint_sdiff_self_right
  have hunion_V : V(A.G) ∪ V(B.G) = V(C.G) := by
    rw [hVB_eq, union_sdiff_cancel hVA_sub]
  have hle_A : A.G ≤ C.G := by
    rw [hAG]
    exact C.G.induce_le hX
  have hle_B : B.G ≤ C.G := by
    rw [hBG]
    exact C.G.induce_le sdiff_subset
  have hdisj_E : Disjoint E(A.G) E(B.G) := by
    rw [disjoint_left]
    intro e heA heB
    rw [hAG, edgeSet_induce] at heA
    rw [hBG, edgeSet_induce] at heB
    obtain ⟨x₁, y₁, hl₁, hx₁, _⟩ := heA
    obtain ⟨x₂, y₂, hl₂, hx₂, hy₂⟩ := heB
    rcases hl₁.eq_and_eq_or_eq_and_eq hl₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx₂.2 hx₁
    · exact hy₂.2 hx₁
  have hunion_E : E(A.G) ∪ E(B.G) = E(C.G) := by
    apply Subset.antisymm (union_subset hle_A.edgeSet_mono hle_B.edgeSet_mono)
    intro e he
    obtain ⟨x, y, hl⟩ := exists_isLink_of_mem_edgeSet he
    by_cases hx : x ∈ X
    · have hy : y ∈ X := (hlink e x y hl).mp hx
      left
      rw [hAG, edgeSet_induce]
      exact ⟨x, y, hl, hx, hy⟩
    · have hy : y ∉ X := fun hy => hx ((hlink e x y hl).mpr hy)
      right
      rw [hBG, edgeSet_induce]
      exact ⟨x, y, hl, ⟨hl.left_mem, hx⟩, ⟨hl.right_mem, hy⟩⟩
  have hAT' : A.T = C.T ∩ V(A.G) := by rw [hAT, hVA]
  have hBT' : B.T = C.T \ V(A.G) := by rw [hBT, hVA]
  have hdisj_T : Disjoint A.T B.T := by
    rw [hAT', hBT']
    exact disjoint_sdiff_self_right.mono_left inter_subset_right
  have hunion_T : A.T ∪ B.T = C.T := by
    rw [hAT', hBT', inter_union_sdiff]
  exact ⟨hVA_sub, hVB_eq, hdisj_V, hunion_V, hle_A, hle_B, hdisj_E, hunion_E,
    hAT', hBT', hdisj_T, hunion_T⟩

/-- Every edge of $A.G$ in $C = A \oplus B$ has both ends in $V(A.G)$, and every edge of $C.G$
incident with a vertex in $V(A.G)$ belongs to $E(A.G)$. -/
theorem isGraftDirectSum_inc_iff {α : Type u} {β : Type v} {C A B : Graft α β}
    (h : IsGraftDirectSum C A B) :
    (∀ {e x}, C.G.Inc e x → x ∈ V(A.G) → e ∈ E(A.G) ∧ A.G.Inc e x) ∧
    (∀ {e x}, C.G.Inc e x → x ∈ V(B.G) → e ∈ E(B.G) ∧ B.G.Inc e x) := by
  obtain ⟨X, hX, hlink, hAG, hBG, _, _⟩ := h
  constructor
  · intro e x ⟨y, hl⟩ hx
    rw [hAG] at hx ⊢
    have hxX : x ∈ X := hx
    have hyX : y ∈ X := (hlink e x y hl).mp hxX
    have hlA : (C.G.induce X).IsLink e x y := ⟨hl, hxX, hyX⟩
    exact ⟨hlA.edge_mem, hlA.inc_left⟩
  · intro e x ⟨y, hl⟩ hx
    rw [hBG] at hx ⊢
    have hxX : x ∈ V(C.G) \ X := hx
    have hyX : y ∈ V(C.G) \ X := ⟨hl.right_mem, fun hy => hxX.2 ((hlink e x y hl).mpr hy)⟩
    have hlB : (C.G.induce (V(C.G) \ X)).IsLink e x y := ⟨hl, hxX, hyX⟩
    exact ⟨hlB.edge_mem, hlB.inc_left⟩

/-- If $C_1 = A_1 \oplus B_1$ and $C_2 = A_2 \oplus B_2$, and $A_1$ is simulated in $A_2$ and $B_1$
is simulated in $B_2$, then $C_1$ is simulated in $C_2$ (page 274). -/
theorem isGraftSimulatedIn_of_isGraftDirectSum {α : Type u} {β : Type v}
    {C₁ A₁ B₁ C₂ A₂ B₂ : Graft α β}
    (hC₁ : IsGraftDirectSum C₁ A₁ B₁) (hC₂ : IsGraftDirectSum C₂ A₂ B₂)
    (hA : IsGraftSimulatedIn A₁ A₂) (hB : IsGraftSimulatedIn B₁ B₂) :
    IsGraftSimulatedIn C₁ C₂ := by
  classical
  obtain ⟨ηvA, ηeA, hsimA⟩ := hA
  obtain ⟨ηvB, ηeB, hsimB⟩ := hB
  obtain ⟨hVA₁_sub, hVB₁_eq, hdisj_V₁, hunion_V₁, hle_A₁, hle_B₁, hdisj_E₁, hunion_E₁,
    hAT₁, hBT₁, hdisj_T₁, hunion_T₁⟩ := isGraftDirectSum_props hC₁
  obtain ⟨hVA₂_sub, hVB₂_eq, hdisj_V₂, hunion_V₂, hle_A₂, hle_B₂, hdisj_E₂, hunion_E₂,
    hAT₂, hBT₂, hdisj_T₂, hunion_T₂⟩ := isGraftDirectSum_props hC₂
  obtain ⟨hincA₁, hincB₁⟩ := isGraftDirectSum_inc_iff hC₁
  obtain ⟨hincA₂, hincB₂⟩ := isGraftDirectSum_inc_iff hC₂
  let ηv : α → Set α := fun v => if v ∈ V(A₁.G) then ηvA v else ηvB v
  let ηe : β → β := fun e => if e ∈ E(A₁.G) then ηeA e else ηeB e
  have hmem_VB₁ : ∀ {v}, v ∈ V(C₁.G) → v ∉ V(A₁.G) → v ∈ V(B₁.G) := by
    intro v hv hva
    rw [hVB₁_eq]
    exact ⟨hv, hva⟩
  have hmem_EB₁ : ∀ {e}, e ∈ E(C₁.G) → e ∉ E(A₁.G) → e ∈ E(B₁.G) := by
    intro e he hea
    rw [← hunion_E₁] at he
    exact he.resolve_left hea
  refine ⟨ηv, ηe, ?_, ?_, ?_⟩
  · refine
      { vertex_nonempty := fun v hv => by
          dsimp [ηv]
          split_ifs with hva
          · exact hsimA.1.vertex_nonempty v hva
          · exact hsimB.1.vertex_nonempty v (hmem_VB₁ hv hva)
        vertex_subset := fun v hv => by
          dsimp [ηv]
          split_ifs with hva
          · exact (hsimA.1.vertex_subset v hva).trans hVA₂_sub
          · exact (hsimB.1.vertex_subset v (hmem_VB₁ hv hva)).trans hle_B₂.vertexSet_mono
        edge_mem := fun e he => by
          dsimp [ηe]
          split_ifs with hea
          · exact hle_A₂.edgeSet_mono (hsimA.1.edge_mem e hea)
          · exact hle_B₂.edgeSet_mono (hsimB.1.edge_mem e (hmem_EB₁ he hea))
        vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne => by
          dsimp [ηv]
          split_ifs with h₁ h₂ h₂
          · exact hsimA.1.vertex_disjoint v₁ h₁ v₂ h₂ hne
          · exact hdisj_V₂.mono (hsimA.1.vertex_subset v₁ h₁)
              (hsimB.1.vertex_subset v₂ (hmem_VB₁ hv₂ h₂))
          · exact hdisj_V₂.symm.mono (hsimB.1.vertex_subset v₁ (hmem_VB₁ hv₁ h₁))
              (hsimA.1.vertex_subset v₂ h₂)
          · exact hsimB.1.vertex_disjoint v₁ (hmem_VB₁ hv₁ h₁) v₂ (hmem_VB₁ hv₂ h₂) hne
        edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
          dsimp [ηe] at heq
          split_ifs at heq with h₁ h₂ h₂
          · exact hsimA.1.edge_injOn h₁ h₂ heq
          · exfalso
            exact hdisj_E₂.notMem_of_mem_left (hsimA.1.edge_mem e₁ h₁)
              (heq ▸ hsimB.1.edge_mem e₂ (hmem_EB₁ he₂ h₂))
          · exfalso
            exact hdisj_E₂.notMem_of_mem_left (heq ▸ hsimA.1.edge_mem e₂ h₂)
              (hsimB.1.edge_mem e₁ (hmem_EB₁ he₁ h₁))
          · exact hsimB.1.edge_injOn (hmem_EB₁ he₁ h₁) (hmem_EB₁ he₂ h₂) heq
        inc_iff := fun v hv e he => by
          dsimp [ηv, ηe]
          split_ifs with hva hea hea
          · rw [← hle_A₁.inc_congr hea, hsimA.1.inc_iff v hva e hea]
            refine exists_congr fun x => and_congr_right fun hx => ?_
            exact hle_A₂.inc_congr (hsimA.1.edge_mem e hea)
          · have heb : e ∈ E(B₁.G) := hmem_EB₁ he hea
            constructor
            · intro hinc
              exfalso
              exact hea (hincA₁ hinc hva).1
            · rintro ⟨x, hx, hinc⟩
              exfalso
              have hxA₂ : x ∈ V(A₂.G) := hsimA.1.vertex_subset v hva hx
              exact hdisj_E₂.notMem_of_mem_left (hincA₂ hinc hxA₂).1 (hsimB.1.edge_mem e heb)
          · have hvb : v ∈ V(B₁.G) := hmem_VB₁ hv hva
            constructor
            · intro hinc
              exfalso
              exact hdisj_E₁.notMem_of_mem_left hea (hincB₁ hinc hvb).1
            · rintro ⟨x, hx, hinc⟩
              exfalso
              have hxB₂ : x ∈ V(B₂.G) := hsimB.1.vertex_subset v hvb hx
              exact hdisj_E₂.notMem_of_mem_left (hsimA.1.edge_mem e hea) (hincB₂ hinc hxB₂).1
          · have hvb : v ∈ V(B₁.G) := hmem_VB₁ hv hva
            have heb : e ∈ E(B₁.G) := hmem_EB₁ he hea
            rw [← hle_B₁.inc_congr heb, hsimB.1.inc_iff v hvb e heb]
            refine exists_congr fun x => and_congr_right fun hx => ?_
            exact hle_B₂.inc_congr (hsimB.1.edge_mem e heb)
        isLoopAt_iff := fun v hv e he => by
          dsimp [ηv, ηe]
          by_cases hva : v ∈ V(A₁.G) <;> by_cases hea : e ∈ E(A₁.G) <;>
            simp only [hva, hea, ↓reduceIte]
          · rw [← hle_A₁.isLoopAt_congr hea, hsimA.1.isLoopAt_iff v hva e hea]
            have heA₂ := hsimA.1.edge_mem e hea
            refine forall_congr' fun x => imp_congr_left ?_
            exact hle_A₂.inc_congr heA₂
          · have heb : e ∈ E(B₁.G) := hmem_EB₁ he hea
            constructor
            · intro hloop
              exfalso
              exact hea (hincA₁ hloop.inc_left hva).1
            · intro hall
              exfalso
              have heB₂ := hsimB.1.edge_mem e heb
              obtain ⟨x, y, hlB₂⟩ := exists_isLink_of_mem_edgeSet heB₂
              have hxA : x ∈ ηvA v := hall x (hlB₂.mono hle_B₂).inc_left
              exact hdisj_V₂.notMem_of_mem_left (hsimA.1.vertex_subset v hva hxA) hlB₂.left_mem
          · have hvb : v ∈ V(B₁.G) := hmem_VB₁ hv hva
            constructor
            · intro hloop
              exfalso
              exact hdisj_E₁.notMem_of_mem_left hea (hincB₁ hloop.inc_left hvb).1
            · intro hall
              exfalso
              have heA₂ := hsimA.1.edge_mem e hea
              obtain ⟨x, y, hlA₂⟩ := exists_isLink_of_mem_edgeSet heA₂
              have hxB : x ∈ ηvB v := hall x (hlA₂.mono hle_A₂).inc_left
              exact hdisj_V₂.notMem_of_mem_left hlA₂.left_mem (hsimB.1.vertex_subset v hvb hxB)
          · have hvb : v ∈ V(B₁.G) := hmem_VB₁ hv hva
            have heb : e ∈ E(B₁.G) := hmem_EB₁ he hea
            rw [← hle_B₁.isLoopAt_congr heb, hsimB.1.isLoopAt_iff v hvb e heb]
            have heB₂ := hsimB.1.edge_mem e heb
            refine forall_congr' fun x => imp_congr_left ?_
            exact hle_B₂.inc_congr heB₂
        connected := fun v hv => by
          dsimp [ηv]
          split_ifs with hva
          · obtain ⟨K, hK_le, hK_V, hK_conn⟩ := hsimA.1.connected v hva
            refine ⟨K, ⟨(hK_le.trans deleteEdges_le).vertexSet_mono.trans hVA₂_sub, ?_⟩,
              hK_V, hK_conn⟩
            intro e x y hlK
            have hlA := hlK.mono hK_le
            rw [deleteEdges_isLink] at hlA ⊢
            refine ⟨hlA.1.mono hle_A₂, ?_⟩
            rintro ⟨e₀, he₀, rfl⟩
            by_cases hea₀ : e₀ ∈ E(A₁.G)
            · simp only [ηe, hea₀, ↓reduceIte] at hlA
              exact hlA.2 ⟨e₀, hea₀, rfl⟩
            · simp only [ηe, hea₀, ↓reduceIte] at hlA
              have heb₀ : e₀ ∈ E(B₁.G) := hmem_EB₁ he₀ hea₀
              exact hdisj_E₂.notMem_of_mem_left hlA.1.edge_mem (hsimB.1.edge_mem e₀ heb₀)
          · have hvb : v ∈ V(B₁.G) := hmem_VB₁ hv hva
            obtain ⟨K, hK_le, hK_V, hK_conn⟩ := hsimB.1.connected v hvb
            refine ⟨K, ⟨(hK_le.trans deleteEdges_le).vertexSet_mono.trans hle_B₂.vertexSet_mono, ?_⟩,
              hK_V, hK_conn⟩
            intro e x y hlK
            have hlB := hlK.mono hK_le
            rw [deleteEdges_isLink] at hlB ⊢
            refine ⟨hlB.1.mono hle_B₂, ?_⟩
            rintro ⟨e₀, he₀, rfl⟩
            by_cases hea₀ : e₀ ∈ E(A₁.G)
            · simp only [ηe, hea₀, ↓reduceIte] at hlB
              exact hdisj_E₂.notMem_of_mem_left (hsimA.1.edge_mem e₀ hea₀) hlB.1.edge_mem
            · simp only [ηe, hea₀, ↓reduceIte] at hlB
              have heb₀ : e₀ ∈ E(B₁.G) := hmem_EB₁ he₀ hea₀
              exact hlB.2 ⟨e₀, heb₀, rfl⟩ }
  · rw [← hunion_T₂, ← hunion_T₁,
      ncard_union_eq hdisj_T₂ A₂.finite_T B₂.finite_T,
      ncard_union_eq hdisj_T₁ A₁.finite_T B₁.finite_T,
      hsimA.2.1, hsimB.2.1]
  · intro u hu
    dsimp [ηv]
    split_ifs with hua
    · have huA₁ : u ∈ A₁.T := by rw [hAT₁]; exact ⟨hu, hua⟩
      obtain ⟨x, hx_eta, hx_T⟩ := hsimA.2.2 u huA₁
      exact ⟨x, hx_eta, hunion_T₂ ▸ Or.inl hx_T⟩
    · have huB₁ : u ∈ B₁.T := by rw [hBT₁]; exact ⟨hu, hua⟩
      obtain ⟨x, hx_eta, hx_T⟩ := hsimB.2.2 u huB₁
      exact ⟨x, hx_eta, hunion_T₂ ▸ Or.inr hx_T⟩

/-- **Graph Minors VIII, (13.1)** (page 274):
"(13.1) *If* $\mathscr{A}, \mathscr{B}$ *are well-rooted then so is* $\mathscr{A} \oplus \mathscr{B}$." -/
theorem theorem_13_1_proof {α : Type u} {β : Type v}
    {𝒜 ℬ : Set (Graft α β)}
    (h𝒜 : IsWellRootedGraftClass 𝒜) (hℬ : IsWellRootedGraftClass ℬ) :
    IsWellRootedGraftClass (graftDirectSumClass 𝒜 ℬ) := by
  intro C hC
  choose A hA_mem B hB_mem hsum using hC
  let A_sub := {X : Graft α β | X ∈ 𝒜}
  let B_sub := {X : Graft α β | X ∈ ℬ}
  have hWQO_A : IsWellQuasiOrder (fun (X₁ X₂ : A_sub) => IsGraftSimulatedIn X₁.1 X₂.1) := by
    refine ⟨⟨fun X => IsGraftSimulatedIn.refl X.1, fun _ _ _ => IsGraftSimulatedIn.trans⟩, ?_⟩
    intro q
    exact h𝒜 (fun n => (q n).1) (fun n => (q n).2)
  have hWQO_B : IsWellQuasiOrder (fun (X₁ X₂ : B_sub) => IsGraftSimulatedIn X₁.1 X₂.1) := by
    refine ⟨⟨fun X => IsGraftSimulatedIn.refl X.1, fun _ _ _ => IsGraftSimulatedIn.trans⟩, ?_⟩
    intro q
    exact hℬ (fun n => (q n).1) (fun n => (q n).2)
  have hWQO_prod := theorem_3_2_proof hWQO_A hWQO_B
  obtain ⟨i, j, hij, hsimA, hsimB⟩ := hWQO_prod.2
    (fun n => (⟨A n, hA_mem n⟩, ⟨B n, hB_mem n⟩))
  exact ⟨i, j, hij, isGraftSimulatedIn_of_isGraftDirectSum (hsum i) (hsum j) hsimA hsimB⟩

/-! ## Vertex identification and (13.2), (13.3) -/

@[simp]
theorem identifyVerticesFun_left {α : Type u} (t₁ t₂ t : α) :
    identifyVerticesFun t₁ t₂ t t₁ = t := by
  simp [identifyVerticesFun]

@[simp]
theorem identifyVerticesFun_right {α : Type u} (t₁ t₂ t : α) :
    identifyVerticesFun t₁ t₂ t t₂ = t := by
  simp [identifyVerticesFun]

theorem identifyVerticesFun_of_ne {α : Type u} {t₁ t₂ t v : α}
    (hv₁ : v ≠ t₁) (hv₂ : v ≠ t₂) :
    identifyVerticesFun t₁ t₂ t v = v := by
  simp [identifyVerticesFun, hv₁, hv₂]

theorem identifyVerticesFun_eq_self_iff {α : Type u} {V : Set α} {t₁ t₂ t v : α}
    (hv : v ∈ V) (ht : t ∉ V \ {t₁, t₂}) :
    identifyVerticesFun t₁ t₂ t v = t ↔ v = t₁ ∨ v = t₂ := by
  constructor
  · intro heq
    by_contra hne
    rw [not_or] at hne
    rw [identifyVerticesFun_of_ne hne.1 hne.2] at heq
    exact ht ⟨heq ▸ hv, by simp [heq ▸ hne.1, heq ▸ hne.2]⟩
  · rintro (rfl | rfl) <;> simp

theorem identifyVerticesFun_eq_iff_of_mem {α : Type u} {V : Set α} {t₁ t₂ t x y : α}
    (hx : x ∈ V) (hy : y ∈ V) (ht : t ∉ V \ {t₁, t₂}) :
    identifyVerticesFun t₁ t₂ t x = identifyVerticesFun t₁ t₂ t y ↔
      x = y ∨ ((x = t₁ ∨ x = t₂) ∧ (y = t₁ ∨ y = t₂)) := by
  constructor
  · intro heq
    by_cases hx_t : x = t₁ ∨ x = t₂
    · right
      refine ⟨hx_t, ?_⟩
      have hxt : identifyVerticesFun t₁ t₂ t x = t :=
        (identifyVerticesFun_eq_self_iff hx ht).mpr hx_t
      exact (identifyVerticesFun_eq_self_iff hy ht).mp (heq.symm.trans hxt)
    · left
      have hy_t : ¬ (y = t₁ ∨ y = t₂) := by
        intro hyt
        have hyt' : identifyVerticesFun t₁ t₂ t y = t :=
          (identifyVerticesFun_eq_self_iff hy ht).mpr hyt
        exact hx_t ((identifyVerticesFun_eq_self_iff hx ht).mp (heq.trans hyt'))
      rw [not_or] at hx_t hy_t
      rwa [identifyVerticesFun_of_ne hx_t.1 hx_t.2,
        identifyVerticesFun_of_ne hy_t.1 hy_t.2] at heq
  · rintro (rfl | ⟨hx_t, hy_t⟩)
    · rfl
    · rw [(identifyVerticesFun_eq_self_iff hx ht).mpr hx_t,
        (identifyVerticesFun_eq_self_iff hy ht).mpr hy_t]

/-- Mapping a connected graph along any vertex function `f` yields a connected graph. -/
theorem graphConnected_map {α : Type u} {β : Type v} {K : Graph α β}
    (f : α → α) (hK : GraphConnected K) :
    GraphConnected (K.map f) := by
  obtain ⟨⟨x₀, hx₀⟩, hwalk⟩ := hK
  refine ⟨⟨f x₀, mem_image_of_mem f hx₀⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  have hxy := hwalk x hx y hy
  clear hx hy
  induction hxy with
  | refl => exact .refl
  | tail _ hadj ih => exact ih.tail (hadj.map f)

/-- If $K_1, K_2 \le D$ are connected subgraphs of $D$ whose vertex sets share a vertex $u_0$, then
the induced-and-restricted union subgraph on $V(K_1) \cup V(K_2)$ with edges $E(K_1) \cup E(K_2)$ is
a connected subgraph of $D$ with vertex set $V(K_1) \cup V(K_2)$. -/
theorem exists_connected_union_of_inter_nonempty {α : Type u} {β : Type v}
    {D K₁ K₂ : Graph α β} {u₀ : α}
    (hK₁_le : K₁ ≤ D) (hK₂_le : K₂ ≤ D)
    (hK₁_conn : GraphConnected K₁) (hK₂_conn : GraphConnected K₂)
    (hu₁ : u₀ ∈ V(K₁)) (hu₂ : u₀ ∈ V(K₂)) :
    ∃ K ≤ D, V(K) = V(K₁) ∪ V(K₂) ∧ GraphConnected K := by
  let K : Graph α β := (D.induce (V(K₁) ∪ V(K₂))).restrict (E(K₁) ∪ E(K₂))
  have hK_le : K ≤ D :=
    restrict_le.trans (D.induce_le (union_subset hK₁_le.vertexSet_mono hK₂_le.vertexSet_mono))
  have hK₁_sub : K₁ ≤ K := by
    refine ⟨subset_union_left, fun e x y hl => ?_⟩
    exact ⟨Or.inl hl.edge_mem, hl.mono hK₁_le, Or.inl hl.left_mem, Or.inl hl.right_mem⟩
  have hK₂_sub : K₂ ≤ K := by
    refine ⟨subset_union_right, fun e x y hl => ?_⟩
    exact ⟨Or.inr hl.edge_mem, hl.mono hK₂_le, Or.inr hl.left_mem, Or.inr hl.right_mem⟩
  have hwalk₁ : ∀ {x y}, x ∈ V(K₁) → y ∈ V(K₁) → ReflTransGen K.Adj x y := by
    intro x y hx hy
    have h := hK₁_conn.2 x hx y hy
    clear hx hy
    induction h with
    | refl => exact .refl
    | tail _ hadj ih => exact ih.tail (hadj.mono hK₁_sub)
  have hwalk₂ : ∀ {x y}, x ∈ V(K₂) → y ∈ V(K₂) → ReflTransGen K.Adj x y := by
    intro x y hx hy
    have h := hK₂_conn.2 x hx y hy
    clear hx hy
    induction h with
    | refl => exact .refl
    | tail _ hadj ih => exact ih.tail (hadj.mono hK₂_sub)
  refine ⟨K, hK_le, rfl, ⟨u₀, Or.inl hu₁⟩, ?_⟩
  rintro x (hx₁ | hx₂) y (hy₁ | hy₂)
  · exact hwalk₁ hx₁ hy₁
  · exact (hwalk₁ hx₁ hu₁).trans (hwalk₂ hu₂ hy₂)
  · exact (hwalk₂ hx₂ hu₂).trans (hwalk₁ hu₁ hy₁)
  · exact hwalk₂ hx₂ hy₂

/-- Key simulation step in the proof of (13.2) (pages 274–275): if $(H_1, U_1)$ is obtained from
$(G_1, T_1)$ by identifying $t_{1,1}, t_{1,2} \in T_1$ into $u_1$, and $(H_2, U_2)$ is obtained from
$(G_2, T_2)$ by identifying $t_{2,1}, t_{2,2} \in T_2$ into $u_2$ (with the same choice of whether
$u_m \in U_m$), and $(G_1, \tau_1)$ is simulated in $(G_2, \tau_2)$ where $\tau_m$ starts with
$t_{m,1}, t_{m,2}$ and enumerates $T_m$, then $(H_1, U_1)$ is simulated in $(H_2, U_2)$. -/
theorem isGraftSimulatedIn_of_rootedGraphSimulation_identify {α : Type u} {β : Type v}
    {X₁ Y₁ X₂ Y₂ : Graft α β}
    {t₁₁ t₁₂ u₁ t₂₁ t₂₂ u₂ : α} {L₁ L₂ : List α}
    (ht₁₁ : t₁₁ ∈ X₁.T) (ht₁₂ : t₁₂ ∈ X₁.T) (hne₁ : t₁₁ ≠ t₁₂)
    (hu₁ : u₁ ∉ V(X₁.G) \ {t₁₁, t₁₂})
    (hY₁G : Y₁.G = X₁.G.map (identifyVerticesFun t₁₁ t₁₂ u₁))
    (ht₂₁ : t₂₁ ∈ X₂.T) (ht₂₂ : t₂₂ ∈ X₂.T) (hne₂ : t₂₁ ≠ t₂₂)
    (hu₂ : u₂ ∉ V(X₂.G) \ {t₂₁, t₂₂})
    (hY₂G : Y₂.G = X₂.G.map (identifyVerticesFun t₂₁ t₂₂ u₂))
    (hT_choice : (Y₁.T = X₁.T \ {t₁₁, t₁₂} ∧ Y₂.T = X₂.T \ {t₂₁, t₂₂}) ∨
      (Y₁.T = (X₁.T \ {t₁₁, t₁₂}) ∪ {u₁} ∧ Y₂.T = (X₂.T \ {t₂₁, t₂₂}) ∪ {u₂}))
    {R₁ R₂ : RootedGraph α β}
    (hR₁G : R₁.G = X₁.G) (hR₁τ : R₁.τ = t₁₁ :: t₁₂ :: L₁) (hR₁T : R₁.toGraft.T = X₁.T)
    (hR₁_nodup : R₁.τ.Nodup)
    (hR₂G : R₂.G = X₂.G) (hR₂τ : R₂.τ = t₂₁ :: t₂₂ :: L₂) (hR₂T : R₂.toGraft.T = X₂.T)
    (hR₂_nodup : R₂.τ.Nodup)
    (hsimR : IsRootedGraphSimulatedIn R₁ R₂) :
    IsGraftSimulatedIn Y₁ Y₂ := by
  classical
  obtain ⟨ηv, ηe, hmodel, hlen, hτ_mem, hτ_eq⟩ := hsimR
  rw [hR₁G, hR₂G] at hmodel
  let π₁ := identifyVerticesFun t₁₁ t₁₂ u₁
  let π₂ := identifyVerticesFun t₂₁ t₂₂ u₂
  have hlen₂ : 2 ≤ R₂.τ.length := by simp [hR₂τ]
  have h0_mem : t₂₁ ∈ ηv t₁₁ := by
    have h := hτ_mem ⟨0, by omega⟩
    simpa [hR₁τ, hR₂τ] using h
  have h1_mem : t₂₂ ∈ ηv t₁₂ := by
    have h := hτ_mem ⟨1, by omega⟩
    simpa [hR₁τ, hR₂τ] using h
  have ht₁₁V : t₁₁ ∈ V(X₁.G) := X₁.T_subset ht₁₁
  have ht₁₂V : t₁₂ ∈ V(X₁.G) := X₁.T_subset ht₁₂
  have ht₂₁V : t₂₁ ∈ V(X₂.G) := X₂.T_subset ht₂₁
  have ht₂₂V : t₂₂ ∈ V(X₂.G) := X₂.T_subset ht₂₂
  -- Key separation property: π₂ maps z ∈ ηv v₁ and z' ∈ ηv v₂ to the same vertex in Y₂.G
  -- only when π₁ v₁ = π₁ v₂.
  have hπ_compat : ∀ {v₁ v₂ : α}, v₁ ∈ V(X₁.G) → v₂ ∈ V(X₁.G) →
      ∀ {z₁ z₂ : α}, z₁ ∈ ηv v₁ → z₂ ∈ ηv v₂ → π₂ z₁ = π₂ z₂ → π₁ v₁ = π₁ v₂ := by
    intro v₁ v₂ hv₁ hv₂ z₁ z₂ hz₁ hz₂ heq
    have hz₁V : z₁ ∈ V(X₂.G) := hmodel.vertex_subset v₁ hv₁ hz₁
    have hz₂V : z₂ ∈ V(X₂.G) := hmodel.vertex_subset v₂ hv₂ hz₂
    have hiff := (identifyVerticesFun_eq_iff_of_mem hz₁V hz₂V hu₂).mp heq
    have hv_of_zt : ∀ {v z}, v ∈ V(X₁.G) → z ∈ ηv v → (z = t₂₁ ∨ z = t₂₂) →
        (v = t₁₁ ∨ v = t₁₂) := by
      intro v z hv hz hzt
      rcases hzt with rfl | rfl
      · left
        by_contra hne
        exact (hmodel.vertex_disjoint v hv t₁₁ ht₁₁V hne).notMem_of_mem_left hz h0_mem
      · right
        by_contra hne
        exact (hmodel.vertex_disjoint v hv t₁₂ ht₁₂V hne).notMem_of_mem_left hz h1_mem
    rcases hiff with rfl | ⟨hz₁_t, hz₂_t⟩
    · have hv_eq : v₁ = v₂ := by
        by_contra hne
        exact (hmodel.vertex_disjoint v₁ hv₁ v₂ hv₂ hne).notMem_of_mem_left hz₁ hz₂
      rw [hv_eq]
    · exact (identifyVerticesFun_eq_iff_of_mem hv₁ hv₂ hu₁).mpr
        (Or.inr ⟨hv_of_zt hv₁ hz₁ hz₁_t, hv_of_zt hv₂ hz₂ hz₂_t⟩)
  let ηv' : α → Set α := fun w => ⋃ (v ∈ V(X₁.G)) (_ : π₁ v = w), π₂ '' ηv v
  have hmem_ηv' : ∀ {w x : α}, x ∈ ηv' w ↔
      ∃ v ∈ V(X₁.G), π₁ v = w ∧ ∃ z ∈ ηv v, π₂ z = x := by
    intro w x
    simp only [ηv', mem_iUnion, mem_image, exists_prop]
  -- Also, map and deleteEdges commute:
  have hmap_del : ∀ (G : Graph α β) (f : α → α) (F : Set β),
      (G.map f).deleteEdges F = (G.deleteEdges F).map f := by
    intro G f F
    ext a b c
    · simp
    · simp only [deleteEdges_isLink, map_isLink, Relation.Map]
      exact ⟨fun ⟨⟨x, y, hl, hx, hy⟩, ha⟩ => ⟨x, y, ⟨hl, ha⟩, hx, hy⟩,
        fun ⟨x, y, ⟨hl, ha⟩, hx, hy⟩ => ⟨⟨x, y, hl, hx, hy⟩, ha⟩⟩
  have hmodel' : IsGraphSimulation Y₁.G Y₂.G ηv' ηe := by
    rw [hY₁G, hY₂G]
    refine
      { vertex_nonempty := fun w hw => by
          obtain ⟨v, hv, rfl⟩ := hw
          obtain ⟨z, hz⟩ := hmodel.vertex_nonempty v hv
          exact ⟨π₂ z, hmem_ηv'.mpr ⟨v, hv, rfl, z, hz, rfl⟩⟩
        vertex_subset := fun w _ x hx => by
          obtain ⟨v, hv, _, z, hz, rfl⟩ := hmem_ηv'.mp hx
          exact mem_image_of_mem π₂ (hmodel.vertex_subset v hv hz)
        edge_mem := fun e he => hmodel.edge_mem e he
        vertex_disjoint := fun w₁ _ w₂ _ hne => by
          rw [disjoint_left]
          intro x hx₁ hx₂
          obtain ⟨v₁, hv₁, rfl, z₁, hz₁, rfl⟩ := hmem_ηv'.mp hx₁
          obtain ⟨v₂, hv₂, rfl, z₂, hz₂, heq⟩ := hmem_ηv'.mp hx₂
          exact hne (hπ_compat hv₁ hv₂ hz₁ hz₂ heq.symm)
        edge_injOn := hmodel.edge_injOn
        inc_iff := fun w hw e he => by
          have heX₁ : e ∈ E(X₁.G) := he
          constructor
          · intro hinc
            rw [map_inc] at hinc
            obtain ⟨v, hinc_v, rfl⟩ := hinc
            have hv : v ∈ V(X₁.G) := hinc_v.vertex_mem
            obtain ⟨z, hz, hinc_z⟩ := (hmodel.inc_iff v hv e heX₁).mp hinc_v
            exact ⟨π₂ z, hmem_ηv'.mpr ⟨v, hv, rfl, z, hz, rfl⟩, hinc_z.map π₂⟩
          · rintro ⟨x, hx, hinc⟩
            obtain ⟨v, hv, rfl, z, hz, rfl⟩ := hmem_ηv'.mp hx
            rw [map_inc] at hinc
            obtain ⟨z', hinc_z', heq⟩ := hinc
            obtain ⟨v₁, v₂, hl₁⟩ := exists_isLink_of_mem_edgeSet heX₁
            have hz'_mem : ∃ v' ∈ V(X₁.G), X₁.G.Inc e v' ∧ z' ∈ ηv v' := by
              by_cases hloop : X₁.G.IsLoopAt e v₁
              · exact ⟨v₁, hl₁.left_mem, hl₁.inc_left,
                  (hmodel.isLoopAt_iff v₁ hl₁.left_mem e heX₁).mp hloop z' hinc_z'⟩
              · have hne_v : v₁ ≠ v₂ := fun h => hloop (h ▸ hl₁)
                obtain ⟨a₁, ha₁, a₂, hl₂⟩ :=
                  (hmodel.inc_iff v₁ hl₁.left_mem e heX₁).mp hl₁.inc_left
                obtain ⟨b₁, hb₁, hinc_b₁⟩ :=
                  (hmodel.inc_iff v₂ hl₁.right_mem e heX₁).mp hl₁.inc_right
                have hab_ne : a₁ ≠ b₁ :=
                  (hmodel.vertex_disjoint v₁ hl₁.left_mem v₂ hl₁.right_mem hne_v).ne_of_mem ha₁ hb₁
                have hb₁a₂ : b₁ = a₂ := hinc_b₁.eq_of_isLink_of_ne_left hl₂ hab_ne.symm
                rcases hinc_z'.eq_or_eq_of_isLink hl₂ with rfl | rfl
                · exact ⟨v₁, hl₁.left_mem, hl₁.inc_left, ha₁⟩
                · exact ⟨v₂, hl₁.right_mem, hl₁.inc_right, hb₁a₂ ▸ hb₁⟩
            obtain ⟨v', hv', hinc_v', hz'v'⟩ := hz'_mem
            have hπ_eq : π₁ v = π₁ v' := hπ_compat hv hv' hz hz'v' heq
            rw [hπ_eq]
            exact hinc_v'.map π₁
        isLoopAt_iff := fun w hw e he => by
          have heX₁ : e ∈ E(X₁.G) := he
          constructor
          · intro hloop x hinc
            rw [map_isLoopAt] at hloop
            obtain ⟨v₁, v₂, hl₁, hv₁_eq, hv₂_eq⟩ := hloop
            rw [map_inc] at hinc
            obtain ⟨z, hinc_z, rfl⟩ := hinc
            by_cases hloop₁ : X₁.G.IsLoopAt e v₁
            · have hz : z ∈ ηv v₁ :=
                (hmodel.isLoopAt_iff v₁ hl₁.left_mem e heX₁).mp hloop₁ z hinc_z
              exact hmem_ηv'.mpr ⟨v₁, hl₁.left_mem, hv₁_eq, z, hz, rfl⟩
            · have hne_v : v₁ ≠ v₂ := fun h => hloop₁ (h ▸ hl₁)
              obtain ⟨a₁, ha₁, a₂, hl₂⟩ :=
                (hmodel.inc_iff v₁ hl₁.left_mem e heX₁).mp hl₁.inc_left
              obtain ⟨b₁, hb₁, hinc_b₁⟩ :=
                (hmodel.inc_iff v₂ hl₁.right_mem e heX₁).mp hl₁.inc_right
              have hab_ne : a₁ ≠ b₁ :=
                (hmodel.vertex_disjoint v₁ hl₁.left_mem v₂ hl₁.right_mem hne_v).ne_of_mem ha₁ hb₁
              have hb₁a₂ : b₁ = a₂ := hinc_b₁.eq_of_isLink_of_ne_left hl₂ hab_ne.symm
              rcases hinc_z.eq_or_eq_of_isLink hl₂ with hza₁ | hza₂
              · subst hza₁
                exact hmem_ηv'.mpr ⟨v₁, hl₁.left_mem, hv₁_eq, z, ha₁, rfl⟩
              · subst hza₂
                exact hmem_ηv'.mpr ⟨v₂, hl₁.right_mem, hv₂_eq, z, hb₁a₂ ▸ hb₁, rfl⟩
          · intro hall
            obtain ⟨v₁, v₂, hl₁⟩ := exists_isLink_of_mem_edgeSet heX₁
            obtain ⟨z₁, hz₁, hinc₁⟩ := (hmodel.inc_iff v₁ hl₁.left_mem e heX₁).mp hl₁.inc_left
            obtain ⟨z₂, hz₂, hinc₂⟩ := (hmodel.inc_iff v₂ hl₁.right_mem e heX₁).mp hl₁.inc_right
            have hx₁ := hall (π₂ z₁) (hinc₁.map π₂)
            have hx₂ := hall (π₂ z₂) (hinc₂.map π₂)
            obtain ⟨u₁', hu₁', hu₁'_eq, w₁, hw₁, hw₁_eq⟩ := hmem_ηv'.mp hx₁
            obtain ⟨u₂', hu₂', hu₂'_eq, w₂, hw₂, hw₂_eq⟩ := hmem_ηv'.mp hx₂
            have hπv₁ : π₁ v₁ = w := (hπ_compat hl₁.left_mem hu₁' hz₁ hw₁ hw₁_eq.symm).trans hu₁'_eq
            have hπv₂ : π₁ v₂ = w := (hπ_compat hl₁.right_mem hu₂' hz₂ hw₂ hw₂_eq.symm).trans hu₂'_eq
            rw [map_isLoopAt]
            exact ⟨v₁, v₂, hl₁, hπv₁, hπv₂⟩
        connected := fun w hw => by
          obtain ⟨v₀, hv₀, rfl⟩ := hw
          by_cases hvt : v₀ = t₁₁ ∨ v₀ = t₁₂
          · have hπv₀ : π₁ v₀ = u₁ := (identifyVerticesFun_eq_self_iff hv₀ hu₁).mpr hvt
            obtain ⟨K₁, hK₁_le, hK₁_V, hK₁_conn⟩ := hmodel.connected t₁₁ ht₁₁V
            obtain ⟨K₂, hK₂_le, hK₂_V, hK₂_conn⟩ := hmodel.connected t₁₂ ht₁₂V
            let D := (X₂.G.map π₂).deleteEdges (ηe '' E(X₁.G.map π₁))
            have hK₁_map_le : K₁.map π₂ ≤ D := by
              show K₁.map π₂ ≤ (X₂.G.map π₂).deleteEdges (ηe '' E(X₁.G.map π₁))
              rw [edgeSet_map, hmap_del]
              exact hK₁_le.map π₂
            have hK₂_map_le : K₂.map π₂ ≤ D := by
              show K₂.map π₂ ≤ (X₂.G.map π₂).deleteEdges (ηe '' E(X₁.G.map π₁))
              rw [edgeSet_map, hmap_del]
              exact hK₂_le.map π₂
            have hu₂_K₁ : u₂ ∈ V(K₁.map π₂) := by
              rw [vertexSet_map, hK₁_V]
              exact ⟨t₂₁, h0_mem, identifyVerticesFun_left t₂₁ t₂₂ u₂⟩
            have hu₂_K₂ : u₂ ∈ V(K₂.map π₂) := by
              rw [vertexSet_map, hK₂_V]
              exact ⟨t₂₂, h1_mem, identifyVerticesFun_right t₂₁ t₂₂ u₂⟩
            obtain ⟨K, hK_le, hK_V, hK_conn⟩ := exists_connected_union_of_inter_nonempty
              hK₁_map_le hK₂_map_le
              (graphConnected_map π₂ hK₁_conn) (graphConnected_map π₂ hK₂_conn)
              hu₂_K₁ hu₂_K₂
            refine ⟨K, hK_le, ?_, hK_conn⟩
            change V(K) = ηv' (π₁ v₀)
            rw [hK_V, vertexSet_map, vertexSet_map, hK₁_V, hK₂_V, hπv₀]
            ext x
            rw [mem_union, hmem_ηv']
            constructor
            · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
              · exact ⟨t₁₁, ht₁₁V, identifyVerticesFun_left t₁₁ t₁₂ u₁, z, hz, rfl⟩
              · exact ⟨t₁₂, ht₁₂V, identifyVerticesFun_right t₁₁ t₁₂ u₁, z, hz, rfl⟩
            · rintro ⟨v, hv, hπv, z, hz, rfl⟩
              rcases (identifyVerticesFun_eq_self_iff hv hu₁).mp hπv with rfl | rfl
              · exact Or.inl ⟨z, hz, rfl⟩
              · exact Or.inr ⟨z, hz, rfl⟩
          · obtain ⟨K₀, hK₀_le, hK₀_V, hK₀_conn⟩ := hmodel.connected v₀ hv₀
            refine ⟨K₀.map π₂, ?_, ?_, graphConnected_map π₂ hK₀_conn⟩
            · rw [edgeSet_map, hmap_del]
              exact hK₀_le.map π₂
            · change V(K₀.map π₂) = ηv' (π₁ v₀)
              rw [vertexSet_map, hK₀_V]
              ext x
              rw [mem_image, hmem_ηv']
              constructor
              · rintro ⟨z, hz, rfl⟩
                exact ⟨v₀, hv₀, rfl, z, hz, rfl⟩
              · rintro ⟨v, hv, hπv, z, hz, rfl⟩
                have hv_eq : v = v₀ := by
                  rcases (identifyVerticesFun_eq_iff_of_mem hv hv₀ hu₁).mp hπv with rfl | ⟨_, h⟩
                  · rfl
                  · exact False.elim (hvt h)
                subst hv_eq
                exact ⟨z, hz, rfl⟩ }
  -- Now verify condition (S6): |Y₂.T| = |Y₁.T| and every root of Y₁.T meets ηv' in Y₂.T.
  have hncard_τ : ∀ (R : RootedGraph α β) (X : Graft α β),
      R.toGraft.T = X.T → R.τ.Nodup → X.T.ncard = R.τ.length := by
    intro R X hRT hnd
    have hfin_eq : (R.τ.toFinset : Set α) = X.T := by
      rw [← hRT]
      ext x
      simp [RootedGraph.toGraft]
    rw [← hfin_eq, ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  have hcard_X : X₂.T.ncard = X₁.T.ncard := by
    rw [hncard_τ R₂ X₂ hR₂T hR₂_nodup, hncard_τ R₁ X₁ hR₁T hR₁_nodup, hlen]
  have hcard_diff : ∀ (X : Graft α β) {t₁ t₂ : α},
      t₁ ∈ X.T → t₂ ∈ X.T → t₁ ≠ t₂ →
      (X.T \ {t₁, t₂}).ncard + 2 = X.T.ncard := by
    intro X t₁ t₂ ht₁ ht₂ hne
    have hsub : ({t₁, t₂} : Set α) ⊆ X.T := by
      rintro x (rfl | rfl) <;> assumption
    have hpair : ({t₁, t₂} : Set α).ncard = 2 := ncard_pair hne
    have h := ncard_sdiff_add_ncard_of_subset hsub X.finite_T
    omega
  have hcard_sdiff_eq : (X₂.T \ {t₂₁, t₂₂}).ncard = (X₁.T \ {t₁₁, t₁₂}).ncard := by
    have h₁ := hcard_diff X₁ ht₁₁ ht₁₂ hne₁
    have h₂ := hcard_diff X₂ ht₂₁ ht₂₂ hne₂
    omega
  have hu₁_notMem : u₁ ∉ X₁.T \ {t₁₁, t₁₂} :=
    fun h => hu₁ ⟨X₁.T_subset h.1, h.2⟩
  have hu₂_notMem : u₂ ∉ X₂.T \ {t₂₁, t₂₂} :=
    fun h => hu₂ ⟨X₂.T_subset h.1, h.2⟩
  have hroot_other : ∀ w ∈ X₁.T \ {t₁₁, t₁₂},
      ∃ y ∈ X₂.T \ {t₂₁, t₂₂}, y ∈ ηv' w := by
    intro w ⟨hwT, hw_ne⟩
    have hw_mem_τ : w ∈ R₁.τ := by
      have : w ∈ R₁.toGraft.T := hR₁T.symm ▸ hwT
      exact this
    obtain ⟨idx₁, hidx₁_lt, rfl⟩ := List.getElem_of_mem hw_mem_τ
    let idx₂ : Fin R₂.τ.length := ⟨idx₁, hlen.symm ▸ hidx₁_lt⟩
    let idx0 : Fin R₂.τ.length := ⟨0, by omega⟩
    let idx1 : Fin R₂.τ.length := ⟨1, by omega⟩
    let y := R₂.τ[idx₂]
    have hy_T : y ∈ X₂.T := by
      rw [← hR₂T]
      exact List.getElem_mem _
    have hy_ne₁ : y ≠ t₂₁ := by
      intro heq
      have h0 : R₂.τ[idx0] = t₂₁ := by simp [idx0, hR₂τ]
      have h0' : R₁.τ[idx0.cast hlen] = t₁₁ := by simp [idx0, hR₁τ]
      have := (hτ_eq idx₂ idx0).mp (heq.trans h0.symm)
      exact hw_ne (Or.inl (this.trans h0'))
    have hy_ne₂ : y ≠ t₂₂ := by
      intro heq
      have h1 : R₂.τ[idx1] = t₂₂ := by simp [idx1, hR₂τ]
      have h1' : R₁.τ[idx1.cast hlen] = t₁₂ := by simp [idx1, hR₁τ]
      have := (hτ_eq idx₂ idx1).mp (heq.trans h1.symm)
      exact hw_ne (Or.inr (this.trans h1'))
    refine ⟨y, ⟨hy_T, by simp [hy_ne₁, hy_ne₂]⟩, ?_⟩
    rw [hmem_ηv']
    have hw_ne₁ : R₁.τ[idx₁] ≠ t₁₁ := fun h => hw_ne (Or.inl h)
    have hw_ne₂ : R₁.τ[idx₁] ≠ t₁₂ := fun h => hw_ne (Or.inr h)
    refine ⟨R₁.τ[idx₁], X₁.T_subset hwT, identifyVerticesFun_of_ne hw_ne₁ hw_ne₂,
      y, hτ_mem idx₂, identifyVerticesFun_of_ne hy_ne₁ hy_ne₂⟩
  refine ⟨ηv', ηe, hmodel', ?_, ?_⟩
  · rcases hT_choice with ⟨hY₁T, hY₂T⟩ | ⟨hY₁T, hY₂T⟩
    · rw [hY₁T, hY₂T, hcard_sdiff_eq]
    · rw [hY₁T, hY₂T, union_comm _ {u₁}, union_comm _ {u₂},
        ← insert_eq, ← insert_eq,
        ncard_insert_of_notMem hu₁_notMem (X₁.finite_T.subset sdiff_subset),
        ncard_insert_of_notMem hu₂_notMem (X₂.finite_T.subset sdiff_subset),
        hcard_sdiff_eq]
  · intro w hw
    rcases hT_choice with ⟨hY₁T, hY₂T⟩ | ⟨hY₁T, hY₂T⟩
    · rw [hY₁T] at hw
      obtain ⟨y, hy_diff, hy_eta⟩ := hroot_other w hw
      exact ⟨y, hy_eta, hY₂T ▸ hy_diff⟩
    · rw [hY₁T] at hw
      rcases hw with hw_diff | hw_eq
      · obtain ⟨y, hy_diff, hy_eta⟩ := hroot_other w hw_diff
        exact ⟨y, hy_eta, hY₂T ▸ Or.inl hy_diff⟩
      · rw [mem_singleton_iff] at hw_eq
        rw [hw_eq]
        refine ⟨u₂, ?_, hY₂T ▸ Or.inr rfl⟩
        rw [hmem_ηv']
        exact ⟨t₁₁, ht₁₁V, identifyVerticesFun_left t₁₁ t₁₂ u₁,
          t₂₁, h0_mem, identifyVerticesFun_left t₂₁ t₂₂ u₂⟩

/-- Extensionality for grafts: two grafts with the same underlying graph and root set are equal. -/
theorem Graft.ext {α : Type u} {β : Type v} {X Y : Graft α β}
    (hG : X.G = Y.G) (hT : X.T = Y.T) : X = Y := by
  cases X
  cases Y
  cases hG
  cases hT
  rfl

/-- Helper for extracting a strictly increasing sequence from an infinite set of naturals. -/
private theorem exists_strictMono_of_infinite {S : Set ℕ} (hS : S.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, φ n ∈ S := by
  have hex : ∀ m : ℕ, ∃ n, n ∈ S ∧ m < n := by
    intro m
    by_contra! hle
    exact hS ((Set.finite_le_nat m).subset hle)
  choose next hnext_mem hnext_lt using hex
  let φ : ℕ → ℕ := fun k => Nat.recOn k (next 0) (fun _ prev => next prev)
  refine ⟨φ, strictMono_nat_of_lt_succ (fun k => hnext_lt (φ k)), ?_⟩
  intro k
  induction k with
  | zero => exact hnext_mem 0
  | succ k _ => exact hnext_mem (φ k)

/-- **Graph Minors VIII, (13.2)** (page 274):
"(13.2) *If* $\mathscr{A}$ *is well-rooted, then the class of all grafts which can be obtained from
a member of* $\mathscr{A}$ *by a vertex identification is well-rooted*." -/
theorem theorem_13_2_proof {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (W1GraftClass 𝒜) := by
  classical
  intro H hH
  choose X hX_mem t₁ ht₁ t₂ ht₂ hne u hu hHG hHT using hH
  -- Build the rooted graph R n = (X n, t₁ n :: t₂ n :: L n) for each n:
  let L : ∀ n : ℕ, List α := fun n =>
    ((X n).finite_T.subset sdiff_subset : ((X n).T \ {t₁ n, t₂ n}).Finite).toFinset.toList
  have hL_mem : ∀ n x, x ∈ L n ↔ x ∈ (X n).T \ {t₁ n, t₂ n} := by
    intro n x
    simp [L]
  have hL_nodup : ∀ n, (L n).Nodup := fun n => Finset.nodup_toList _
  let R : ℕ → RootedGraph α β := fun n =>
    { G := (X n).G
      τ := t₁ n :: t₂ n :: L n
      τ_subset := by
        intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | rfl | hvL
        · exact (X n).T_subset (ht₁ n)
        · exact (X n).T_subset (ht₂ n)
        · exact (X n).T_subset ((hL_mem n v).mp hvL).1
      finite_G := (X n).finite_G }
  have hR_toGraft_T : ∀ n, (R n).toGraft.T = (X n).T := by
    intro n
    ext x
    simp only [RootedGraph.toGraft, R, mem_ofPred_eq, List.mem_cons, hL_mem]
    constructor
    · rintro (rfl | rfl | ⟨hxT, _⟩)
      · exact ht₁ n
      · exact ht₂ n
      · exact hxT
    · intro hxT
      by_cases hx₁ : x = t₁ n
      · exact Or.inl hx₁
      · by_cases hx₂ : x = t₂ n
        · exact Or.inr (Or.inl hx₂)
        · exact Or.inr (Or.inr ⟨hxT, by simp [hx₁, hx₂]⟩)
  have hR_toGraft_eq : ∀ n, (R n).toGraft = X n :=
    fun n => Graft.ext rfl (hR_toGraft_T n)
  have hR_nodup : ∀ n, (R n).τ.Nodup := by
    intro n
    dsimp [R]
    rw [List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, hL_nodup n⟩
    · simp only [List.mem_cons, hL_mem, not_or]
      exact ⟨hne n, fun h => h.2 (Or.inl rfl)⟩
    · rw [hL_mem]
      exact fun h => h.2 (Or.inr rfl)
  -- The class ℬ = range R has bounded index (by (4.1)) and underlying grafts in 𝒜:
  obtain ⟨K, hK⟩ := theorem_4_1_proof h𝒜
  have hB_idx : HasBoundedRootedGraphIndex (range R) := by
    refine ⟨K, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hlen_eq : (R n).index = (X n).index := by
      unfold RootedGraph.index Graft.index
      have hfin_eq : ((R n).τ.toFinset : Set α) = (X n).T := by
        rw [← hR_toGraft_T n]
        ext x
        simp [RootedGraph.toGraft]
      rw [← hfin_eq, ncard_coe_finset, List.toFinset_card_of_nodup (hR_nodup n)]
    rw [hlen_eq]
    exact hK (X n) (hX_mem n)
  have hB_graft : ∀ Z ∈ range R, Z.toGraft ∈ 𝒜 := by
    rintro _ ⟨n, rfl⟩
    rw [hR_toGraft_eq n]
    exact hX_mem n
  have hWQO_R := theorem_4_3_proof h𝒜 hB_idx hB_graft
  -- Pass to a subsequence where all n make the same choice of whether u n ∈ (H n).T:
  let S₁ : Set ℕ := {n | (H n).T = (X n).T \ {t₁ n, t₂ n}}
  let S₂ : Set ℕ := {n | (H n).T = ((X n).T \ {t₁ n, t₂ n}) ∪ {u n}}
  by_cases hinf₁ : S₁.Infinite
  · obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_of_infinite hinf₁
    obtain ⟨i, j, hij, hsimR⟩ := hWQO_R (fun k => R (φ k)) (fun k => ⟨φ k, rfl⟩)
    refine ⟨φ i, φ j, hφ_mono hij,
      isGraftSimulatedIn_of_rootedGraphSimulation_identify
        (ht₁ (φ i)) (ht₂ (φ i)) (hne (φ i)) (hu (φ i)) (hHG (φ i))
        (ht₁ (φ j)) (ht₂ (φ j)) (hne (φ j)) (hu (φ j)) (hHG (φ j))
        (Or.inl ⟨hφ_mem i, hφ_mem j⟩)
        rfl rfl (hR_toGraft_T (φ i)) (hR_nodup (φ i))
        rfl rfl (hR_toGraft_T (φ j)) (hR_nodup (φ j)) hsimR⟩
  · have hinf₂ : S₂.Infinite := by
      have huniv : S₁ ∪ S₂ = univ := by
        ext n
        exact ⟨fun _ => mem_univ n, fun _ => hHT n⟩
      have hfin₁ : S₁.Finite := Set.not_infinite.mp hinf₁
      intro hfin₂
      exact Set.infinite_univ (huniv ▸ hfin₁.union hfin₂)
    obtain ⟨φ, hφ_mono, hφ_mem⟩ := exists_strictMono_of_infinite hinf₂
    obtain ⟨i, j, hij, hsimR⟩ := hWQO_R (fun k => R (φ k)) (fun k => ⟨φ k, rfl⟩)
    refine ⟨φ i, φ j, hφ_mono hij,
      isGraftSimulatedIn_of_rootedGraphSimulation_identify
        (ht₁ (φ i)) (ht₂ (φ i)) (hne (φ i)) (hu (φ i)) (hHG (φ i))
        (ht₁ (φ j)) (ht₂ (φ j)) (hne (φ j)) (hu (φ j)) (hHG (φ j))
        (Or.inr ⟨hφ_mem i, hφ_mem j⟩)
        rfl rfl (hR_toGraft_T (φ i)) (hR_nodup (φ i))
        rfl rfl (hR_toGraft_T (φ j)) (hR_nodup (φ j)) hsimR⟩

/-- Vertex identification strictly decreases the graft index: if $Y$ is obtained from $X$ by a
vertex identification, then $2 \le X.\text{index}$ and $Y.\text{index} + 1 \le X.\text{index}$. -/
theorem index_lt_of_obtainedByVertexIdentification {α : Type u} {β : Type v}
    {X Y : Graft α β} (h : ObtainedByVertexIdentification X Y) :
    2 ≤ X.index ∧ Y.index + 1 ≤ X.index := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hne, t, ht, _, hYT⟩ := h
  unfold Graft.index
  have hsub : ({t₁, t₂} : Set α) ⊆ X.T := by
    rintro x (rfl | rfl) <;> assumption
  have hpair : ({t₁, t₂} : Set α).ncard = 2 := ncard_pair hne
  have hdiff := ncard_sdiff_add_ncard_of_subset hsub X.finite_T
  have ht_notMem : t ∉ X.T \ {t₁, t₂} := fun hmem => ht ⟨X.T_subset hmem.1, hmem.2⟩
  rcases hYT with hYT | hYT
  · rw [hYT]
    omega
  · rw [hYT, union_comm, ← insert_eq,
      ncard_insert_of_notMem ht_notMem (X.finite_T.subset sdiff_subset)]
    omega

/-- Shift identity for $W^i$: $W^{i+1}(\mathscr{A}) = W^i(W^1(\mathscr{A}))$. -/
theorem WiGraftClass_succ_eq {α : Type u} {β : Type v}
    (i : ℕ) (𝒜 : Set (Graft α β)) :
    WiGraftClass (i + 1) 𝒜 = WiGraftClass i (W1GraftClass 𝒜) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change W1GraftClass (WiGraftClass (i + 1) 𝒜) = W1GraftClass (WiGraftClass i (W1GraftClass 𝒜))
    rw [ih]

/-- Recursive decomposition $W(\mathscr{A}) = \mathscr{A} \cup W(W^1(\mathscr{A}))$ (page 275). -/
theorem WGraftClass_eq_union_W1 {α : Type u} {β : Type v} (𝒜 : Set (Graft α β)) :
    WGraftClass 𝒜 = 𝒜 ∪ WGraftClass (W1GraftClass 𝒜) := by
  ext Y
  simp only [WGraftClass, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | zero => exact Or.inl hi
    | succ i =>
      rw [WiGraftClass_succ_eq] at hi
      exact Or.inr ⟨i, hi⟩
  · rintro (h0 | ⟨i, hi⟩)
    · exact ⟨0, h0⟩
    · refine ⟨i + 1, ?_⟩
      rwa [WiGraftClass_succ_eq]

@[simp]
theorem W1GraftClass_empty {α : Type u} {β : Type v} :
    W1GraftClass (∅ : Set (Graft α β)) = ∅ := by
  ext Y
  simp [W1GraftClass]

@[simp]
theorem WiGraftClass_empty {α : Type u} {β : Type v} (i : ℕ) :
    WiGraftClass i (∅ : Set (Graft α β)) = ∅ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [WiGraftClass, ih, W1GraftClass_empty]

@[simp]
theorem WGraftClass_empty {α : Type u} {β : Type v} :
    WGraftClass (∅ : Set (Graft α β)) = ∅ := by
  ext Y
  simp [WGraftClass, WiGraftClass_empty]

/-- **Graph Minors VIII, (13.3)** (page 275):
"(13.3) *If $\mathcal{A}$ is well-rooted then so is $W(\mathcal{A})$.*" -/
theorem theorem_13_3_proof {α : Type u} {β : Type v}
    {𝒜 : Set (Graft α β)} (h𝒜 : IsWellRootedGraftClass 𝒜) :
    IsWellRootedGraftClass (WGraftClass 𝒜) := by
  obtain ⟨k, hk⟩ := theorem_4_1_proof h𝒜
  -- Follow the paper's induction on the index bound k of 𝒜:
  suffices hind : ∀ (k : ℕ) (𝒜 : Set (Graft α β)),
      IsWellRootedGraftClass 𝒜 → (∀ X ∈ 𝒜, X.index ≤ k) →
      IsWellRootedGraftClass (WGraftClass 𝒜) from hind k 𝒜 h𝒜 hk
  intro k
  induction k with
  | zero =>
    intro 𝒜 h𝒜 hk₀
    have hW1_empty : W1GraftClass 𝒜 = ∅ := by
      ext Y
      simp only [W1GraftClass, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
      intro X hX hXY
      have := (index_lt_of_obtainedByVertexIdentification hXY).1
      have := hk₀ X hX
      omega
    have hW_eq : WGraftClass 𝒜 = 𝒜 := by
      rw [WGraftClass_eq_union_W1, hW1_empty, WGraftClass_empty, union_empty]
    rwa [hW_eq]
  | succ k ih =>
    intro 𝒜 h𝒜 hk_succ
    have hW1_wqo : IsWellRootedGraftClass (W1GraftClass 𝒜) := theorem_13_2_proof h𝒜
    have hW1_idx : ∀ Y ∈ W1GraftClass 𝒜, Y.index ≤ k := by
      rintro Y ⟨X, hX, hXY⟩
      have hlt := (index_lt_of_obtainedByVertexIdentification hXY).2
      have hle := hk_succ X hX
      omega
    have hWW1_wqo : IsWellRootedGraftClass (WGraftClass (W1GraftClass 𝒜)) :=
      ih (W1GraftClass 𝒜) hW1_wqo hW1_idx
    rw [WGraftClass_eq_union_W1]
    exact theorem_4_2_proof h𝒜 hWW1_wqo

end GraphMinor.GM08

