module

public import GraphMinor.GM17.Section13d
public import GraphMinor.Surface.DrawCarry
public import GraphMinor.GM20.Draw8

import GraphMinor.GM17.Section8Proved

/-!
# Graph Minors XVII, (13.4)

(13.4) follows the paper's proof (page 207): a planar `H` is handled by (13.1) directly; otherwise
`a*`, `b*` are chosen with `2a* + b*` maximum such that `H` cannot be drawn in `Σ(a*, b*, 0)`, and
`q = 4a* + 2b* + q₀`. That maximum exists because `H` can be drawn in `Σ(a, b, c)` once `a` or `b` is
large (`GM20.Draw.exists_canBeDrawn`).
-/

public section

namespace GraphMinor.GM17

open Set Function Topology
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- Explicit `(p, q, z, θ)` bounds for Graph Minors XVII, (13.4), parameterized by `V` and `σM`. -/
@[expose] def theorem_13_4_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (σM : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (vB eB : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let res1 := theorem_13_1_bound V vB eB
  let p₀ := res1.1
  let q₀ := res1.2.1
  let z₀ := res1.2.2.1
  let θ₀ := res1.2.2.2
  let p := max p₀ 1
  let L := GM20.Draw.drawBound eB
  let q := 6 * L + q₀
  let res3 := theorem_13_3_bound σM p (q ^ 2 * p + q₀ * p) z₀
  (p, q, res3.2, max θ₀ res3.1)

/-- **Graph Minors XVII, (13.4)** (page 206), with explicit bounds `theorem_13_4_bound V σM vB eB`. -/
theorem theorem_13_4_explicit (V : ℕ → ℕ → ℕ → ℕ → ℕ)
    (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph)
    {vB eB : ℕ} (hvB : H.vertexSet.ncard ≤ vB) (heB : H.edgeSet.ncard ≤ eB)
    (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (hσ : IsStandard σ)
    (σM : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ)
    (hσM : ∀ a b c p z, σ (SurfaceModel a b c) p z ≤ σM a b c p z) :
    let res := theorem_13_4_bound V σM vB eB
    res.2.2.1 < res.2.2.2 ∧
    ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → res.2.2.2 ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ res.2.2.1 ∧ ∃ π : Portrayal (G.deleteVertices Z),
        π.warp ≤ res.1 ∧ (cuffs π.S).encard ≤ res.2.1 ∧ ¬ CanBeDrawn π.S H ∧ π.IsTrue (deleteVerticesTangle G Z 𝒯 θ') ∧
        π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S res.1 Z.ncard) := by
  classical
  dsimp only [theorem_13_4_bound]
  obtain ⟨hz₀, h1⟩ := theorem_13_1_explicit.{u, v} V hV H hH hvB heB
  set res1 := theorem_13_1_bound V vB eB
  set p₀ := res1.1
  set q₀ := res1.2.1
  set z₀ := res1.2.2.1
  set θ₀ := res1.2.2.2
  set p := max p₀ 1
  have hp : 1 ≤ p := le_max_right _ _
  set L := GM20.Draw.drawBound eB
  set q := 6 * L + q₀
  obtain ⟨hz, hzz, h3⟩ := theorem_13_3_explicit.{u, v} σ hσ σM hσM hp (q ^ 2 * p + q₀ * p) z₀
  set res3 := theorem_13_3_bound σM p (q ^ 2 * p + q₀ * p) z₀
  refine ⟨lt_max_of_lt_right hz, ?_⟩
  intro α β G hG θ' 𝒯 h𝒯 hθ
  rcases h1 G hG θ' 𝒯 h𝒯 ((le_max_left _ _).trans hθ) with hctrl | ⟨Z₀, hZ₀, hc₀, π₀, hcen₀, hw₀, hcu₀, hdr₀⟩
  · exact .inl hctrl
  refine .inr ?_
  have hθ₁ : res3.1 ≤ θ' := (le_max_right _ _).trans hθ
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification π₀.S π₀.isSurface π₀.connected
  have hc₀c : c₀ ≤ q₀ := by
    have h₁ := ncard_cuffs_of_homeo e₀
    have h₂ : ((cuffs π₀.S).ncard : ℕ∞) = (cuffs π₀.S).encard := π₀.finite_cuffs.cast_ncard_eq
    rw [← h₂, h₁] at hcu₀
    exact_mod_cast hcu₀
  have hnd₀ : ¬ CanBeDrawn (SurfaceModel a₀ b₀ 0) H := by
    intro hd
    have : T2Space π₀.S := π₀.isSurface.2.1
    have : T2Space (SurfaceModel a₀ b₀ c₀) := e₀.symm.isEmbedding.t2Space
    exact hdr₀ (GM20.Draw.CanBeDrawn.map e₀.symm (canBeDrawn_of_le hH le_rfl le_rfl hd))
  have hab : a₀ < L ∧ b₀ < L := by
    have : T2Space (SurfaceModel a₀ b₀ 0) := (isSurface_model a₀ b₀ 0).1.2.1
    by_contra h
    exact hnd₀ (GM20.Draw.canBeDrawn_of_drawBound H hH heB a₀ b₀ 0 (by omega))
  have hrank₀ : 4 * a₀ + 2 * b₀ + c₀ ≤ q := by dsimp [q]; omega
  have hh : π₀.hp p ≤ q ^ 2 * p + q₀ * p := by
    rw [π₀.hp_eq p e₀]
    have h₁ := π₀.totalCuffWarp_le (p := p) (hw₀.trans (le_max_left _ _)) (ncard_cuffs_of_homeo e₀)
    have h₂ : (4 * a₀ + 2 * b₀ + c₀) ^ 2 * p ≤ q ^ 2 * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hrank₀ 2)
    have h₃ : c₀ * p ≤ q₀ * p := Nat.mul_le_mul_right _ hc₀c
    omega
  obtain ⟨Z, -, hZ, hcZ, π, hcen, hrel, hred⟩ := h3 G hG θ' 𝒯 h𝒯 hθ₁ Z₀ hZ₀ hc₀ π₀ hcen₀ (hw₀.trans (le_max_left _ _)) hh
  have hzθ : Z.ncard < θ' := by omega
  have ht := GM10.theorem_8_5_proof hG h𝒯 hZ hzθ
  obtain ⟨π', htrue, hres, hred'⟩ := exists_true_resembling ht hcen hred
  obtain ⟨a, b, c, ⟨e⟩⟩ := classification π.S π.isSurface π.connected
  have hstep : (4 * a + 2 * b + c ≤ q) ∧ ¬ CanBeDrawn π.S H := by
    rcases hrel with hs | hs
    · rcases hs with ⟨hS, -⟩ | ⟨ψ, -, -⟩
      · refine ⟨?_, fun hd => hdr₀ (hS.canBeDrawn hH hd)⟩
        obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, ⟨e₁⟩, ⟨e₂⟩, -, -, hlt⟩ := hS
        have h₁ := model_rank_eq e e₁
        have h₂ := model_rank_eq e₀ e₂
        omega
      · exact ⟨by rw [model_rank_eq e (ψ.trans e₀)]; exact hrank₀, fun hd => hdr₀ (GM20.Draw.CanBeDrawn.map ψ hd)⟩
    · obtain ⟨ψ, -⟩ := hs
      exact ⟨by rw [model_rank_eq e (ψ.trans e₀)]; exact hrank₀, fun hd => hdr₀ (GM20.Draw.CanBeDrawn.map ψ hd)⟩
  obtain ⟨ψ', -⟩ := id hres
  have hwarp : π'.warp ≤ p := by
    rw [hres.warp_eq]
    rcases hrel with hs | hs
    · exact hs.warp_le.trans (hw₀.trans (le_max_left _ _))
    · rw [hs.warp_eq]
      exact hw₀.trans (le_max_left _ _)
  refine ⟨Z, hZ, hcZ, π', hwarp, ?_, fun hd => hstep.2 (GM20.Draw.CanBeDrawn.map ψ' hd), htrue, ?_⟩
  · have h₁ := ncard_cuffs_of_homeo (ψ'.trans e)
    rw [← π'.finite_cuffs.cast_ncard_eq, h₁]
    have : c ≤ q := by omega
    exact_mod_cast this
  · rw [hσ π'.S π.S p Z.ncard π'.isSurface π'.connected π.isSurface π.connected ⟨ψ'⟩]
    exact hred'

/-- **Graph Minors XVII, (13.4)** (page 206): "For any graph $H$ and standard $\sigma$, there are numbers $p, q, z$ and $\theta > z$, such that for every graph $G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge \theta$, either (i) $\mathscr{T}$ controls an $H$-minor of $G$, or (ii) there exists $Z \subseteq V(G)$ with $|Z| \le z$, and a $(\mathscr{T} \setminus Z)$-central portrayal $\pi = (\Sigma, \Gamma, \alpha, \beta, \gamma)$ of $G \setminus Z$ with warp $\le p$, such that $\Sigma$ has $\le q$ cuffs, $H$ cannot be drawn in $\Sigma$, and $\pi$ is $\sigma(\Sigma, p, |Z|)$-redundant and true." -/
theorem theorem_13_4_proof  {α' β' : Type} (H : Hypergraph α' β') (hH : H.IsGraph)
    (σ : (S : Type) → [TopologicalSpace S] → ℕ → ℕ → ℕ) (hσ : IsStandard σ) :
    ∃ p q z θ : ℕ, z < θ ∧ ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph → ∀ (θ' : ℕ)
      (𝒯 : Set (Hypergraph α β × Hypergraph α β)), IsTangle G θ' 𝒯 → θ ≤ θ' →
      ControlsMinor G 𝒯 H ∨ ∃ Z ⊆ G.vertexSet, Z.ncard ≤ z ∧ ∃ π : Portrayal (G.deleteVertices Z),
        π.warp ≤ p ∧ (cuffs π.S).encard ≤ q ∧ ¬ CanBeDrawn π.S H ∧ π.IsTrue (deleteVerticesTangle G Z 𝒯 θ') ∧
        π.IsRedundant (deleteVerticesTangle G Z 𝒯 θ') (θ' - Z.ncard) (σ π.S p Z.ncard) := by
  let σM := fun a b c p z => σ (SurfaceModel a b c) p z
  let res := theorem_13_4_bound GM07.vModel σM H.vertexSet.ncard H.edgeSet.ncard
  exact ⟨res.1, res.2.1, res.2.2.1, res.2.2.2,
    theorem_13_4_explicit.{u, v} GM07.vModel (fun _ _ _ _ => le_rfl) H hH le_rfl le_rfl σ hσ σM
      (fun _ _ _ _ _ => le_rfl)⟩

end GraphMinor.GM17
