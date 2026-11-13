module

public import GraphMinor.GM21.Section6CutSystem
import GraphMinor.GM21.Section6Jumps
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, (6.3), claim (2): the jumps of the cut drawing

Claim (2) of the proof of (6.3) (page 28 of the preprint) ends: "But these $\Sigma'$-jumps are
in 1-1 correspondence with the $\Sigma$-jumps of $\Gamma$, and so $\Gamma$ has at most
$\lambda(p + 4q, q, r + 2) \le \lambda$ $\Sigma$-jumps". We need only one direction: each
`Σ`-jump `J` of `Γ` gives a `Σ'`-jump of `Γ'`, and different jumps give different ones
(`encard_sigmaJumps_le_cut`).

The `Σ'`-jump of `J` is its copy on the sides of `J`: a jump meets `a` at most at one end, and
there it has one edge; the first side of `J` is the side of that edge at `a` (and the second side
the side of its edge at `b`). All other vertices of `J` are not split, so their copies do not
depend on the sides.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface Hypergraph GraphMinor.GM21.Split

universe u v

variable {α : Type u} {β : Type v} {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

omit [TopologicalSpace S] [TopologicalSpace S'] in
/-- A subgraph is copied on the sides `c` into the twice split graph when each of its edges is on
the sides `c` at each split end. -/
theorem isoImage_nm2_le' {G : Hypergraph α β} {Xa : Set α} {Ea : Set β}
    {Xb : Set (α ⊕ α ⊕ α)} {Eb : Set β} {A : Hypergraph α β} {c : Bool × Bool} (hA : A ≤ G)
    (hc : ∀ e ∈ A.edgeSet, ∀ v, A.Inc e v → (v ∈ Xa → (e ∈ Ea ↔ c.1 = true)) ∧
      (splitName Xa c.1 v ∈ Xb → (e ∈ Eb ↔ c.2 = true))) :
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
      obtain ⟨c', v, -, rfl⟩ := exists_nm2_of_mem ((split2 G Xa Ea Xb Eb).vertex_mem_of_inc hx)
      obtain ⟨hGv, h1, h2⟩ := split2_inc_nm2_iff'.mp hx
      have hAv : A.Inc e v := (GM10.inc_iff_of_le hA he).mpr hGv
      obtain ⟨k1, k2⟩ := hc e he v hAv
      have e1 : v ∈ Xa → c.1 = c'.1 := fun hv =>
        Bool.eq_iff_iff.mpr ((k1 hv).symm.trans (h1 hv))
      have hsn : splitName Xa c.1 v = splitName Xa c'.1 v := by
        by_cases hv : v ∈ Xa
        · rw [e1 hv]
        · rw [splitName_of_notMem hv, splitName_of_notMem hv]
      refine ⟨e, v, hAv, rfl, nm2_eq_of_sides e1 fun hb => ?_⟩
      exact Bool.eq_iff_iff.mpr ((k2 hb).symm.trans (h2 (hsn ▸ hb)))
    · rintro ⟨e₀, v, hv, rfl, rfl⟩
      obtain ⟨k1, k2⟩ := hc e₀ he v hv
      exact split2_inc_nm2_iff'.mpr ⟨GM10.inc_of_le hA hv, k1, k2⟩

/-- Two `Σ`-jumps with the same edges are equal. -/
theorem sigmaJump_eq_of_edgeSet_eq {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
    {ιE : Set S → β} (hiso : IsDrawingIso Γ Γ_sub ιV ιE) {J₁ J₂ : Hypergraph α β}
    (h₁ : J₁ ∈ sigmaJumps Γ Γ_sub ιV) (h₂ : J₂ ∈ sigmaJumps Γ Γ_sub ιV)
    (hE : J₁.edgeSet = J₂.edgeSet) : J₁ = J₂ := by
  rw [sigmaJumps_eq_jumpSet hiso] at h₁ h₂
  have hV : ∀ {K₁ K₂ : Hypergraph α β}, K₁ ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) →
      K₂ ∈ jumpSet Γ_sub (ιV '' (Γ.V ∩ bd S)) → K₁.edgeSet = K₂.edgeSet →
      K₁.vertexSet ⊆ K₂.vertexSet := by
    intro K₁ K₂ hK₁ hK₂ hE' x hx
    obtain ⟨e, he, hinc⟩ := exists_inc_of_mem_jumpSet hK₁ hx
    have he₂ : e ∈ K₂.edgeSet := hE' ▸ he
    exact K₂.vertex_mem_of_inc ((GM10.inc_iff_of_le hK₂.1 he₂).mpr (GM10.inc_of_le hK₁.1 hinc))
  exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq h₁.1 h₂.1
    ((hV h₁ h₂ hE).antisymm (hV h₂ h₁ hE.symm)) hE

section jumps

variable {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

open Classical in
/-- The sides of a jump `J`: the side of its edge at `a`, and the side of its edge at `b`. -/
noncomputable def jumpSides (ιV : S → α) (a b : S) (Ea Eb : Set β) (J : Hypergraph α β) :
    Bool × Bool :=
  (decide (∃ e ∈ J.edgeSet, J.Inc e (ιV a) ∧ e ∈ Ea),
    decide (∃ e ∈ J.edgeSet, J.Inc e (ιV b) ∧ e ∈ Eb))

/-- A jump has at most one edge at a vertex `x` of `Γ` on the boundary. -/
theorem edge_unique_of_jump {J : Hypergraph α β} (hJ : J ∈ sigmaJumps Γ Γ_sub ιV) {x : S}
    (hx : x ∈ Γ.V ∩ bd S) {e e' : β} (he : e ∈ J.edgeSet) (he' : e' ∈ J.edgeSet)
    (hi : J.Inc e (ιV x)) (hi' : J.Inc e' (ιV x)) : e = e' := by
  obtain ⟨-, -, u, -, w, -, -, hterm, hint⟩ := hJ
  have hxJ : ιV x ∈ J.vertexSet := J.vertex_mem_of_inc hi
  have hxt : ιV x ∈ terminals J := by
    rw [hterm]
    rcases hint x hx hxJ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hdeg : (incidentEdges J (ιV x)).ncard ≤ 1 :=
    (Nat.le_add_right _ _).trans hxt.2
  exact (ncard_le_one (J.edgeSet_finite.subset fun _ h => h.1)).mp hdeg e ⟨he, hi⟩ e' ⟨he', hi'⟩

/-- **Different `Σ`-jumps of `Γ` give different `Σ'`-jumps of `Γ'`.** -/
theorem encard_sigmaJumps_le_cut (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂) (hF : IsProperLineInSurface F a b)
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hFU : F ∩ Γ.U ⊆ {a, b}) {Γ' : Drawing S'}
    (hV : Γ'.V = ψ ⁻¹' Γ.V) {am ap bm bp : S'} (hpa : ψ ⁻¹' {a} = {am, ap}) (hamp : am ≠ ap)
    (hpb : ψ ⁻¹' {b} = {bm, bp}) (hbmp : bm ≠ bp) (cb : Bool) (Ea Eb : Set β) :
    (sigmaJumps Γ Γ_sub ιV).encard ≤
      (sigmaJumps Γ' (subOn (split2 G (μ (.vertex a)).vertexSet Ea (splitB μ a b cb) Eb)
        (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp '' Γ'.V) (ιE '' Γ.E))
        (cutName ψ ιV (μ (.vertex a)).vertexSet (splitB μ a b cb) ap bp)).encard := by
  have hS := hP.is_surface
  have ha : a ∈ Γ.V ∩ bd S := ⟨habV.1, hF.2.1⟩
  have hb : b ∈ Γ.V ∩ bd S := ⟨habV.2, hF.2.2.1⟩
  have hab := hF.ne
  set Xa := (μ (.vertex a)).vertexSet with hXa
  set Xb := splitB μ a b cb with hXb
  set nm := cutName ψ ιV Xa Xb ap bp with hnm
  refine encard_le_encard_of_injOn
    (f := fun J => isoImage (nm2 Xa Xb (jumpSides ιV a b Ea Eb J)) id J) ?_ ?_
  · intro J hJ
    have hJ' := hJ
    obtain ⟨hJA, hpath, u, hu, w, hw, huw, hterm, hint⟩ := hJ'
    set c := jumpSides ιV a b Ea Eb J with hc
    have hJG : J ≤ G := hJA.trans hP.drawing_subgraph
    -- A vertex of `J` is `ιV y` for a vertex `y` of `Γ`.
    have hvert : ∀ v ∈ J.vertexSet, ∃ y ∈ Γ.V, ιV y = v := fun v hv => by
      have : v ∈ ιV '' Γ.V := hP.ιV_image ▸ hJA.vertexSet_subset hv
      exact this
    -- The edges of `J` at `a` and at `b` are on the sides `c`.
    have hside : ∀ e ∈ J.edgeSet, ∀ v, J.Inc e v → (v ∈ Xa → (e ∈ Ea ↔ c.1 = true)) ∧
        (splitName Xa c.1 v ∈ Xb → (e ∈ Eb ↔ c.2 = true)) := by
      intro e he v hv
      obtain ⟨y, hy, rfl⟩ := hvert v (J.vertex_mem_of_inc hv)
      constructor
      · intro hya
        have hya' : y = a := (ιV_mem_μ_iff hP ha hy).mp hya
        subst hya'
        simp only [hc, jumpSides, decide_eq_true_eq]
        refine ⟨fun heE => ⟨e, he, hv, heE⟩, ?_⟩
        rintro ⟨e', he', hv', he'E⟩
        rwa [edge_unique_of_jump hJ ha he he' hv hv']
      · intro hyb
        have hyb' : y = b := (splitName_mem_splitB_iff hP ha hb hab cb _ hy).mp hyb
        subst hyb'
        simp only [hc, jumpSides, decide_eq_true_eq]
        refine ⟨fun heE => ⟨e, he, hv, heE⟩, ?_⟩
        rintro ⟨e', he', hv', he'E⟩
        rwa [edge_unique_of_jump hJ hb he he' hv hv']
    have hle : isoImage (nm2 Xa Xb c) id J ≤ split2 G Xa Ea Xb Eb := isoImage_nm2_le' hJG hside
    -- The ends of the new jump.
    have hlift : ∀ y ∈ Γ.V, ∃ y' ∈ Γ'.V, ψ y' = y ∧ nm y' = nm2 Xa Xb c (ιV y) := by
      intro y hy
      obtain ⟨y', hy', hyy⟩ := nm2_ιV_mem_image_cutName hP h hF habV hV hpa hamp hpb hbmp cb c hy
      refine ⟨y', hy', ?_, hyy⟩
      have hψ : ψ y' ∈ Γ.V := by rw [hV] at hy'; exact hy'
      exact hP.ιV_injOn hψ hy (eq_of_nm2_eq hyy)
    obtain ⟨u', hu'V, hu'ψ, hu'⟩ := hlift u hu.1
    obtain ⟨w', hw'V, hw'ψ, hw'⟩ := hlift w hw.1
    have hbd' : ∀ y', ψ y' ∈ bd S → y' ∈ bd S' := fun y' hy' => by
      rw [h.bd_eq hS hF]
      exact Or.inl hy'
    refine ⟨le_subOn hle ?_ ?_, (isPathGraph_isoImage hJG (nm2_injective c).injOn
      (injOn_id _)).mpr hpath, u', ⟨hu'V, hbd' u' (hu'ψ ▸ hu.2)⟩, w',
      ⟨hw'V, hbd' w' (hw'ψ ▸ hw.2)⟩, fun he => huw (hu'ψ ▸ hw'ψ ▸ congrArg ψ he), ?_, ?_⟩
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨y, hy, rfl⟩ := hvert v hv
      exact nm2_ιV_mem_image_cutName hP h hF habV hV hpa hamp hpb hbmp cb c hy
    · rintro _ ⟨e, he, rfl⟩
      exact hP.ιE_image ▸ hJA.edgeSet_subset he
    · rw [terminals_isoImage hJG (nm2_injective c).injOn (injOn_id _), hterm, image_pair, hu', hw']
    · rintro x' ⟨hx'V, hx'bd⟩ ⟨v, hv, hvx⟩
      have hψx : ψ x' ∈ Γ.V := by rw [hV] at hx'V; exact hx'V
      have hvψ : v = ιV (ψ x') := eq_of_nm2_eq hvx
      have hx'bd' : ψ x' ∈ bd S := by
        rw [h.bd_eq hS hF] at hx'bd
        rcases hx'bd with h' | h'
        · exact h'
        · rcases mem_ends_of_mem_line hFU h' hψx with h'' | h''
          · rw [h'']; exact ha.2
          · rw [h'']; exact hb.2
      rcases hint (ψ x') ⟨hψx, hx'bd'⟩ (hvψ ▸ hv) with h' | h'
      · left
        refine cutName_injOn hP h hF habV hFU hV hpa hamp hpb hbmp cb hx'V hu'V ?_
        exact hvx.symm.trans (by rw [hvψ, h']; exact hu'.symm)
      · right
        refine cutName_injOn hP h hF habV hFU hV hpa hamp hpb hbmp cb hx'V hw'V ?_
        exact hvx.symm.trans (by rw [hvψ, h']; exact hw'.symm)
  · intro J₁ hJ₁ J₂ hJ₂ heq
    have hE := congrArg Hypergraph.edgeSet heq
    simp only [isoImage, image_id] at hE
    exact sigmaJump_eq_of_edgeSet_eq hP.drawing_iso hJ₁ hJ₂ hE

end jumps

end CutLine
end GM21
end GraphMinor
