module

public import GraphMinor.Compute.Algorithm92CompressWall

/-!
# Graph Minors XIII, (9.2): the compressed input (`Algorithm92Input.lean`)

Page 101 of Graph Minors XIII: "First, we determine $F$. ... Since the size of $F$ is bounded
(exept for divalent vertices) by a function of $l, m$, and $p$, we can find an $(l, m)$-star or a
model of $K_p$ in $H \cup F$". Here `F` is given by a list `segs` of paths of `G` and, for each
subwall `H_a`, an `H`-path `paths a` of `G` that runs along `F` from the inside of `H_a` to a vertex
of `H` outside `H_a` (`IsFSystem`). So every `H_a` is non-dividing in `H ∪ F`; this is the property
of `F` that the search uses.

The paths of `H` and of `F` form a path system (`isPathSystem_fPaths`), whose nodes are the branch
vertices of `H` and the ends of the paths of `F`. Compressing it gives an input `compressInput` of
(9.2) on `Fin N`:

* its wall is valid (`IsCompression.isValid_cWall`);
* its subwalls are non-dividing (`IsCompression.isNonDividingSubwall_cWall`): the compressed image
  of `paths a`, with its loops erased, is an `H`-path of the compressed wall;
* its distances are those of `H` (`IsCompression.brickDist_cWall`).

`exists_isAlg92Output_of_isFSystem`: a correct output for `compressInput` gives a correct output
for the input.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {n : ℕ} {S : Finset (Fin n)} {Ps : List (List (Fin n))} {G : MultiDigraph n}

theorem Consec.ne_of_nodup {α : Type*} {L : List α} {u v : α} (h : Consec L u v) (hL : L.Nodup) :
    u ≠ v := by
  obtain ⟨A, B, rfl⟩ := h
  intro huv
  subst huv
  simp [List.nodup_append] at hL

theorem exists_consec_of_mem {α : Type*} {L : List α} {y : α} (hy : y ∈ L) (hL : 2 ≤ L.length) :
    ∃ z, Consec L y z ∨ Consec L z y := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hy
  cases B with
  | cons z B => exact ⟨z, Or.inl ⟨A, B, rfl⟩⟩
  | nil =>
    rcases List.eq_nil_or_concat' A with rfl | ⟨A', z, rfl⟩
    · simp at hL
    · exact ⟨z, Or.inr ⟨A', [], by simp⟩⟩

section Generic

variable {N : ℕ} {e : Fin N → Fin n} {ι : Fin n → Fin N} {h h' : ℕ} {W : WallOfHeight h G}
  {W' : WallOfHeight h' G}

/-- **The compressed subwall is non-dividing.** If `Q` is an `H`-path of `W` along the path system,
from a node inside the subwall `W'` to a node of `W` outside `W'`, then the compressed copy of `W'`
is a non-dividing subwall of the compressed copy of `W`. -/
theorem IsCompression.isNonDividingSubwall_cWall (hC : IsCompression S Ps e ι W)
    (hC' : IsCompression S Ps e ι W') (h2 : 2 ≤ h) (he : Even h)
    (hsub : (cWall S Ps e ι W').IsSubwallOf (cWall S Ps e ι W))
    {Q : List (Fin n)} (hQ : W.IsHPath Q) {y₀ y₁ : Fin n} (h0 : Q.head? = some y₀)
    (h1 : Q.getLast? = some y₁) (hy₀S : y₀ ∈ S) (hy₁S : y₁ ∈ S) (hy₀ : y₀ ∈ W'.insideFinset)
    (hy₁ : y₁ ∈ W.vertexFinset \ W'.vertexFinset) (hedge : ∀ y z, Consec Q y z → CEdge Ps y z)
    (hrep : ∀ y ∈ Q, y ∉ W.vertexFinset → cRep S Ps y ∉ W.vertexFinset) :
    (cWall S Ps e ι W).IsNonDividingSubwall (cWall S Ps e ι W') := by
  obtain ⟨hQne, hQ2, -, -, hQh, -, hQin, -⟩ := hQ
  have hon : ∀ y ∈ Q, OnPath Ps y := by
    intro y hy
    obtain ⟨z, hz | hz⟩ := exists_consec_of_mem hy hQ2
    · exact (hedge y z hz).onPath_left
    · exact (hedge z y hz).onPath_right
  have hrv : ∀ y ∈ Q, cRep S Ps y ∈ cVerts S Ps := fun y hy =>
    hC.path.cRep_mem_cVerts (Or.inr (hon y hy))
  set f : Fin n → Fin N := fun y => ι (cRep S Ps y) with hf
  set P := loopErase (Q.map f) with hPdef
  have hP0 : P.head? = some (ι y₀) := by
    rw [hPdef, head?_loopErase, List.head?_map, h0]
    simp [hf, cRep_of_mem_S hy₀S]
  have hP1 : P.getLast? = some (ι y₁) := by
    rw [hPdef, getLast?_loopErase, List.getLast?_map, h1]
    simp [hf, cRep_of_mem_S hy₁S]
  have hPne : P ≠ [] := by intro h; rw [h] at hP0; simp at hP0
  have hhead : P.head hPne = ι y₀ :=
    Option.some.inj ((List.head?_eq_some_head hPne).symm.trans hP0)
  have hlast : P.getLast hPne = ι y₁ :=
    Option.some.inj ((List.getLast?_eq_some_getLast hPne).symm.trans hP1)
  have hnd : P.Nodup := nodup_loopErase _
  have hy₀v : y₀ ∈ cVerts S Ps := IsCompression.mem_cVerts_of_S hy₀S
  have hy₁v : y₁ ∈ cVerts S Ps := IsCompression.mem_cVerts_of_S hy₁S
  have hy₀W : y₀ ∈ W.vertexFinset := by
    have : Q.head hQne = y₀ := Option.some.inj ((List.head?_eq_some_head hQne).symm.trans h0)
    rw [← this]; exact hQh
  have hy₁W : y₁ ∈ W.vertexFinset := (Finset.mem_sdiff.mp hy₁).1
  have hne01 : ι y₀ ≠ ι y₁ := by
    intro h
    have := hC.ι_inj hy₀v hy₁v h
    subst this
    exact (Finset.mem_sdiff.mp hy₁).2 (Finset.mem_sdiff.mp hy₀).1
  have hlen : 2 ≤ P.length :=
    two_le_length_of_ne_head_getLast hPne (by rw [hhead, hlast]; exact hne01)
  have hin : ι y₀ ∈ (cWall S Ps e ι W').insideFinset :=
    (hC'.mem_insideFinset_cWall_iff hy₀S).mpr hy₀
  have hout : ι y₁ ∈ (cWall S Ps e ι W).vertexFinset \ (cWall S Ps e ι W').vertexFinset := by
    rw [Finset.mem_sdiff, hC.mem_vertexFinset_cWall_iff hy₁v, hC'.mem_vertexFinset_cWall_iff hy₁v]
    exact Finset.mem_sdiff.mp hy₁
  have hV0 : ι y₀ ∈ (cWall S Ps e ι W).vertexFinset :=
    (hC.mem_vertexFinset_cWall_iff hy₀v).mpr hy₀W
  refine ⟨hsub, P, hPne, ⟨hPne, hlen, hnd, ?_, by rw [hhead]; exact hV0,
    by rw [hlast]; exact (Finset.mem_sdiff.mp hout).1, ?_, ?_⟩, by rw [hhead]; exact hin,
    by rw [hlast]; exact hout⟩
  · -- `P` is a walk of the compressed graph
    rw [isSimpleWalkList_iff_consec]
    intro u v huv
    have hne := huv.ne_of_nodup hnd
    obtain ⟨y, z, hyz, rfl, rfl⟩ := exists_of_consec_map (Consec.of_loopErase huv)
    have hrep_ne : cRep S Ps y ≠ cRep S Ps z := fun h => hne (by simp only [hf, h])
    rw [cGraph_adj, hC.e_ι _ (hrv y hyz.mem_left), hC.e_ι _ (hrv z hyz.mem_right)]
    exact ⟨hrep_ne, y, z, hedge y z hyz, rfl, rfl⟩
  · -- the inner vertices of `P` are not on the compressed wall
    rw [not_mem_drop_one_dropLast_iff hPne hlen hnd _ (by rw [hhead]; exact hV0)
      (by rw [hlast]; exact (Finset.mem_sdiff.mp hout).1)]
    intro v hv hvW
    rw [hhead, hlast]
    obtain ⟨y, hyQ, rfl⟩ := List.mem_map.mp (mem_of_mem_loopErase hv)
    rcases mem_head_or_drop_one_dropLast_or_getLast hQne hyQ with hy | hy | hy
    · left
      rw [hy, Option.some.inj ((List.head?_eq_some_head hQne).symm.trans h0)]
      simp [hf, cRep_of_mem_S hy₀S]
    · exfalso
      have := hrep y hyQ (hQin y hy)
      exact this ((hC.mem_vertexFinset_cWall_iff (hrv y hyQ)).mp hvW)
    · right
      rw [hy, Option.some.inj ((List.getLast?_eq_some_getLast hQne).symm.trans h1)]
      simp [hf, cRep_of_mem_S hy₁S]
  · intro _
    rw [hhead, hlast]
    exact (cWall S Ps e ι W).not_isWallEdge_inside_to_outside h2 he hC.isValid_cWall hsub hin hout

/-- **Distances are kept.** Two vertices of compressed subwalls `W₁`, `W₂` of `W` stand for two
vertices of `W₁` and `W₂` with the same distance in `W`. -/
theorem IsCompression.exists_brickDist_eq (hC : IsCompression S Ps e ι W) {h₁ h₂ : ℕ}
    {W₁ : WallOfHeight h₁ G} {W₂ : WallOfHeight h₂ G} (hC₁ : IsCompression S Ps e ι W₁)
    (hC₂ : IsCompression S Ps e ι W₂) (hs₁ : W₁.vertexFinset ⊆ W.vertexFinset)
    (hs₂ : W₂.vertexFinset ⊆ W.vertexFinset) {u v : Fin N}
    (hu : u ∈ (cWall S Ps e ι W₁).vertexFinset) (hv : v ∈ (cWall S Ps e ι W₂).vertexFinset) :
    ∃ y ∈ W₁.vertexFinset, ∃ z ∈ W₂.vertexFinset,
      (cWall S Ps e ι W).brickDist u v = W.brickDist y z := by
  obtain ⟨y, hy, rfl, hyW⟩ := hC₁.exists_of_mem_vertexFinset_cWall hu
  obtain ⟨z, hz, rfl, hzW⟩ := hC₂.exists_of_mem_vertexFinset_cWall hv
  exact ⟨y, hyW, z, hzW, hC.brickDist_cWall hy hz (hs₁ hyW) (hs₂ hzW)⟩

end Generic

/-! ### The subgraph `F` and the compressed input -/

variable {l m p h k r : ℕ} (x : Alg92Input l m p h k r)

/-- The nodes: the branch vertices of the wall and the two ends of each path of `F`. -/
def fNodes (segs : List (List (Fin x.n))) : Finset (Fin x.n) :=
  Finset.univ.image x.W.branchVert ∪
    (segs.flatMap (fun P => P.head?.toList ++ P.getLast?.toList)).toFinset

/-- The path system of `H ∪ F`: the subdivision paths of the wall, then the paths of `F`. -/
def fPaths (segs : List (List (Fin x.n))) : List (List (Fin x.n)) :=
  (List.finRange (elemWallEdges h).length).map x.W.subdivPathVerts ++ segs

/-- The conditions on `F` used by the search in `H ∪ F` (page 101): `F` is a list `segs` of paths
of `G` whose inner vertices (the vertices that are not nodes) are not in `H` and lie on only one
path of `F`; and for each subwall `H_a` there is an `H`-path `paths a` of `G` with all its edges in
`F`, from a vertex inside `H_a` to a vertex of `H` outside `H_a`. So every `H_a` is non-dividing in
`H ∪ F`. -/
structure IsFSystem (segs : List (List (Fin x.n))) (paths : Fin k → List (Fin x.n)) : Prop where
  nodup : ∀ P ∈ segs, P.Nodup
  walk : ∀ P ∈ segs, IsSimpleWalkList x.G P
  inner : ∀ P ∈ segs, ∀ y ∈ P, y ∉ fNodes x segs → y ∉ x.W.vertexFinset
  unique : ∀ P ∈ segs, ∀ Q ∈ segs, ∀ y, y ∉ fNodes x segs → y ∈ P → y ∈ Q → P = Q
  hpath : ∀ a, x.W.IsHPath (paths a)
  head_inside : ∀ a y, (paths a).head? = some y → y ∈ (x.W_sub a).insideFinset
  last_outside : ∀ a y, (paths a).getLast? = some y →
    y ∈ x.W.vertexFinset \ (x.W_sub a).vertexFinset
  edges : ∀ a y z, Consec (paths a) y z → CEdge segs y z

variable {x}

theorem branchVert_mem_fNodes (segs : List (List (Fin x.n))) (u : Fin (elemWallNumVerts h)) :
    x.W.branchVert u ∈ fNodes x segs := by
  unfold fNodes; simp

theorem mem_fNodes_of_head {segs : List (List (Fin x.n))} {P : List (Fin x.n)} (hP : P ∈ segs)
    {a : Fin x.n} (ha : P.head? = some a) : a ∈ fNodes x segs := by
  unfold fNodes
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    Option.mem_toList]
  exact Or.inr ⟨P, hP, Or.inl ha⟩

theorem mem_fNodes_of_getLast {segs : List (List (Fin x.n))} {P : List (Fin x.n)} (hP : P ∈ segs)
    {a : Fin x.n} (ha : P.getLast? = some a) : a ∈ fNodes x segs := by
  unfold fNodes
  simp only [Finset.mem_union, List.mem_toFinset, List.mem_flatMap, List.mem_append,
    Option.mem_toList]
  exact Or.inr ⟨P, hP, Or.inr ha⟩

theorem mem_fPaths {segs : List (List (Fin x.n))} {P : List (Fin x.n)} :
    P ∈ fPaths x segs ↔ (∃ k, P = x.W.subdivPathVerts k) ∨ P ∈ segs := by
  unfold fPaths
  simp [eq_comm]

section FSystem

variable {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
  (hF : IsFSystem x segs paths)
include hF

/-- The paths of `H` and `F` form a path system. -/
theorem IsFSystem.isPathSystem : IsPathSystem x.G (fNodes x segs) (fPaths x segs) := by
  have hv := x.hW_valid.2.2
  have hwall : ∀ (k : Fin (elemWallEdges h).length) (y : Fin x.n), y ∉ fNodes x segs →
      y ∈ x.W.subdivPathVerts k → y ∈ x.W.internalVerts k := by
    intro k y hy hyk
    rcases (x.W.mem_subdivPathVerts_iff k y).mp hyk with h | h | h
    · exact absurd (h ▸ branchVert_mem_fNodes segs _) hy
    · exact h
    · exact absurd (h ▸ branchVert_mem_fNodes segs _) hy
  refine ⟨fun P hP => ?_, fun P hP => ?_, fun P hP a ha => ?_, fun P hP c hc => ?_,
    fun P hP Q hQ y hy hyP hyQ => ?_⟩
  · rcases mem_fPaths.mp hP with ⟨k, rfl⟩ | hP
    · exact (hv.2.1 k).1
    · exact hF.nodup P hP
  · rcases mem_fPaths.mp hP with ⟨k, rfl⟩ | hP
    · exact (hv.2.1 k).2
    · exact hF.walk P hP
  · rcases mem_fPaths.mp hP with ⟨k, rfl⟩ | hP
    · simp only [subdivPathVerts, List.cons_append, List.head?_cons,
        Option.some.injEq] at ha
      rw [← ha]; exact branchVert_mem_fNodes segs _
    · exact mem_fNodes_of_head hP ha
  · rcases mem_fPaths.mp hP with ⟨k, rfl⟩ | hP
    · simp only [subdivPathVerts, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.some.injEq] at hc
      rw [← hc]; exact branchVert_mem_fNodes segs _
    · exact mem_fNodes_of_getLast hP hc
  · rcases mem_fPaths.mp hP with ⟨k, rfl⟩ | hP' <;> rcases mem_fPaths.mp hQ with ⟨k', rfl⟩ | hQ'
    · by_cases hk : k = k'
      · rw [hk]
      · exact absurd (hwall k' y hy hyQ) (List.disjoint_left.mp (hv.2.2.2 k k' hk)
          (hwall k y hy hyP))
    · exact absurd (x.W.mem_vertexFinset_of_mem_subdivPathVerts hyP) (hF.inner Q hQ' y hyQ hy)
    · exact absurd (x.W.mem_vertexFinset_of_mem_subdivPathVerts hyQ) (hF.inner P hP' y hyP hy)
    · exact hF.unique P hP' Q hQ' y hy hyP hyQ

omit hF in
theorem fVerts_card_pos (segs : List (List (Fin x.n))) :
    0 < (cVerts (fNodes x segs) (fPaths x segs)).card :=
  Finset.card_pos.mpr ⟨_, mem_cVerts_iff.mpr (Or.inl (branchVert_mem_fNodes segs
    (elemWallCornerIdx x.hW_valid.1 0)))⟩

end FSystem

variable (x)

/-- The vertices of the compressed graph of `H ∪ F`. -/
noncomputable abbrev fVerts (segs : List (List (Fin x.n))) : Finset (Fin x.n) :=
  cVerts (fNodes x segs) (fPaths x segs)

/-- The numbering of the vertices of the compressed graph, in increasing order. -/
noncomputable def fE (segs : List (List (Fin x.n))) : Fin (fVerts x segs).card → Fin x.n :=
  fun i => (fVerts x segs).orderEmbOfFin rfl i

/-- The number of a vertex of the compressed graph (and `0` for any other vertex). -/
noncomputable def fι (segs : List (List (Fin x.n))) : Fin x.n → Fin (fVerts x segs).card :=
  fun y => if hy : y ∈ fVerts x segs then ((fVerts x segs).orderIsoOfFin rfl).symm ⟨y, hy⟩
    else ⟨0, fVerts_card_pos segs⟩

variable {x}

section FSystem

variable {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
  (hF : IsFSystem x segs paths)
include hF

theorem IsFSystem.isCompression :
    IsCompression (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W where
  path := hF.isPathSystem
  valid := x.hW_valid.2.2
  branch_mem u := branchVert_mem_fNodes segs u
  wall_mem k := mem_fPaths.mpr (Or.inl ⟨k, rfl⟩)
  inj := (Finset.orderEmbOfFin _ _).injective
  mem_cVerts i := Finset.orderEmbOfFin_mem _ _ i
  e_ι y hy := by
    simp only [fE, fι, hy, dite_true, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem IsFSystem.isCompression_sub (a : Fin k) :
    IsCompression (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) (x.W_sub a) ∧
      (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) (x.W_sub a)).IsSubwallOf
        (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W) := by
  obtain ⟨h2', he', hle, i, j, hi, hj, hil, hjl, heq⟩ := (x.hnondiv a).1
  rw [heq]
  exact ⟨hF.isCompression.subwallAt i j _ _ hle hi hj hil hjl,
    ⟨h2', he', hle, i, j, hi, hj, hil, hjl, cWall_subwallAt i j _ _ hle hi hj hil hjl⟩⟩

theorem IsFSystem.isNonDividingSubwall (a : Fin k) :
    (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W).IsNonDividingSubwall
      (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) (x.W_sub a)) := by
  have hQ := hF.hpath a
  obtain ⟨hQne, hQ2, -, -, hQh, hQl, hQin, -⟩ := hQ
  obtain ⟨y₀, h0⟩ : ∃ y, (paths a).head? = some y := ⟨_, List.head?_eq_some_head hQne⟩
  obtain ⟨y₁, h1⟩ : ∃ y, (paths a).getLast? = some y := ⟨_, List.getLast?_eq_some_getLast hQne⟩
  have hon : ∀ y ∈ paths a, ∃ P ∈ segs, y ∈ P := by
    intro y hy
    obtain ⟨z, hz | hz⟩ := exists_consec_of_mem hy hQ2
    · obtain ⟨P, hP, hc | hc⟩ := hF.edges a y z hz
      exacts [⟨P, hP, hc.mem_left⟩, ⟨P, hP, hc.mem_right⟩]
    · obtain ⟨P, hP, hc | hc⟩ := hF.edges a z y hz
      exacts [⟨P, hP, hc.mem_right⟩, ⟨P, hP, hc.mem_left⟩]
  -- a vertex of `paths a` on `H` is a node
  have hnode : ∀ y ∈ paths a, y ∈ x.W.vertexFinset → y ∈ fNodes x segs := by
    intro y hy hyW
    by_contra hyS
    obtain ⟨P, hP, hyP⟩ := hon y hy
    exact hF.inner P hP y hyP hyS hyW
  have hy₀mem : y₀ ∈ paths a := List.mem_of_mem_head? h0
  have hy₁mem : y₁ ∈ paths a := List.mem_of_mem_getLast? h1
  have hy₀' : (paths a).head hQne = y₀ :=
    Option.some.inj ((List.head?_eq_some_head hQne).symm.trans h0)
  have hy₁' : (paths a).getLast hQne = y₁ :=
    Option.some.inj ((List.getLast?_eq_some_getLast hQne).symm.trans h1)
  refine hF.isCompression.isNonDividingSubwall_cWall (hF.isCompression_sub a).1 x.hW_valid.1
    x.hW_valid.2.1 (hF.isCompression_sub a).2 (hF.hpath a) h0 h1
    (hnode y₀ hy₀mem (hy₀' ▸ hQh)) (hnode y₁ hy₁mem (hy₁' ▸ hQl)) (hF.head_inside a y₀ h0)
    (hF.last_outside a y₁ h1) ?_ ?_
  · intro y z hyz
    obtain ⟨P, hP, hc⟩ := hF.edges a y z hyz
    exact ⟨P, mem_fPaths.mpr (Or.inr hP), hc⟩
  · -- the representative of a vertex of `F` outside `H` is outside `H`
    intro y hy hyW
    by_cases hyS : y ∈ fNodes x segs
    · rwa [cRep_of_mem_S hyS]
    · obtain ⟨P, hP, hyP⟩ := hon y hy
      have hPs : P ∈ fPaths x segs := mem_fPaths.mpr (Or.inr hP)
      obtain ⟨hrS, -, -, hrb⟩ := hF.isPathSystem.cRep_not_mem ⟨P, hPs, hyP⟩ hyS
      obtain ⟨A, a', R, c, B, hdec, -, -, -, hyR, hrun⟩ := hF.isPathSystem.exists_run hPs hyP hyS
      rw [(hrun y hyR).1] at hrb
      exact hF.inner P hP _ (by rw [hdec]; simp [hrb]) hrS

theorem IsFSystem.hdist (a b : Fin k) (hab : a ≠ b) (u : Fin (fVerts x segs).card)
    (hu : u ∈ (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs)
      (x.W_sub a)).vertexFinset)
    (v : Fin (fVerts x segs).card)
    (hv : v ∈ (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs)
      (x.W_sub b)).vertexFinset) :
    r ≤ (cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W).brickDist u v := by
  have hsub : ∀ c, (x.W_sub c).vertexFinset ⊆ x.W.vertexFinset := by
    intro c
    obtain ⟨h2', he', hle, i, j, hi, hj, hil, hjl, heq⟩ := (x.hnondiv c).1
    rw [heq]
    exact x.W.subwallAt_vertexFinset_subset i j _ _ hle hi hj hil hjl
  obtain ⟨y, hy, z, hz, hd⟩ := hF.isCompression.exists_brickDist_eq (hF.isCompression_sub a).1
    (hF.isCompression_sub b).1 (hsub a) (hsub b) hu hv
  rw [hd]
  exact x.hdist a b hab y hy z hz

end FSystem

/-- **The compressed input of (9.2).** The compressed copy of `H ∪ F`, with the compressed wall and
the compressed subwalls, is an input of (9.2) with the same `l, m, p, h, k, r`. -/
noncomputable def compressInput {segs : List (List (Fin x.n))} {paths : Fin k → List (Fin x.n)}
    (hF : IsFSystem x segs paths) : Alg92Input l m p h k r where
  n := (fVerts x segs).card
  G := cGraph (fNodes x segs) (fPaths x segs) (fE x segs)
  W := cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) x.W
  h_sub := x.h_sub
  W_sub a := cWall (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs) (x.W_sub a)
  hW_valid := ⟨x.hW_valid.1, x.hW_valid.2.1, hF.isCompression.isValid_cWall⟩
  hnondiv a := hF.isNonDividingSubwall a
  hdist := hF.hdist

/-- **A correct output for the compressed input gives a correct output for the input.** This is
the search step of page 101:
"we can find an $(l, m)$-star or a model of $K_p$ in $H \cup F$"
together with the lift from the compressed copy of `H ∪ F` back to `G`. -/
theorem exists_isAlg92Output_of_isFSystem (hl : 3 ≤ l) {segs : List (List (Fin x.n))}
    {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths) {outK : List ℕ}
    (hout : IsAlg92Output l m p (compressInput hF) outK) :
    ∃ out : List ℕ, IsAlg92Output l m p x out :=
  BlobMap.exists_isAlg92Output_of_blobMap (xK := compressInput hF) hl
    (isBlobMap_cBlobMap _ _ hF.isPathSystem hF.isCompression.inj hF.isCompression.mem_cVerts
      hF.isCompression.e_ι)
    hF.isCompression.isWallBlobMap_cBlobMap hout

end Alg92

end GraphMinor.Compute
