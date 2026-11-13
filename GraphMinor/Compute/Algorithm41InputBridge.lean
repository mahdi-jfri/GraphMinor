module

public import GraphMinor.Compute.Algorithm41
public import GraphMinor.Compute.Algorithm41Aux20

/-!
# Numbered Inputs for the Word RAM Core of GM XIII (4.1)

This file relates the public branch-decomposition inputs to the numbered input
used by the verified core. Parent normalization at the root changes neither
the tree nor the pieces used by the dynamic program.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Normalize the root parent while retaining every other parent entry. -/
def core41Parent {ξ ω : ℕ} (x : Alg41Input ξ ω) (z : ℕ) : ℕ :=
  if z = 0 then 0 else x.p z

private theorem core41Parent_pos {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    ∀ z > 0, core41Parent x z = x.p z := by
  intro z hz
  simp [core41Parent, Nat.ne_of_gt hz]

/-- The public numbered input supplies all combinatorial conditions of the core. -/
def Alg41Input.toCore {ξ ω : ℕ} (x : Alg41Input ξ ω) : Alg41CoreInput ξ ω :=
  have hp : ∀ z, 0 < z → z < x.t → core41Parent x z < z := by
    intro z hz hzt
    rw [core41Parent_pos x z hz]
    exact x.hp z hz hzt
  have hbd : IsDigraphBranchDecompOfWidthLe ω x.G (parentTree x.t (core41Parent x)) x.τ := by
    simpa only [parentTree_congr_pos (core41Parent_pos x)] using x.hbd
  { G := x.G
    Z := x.Z
    hZ := x.hZ
    t := x.t
    ht := x.ht
    ht_le := (t_le_two_mul_numEdges_of_branchDecomp x.ht x.hp x.hbd).trans (Nat.le_succ _)
    p := core41Parent x
    hp0 := by simp [core41Parent]
    hp := hp
    τ := x.τ
    hch := card_childrenFinset_le_three hp hbd
    hleaf := card_leafEdges_le_one hbd
    hQ_acc := fun _ hx _ hk ht => (card_pieceZ_dpAccEB_le_Q_max x.hZ x.ht hp hbd hx hk ht).1
    hQ_child := fun c hc hct => card_pieceZ_dpEB_le x.hZ x.ht hp hbd (x := ⟨c, hct⟩) hc }

/-- The conversion preserves the encoded input words. -/
theorem Alg41Input.enc_toCore {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    encAlg41CoreIn x.toCore = encAlg41In x := by
  rfl

/-- The conversion preserves the graph size. -/
theorem Alg41Input.size_toCore {ξ ω : ℕ} (x : Alg41Input ξ ω) :
    alg41CoreSize x.toCore = alg41Size x := by rfl


/-- Single-node core input for the zero-edge and one-edge branch-width convention. -/
def small41CoreInput {ξ ω : ℕ} (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (hZ : Z.card ≤ ξ) (hm : G.numEdges ≤ 1) : Alg41CoreInput ξ ω where
  G := G
  Z := Z
  hZ := hZ
  t := 1
  ht := by decide
  ht_le := by omega
  p := fun _ => 0
  hp0 := rfl
  hp := fun _ hz _ => hz
  τ := fun _ => ⟨0, by decide⟩
  hch := by
    intro x
    have hemp : childrenFinset 1 (fun _ => 0) x.1 = ∅ := by
      ext c
      simp only [childrenFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      have hx := x.2
      have hc := c.2
      omega
    rw [hemp]
    decide
  hleaf := by
    intro x
    exact (Finset.card_filter_le _ _).trans (by simpa using hm)
  hQ_acc := by
    intro x hx k hk hkt
    have hcard : (dpAccEB G (fun _ => 0) (fun _ => (⟨0, by decide⟩ : Fin 1)) x k).card ≤ 1 :=
      (Finset.card_le_univ _).trans (by simpa using hm)
    exact (card_pieceZ_le_two_of_card_le_one G Z hcard).2.trans (by omega)
  hQ_child := by intro c hc hct; omega

/-- Convert a serialized branch-decomposition input into the core's numbered input. -/
noncomputable def Alg41CodeInput.toCore {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) : Alg41CoreInput ξ ω :=
  if hge2 : 2 ≤ x.G.numEdges then
    (x.toAlg41Input hge2).toCore
  else
    small41CoreInput x.G.toComputeDigraph x.Z x.hZ
      (by have hm : x.G.toComputeDigraph.numEdges = x.G.numEdges := x.G.length_directedEdgesList; omega)

/-- Conversion preserves the graph size, including the zero-edge and one-edge cases. -/
theorem Alg41CodeInput.size_toCore {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    alg41CoreSize x.toCore = alg41CodeSize x := by
  unfold Alg41CodeInput.toCore
  split_ifs <;> simp [Alg41Input.toCore, Alg41CodeInput.toAlg41Input,
    small41CoreInput, alg41CoreSize, alg41CodeSize]


/-- The public code input has exactly the core's input encoding. -/
theorem Alg41CodeInput.enc_toCore {ξ ω : ℕ} (x : Alg41CodeInput ξ ω) :
    encAlg41CoreIn x.toCore = encAlg41CodeIn x := by
  by_cases hge2 : 2 ≤ x.G.numEdges
  · let q := x.toAlg41Input hge2
    have hc : x.toCore = q.toCore := by simp only [Alg41CodeInput.toCore, hge2, ↓reduceDIte]; rfl
    rw [hc, Alg41Input.enc_toCore]
    have hqt : q.t = bdNumTreeVerts x.bdCode := by rfl
    have htpos : 0 < bdNumTreeVerts x.bdCode := q.ht
    have hp : ∀ z, 0 < z → z < bdNumTreeVerts x.bdCode → bdParent x.bdCode z < z := q.hp
    have htcode : tCode x = bdNumTreeVerts x.bdCode := by simp [tCode, htpos]
    have hheader : [q.G.numVerts, q.G.numEdges, q.t] =
        [x.G.toComputeDigraph.numVerts, x.G.toComputeDigraph.numEdges, tCode x] := by
      rw [htcode]
      rfl
    have hparent : List.ofFn (normParent q) = List.ofFn (normParentCode x) := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, htcode]
        rfl
      · intro i hi hj
        simp only [List.getElem_ofFn]
        change (if i = 0 then 0 else bdParent x.bdCode i) = (if i = 0 then 0 else pCode x i)
        by_cases hi0 : i = 0
        · simp [hi0]
        · have hit : i < bdNumTreeVerts x.bdCode := by simpa only [List.length_ofFn, hqt] using hi
          simp [hi0, pCode, hp i (Nat.pos_of_ne_zero hi0) hit]
    have htau : List.ofFn (fun e => (q.τ e).1) = List.ofFn (fun e => (tauCode x e).1) := by
      apply List.ext_getElem
      · simp only [List.length_ofFn]; rfl
      · intro i hi hj
        simp only [List.getElem_ofFn, tauCode, htpos, ↓reduceDIte]
        rfl
    exact congrArg₂ List.append
      (congrArg₂ List.append
        (congrArg₂ List.append
          (congrArg₂ List.append (congrArg₂ List.append hheader rfl) rfl) rfl) hparent) htau
  · have hm : x.G.numEdges ≤ 1 := by omega
    have htzero : bdNumTreeVerts x.bdCode = 0 := by
      rcases x.hbd.2.2.2 with hsmall | hbig
      · exact hsmall.2.1
      · omega
    have htcode : tCode x = 1 := by simp [tCode, htzero]
    let q : Alg41CoreInput ξ ω := small41CoreInput x.G.toComputeDigraph x.Z x.hZ
      (by have hm' : x.G.toComputeDigraph.numEdges = x.G.numEdges := x.G.length_directedEdgesList; omega)
    have hc : x.toCore = q := by simp only [Alg41CodeInput.toCore, hge2, ↓reduceDIte]; rfl
    rw [hc]
    have hheader : [q.G.numVerts, q.G.numEdges, q.t] =
        [x.G.toComputeDigraph.numVerts, x.G.toComputeDigraph.numEdges, tCode x] := by
      rw [htcode]
      rfl
    have hparent : List.ofFn (fun z : Fin q.t => q.p z.1) = List.ofFn (normParentCode x) := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, htcode]
        rfl
      · intro i hi hj
        have hi0 : i = 0 := by change i < 1 at hi; omega
        subst i
        simp only [List.getElem_ofFn, normParentCode, ↓reduceIte]
        rfl
    have htau : List.ofFn (fun e => (q.τ e).1) = List.ofFn (fun e => (tauCode x e).1) := by
      apply congrArg List.ofFn
      funext e
      simp [tauCode, htzero, q, small41CoreInput]
    exact congrArg₂ List.append
      (congrArg₂ List.append
        (congrArg₂ List.append
          (congrArg₂ List.append (congrArg₂ List.append hheader rfl) rfl) rfl) hparent) htau

end GraphMinor.Compute
