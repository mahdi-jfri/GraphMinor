module

public import GraphMinor.Compute.F92Parse
public import GraphMinor.Compute.F92GraphCopy
public import GraphMinor.Compute.F92Paths

/-!
# From the encoded input to a stored family of subwall paths

Parse and mark the input, copy the CSR graph into a separate search block, then run one
search for each subwall. This joins the parsing and path-search phases with their cost and
preservation guarantees. No prepared source, label or path arrays are required of the caller.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- Parse the input and write one path for each subwall. -/
def f92PreparePathsProg (h k a_G a_W a_base r_base base : ℕ) : Cmd :=
  .seq (f92ParseProg h k a_G a_W a_base r_base)
    (.seq (f92GraphCopyProg (aStart a_base) (aEnd a_base) (aEntries a_base) r_base base)
      (f92PathsUpTo a_base base k))

/-- The first two phases of the `F` program, starting only from the encoded input.
The caller supplies disjoint addresses and word bounds. Every path is found by the
executed searches, using the non-dividing conditions in the input. -/
theorem f92PreparePathsProg_exec {w l m p h k r : ℕ} (x : Alg92Input l m p h k r)
    (a_G a_W a_base r_base base : ℕ)
    (hin_lt : inArr < a_base) (haG_lt : a_G < a_base) (haW_lt : a_W < a_base)
    (hne_in_G : inArr ≠ a_G) (hne_in_W : inArr ≠ a_W) (hne_G_W : a_G ≠ a_W)
    (hb : 100 ≤ base) (hspace : a_base + 13 + 3 * k ≤ base) (hrbase : r_base < base)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hh : h < 2 ^ w)
    (hc : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (he : x.G.numEdges < 2 ^ w) (hin : (encAlg92In x).length < 2 ^ w)
    (hent : 2 * (edgeListOf x.G.toSimpleGraph).length < 2 ^ w)
    {s : State} (hs : s.arrs inArr = encAlg92In x) :
    ∃ s' t, ∃ P : Fin k → List (Fin x.n),
      Exec w (f92PreparePathsProg h k a_G a_W a_base r_base base) s s' t ∧
      t ≤ (f92InitFactor h k + 3 + k * (41 + 4 * h + 214 * elemWallNumVerts h)) * alg92Size x +
        31 + 34 * x.n + 17 * (2 * (edgeListOf x.G.toSimpleGraph).length) +
        k * (69 + 145 * x.n + 29 * totalAdjEntries (edgeNeighbors (edgeListOf x.G.toSimpleGraph))) ∧
      s'.arrs a_G = x.G.enc ∧ s'.arrs a_W = x.W.encList ∧ s'.regs r_base = x.n ∧
      IsBitSet x.W.vertexFinset (aHV a_base) s' ∧
      (∀ i, IsSubwallHPath x.W (x.W_sub i) (P i) ∧
        s'.arrs (aPath a_base i.val) = (P i).map Fin.val) ∧
      (∀ b : ℕ, b < a_base → b ≠ a_G → b ≠ a_W → s'.arrs b = s.arrs b) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hrn₁, hG₁, hW₁, hHV₁, hsub₁, hadj₁, hent₁, harr₁, hreg₁⟩ :=
    f92ParseProg_exec x a_G a_W a_base r_base hin_lt haG_lt haW_lt hne_in_G hne_in_W
      hne_G_W (by omega) (by omega) hh hc he hin hs
  obtain ⟨s₂, t₂, hex₂, ht₂, hadj₂, hrn₂, hent₂, harr₂, hreg₂⟩ :=
    f92GraphCopyProg_exec (w := w) x.G.toSimpleGraph (edgeNeighbors (edgeListOf x.G.toSimpleGraph))
      (aStart a_base) (aEnd a_base) (aEntries a_base) r_base base
      (by f92_omega) (by f92_omega) (by f92_omega) hrbase (by omega) (by omega)
      hadj₁ (by rw [hent₁]; exact hent) hrn₁
  have hHV₂ : IsBitSet x.W.vertexFinset (aHV a_base) s₂ :=
    hHV₁.of_arr_eq (harr₂ _ (by f92_omega))
  have hsub₂ : ∀ i : Fin k, IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s₂ ∧
      IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s₂ := by
    intro i
    exact ⟨(hsub₁ i).1.of_arr_eq (harr₂ _ (by have := i.isLt; f92_omega)),
      (hsub₁ i).2.of_arr_eq (harr₂ _ (by have := i.isLt; f92_omega))⟩
  obtain ⟨s₃, t₃, P, hex₃, ht₃, hpaths₃, harr₃, hreg₃⟩ :=
    f92PathsProg_exec x (edgeNeighbors (edgeListOf x.G.toSimpleGraph)) a_base base hb hspace hw hn
      hadj₂ (by rw [hent₂, hent₁]; exact hent) hrn₂ hHV₂ hsub₂
  have hlow (b : ℕ) (hb : b < a_base + 13) : s₃.arrs b = s₁.arrs b :=
    (harr₃ b (by omega) (fun i _ => by f92_omega)).trans (harr₂ b (by omega))
  refine ⟨s₃, t₁ + (t₂ + t₃), P, .seq hex₁ (.seq hex₂ hex₃), ?_,
    (hlow a_G (by omega)).trans hG₁, (hlow a_W (by omega)).trans hW₁,
    (hreg₃ r_base hrbase).trans ((hreg₂ r_base hrbase).trans hrn₁),
    hHV₁.of_arr_eq (hlow _ (by f92_omega)), hpaths₃,
    fun b hb hG hW => (hlow b (by omega)).trans (harr₁ b hb hG hW), ?_⟩
  · rw [hent₁] at ht₂
    omega
  · intro q hq
    exact (hreg₃ q (by omega)).trans ((hreg₂ q (by omega)).trans (hreg₁ q hq))

end GraphMinor.Compute.Alg92
