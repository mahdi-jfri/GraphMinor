module

public import GraphMinor.Compute.F92Mark

/-!
# Parsing the input of (9.2)

First copy the graph and main wall, mark the main wall and build its graph's adjacency lists.
Then scan the packed subwalls, marking each vertex set and each inside. Both phases preserve
arrays below the scratch base except the two designated output arrays. Their costs add to a
constant times the input size, with a constant depending only on the height and subwall count.
-/

@[expose] public section

namespace GraphMinor.Compute.Alg92

/-- The complete parsing and vertex-marking phase. -/
def f92ParseProg (h k a_G a_W a_base r_base : ℕ) : Cmd :=
  .seq (f92InitProg h a_G a_W a_base r_base) (f92MarkSubwallsProg h k a_base r_base)

/-- The parsing phase copies the graph and wall and marks the main wall, every subwall,
and every subwall inside. It also supplies CSR adjacency lists for the path searches.
Its hypotheses are precisely the input, array separation, word bounds and initial encoding. -/
theorem f92ParseProg_exec {w l m p h k r : ℕ} (x : Alg92Input l m p h k r)
    (a_G a_W a_base r_base : ℕ)
    (hin_lt : inArr < a_base) (haG_lt : a_G < a_base) (haW_lt : a_W < a_base)
    (hne_in_G : inArr ≠ a_G) (hne_in_W : inArr ≠ a_W) (hne_G_W : a_G ≠ a_W)
    (hw3 : 3 < 2 ^ w) (hn_w : x.n < 2 ^ w) (hh_w : h < 2 ^ w)
    (hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w)
    (he_w : x.G.numEdges < 2 ^ w) (hin_w : (encAlg92In x).length < 2 ^ w)
    {s : State} (hs : s.arrs inArr = encAlg92In x) :
    ∃ s' t, Exec w (f92ParseProg h k a_G a_W a_base r_base) s s' t ∧
      t ≤ (f92InitFactor h k + 3 + k * (41 + 4 * h + 214 * elemWallNumVerts h)) * alg92Size x ∧
      s'.regs r_base = x.n ∧ s'.arrs a_G = x.G.enc ∧ s'.arrs a_W = x.W.encList ∧
      IsBitSet x.W.vertexFinset (aHV a_base) s' ∧
      (∀ i : Fin k, IsBitSet (x.W_sub i).vertexFinset (aSubV a_base i.val) s' ∧
        IsBitSet (x.W_sub i).insideFinset (aSubIn a_base i.val) s') ∧
      IsAdjList x.G.toSimpleGraph (aStart a_base) (aEnd a_base) (aEntries a_base)
        (edgeNeighbors (edgeListOf x.G.toSimpleGraph)) s' ∧
      (s'.arrs (aEntries a_base)).length = 2 * (edgeListOf x.G.toSimpleGraph).length ∧
      (∀ a : ℕ, a < a_base → a ≠ a_G → a ≠ a_W → s'.arrs a = s.arrs a) ∧
      (∀ q < r_base, s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hrn₁, hG₁, hW₁, hHV₁, hsub₁, hadj₁, hent₁, harr₁, hreg₁⟩ :=
    f92InitProg_exec x a_G a_W a_base r_base hin_lt haG_lt haW_lt
      hne_in_G hne_in_W hne_G_W hw3 hn_w hh_w hc2_w he_w hin_w hs
  have hsubLen : ((List.finRange k).flatMap (fun i => (x.W_sub i).encList)).length < 2 ^ w := by
    have hinLen : (encAlg92In x).length = x.G.enc.length + x.W.encList.length +
        ((List.finRange k).flatMap (fun i => (x.W_sub i).encList)).length := by
      simp only [encAlg92In, List.length_append]
    omega
  obtain ⟨s₂, t₂, hex₂, ht₂, hbits₂, harr₂, hreg₂⟩ :=
    f92MarkSubwallsProg_exec x a_base r_base (by omega) hn_w hh_w (by omega)
      hsubLen hsub₁ hrn₁
  have hfixed (a : ℕ) (ha : a < a_base + 6) (hatmp : a ≠ aTmp2 a_base) :
      s₂.arrs a = s₁.arrs a :=
    harr₂ a hatmp (fun i _ => by constructor <;> f92_omega)
  have hcost₁ := f92InitCost_le_mul x
  have hcost₂ := f92MarkSubwallsCost_le_mul x
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_,
    (hreg₂ r_base (Or.inl (by omega))).trans hrn₁,
    (hfixed a_G (by omega) (by f92_omega)).trans hG₁,
    (hfixed a_W (by omega) (by f92_omega)).trans hW₁,
    hHV₁.of_arr_eq (hfixed _ (by f92_omega) (by f92_omega)), hbits₂,
    hadj₁.of_arrs_eq (hfixed _ (by f92_omega) (by f92_omega))
      (hfixed _ (by f92_omega) (by f92_omega))
      (hfixed _ (by f92_omega) (by f92_omega)),
    by rw [hfixed _ (by f92_omega) (by f92_omega), hent₁],
    fun a ha hGa hWa => (hfixed a (by omega) (by f92_omega)).trans (harr₁ a ha hGa hWa),
    fun q hq => (hreg₂ q (Or.inl (by omega))).trans (hreg₁ q hq)⟩
  rw [show f92InitFactor h k + 3 + k * (41 + 4 * h + 214 * elemWallNumVerts h) =
    f92InitFactor h k + (3 + k * (41 + 4 * h + 214 * elemWallNumVerts h)) by omega,
    Nat.add_mul]
  omega

end GraphMinor.Compute.Alg92
