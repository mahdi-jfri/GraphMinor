module

public import GraphMinor.Compute.GM06CandidateEdgeProgram
public import GraphMinor.Compute.GM06CutAdjacencyProgram

/-!
# Building the exact candidate adjacency arrays

Sections 12--13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) build a
fresh candidate graph for each eligible contact. The vertex and edge passes
compute its restrictions from the input rows. The verified cut-rotation
CSR pass then lists its neighbours in increasing permanent vertex
order. The correctness theorem gives exactly the adjacency family
used by the pure BFS procedure, with a polynomial construction bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Every candidate dart belongs to the original rotation encoding
when nonzero face-edge incidence refers to complete original edges. -/
theorem gm06CandidateDarts_in_rotations {m : ℕ} (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ)
    (hinc : ∀ e, e < m → incE[e]?.getD 0 ≠ 0 →
      2 * e ∈ data.rotations.flatten ∧ 2 * e + 1 ∈ data.rotations.flatten)
    {d : ℕ} (hd : d ∈ gm06CandidateDarts m data.origins ordinary incV incE upper path j) :
    d ∈ data.rotations.flatten := by
  have hp := (gm06CandidateDarts_mem_iff m data.origins ordinary incV incE upper path j d).mp hd
  have he := (gm06CandidateEdges_mem_iff _ ordinary incV incE upper path j (d / 2)).mp hp.2
  have hem : d / 2 < m := by simpa only [gm06CandidateEnds_length] using he.1
  have hpair := hinc (d / 2) hem he.2.2.1
  rcases gm06DartMate_end_cases d with ⟨hd', _⟩ | ⟨hd', _⟩
  · exact hd'.symm ▸ hpair.1
  · exact hd'.symm ▸ hpair.2

/-- Restricting the active darts preserves the row-origin encoding. -/
theorem gm06CandidateData_proper {n m : ℕ} (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path : List ℕ) (j : ℕ)
    (hproper : ∀ d ∈ data.rotations.flatten, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD [])
    (hinc : ∀ e, e < m → incE[e]?.getD 0 ≠ 0 →
      2 * e ∈ data.rotations.flatten ∧ 2 * e + 1 ∈ data.rotations.flatten) :
    ∀ d ∈ (gm06CandidateData n m data ordinary incV incE upper path j).activeDarts,
      ∀ u : Fin n, (gm06CandidateData n m data ordinary incV incE upper path j).origins[d]?.getD 0 = u.val ↔
        d ∈ (gm06CandidateData n m data ordinary incV incE upper path j).rotations[u.val]?.getD [] := by
  intro d hd u
  exact hproper d (gm06CandidateDarts_in_rotations data ordinary incV incE upper path j hinc hd) u

/-- Construct vertex and edge restrictions, prepare all permanent vertex
slots, and build CSR from the unchanged input rotations. -/
def gm06CandidateCSRProg : Cmd :=
  .seq gm06CandidateVerticesProg
    (.seq gm06CandidateEdgeBitsProg
      (.seq (gm13TabulateProg 650 (.reg 620) (.reg 650) 629) gm06CutAdjacencyProg))

/-- Complete write frame of candidate-graph construction. -/
def gm06CandidateCSRRegs : List ℕ := [650, 610, 611, 612] ++ gm06CutAdjacencyRegs

/-- All candidate graph storage lies in the reserved finite workspace. -/
def gm06CandidateCSRArrs : List ℕ := [611, 615, 623, 619, 627, 629] ++ gm06CutAdjacencyArrs

/-- Starting with rotations, ordinary flags, incidence and linkage rows,
the RAM constructs the exact ordered adjacency representation of A_(i,j).
The representation assumptions concern only those input encodings. -/
theorem gm06CandidateCSRProg_exec {w n m j : ℕ} (data : GM06CutData) (ordinary : List Bool)
    (incV incE upper path padding : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hfit : n * n + 2 < 2 ^ w) (hlen : data.rotations.length = n)
    (horgLen : data.origins.length = 2 * m) (hvalues : ∀ v ∈ data.origins, v < n)
    (hdarts : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hproper : ∀ d ∈ data.rotations.flatten, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD [])
    (hinc : ∀ e, e < m → incE[e]?.getD 0 ≠ 0 →
      2 * e ∈ data.rotations.flatten ∧ 2 * e + 1 ∈ data.rotations.flatten)
    (hVlen : incV.length = n) (hElen : incE.length = m) (hordinary : ordinary.length = m)
    (hVwords : ∀ x ∈ incV, x < 2 ^ w) (hEwords : ∀ x ∈ incE, x < 2 ^ w)
    (hpathLen : path.length < 2 ^ w) (hupperLen : upper.length < 2 ^ w) (hj : j < path.length)
    (hpath : ∀ x ∈ path, x < n) (hupper : ∀ x ∈ upper, x < n)
    (h606 : s.arrs 606 = incV) (h607 : s.arrs 607 = incE) (h608 : s.arrs 608 = upper)
    (h609 : s.arrs 609 = path) (h624 : s.arrs 624 = ordinary.map Bool.toNat)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h620 : s.regs 620 = n)
    (h649 : s.regs 649 = m) (h673 : s.regs 673 = j) :
    let G := gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j
    ∃ sf t, Exec w gm06CandidateCSRProg s sf t ∧
      t ≤ 146 + 184 * n + 150 * m + 100 * path.length + 100 * upper.length +
        21 * (n * n) + 129 * data.rotations.flatten.length ∧
      Keeps gm06CandidateCSRRegs gm06CandidateCSRArrs s sf ∧
      IsAdjList G 620 621 622 (gm06OrderedNeighbours G) sf ∧ (sf.arrs 622).length = n * n ∧
      sf.arrs 627 = gm06IncidenceBits (2 * m)
        (gm06CandidateDarts m data.origins ordinary incV incE upper path j) ∧
      sf.arrs 620 = (encodeLists (gm06OrderedNeighbours G)).1 ∧
      sf.arrs 621 = (encodeLists (gm06OrderedNeighbours G)).2.1 ∧
      GraphMinor.Compute.Crossing.IsBuf 622 655 (encodeLists (gm06OrderedNeighbours G)).2.2
        (n * n - (encodeLists (gm06OrderedNeighbours G)).2.2.length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06CandidateVerticesProg_exec incV upper path s hw1 hn
    hpathLen hupperLen hj hVlen hVwords hpath hupper h606 h608 h609 h620 h673
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06CandidateEdgeBitsProg_exec data.origins ordinary
    incV incE upper path s₁ hw hn hm horgLen hvalues hordinary hElen hEwords
    ((hk₁.2 624 (by decide)).trans h624) ((hk₁.2 607 (by decide)).trans h607)
    ((hk₁.2 626 (by decide)).trans h626) hd₁ ((hk₁.1 649 (by decide)).trans h649)
  have hk₁₂ : Keeps gm06CandidateCSRRegs gm06CandidateCSRArrs s s₂ :=
    (hk₁.mono (by simp [gm06CandidateCSRRegs]) (by simp [gm06CandidateCSRArrs])).trans hk₂
      (by simp [gm06CandidateCSRRegs]) (by simp [gm06CandidateCSRArrs])
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm13TabulateProg_exec
    650 (.reg 620) (.reg 650) 629 (List.range n) s₂ hw1 (by simpa using hn)
    (fun st hk => by
      simpa only [List.length_range] using GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 620 (by decide)).trans ((hk₁₂.1 620 (by
          simp [gm06CandidateCSRRegs, gm06CutAdjacencyRegs, gm06CutAdjacencyRowsRegs])).trans h620)) hn)
    (fun _ i hi _ hr => by
      simpa only [List.getElem_range] using GraphMinor.Compute.Crossing.eval_reg hr
        (by simpa only [List.length_range] using hi.trans (by simpa using hn)))
  have hk₁₃ : Keeps gm06CandidateCSRRegs gm06CandidateCSRArrs s s₃ :=
    hk₁₂.trans hk₃ (by simp [gm06CandidateCSRRegs]) (by simp [gm06CandidateCSRArrs])
  let candidate := gm06CandidateData n m data ordinary incV incE upper path j
  obtain ⟨sf, tf, hef, htf, hkf, hsf, hefTab, hbf⟩ := gm06CutAdjacencyProg_exec candidate padding s₃
    hw hn hm hfit hlen horgLen hvalues hdarts
    (fun v hv => List.mem_range.mp hv) (by simpa only [candidate, gm06CandidateData, List.length_range] using hn)
    ((hk₁₃.2 625 (by simp [gm06CandidateCSRArrs, gm06CutAdjacencyArrs])).trans h625)
    (by rw [hk₁₃.2 625 (by simp [gm06CandidateCSRArrs, gm06CutAdjacencyArrs])]; exact hcode)
    (by rw [hk₁₃.2 625 (by simp [gm06CandidateCSRArrs, gm06CutAdjacencyArrs])]; exact hwords)
    ((hk₁₃.2 626 (by simp [gm06CandidateCSRArrs, gm06CutAdjacencyArrs])).trans h626)
    ((hk₃.2 627 (by decide)).trans hd₂) hd₃
    ((hk₁₃.1 620 (by simp [gm06CandidateCSRRegs, gm06CutAdjacencyRegs,
      gm06CutAdjacencyRowsRegs])).trans h620)
  have hproper' := gm06CandidateData_proper data ordinary incV incE upper path j hproper hinc
  have hadj := gm06CutCSR_isAdjList candidate _ sf hlen hproper' hsf hefTab hbf.1
  have hlist : gm06CutAdjacencyLists n candidate = gm06OrderedNeighbours (gm06CutGraph n candidate) :=
    funext (gm06CutAdjacencyLists_eq_ordered candidate hproper')
  rw [hlist] at hadj
  have hadj' : IsAdjList
      (gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j)
      620 621 622 (gm06OrderedNeighbours
        (gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j)) sf := by
    have hg := gm06CandidateData_graph n m data ordinary incV incE upper path j
    rw [gm06OrderedNeighbours_congr _ _ hg] at hadj
    rw [hg] at hadj
    exact hadj
  let G := gm06CandidateGraph n (gm06CandidateEnds m data.origins) ordinary incV incE upper path j
  have hrows : gm06CutAdjacencyRowsFrom n 0 candidate.origins candidate.activeDarts
      candidate.vertices candidate.rotations = List.ofFn (gm06OrderedNeighbours G) := by
    rw [gm06CutAdjacencyRowsFrom_eq_ofFn candidate hlen, hlist]
    exact congrArg List.ofFn (gm06OrderedNeighbours_congr _ _
      (gm06CandidateData_graph n m data ordinary incV incE upper path j))
  have hstartCanonical : sf.arrs 620 = (encodeLists (gm06OrderedNeighbours G)).1 := by
    rw [hsf, hrows, gm06CSRStarts_encodeLists]
  have hendCanonical : sf.arrs 621 = (encodeLists (gm06OrderedNeighbours G)).2.1 := by
    rw [hefTab, hrows, gm06CSREnds_encodeLists]
  have hbufferCanonical : GraphMinor.Compute.Crossing.IsBuf 622 655
      (encodeLists (gm06OrderedNeighbours G)).2.2
      (n * n - (encodeLists (gm06OrderedNeighbours G)).2.2.length) sf := by
    simpa only [hrows, encodeLists] using hbf
  refine ⟨sf, t₁ + (t₂ + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    hk₁₃.trans hkf (by intro r hr; exact List.mem_append_right _ hr)
      (by intro a ha; exact List.mem_append_right _ ha), hadj', ?_,
    (hkf.2 627 (by simp [gm06CutAdjacencyArrs])).trans ((hk₃.2 627 (by decide)).trans hd₂),
    hstartCanonical, hendCanonical, hbufferCanonical⟩
  · simp only [Expr.cost, List.length_range] at ht₃
    change tf ≤ 30 + 57 * n + 21 * (n * n) + 14 * (List.range n).length +
      129 * data.rotations.flatten.length at htf
    rw [List.length_range] at htf
    omega
  · have hlenRows := gm06CutAdjacencyRowsFrom_flatten_length_le n 0 candidate.origins
      candidate.activeDarts candidate.vertices candidate.rotations
    change _ ≤ n * data.rotations.length at hlenRows
    rw [hlen] at hlenRows
    rw [hbf.1, List.length_append, List.length_replicate]
    omega

end GraphMinor.Compute
