module

public import GraphMinor.Compute.GM02BoundaryInput

/-!
# Uniqueness of finite boundary inputs

The termination prefix is self-delimiting, and its header fixes its
length. Equal complete encodings therefore have equal termination
prefixes and equal side-bit suffixes. The prefix determines the vertex
count and terminal pairs. Each side-bit array determines its vertex set.
Thus the plain encoding determines the entire boundary input.
-/

public section
namespace GraphMinor.Compute

private theorem termination_heq_of_input_eq {x y : GM02SimpleTerminatedInput} (h : x = y) :
    HEq x.A y.A := by cases h; rfl

private theorem vertexBits_injective {n : ℕ} : Function.Injective (gm02VertexBits (n := n)) := by
  intro L R h
  apply Finset.coe_injective
  exact (gm02DecodedVertices_bits L).symm.trans
    ((congrArg (fun words => gm02DecodedVertices (n := n) words) h).trans (gm02DecodedVertices_bits R))

/-- The termination-index header fixes the prefix length. -/
theorem GM02BoundaryInput.prefix_length (x : GM02BoundaryInput) :
    x.prefix.enc.length = 3 + 2 * x.A.index := by
  simp only [x.prefix_enc, List.length_append, List.length_cons, List.length_nil,
    length_flatEdges, gm02Termination_pairList_length]

/-- The boundary encoding determines all supplied terminal pairs and both
side-membership subsets. -/
theorem gm02BoundaryEncoding_injective : Function.Injective GM02BoundaryInput.enc := by
  intro x y henc
  have hx := x.enc_length
  have hk : x.A.index = y.A.index := by
    apply Option.some.inj
    exact x.enc_two.symm.trans ((congrArg (fun words : List ℕ => words[2]?) henc).trans y.enc_two)
  have hprefixlen : x.prefix.enc.length = y.prefix.enc.length := by
    rw [x.prefix_length, y.prefix_length, hk]
  have hparts : x.prefix.enc = y.prefix.enc ∧
      gm02VertexBits x.left ++ gm02VertexBits x.right =
        gm02VertexBits y.left ++ gm02VertexBits y.right :=
    List.append_inj (by simpa only [GM02BoundaryInput.enc, List.append_assoc] using henc) hprefixlen
  have hbase := gm02SimpleTerminatedEncoding_injective hparts.1
  have hn := congrArg GM02SimpleTerminatedInput.n hbase
  have hA := termination_heq_of_input_eq hbase
  rcases x with ⟨n, A, L, R⟩
  rcases y with ⟨m, B, L', R'⟩
  change n = m at hn
  subst m
  have hAB : A = B := eq_of_heq hA
  subst B
  have hs : gm02VertexBits L ++ gm02VertexBits R = gm02VertexBits L' ++ gm02VertexBits R' := hparts.2
  obtain ⟨hL, hR⟩ := List.append_inj hs (by simp only [gm02VertexBits, List.length_ofFn])
  have hLL : L = L' := vertexBits_injective hL
  have hRR : R = R' := vertexBits_injective hR
  subst L'
  subst R'
  rfl

end GraphMinor.Compute
