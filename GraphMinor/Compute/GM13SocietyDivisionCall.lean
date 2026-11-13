module

public import GraphMinor.Compute.GM13SocietyInput
public import GraphMinor.Compute.Algorithm86

/-!
# The exact serialized division call

The simple program computes a 4-linked core and serializes both its raw
members and its merged members. We retain this exact record format for the
loop-owner scan. The record length and member counts are bounded by the
Section 8 size. Rurality is used only after the cross test has returned no.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The full simple division record, before unused buffer padding. -/
noncomputable def gm13DivisionPrefix (x : Alg81Input) (Z : Finset (Fin x.n))
    (edges : List (Fin x.n × Fin x.n)) : List ℕ :=
  [0] ++ encAlg86Subgraph Z edges ++
    encAlg86PairList (alg86RawPairList x.G Z x.omega.toFinset (edgeListOf x.G)) ++
    encAlg86PairList (alg86DivPairList x.G Z x.omega.toFinset (edgeListOf x.G))

/-- The exact array written by the simple division implementation. -/
noncomputable def gm13DivisionCode (x : Alg81Input) (Z : Finset (Fin x.n))
    (edges : List (Fin x.n × Fin x.n)) : List ℕ :=
  gm13DivisionPrefix x Z edges ++
    List.replicate (12 * alg81Size x - (gm13DivisionPrefix x Z edges).length) 0

/-- Data and correctness supplied by the simple core-and-division program. -/
def GM13SimpleDivisionData (x : Alg81Input) (out : List ℕ) : Prop :=
  ∃ (Z : Finset (Fin x.n)) (C : SimpleGraph (Fin x.n)) (edges : List (Fin x.n × Fin x.n)),
    Alg83Trace x Z C ∧ IsFourLinkedCore x.omega Z C ∧
    edges.length ≤ (edgeListOf x.G).length + 3 * x.n ∧ out = gm13DivisionCode x Z edges

/-- The polynomial word bound covers a fixed linear multiple of the size. -/
theorem gm13_section8_word_bound (S : ℕ) (hS : 1 ≤ S) :
    16 * (S + 2) < 2 ^ wordSize 4 S := by
  have hbase : 3 ≤ S + 2 := by omega
  have hc : 16 ≤ (S + 2) ^ 3 :=
    (by decide : 16 ≤ 3 ^ 3).trans (Nat.pow_le_pow_left hbase 3)
  have hm := Nat.mul_le_mul_right (S + 2) hc
  have hp := pow_lt_two_pow_wordSize (c := 4) (by decide) S
  rw [pow_succ] at hp
  exact hm.trans_lt hp

/-- The complete unpadded record has length at most twelve times vε. -/
theorem gm13DivisionPrefix_length_le (x : Alg81Input) (Z : Finset (Fin x.n))
    (edges : List (Fin x.n × Fin x.n))
    (he : edges.length ≤ (edgeListOf x.G).length + 3 * x.n) :
    (gm13DivisionPrefix x Z edges).length ≤ 12 * alg81Size x := by
  have hr := (length_encAlg86PairList_raw_le x.G Z x.omega.toFinset (edgeListOf x.G)).1
  have hd := (length_encAlg86PairList_div_le x.G Z x.omega.toFinset (edgeListOf x.G)).1
  have hS : alg81Size x = x.n * (edgeListOf x.G).length + x.n * x.n +
      2 * x.n + (edgeListOf x.G).length + 1 := by
    unfold alg81Size societySize
    rw [← length_edgeListOf_eq_card_edgeFinset x.G]
    ring
  simp only [gm13DivisionPrefix, List.length_append, List.length_cons, List.length_nil,
    length_encAlg86Subgraph]
  ring_nf at hS hr hd
  rw [hS]
  omega

/-- The simple division program writes its exact core and member lists in
O(vε) time. This call does not assume the outcome of the cross test. -/
theorem gm13SimpleDivisionProgram :
    ComputesArrRelInTime alg81Size encAlg81In GM13SimpleDivisionData
      alg86DivisionsProg (fun s => s) := by
  refine ⟨5000, 4, by decide, by decide, ?_⟩
  intro x s hin
  have hS : 1 ≤ alg81Size x := by
    exact Nat.mul_pos (by omega) (by omega)
  have hw := gm13_section8_word_bound (alg81Size x) hS
  obtain ⟨s', t, Z, C, edges, hex, ht, htrace, _, _, h4, _, he, hout⟩ :=
    alg86DivisionsProg_exec (w := wordSize 4 (alg81Size x)) x (by omega) hw hin
  exact ⟨s', t, hex, ht, Z, C, edges, htrace, h4, he, hout⟩

/-- Plain multigraph input supplies the exact simple division record while
retaining the original multigraph for output restoration. -/
theorem gm13SocietyDivisionCall :
    ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      (fun x s => GM13SimpleDivisionData x.simple (s.arrs 65) ∧ s.arrs 0 = x.enc)
      (gm13SocietyRunProg alg86DivisionsProg) (fun s => s) :=
  gm13SocietyRunProg_computes alg86DivisionsProg GM13SimpleDivisionData gm13SimpleDivisionProgram

end GraphMinor.Compute
