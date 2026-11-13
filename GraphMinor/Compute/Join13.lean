module

public import GraphMinor.Compute.Join13Adapter101
public import GraphMinor.Compute.Join13Adapter72
import GraphMinor.Compute.Algorithm72
import GraphMinor.Compute.Algorithm92Final
public import GraphMinor.Compute.Algorithm105
public import GraphMinor.Compute.Join104
public import GraphMinor.Compute.Algorithm97
public import GraphMinor.Compute.Algorithm94
public import GraphMinor.Compute.Algorithm77

/-!
# Joining the programs of Graph Minors XIII

The width supplied by (9.9) can be used directly in (10.5), since (10.4) works for
every width. The final folio call writes the folio prefix using the raw (4.1) adapter.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The promised (9.9) theorem, with its three subroutine hypotheses. -/
def Claim99 : Prop :=
  Shiloach80Statement → Algorithm72Statement → Algorithm97Statement →
    Algorithm99Statement case3Decoder

/-- Graph Minors XIII, (4.1), pages 75–76: the core folio dynamic program runs in linear time. -/
theorem claim41_proved : Claim41 :=
  fun δ ξ ω => ⟨alg41CoreProg δ ξ ω, algorithm_4_1_core δ ξ ω⟩

/-- Graph Minors XIII, (10.5), pages 108–109, with the width returned by (9.9).
The raw (4.1) adapter writes the folio in the format required by `FolioStatement`. -/
theorem folioStatement_of_claim41_and_algorithm99 (h41 : Claim41)
    (h99 : Algorithm99Statement case3Decoder) (δ ξ : ℕ) : FolioStatement δ ξ := by
  obtain ⟨ω, _, h99spec⟩ := h99 (alg62Param ξ δ) (sec105WallHeight ξ δ)
    (two_le_and_even_sec105WallHeight ξ δ).1
    (two_le_and_even_sec105WallHeight ξ δ).2
  have h104 : Alg104Spec case3Decoder (alg62Param ξ δ)
      ((alg62Param ξ δ).choose 2 + ξ - 1) δ (sec105WallHeight ξ δ) ω :=
    alg104Spec_proved
  obtain ⟨prog41, C41, c41, _, _, hraw⟩ :=
    alg41RawSpec_of_claim41 h41 (alg62Param ξ δ) ξ δ (max ω 2 + ξ)
  refine algorithm_10_5_core ξ δ (sec105WallHeight ξ δ) ω case3Decoder
    (IsValidFolioOutput δ) h99spec h104 prog41 C41 c41 ?_
  intro w n G Z t par tau s
  dsimp only
  intro hw hZ hbd hb hb1 hr26 hr28 hr52 hb2len hb2get hb3len hb3get hb5 hb6
  obtain ⟨s', time, F, hex, ht, hout, hF⟩ :=
    hraw G Z t par tau s hw hZ hbd hb hb1 hr26 hr28 hr52 hb2len hb2get hb3len hb3get hb5 hb6
  exact ⟨s', time, hex, ht, fun x hcard hfolio =>
    ⟨F.castCard hcard, by rw [hout, encFolioSetRep_castCard], hfolio F hF⟩⟩

/-- Join (9.4), (9.7), (9.9), (10.4), (10.5), and the Section 2 reduction.
This theorem still requires the (7.2) interface. -/
theorem disjointPathsStatement_of_claims_and_algorithm72
    (hShiloach : Shiloach80Statement) (h41 : Claim41)
    (h92 : Algorithm92Statement) (h99 : Claim99) (h72 : Algorithm72Statement) :
    DisjointPathsStatement := by
  have h94 := gm13_algorithm_9_4 gm13_algorithm_7_7 h92
  have h97 := gm13_algorithm_9_7 hShiloach h94
  exact dp_of_folio (folioStatement_of_claim41_and_algorithm99 h41
    (h99 hShiloach h72 h97))

/-- The three forms of Claim (4.1) supply every call in the chain from (7.2)
through (10.5). The width returned by (9.9) is used directly in (10.5). -/
theorem disjointPathsStatement_of_claims (hShiloach : Shiloach80Statement)
    (h41 : Claim41) (h92 : Algorithm92Statement) (h99 : Claim99) : DisjointPathsStatement := by
  have h72 : Algorithm72Statement := algorithm_7_2_statement
  exact disjointPathsStatement_of_claims_and_algorithm72 hShiloach h41 h92 h99 h72

/-- The main result of Graph Minors XIII (page 65), through Folio as on page 69, from Shiloach's
two-paths algorithm and (9.9), using `claim41_proved` for (4.1) and `Alg92.gm13_algorithm_9_2` for
(9.2). -/
theorem disjointPathsStatement_of_shiloach (hShiloach : Shiloach80Statement) (h99 : Claim99) :
    DisjointPathsStatement :=
  disjointPathsStatement_of_claims hShiloach claim41_proved Alg92.gm13_algorithm_9_2 h99

end GraphMinor.Compute
