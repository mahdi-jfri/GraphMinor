module

public import GraphMinor.GM03.Defs

/-!
# Results cited in Graph Minors III

*Graph Minors. III. Planar Tree-Width* (J. Combin. Theory Ser. B **36** (1984), 49–64) cites the
following results from other papers, all of which are proved in the library (except (1.2), which is
mentioned in the introduction on page 50 only as background motivation and is not used in any proof
in Graph Minors III):

- **(1.1)** (page 50, citing Graph Minors IV, (1.5)): proved in `GraphMinor/GM04/Main.lean`
  (`GM04.theorem_1_5_proved`) and restated in `GraphMinor/GM03/Section1.lean` (`theorem_1_1`).
- **Menger's theorem** (used in (3.6), page 57, and (4.2), page 61): proved in
  `GraphMinor/Menger/Basic.lean` (`GraphMinor.menger`).
- **(5.1)** (page 62, citing Graph Minors V / VI): proved in `GraphMinor/Planar/Grid.lean`
  (`IsPlanar.exists_even_grid_minor`) and `GraphMinor/GM03/Section5.lean` (`theorem_5_1`).
- **(6.1)** (page 64, citing Graph Minors VII): proved in `GraphMinor/GM07/Section9.lean`
  (`GM07.gm07_theorem_9_2`), `GraphMinor/GM19/Section6a.lean` (`GM19.theorem_6_4_proof`), and
  `GraphMinor/GM19/FragmentCut.lean` (`GM19.exists_cut_simpler`), and assembled in
  `GraphMinor/GM03/Section6.lean` (`theorem_6_1`).
-/

@[expose] public section

namespace GraphMinor.GM03

end GraphMinor.GM03
