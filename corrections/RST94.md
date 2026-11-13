# Quickly excluding a planar graph: corrections

N. Robertson, P. D. Seymour and R. Thomas, *Quickly excluding a planar graph*, J. Combin. Theory
Ser. B **62** (1994), 323–348.

The corrections are in the order of the pages.

## 1. Proof of (3.1), page 332: the paths counted by $a$ and $b$

**Kind.** Proof gap.

**What goes wrong.** Here $\mathscr{P}$ is a set of $9k$ disjoint paths between $S$ and $T$, the
path $P \in \mathscr{P}$ splits fewer than $55k^2/4$ unordered pairs of members of $\mathscr{P}$,
and $(A, B)$ is a separation of $G$ with $V(P) \subseteq V(A \cap B)$ and
$|V(A \cap B)| - |V(P)| < k$. The proof lets $a$ be the number of members $P' \ne P$ of
$\mathscr{P}$ with $V(P') \subseteq V(A)$, "and define $b$ similarly". It then uses
$ab < 55k^2/4$, because $P$ splits every pair made of a path counted by $a$ and a path counted by
$b$. But a path $P' \ne P$ with $V(P') \subseteq V(A \cap B)$ is counted by both $a$ and $b$. Then
the product $ab$ counts the pair $(P', P')$, which is not a pair of distinct paths, and it counts
some unordered pairs twice. So $ab$ need not be at most the number of pairs split by $P$.

**Correction.** Let $b$ be the number of members $P' \ne P$ of $\mathscr{P}$ with
$V(P') \subseteq V(B)$ and $V(P') \not\subseteq V(A)$. The three facts that the proof uses still
hold.

- First, $a + b + k \ge 9k$. A member of $\mathscr{P}$ other than $P$ that is counted by neither $a$
  nor $b$ has a vertex in $V(A) - V(B)$ and a vertex in $V(B) - V(A)$, so it meets
  $V(A \cap B) - V(P)$. These members are disjoint, so there are fewer than $k$ of them.
- Second, $ab$ is at most the number of unordered pairs split by $P$. Indeed, $P$ splits each pair
  made of a path counted by $a$ and a path counted by $b$, since every path of $G$ between them
  meets $V(A \cap B)$, which has fewer than $k$ vertices outside $V(P)$. And now no path is counted
  by both $a$ and $b$.
- Third, $|V(B) \cap Z| \le 2(b + 1) + k - 1$. Each vertex of $Z$ is an end of a member of
  $\mathscr{P}$. The members counted by $b$, and $P$, have at most $2(b + 1)$ ends. Let $Q \ne P$ be
  any other member. If $V(Q) \subseteq V(A \cap B)$, each end of $Q$ is in $V(A \cap B) - V(P)$.
  Otherwise fix a vertex $x$ of $Q$ outside $V(B)$. Each end of $Q$ in $V(B)$ gives the first vertex
  of $V(A \cap B)$ on the subpath of $Q$ from that end to $x$. In both cases different ends give
  different vertices of $V(A \cap B) - V(P)$. So these members have at most $k - 1$ ends in $V(B)$.

The rest of the proof is unchanged, and (3.1) holds as printed.

**Lean.** `GraphMinor.RST94.theorem_3_1` in `GraphMinor/RST94/Section3b.lean`.

## 2. Proof of (3.2), page 334: $6k$, not $k$

**Kind.** Misprint.

**What goes wrong.** To check the first tangle axiom for $\mathscr{T}'$, the proof says "by (8) one of
$|V(A' \cap G') \cap Z'|$, $|V(B' \cap G') \cap Z'| < k$; that is, one of $|V(A') \cap Z'|$,
$|V(B') \cap Z'| < k$". Claim (8) says that there is no separation $(A', B')$ of
$G' \setminus V(P')$ of order $< k$ with $|V(A') \cap Z'|, |V(B') \cap Z'| \ge 6k$. So it gives
$< 6k$, not $< k$. The definition of $\mathscr{T}'$ also uses $< 6k$.

**Correction.** Both places read "$< 6k$". Then one of $(A', B')$, $(B', A')$ belongs to
$\mathscr{T}'$, as the proof says. The statement is not affected.

**Lean.** `GraphMinor.RST94.isTangle_pathTangle` in `GraphMinor/RST94/Section3d.lean`, where
$\mathscr{T}'$ is `GraphMinor.RST94.pathTangle`. (3.2) is `GraphMinor.RST94.theorem_3_2`, in the
same file.

## 3. Proof of (4.1), page 335: the edge $e$ must not be a loop

**Kind.** Proof gap.

**What goes wrong.** In this paper graphs may have loops and multiple edges (page 323). The proof of
(4.1) is by induction on $|V(C) - Z|$. In Case 1, where $E(C) \not\subseteq E(A)$, it says "Choose
$e \in E(C) - E(A)$", and then applies the induction to $G/e$ and $C/e$. If $e$ is a loop, then
$G/e$ is $G$ with $e$ deleted, and $|V(C/e) - Z| = |V(C) - Z|$, so the induction does not apply.
This can happen: a loop of $C$ at a vertex outside $V(A)$ is in $E(C) - E(A)$.

**Correction.** Choose $e \in E(C) - E(A)$ that is not a loop. Such an edge exists. A loop
$f \in E(C) - E(A)$ cannot be at a vertex of $V(A \cap B)$: otherwise, moving $f$ from $B$ to $A$
gives a separation of the same order with the same $V(A)$, which is in $\mathscr{T}_0$ by (2.8),
contrary to the maximality of $A$. So a loop in $E(C) - E(A)$ is at a vertex of $C$ outside
$V(A)$. Since $C$ is connected and meets $Z \subseteq V(A)$, some edge of $C$ then has one end in
$V(A)$ and the other end outside $V(A)$. This edge is in $E(C) - E(A)$ and is not a loop. When
$e$ is not a loop, not both ends of $e$ are in $Z$, as the paper shows, so contracting $e$ lowers
$|V(C) - Z|$ by one and the induction applies. (4.1) holds as printed.

**Lean.** `GraphMinor.RST94.theorem_4_1` in `GraphMinor/RST94/Section4b.lean`. It is stated for a
connected set of vertices in place of $C$ (`GraphMinor.RST94.Conn` in
`GraphMinor/RST94/Basic.lean`). The conclusion depends only on $V(C)$, so this is the same
statement.

## 4. Definition of a shadow, page 341, and proof of (5.5), page 342: $C_i \setminus Z'$ connected

**Kind.** Proof gap.

**What goes wrong.** A graph $S$ with $V(S) = Z$ is a shadow of $G', \mathscr{T}', Z'$ if there are
disjoint connected subgraphs $C_i$ of $G \setminus (V(G') - Z')$, one for each $z_i \in Z$, such
that $C_i$ has exactly one vertex in $Z$, namely $z_i$, and exactly one vertex in $Z'$, and such
that $C_i \setminus Z'$ and $C_j \setminus Z'$ touch whenever $z_i$ and $z_j$ are adjacent in $S$.
The proof of (5.5) applies (5.4) to the nodule $G'', \mathscr{T}'', Y$ and gets a residual nodule
$G', \mathscr{T}', Y'$ with a shadow $S$ that is a tree with at least $m$ leaves. Write $y_i$ and
$y'_i$ for the vertices of $C_i$ in $Y$ and $Y'$. The proof then states at once that there are a
linkage $\mathscr{P}'$ and a connected subgraph $C$ of $G'' \setminus V(G')$ that touches but does
not meet $P \setminus Y'$ for at least $m$ members $P$ of $\mathscr{P}'$. The definition of a shadow
does not give this, because $C_i \setminus Y'$ need not be connected. For example, $C_i$ may be the
path $y_i\, y'_i\, u_i$. Then $C_i \setminus Y'$ has the two components $\{y_i\}$ and $\{u_i\}$, and
the path of $C_i$ from $y_i$ to $Y'$ is $y_i\, y'_i$. If $y_i$ has no neighbour other than $y'_i$,
and the rest of the shadow touches $C_i \setminus Y'$ only at $u_i$, then no subgraph of
$G'' \setminus V(G')$ that misses $y_i$ touches $y_i$. Also, for an inner vertex $y_j$ of the tree,
its neighbours in $S$ may touch different components of $C_j \setminus Y'$, so the union of the sets
$C_j \setminus Y'$ need not be connected.

**Correction.** In the definition of a shadow, ask also that each $C_i \setminus Z'$ is connected.
The proof of (5.4) gives this stronger form: in (1) the subgraphs can be chosen with this property,
and the step in (2) keeps it. Then the step in (5.5) is as follows. Choose $m$ leaves of $S$, and
let $C$ be the union of the sets $C_j \setminus Y'$ over the other vertices $y_j$ of $S$. These
vertices form a subtree of $S$, so $C$ is connected. Let $y_i$ be a chosen leaf, let $y_j$ be its
neighbour in $S$, and let $x$ be a vertex of $C_i \setminus Y'$ adjacent to $C_j \setminus Y'$.
Since $C_i$ is connected and $y_i \ne y'_i$, some neighbour of $y'_i$ lies in $C_i \setminus Y'$.
Since $C_i \setminus Y'$ is connected, it contains a path $Q$ from $y_i$ to such a neighbour, and a
path $R$ from $x$ to $V(Q)$. Let $P_i$ be $Q$ followed by $y'_i$, and add to $C$ the vertices of $R$
not in $Q$. Then $C$ stays connected, and it touches but does not meet $P_i \setminus Y'$. (5.4) and
(5.5) hold as printed.

**Lean.** The stronger shadow is `GraphMinor.RST94.Shadow` in `GraphMinor/RST94/Section5c.lean`.
Steps (1) and (2) of the proof of (5.4) are `GraphMinor.RST94.shadow_base` and
`GraphMinor.RST94.Shadow.step`, and (5.4) is `GraphMinor.RST94.theorem_5_4`, all in the same file.
The step in (5.5) is `GraphMinor.RST94.shadow_touch`, and (5.5) is `GraphMinor.RST94.theorem_5_5`,
both in `GraphMinor/RST94/Section5d.lean`.
