# The colouring

r1212_1657.graph has 1657 lines of 1657 characters, 2,747,306 bytes. Character w of line v is 1 if the edge vw is red and 0 if it is blue. The diagonal is 0. SHA-256: see SHA256SUMS.

There is no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1658.

## Vertex order

| Vertices | Role |
|---|---|
| 0–796 | A_x = x of the Mathon graph M(797) |
| 797–1593 | B_x = 797 + x |
| 1594 | a |
| 1595 | b |
| 1596–1656 | the 61 added vertices; see below |

Vertices 0–1595 are exactly vertices 0–1595 of r1212-1642's graph/r1212_1641.graph. In M(797):

- A_x A_y and B_x B_y are red iff x − y is a nonzero square mod 797;
- A_x B_y is red iff x ≠ y and x − y is not a square;
- a is red to all of A, b is red to all of B, and every other pair is blue.

## Certificates and V°

The certificates are those of r1212-1642:

- C = (c₀, …, c₉) = (930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595), a red K₁₀;
- I = (i₀, …, i₉) = (1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267), a blue K₁₀.

V° denotes the 1576 vertices of M(797) outside C ∪ I.

## The added vertices

Each added vertex has one of three types towards V°:

- **copy of g**, for some g in C ∪ I: for every x in V°, the edge to x has the colour of gx;
- **constant red**: all edges to V° are red;
- **constant blue**: all edges to V° are blue.

The colours among the 81 vertices of C ∪ I and the added vertices are given by the file.

| Vertices | Names | Type |
|---|---|---|
| 1596–1605 | a₀,…,a₉ | constant blue |
| 1606–1615 | b₀,…,b₉ | copies of c₀,…,c₉ |
| 1616–1626 | x₀,…,x₉, x_* | constant red |
| 1627–1636 | y₀,…,y₉ | copies of i₀,…,i₉ |
| 1637 | y_* | constant blue |
| 1638 | z | copy of c₀ |
| 1639, 1640 | w, u | copies of i₀ |
| 1641–1647 | v₁,…,v₇ | copies of c₁,…,c₇ |
| 1648 | v₈ | copy of i₆ |
| 1649 | v₉ | copy of c₆ |
| 1650–1656 | v₁₀,…,v₁₆ | copies of i₅, i₂, i₉, c₈, i₃, i₄, i₈ |

The names a₀ … u are those of the 45 added vertices of r1212-1642, which have the same types there. The colours among the added vertices are different. In total there are 11 constant red, 11 constant blue and 39 copies:

| | c₀ | c₁ | c₂ | c₃ | c₄ | c₅ | c₆ | c₇ | c₈ | c₉ |
|---|---|---|---|---|---|---|---|---|---|---|
| copies | 2 | 2 | 2 | 2 | 2 | 2 | 3 | 2 | 2 | 1 |

| | i₀ | i₁ | i₂ | i₃ | i₄ | i₅ | i₆ | i₇ | i₈ | i₉ |
|---|---|---|---|---|---|---|---|---|---|---|
| copies | 3 | 1 | 2 | 2 | 2 | 2 | 2 | 1 | 2 | 2 |

r1212_1657.json records the same data in machine-readable form. verify/check_projection.py reads the types from the file itself, so it does not rely on this table.
