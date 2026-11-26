# L-meta-18249: a perfect matching in 4 by 4 bipartite graphs

The posted function is the OR of the twenty-four perfect matchings of K4,4, on
the sixteen edge bits (row major: the bit `4*i+j` is the edge from row `i` to
column `j`).  The step asks for 36 gates.  The fleet holds 45, "built by the
first row expanded, every smaller minor shared".

## A construction with 47 gates

Split the rows in two and the columns in two.  For a pair of columns `S` let

    A(S) = the rows 0,1 are matched to S   = (x0s & x1t) | (x0t & x1s)
    B(T) = the rows 2,3 are matched to T   = (x2u & x3v) | (x2v & x3u)

Then

    f = OR over the six pairs S of columns of ( A(S) & B(complement of S) )

because every perfect matching splits the columns between the two rows pairs
in exactly one way.  Twelve two-row functions cost three gates each, six
products cost one each and the final OR costs five, so 47 gates in all.
`methods/find/pm44.py` builds the circuit and checks it on all 65536 inputs.

## Why it does not beat 45

The first row expanded, with the minors shared, is cheaper here.  Writing the
4 by 4 case as

    f = OR over the column j of row 0 of ( x0j & PM3(j) )

the minor `PM3(j)` is the perfect matching of rows 1,2,3 on the three columns
left over.  Each of the six `PM2` minors (rows 2,3 on a pair of columns) costs
three gates and is used twice, the twelve products `x1k & PM2` cost one each,
the four `PM3` cost two ORs each, and the final step four products and three
ORs:

    18 + 12 + 8 + 4 + 3 = 45

which is the fleet's number.  The two constructions sit on either side of the
same wall: the two-row split needs twelve two-row permanents where the
first-row split needs six plus twelve single products, and 36 + 11 against
18 + 12 + 8 + 4 + 3 is the comparison.

## What would be needed

36 gates is 20 per cent below the record.  A gate count below 45 needs a
different arrangement, not a different split of the same rows and columns.
Two things worth trying next, neither of them done here: sharing the `PM3`
minors between the four cases of the first row split, and the `PM2` minors
across a split of the columns as well as of the rows, which is what the
47-gate construction does and which does not pay.

The 4 by 4 step is also the second rung of a ladder; the perfect matching in
3 by 3 bipartite graphs sits at rungs 13, 12 and 11 (L-meta-17387,
L-meta-17388, L-meta-17389) and the same first-row split gives 14 there, so
that ladder is one gate out of reach as well.
