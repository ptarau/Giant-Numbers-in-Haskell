# Giant-Numbers-in-Haskell
Hereditarily Binary Numbers - a tree representation of giant numbers with a complete set of arithmetic operations

### Complete documentation - in the form of two literate programs from which HBin.hs and HBinX.hs have been extracted is in directory [doc](https://github.com/ptarau/Giant-Numbers-in-Haskell/tree/master/doc).

### Here are the two summaries:

#### HBin.hs / HBin.pdf

In a typed functional language we specify a new tree-based number representation, hereditarily binary numbers, defined by applying recursively run-length encoding of bijective base- 2 digits.

Hereditarily binary numbers support arithmetic operations that are limited by the structural complexity of their operands, rather than their bitsizes.

As a result, they enable new algorithms that, in the best case, collapse the complexity of arithmetic computations by super-exponential factors and in the worst case are within a constant factor of their traditional counterparts.

#### HBinX.hs / HBinX.pdf

Hereditarily binary numbers are a tree-based number representation derived from a bijection between natural numbers and iterated applications of two simple functions corresponding to bijective base 2 numbers. 

We describes several new arithmetic algorithms on hereditarily binary numbers that, while within constant factors from their traditional counterparts for their average case behavior, make tractable important computations that are impossible with traditional number representations.

###Keywords: hereditary numbering systems, compressed number representations, arithmetic computations with giant numbers, compact representation of large prime numbers