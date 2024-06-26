Misc.v: extended standard library
Inductive.v: generated by Inductive.ml, a library for user-defined stronger induction principles
GenInd.v: a library for automatically generating induction principles for nested or mutually-recursive inductive predicates
Freevar.v: free variables and fresh name generation; provides tactics to generate fresh names
FEnv.v: environments, represented as associative lists from free variables to terms
Rewrite.v: general-purpose theorems and definitions for rewriting systems, including the various reflexive, symmetric or transitive closures of relations
Costar.v: coinductive transitive closure of a relation, specifying transitive closure or divergence
Pretty.v: general definitions for pretty-big-step semantics

STerm.v: definition of terms, represented by de Bruijn indices, and of substitutions and renamings
Beta.v: definition of beta-reduction and theorems on it, including confluence

Red.v: definition of pretty-big-step substitution semantics
RedProof.v: proof that this semantics is compatible with beta-reduction

RedE.v: definition of pretty-big-step environment semantics
RedEProof.v: proof that this semantics is compatible with the previous one

RedM.v: definition of pretty-big-step call-by-need semantics
RedMProof.v: proof that this semantics is compatible with the previous one

Convert.v: definition of the efficient convertibility machine and its correctness
