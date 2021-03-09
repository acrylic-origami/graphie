# Graphie

Graphie is a graph database converter and query frontend for HIE files for GHC. It converts the ASTs in HIE files to a Neo4J graph and provides a frontend client for navigating a codebase by following relationships and using graph queries.

**Compatibility note**: Graphie is only compatible with Neo4J 3.x, as the BOLT/Neo4J driver for Haskell ([Hasbolt](http://hackage.haskell.org/package/hasbolt)) [isn't yet compatible with Neo4J 4.x](https://github.com/zmactep/hasbolt/issues/21) - the latest BOLT protocol [has only recently been open-sourced](https://github.com/neo4j/neo4j/issues/12361#issuecomment-716483442).

Graphie fulfills a long-standing need I've had for a way to acquaint with a codebase quickly through statistics and data exploration. A notable example is [stacker](https://github.com/acrylic-origami/stacker) which I developed for this purpose too, specifically to identify the dependency set of a given callsite or value: this has been superceded by graphie. The Haskell code using the HIE API to navigate the ASTs can all be distilled into a few short graph queries.

**2020-12-28**: HIE &rarr; Neo4J direction works, albeit slowly. Investigating a faster way to shove data in, probably [using the bulk insertion methods provided by Neo4J](https://neo4j.com/developer/guide-import-csv/). Here's some idea of what the schema looks like, where node labels are camel-case and relationship types are uppercase snake-case ([standard Neo4J naming conventions](https://neo4j.com/docs/cypher-manual/current/syntax/naming/#_recommendations)), standard DDL convention for 1 (one), &gt;0 (+), 0 or 1 (?), &ge;0 (\*), relationships from (-) and to ([\*+?1]->), parameter sets that are disjoint (based on a `case` over datacons usually) are represented by brackets and pipes `|`:

```
GraphieAST
  1 ann_ctors [str]
  1 ann_tys [str]
  1 <span>
GraphieTy
  1 con string
  1 path string
  1 idx int
    ( 1 name string )
  | ( 1 value (int | str) )
GRAPHIE_AST2TY
  - GraphieAST
  *-> GraphieTy
  1 pos int
GraphieIdent
  1 con {Name, ModuleName}
  1 name string
  1 uniq string
GRAPHIE_AST2CTX
  - GraphieAST
  *-> GraphieCtx
GRAPHIE_AST2IDENT
  - GraphieAST
  *-> GraphieIdent
GRAPHIE_IDENT2TY
  - GraphieIdent
  *-> GraphieTy
GRAPHIE_AST2AST
  - GraphieAST
  *-> GraphieAST
  1 pos int
GraphieCtx
  1 con string
  1 path string
    ( 1 ietycon string)
  | ( 1 bindtycon string
      ? bind_<span>
    )
  | ( ? bind_<span>
      1 pat_<scope>
      1 out_<scope>
    )
  | ( ? bind_<span> )
  | ( 1 decltycon string
      ? bind_<span>
    )
  | ( 1 <scope> )
  | ( 1 ctxtycon string
      ? bind_<span>
    )
GRAPHIE_TY_REL
  - GraphieTy
  *-> GraphieTy
  1 path string
# GRAPHIE_NAME2NAME
#   - GraphieAST
#   - GraphieAST
GraphieHieFile
  1 hs_file string
  1 hie_module string
  1 hie_module_uniq string
GRAPHIE_FILE2AST
  - GraphieHieFile
  *-> GraphieHieAST
<span>
  1 ^sp_fn string
  1 ^sp_l0 int
  1 ^sp_ch0 int
  1 ^sp_lf int
  1 ^sp_chf int
<scope>
  1 ^scope string
  ? ^<span>
```