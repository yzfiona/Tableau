$Id: DLExploration.lhs,v 1.10 2004/11/23 16:27:19 graham Exp $

An exploration of Description Logics
====================================

This file is my attempt to better understand the structure and uses
of Description Logic (DL) [1] languages for knowledge reresentation and
inference, with the ultimate aim of better understanding the capabilities
and limitations of the Semantic Web [3] ontology language OWL [4], whose
design draws much from Description Logic languages.

"The main effort of the research in knowledge representation is providing
theories and systems for expressing structured knowledge and for accessing
and reasoning with it in a principled way. Description Logics are
considered the most important knowledge representation formalism unifying
and giving a logical basis to the well known traditions of Frame-based
systems, Semantic Networks and KL-ONE-like languages, Object-Oriented
representations, Semantic data models, and Type systems." [1]

This exploration is my attempt to consolidate my understanding of key
concepts from a reading of the Description Logics Handbook [2].

[1] http://dl.kr.org/

[2] http://www.dis.uniroma1.it/~nardi/dlhb/

[3] http://www.w3.org/2001/sw/

[4] http://www.w3.org/2001/sw/WebOnt/


My goal in doing this is to develop a deeper understanding of DL mechanics,
and in particular to understand the kinds of inference that can be
expressed using DLs.  It is not a goal of this exploration to address
issues of efficiency and decideability of inferences.

This file contains free text and embedded Haskell [5] code using
the conventions of "Literate Haskell" source code.  Each line starting
with a '>' character is executable source code.  This file can be loaded
and the expressions it contains can be evaluated using an interactive
Haskell system such as Hugs [6] or GHCi [7].  The file makes use of
standard Haskell library functions, and also two external libraries
called Data.Set and Data.Map.  When executing this module, the source
modules for these libraries should be available in subdirectory data
relative to a directory on the library search path for the Haskell
compiler used, or relative to the directory containing this module.

[5] http://www.haskell.org/

[6] http://www.haskell.org/hugs/

[7] http://www.haskell.org/ghc/
    http://www.haskell.org/ghc/docs/latest/html/users_guide/ghci.html


1. Preliminaries
================

1.1 Haskell preliminaries
-------------------------

> module DLExploration
> where
>
> import List ( partition, groupBy )
> import Maybe( catMaybes )
> import Monad( foldM, liftM )
> import Data.Map( Map(..) )
> import qualified Data.Map as Map
> import Data.Set( Set(..) )
> import qualified Data.Set as Set
>
> import Debug.Trace( trace )
>
> mkSet :: Ord a => [a] -> Set a
> mkSet = Set.fromList
>
> subsetOf :: Ord a => Set a -> Set a -> Bool
> subsetOf = Set.subset
>
> elementOf :: Ord a => a -> Set a -> Bool
> elementOf = Set.member

Use justElementOf to test that a value exists and, if so, to test
that it is a member of an indicated set.

> justElementOf :: Ord a => Maybe a -> Set a -> Bool
> justElementOf = maybe (const False) elementOf

Use pairSwapM to convert a pair of Maybe values into Maybe a pair of
bare values.  If either of the supplied values is Nothing, the result
is Nothing.  This is generalized to any monadic type:  it does for pairs
what sequence does for lists.

> pairSwapM :: Monad m => (m a,m b) -> m (a,b)
> pairSwapM (ma,mb) = do { a <- ma ; b <- mb ; return (a,b) }

-- pairSwapM (Just a,Just b) = Just (a,b)
-- pairSwapM _               = Nothing

Make list from reversed initial sublist and given trailing sublist.
This is a performance hack used as part of the logic that avoids repeated
scanning of a list when appending values, by allowing a list to be built
in reverse.

> revcat :: [a] -> [a] -> [a]
> revcat []     more = more
> revcat (a:as) more = revcat as (a:more)


1.2 DL Preliminaries
--------------------

DL's are centred on the idea of "Concept Descriptors", which are logical
descriptions of values, typically presented in a form analogous to
the point-free style of functional programs.

Elementary terms in a DL consist of:

> type AtomicConcept = String   -- named atomic concept
> type AtomicRole    = String   -- named atomic role

When performing inference with DL concepts, it is sometimes necessary
to consider individual members of some concept:

> type Individual    = String   -- named individual value


2. Defining and interpreting concepts in AL
===========================================

One of the simpler members of the DL family, known as AL (Attribute
Language), allows the following forms of concept expression:

> data ALConcept = ALAtomic AtomicConcept
>                | ALUniversal
>                | ALBottom
>                | ALNegate AtomicConcept
>                | ALIntersect ALConcept ALConcept
>                | ALAll AtomicRole ALConcept
>                | ALExistsAny AtomicRole
>     deriving (Show, Eq)

The semantics are defined in terms of a domain of interpretation,
to which all individuals must belong.  Any concept expression
is interpreted as some subset of the domain of interpretation,
and any role is interpreted as a set of pairs (a binary relation)
from the domain of interpretation.

An interpretation consists of:
- a set of values that is the domain of interpretation,
- a set of named atomic concepts
- a set of named atomic roles
thus (where all members of the domain of interpretation are
values of type 'a'):

> type AtomicConcepts a  = [(AtomicConcept,Set a    )]
> type AtomicRoles a     = [(AtomicRole   ,Set (a,a))]
>
> type TInterpretation a = (Set a,AtomicConcepts a,AtomicRoles a)

The name TInterpretation is used here to distinguish an
interpretetion of terminological definitions (Tbox) from an
interpretation of individual definitions (Abox).  These ideas
are described later in sections 2.1 and 2.2.

With the following functions provided to access an interpretation:

> iDom :: TInterpretation a -> Set a
> iDom (idom,_,_) = idom
>
> iC :: TInterpretation a -> AtomicConcept -> Set a
> iC (_,acs,_) cn = maybe Set.empty id $ lookup cn acs
>
> iR :: TInterpretation a -> AtomicRole -> Set (a,a)
> iR (_,_,ars) rn = maybe Set.empty id $ lookup rn ars

and some helper functions for dealing with role interpretations:

> iSuccessors :: (Ord a) => Set (a,b) -> [(a,Set b)]
> iSuccessors abs =
>     [ (head as,Set.fromDistinctAscList bs)
>     | abs1 <- groupBy fstEq (Set.toAscList abs)
>     , let (as,bs) = unzip abs1
>     ]
>     where
>         fstEq (a,_) (b,_) = a == b
> -- Map.toAscList . iSuccessorMap
>
> iSuccessorMap :: (Ord a) => Set (a,b) -> Map a (Set b)
> iSuccessorMap = Map.fromDistinctAscList . iSuccessors

To be a valid interpretation, all of the concept and role values must
be in the given domain of interpretation:

> isValidTInterpretation :: Ord a => TInterpretation a -> Bool
> isValidTInterpretation (idom,ics,irs) =
>     all ((`subsetOf`  idom) . snd) ics &&
>     all ((`elementOf` idom) . fst) rvals &&
>     all ((`elementOf` idom) . snd) rvals
>     where
>         rvals = concatMap (Set.toList . snd) irs

[[[TODO:  optimize the above to use Set functions more effectively]]]

The various forms of ALConcept expression can then be interpreted as follows:

> iAL :: Ord a => TInterpretation a -> ALConcept -> Set a
> iAL i (ALAtomic c)       = iC i c
> iAL i ALUniversal        = iDom i
> iAL _ ALBottom           = Set.empty
> iAL i (ALNegate c)       = iDom i `Set.difference` (iC i c)
> iAL i (ALIntersect c d)  = iAL i c `Set.intersection` iAL i d
> iAL i (ALAll r c)        = Set.fromDistinctAscList
>                                [ a | (a,bs) <- iSuccessors (iR i r)
>                                ,     bs `subsetOf` cs
>                                ]
>                            where cs = iAL i c
> iAL i (ALExistsAny r)    = Set.fromDistinctAscList
>                                [ a | (a,bs) <- iSuccessors (iR i r)
>                                ]

[[[
Note some conditions that must be satisfied, such as
   forall c, iAL c `subset` iAL ALUniversal
   forall c, iAL ALBottom `subset` iAL c

where a `subset` b = isEmptySet (a `minusSet` b)

Should the definitions be qualified by role and concept vocabularies?
]]]


2.1 Describing Concepts: the TBox
---------------------------------

How are inferences to be performed with such a structure?
Inferrable properties of concepts include:
- Satisfiability of C:  the existence of an interpretation such that
C is non-empty.
- Subsumption of C by D, if in every interpretation, all members of C
are also members of D.
- Equivalence of C and D, if in every interpretation C and D have
the same members.
- Disjointness, if in every interpretation, C and D have no members
in common.

The references here are to properties being satisfied by arbitrary
interpretations, rather than just some set of values, is something that
sets description logics apart from, say, simple database implementations.
In particular, this kind of concept-based reasoning can be used to draw
conclusions from partial information.

As it happens, the above properties can all be expressed in terms of
subsumption, so subsumption is a key relationship between DL concepts.

So far, the discussion has been in terms of unconstrained atomic concepts.
It is also possible to add constraints on the relationship between concepts,
using definitions:

> type ALDefinition = (AtomicConcept,ALConcept)

where the named atomic concept is taken to contain the same members as the
concept expression in every "acceptable" interpretation.  A collection of
such definitions, where no atomic concept is defined more than once,
is a TBox:

> type ALTBox = [ALDefinition]

A TBox can be understood as describing some concept interpretations that are
true in some world view;  i.e. those interpretations that satisfy all the
definitions in the TBox.  Such interpretations are models of the TBox.

> isALTModel :: Ord a => ALTBox -> TInterpretation a -> Bool
> isALTModel tbox i =
>     isValidTInterpretation i && all conceptMatch tbox
>     where
>         conceptMatch (ac,c) = iAL i c == iC i ac

Note that TBox constraints are sometimes expressed as subsumption relations
rather than as equalities.  These constraints can be expressed as equallities
through the introduction of new atomic concepts.
For example, the  constrant that C is included in D can be expressed by
a definition of C as the intersection of D with some new atomic concept:

> c_in_d = ("C",ALIntersect (ALAtomic "CnotD") (ALAtomic "D"))

where "CnotD" is a concept name not used elsewhere.

A TBox (or Terminology Box) can be thought of as defining a number of
named atomic concepts with respect to a number of base atomic concepts.
The base concepts are those whose members are determined solely by an
interpretation.

A definitorial TBox is one in which each of its named atomic concepts
is fully determined by any given interpretation of the base concepts.
That is, the TBox has exactly one model containing any given
interpretation of the base concepts.  Any TBox in which the definitions
are acyclic is definitorial;  I skip further discussion of this for now.


2.1.1 Examples

> exTBox211 :: ALTBox
> exTBox211 =
>     [ ("Woman",  ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>     , ("Man",    ALIntersect (ALAtomic "Person") (ALNegate "Female"))
>     , ("Mother", ALIntersect (ALAtomic "Woman")  (ALExistsAny "hasChild"))
>     , ("Father", ALIntersect (ALAtomic "Man")    (ALExistsAny "hasChild"))
>     , ("Parent", ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>     ]

Following the example from the DL handbook [2], section 2.2.2, I can see no
way to describe concepts like GrandMother, MotherWithoutDaughter and Wife
using only the terms of AL (except by the introduction of additional base
concepts).

Then the following interpretation is a model of exTBox1:

> exTInt211 :: TInterpretation String
> exTInt211 =
>     ( mkSet ["Peter","Paul","Mary","Harry","Spot","Rover"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Spot"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul","Harry"])
>             , ("Mother", mkSet ["Mary"])
>             , ("Father", mkSet ["Harry","Paul"])
>             , ("Parent", mkSet ["Mary","Harry","Paul"])
>             ]
>         aRoles =
>             [ ("hasChild", mkSet [ ("Mary","Paul")
>                                  , ("Harry","Paul")
>                                  , ("Paul","Peter") ] )
>             ]

Try it:

> tryTInt211 = isALTModel exTBox211 exTInt211

Note that 'Female' and 'Person' are base concepts here (i.e. are not defined
by the TBox in terms of other concepts, but they are not treated in any special
way by the interpretation.)

A model may interpret additional concepts and roles not mentioned by the TBox,
provided that they are in the domain of interpretation.

> exTInt211a :: TInterpretation String
> exTInt211a =
>     ( mkSet ["Peter","Paul","Mary","Harry","Spot","Rover","Thumper"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Spot"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul","Harry"])
>             , ("NewCon", mkSet ["Mary","Spot","Thumper"])
>             ]
>         aRoles =
>             [ ("NewRole", mkSet [ ("Mary","Peter")
>                                 , ("Rover","Thumper") ])
>             ]
> tryTInt211a = isALTModel exTBox211 exTInt211a

In this case, almost exactly the same interpretation is not valid because
"Thumper" is not in the domain of interpretation:

> exTInt211b :: TInterpretation String
> exTInt211b =
>     ( mkSet ["Peter","Paul","Mary","Harry","Spot","Rover"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Spot"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul","Harry"])
>             , ("NewCon", mkSet ["Mary","Spot","Thumper"])
>             ]
>         aRoles =
>             [ ("NewRole", mkSet [ ("Mary","Peter")
>                                 , ("Rover","Thumper") ])
>             ]
> tryTInt211b = isALTModel exTBox211 exTInt211b

This interpretation is not a model of exTBox1 because the interpretation
of concept "Man" does not agreee with the TBox description:

> exTInt211c :: TInterpretation String
> exTInt211c =
>     ( mkSet ["Peter","Paul","Mary","Harry","Spot","Rover"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Spot"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul"])
>             ]
>         aRoles = []
> tryTInt211c = isALTModel exTBox211 exTInt211c

This interpretation is not a model of exTBox1 because the interpretation
of role "hasChild" does not match in the TBox concept descriptions of
"Parent" and "Father".

> exTInt211d :: TInterpretation String
> exTInt211d =
>     ( mkSet ["Peter","Paul","Mary","Harry","Spot","Rover"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Spot"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul","Harry"])
>             , ("Mother", mkSet ["Mary"])
>             , ("Father", mkSet ["Harry","Paul"])
>             , ("Parent", mkSet ["Mary","Harry","Paul"])
>             ]
>         aRoles =
>             [ ("hasChild", mkSet [ ("Mary","Paul")
>                                  , ("Paul","Peter") ] )
>             ]
> tryTInt211d = isALTModel exTBox211 exTInt211d

(Check all of the above examples:)

> ex211 = and
>     [tryTInt211==True,tryTInt211a==True
>     ,tryTInt211b==False,tryTInt211c==False,tryTInt211d==False]


2.2 Describing Individuals: the ABox
------------------------------------

A knowledge base consists of a TBox and an ABox.  Where the TBox contains
assertions about concepts that are generally applicable to multiple
worldviews, an ABox contains assertions about individuals that are
applicable to a single worldview.  An ABox can make two kinds of assertion
about individuals, concept membership and role membership:

> type ALConceptAssertion = (ALConcept,Individual)
> type ALRoleAssertion    = (AtomicRole,Individual,Individual)
> type ALABox             = ([ALConceptAssertion],[ALRoleAssertion])

To deal with ABox semantics, interpretations are extended to deal with
individual names as well as concept names.

> type Individuals a     = [(Individual,a)]
> type AInterpretation a = Individuals a
> type Interpretation a  = (TInterpretation a,AInterpretation a)
>
> iA :: AInterpretation a -> Individual -> Maybe a
> iA ias a = lookup a ias

To be a valid interpretation (with respect to a given TInterpretation),
all values given by the AInterpretation must be in the domain of discourse,
and the TInterpretation must be valid.

> isValidAInterpretation :: Ord a => TInterpretation a -> AInterpretation a -> Bool
> isValidAInterpretation (idom,_,_) ias = all ((`elementOf` idom) . snd) ias
>
> isValidInterpretation it ia =
>     isValidTInterpretation it && isValidAInterpretation it ia

An interpretation is a model of an ABox if it is a valid interpretation
and if it satisfies the assertions in the ABox:

> isALAModel :: Ord a => ALABox -> Interpretation a -> Bool
> isALAModel abox i@(it,ia) =
>     isValidInterpretation it ia &&
>     all isValidConceptAssertion (fst abox) &&
>     all isValidRoleAssertion    (snd abox)
>     where
>         isValidConceptAssertion (c,a) = iA ia a `justElementOf` iAL it c
>         isValidRoleAssertion (r,a,b)  = pairSwapM (iA ia a,iA ia b) `justElementOf` iR it r

(recall: PairSwapM moves the Maybe outside the pair.)

An interpretation is a model of an ABox with respect to a TBox if
it is a model of the ABox and its TInterpretation component
is also a model of the TBox:

> isALModel :: Ord a => ALTBox -> ALABox -> Interpretation a -> Bool
> isALModel tbox abox i@(it,_) = isALAModel abox i && isALTModel tbox it


2.2.1 Examples

Using the TBox example from section 2.1.1, define an ABox
(using names prefixed with 'i' to distinguish individual names):

> exABox221 :: ALABox
> exABox221 =
>     ( [ (ALAtomic "Female","imary")
>       , (ALAtomic "Person","ipeter")
>       , (ALAtomic "Person","ipaul")
>       , (ALAtomic "Person","imary")
>       , (ALAtomic "Person","iharry")
>       ]
>     , [ ("hasChild","imary","ipaul")
>       ]
>     )

Then define an AInterpretation for the symbols introduced here,
and hence a combined interpretation with exTInt1:

> exAInt221 :: AInterpretation String
> exAInt221 =
>     [("ipeter","Peter")
>     ,("ipaul" ,"Paul" )
>     ,("imary" ,"Mary" )
>     ,("iharry","Harry")
>     ]
> exInt221 :: Interpretation String
> exInt221 = (exTInt211,exAInt221)

And try it:

> tryInt221 = isALModel exTBox211 exABox221 exInt221

But with a different interpretation of the individuals that does not
match the TBox interpretation and constraints, we have an interpretation
that is not a model with respect to the TBox and its interpretation:

> exAInt221a :: AInterpretation String
> exAInt221a =
>     [("ipeter","Paul")
>     ,("ipaul" ,"Peter" )
>     ,("imary" ,"Mary" )
>     ,("iharry","Harry")
>     ]
> exInt221a :: Interpretation String
> exInt221a = (exTInt211,exAInt221a)
>
> tryInt221a = isALModel exTBox211 exABox221 exInt221a

> ex221 = and [tryInt221==True, tryInt221a==False]


2.3 Inferences
--------------

So how can the above be used to derive new information?
What are the limits of possible inference?
Published results suggest that there are quite severe limits on what
can be inferred using a description logic like AL.


2.3.1 Concept inferences

Noted previously, inference tasks for concepts include:
- Satisfiability of C
- Subsumption of C by D
- Equivalence of C and D
- Disjointness of C and D

All of these can be reduced to subsumption.  Define:

> isALSatisfiable :: ALConcept -> Bool
> isALSatisfiable c = not (c `isALSubsumedBy` ALBottom)
>
> isALEquivalent  :: ALConcept -> ALConcept -> Bool
> isALEquivalent c d = (c `isALSubsumedBy` d) && (d `isALSubsumedBy` c)
>
> isALDisjoint    :: ALConcept -> ALConcept -> Bool
> isALDisjoint c d = (ALIntersect c d) `isALSubsumedBy` ALBottom

Then the hard work is all in the subsumption test.
For simple description logics, a structural subsumption algorithm
can be used, which operates by normalizing the concept expressions
to be tested, then performing a comparison of their syntactic structures.

The normalized form of concept expression consists of a conjunction
of simple concept expressions which are for the most part treated as
atomic concepts (except that in some cases they can be combined),
and compound expressions themselves containing concept expressionbs
which are normalized recursively.

For AL, the concept expressions in a normalized conjunction are:
- bottom concept (bot)
- universal concept (univ)
- atomic named concepts (A and -A), with each A at most once
- values all of whose fillers for a named role are a given concept c (all R.c),
  with each distinct R appearing no more than once.
- values with named role relationship with some other value (exists R.univ),
  with each distinct R appearing at most once.

The normalized form is sorted so that the comparison for subsumption can
proceed in a single pass of the conjunct:
- atomic named concepts and negations, sorted by concept name
- role expressions, sorted by role name

The following simplifications can then be applied to the conjunct:

  (bot /\ x)  ==> bot,                  for any x
  (univ /\ x) ==> x,                    for any x
  (A /\ -A)   ==> bot,                  for any A

(hence bot and univ appear only as isolated terms, not as part of a conjunction.)

  (all R.c) /\ (all R.d) ==> (all R.(c /\ d))
  (all R.univ)           ==> univ
  (all R.bot) /\ (exists R.univ) ==> bot

NOTE: (all R.bot) is satisfiable by concepts which have no fillers for role R.

Define data structure for normalized concept expression.

> data ALNormalized = ALbot | ALtop | ALconj [ALTerm]
>     deriving Eq
>
> data ALTerm       = ALnam AtomicConcept
>                   | ALneg AtomicConcept
>                   | ALany AtomicRole
>                   | ALall AtomicRole ALNormalized
>     deriving Eq

Normalization works from bottom up, sorting as conjunctions are merged.

> normalizeAL :: ALConcept -> ALNormalized
> normalizeAL (ALBottom)        = ALbot
> normalizeAL (ALUniversal)     = ALtop
> normalizeAL (ALAtomic c)      = ALconj [ALnam c]
> normalizeAL (ALNegate c)      = ALconj [ALneg c]
> normalizeAL (ALExistsAny r)   = ALconj [ALany r]
> normalizeAL (ALAll r c)       = ALconj [ALall r (normalizeAL c)]
> normalizeAL (ALIntersect c d) = conj (normalizeAL c) (normalizeAL d)
>     where
>         conj ALbot _     = ALbot
>         conj _     ALbot = ALbot
>         conj ALtop c     = c
>         conj c     ALtop = c
>         conj (ALconj cs) (ALconj ds) = (conj1 cs ds) []
>         conj1 cs               []               acc = ALconj (revcat acc cs)
>         conj1 []               ds               acc = ALconj (revcat acc ds)
>         conj1 c@(ALnam cn:_)   d@(ALnam dn:_)   acc = conjEq cn dn c d acc
>         conj1 c@(ALnam cn:_)   d@(ALneg dn:_)   acc = conjNe cn dn c d acc
>         conj1 c@(ALneg cn:_)   d@(ALnam dn:_)   acc = conjNe cn dn c d acc
>         conj1 c@(ALneg cn:_)   d@(ALneg dn:_)   acc = conjEq cn dn c d acc
>         conj1   (ALnam cn:cs)  d                acc = conj1 cs d  (ALnam cn:acc)
>         conj1 c                  (ALnam dn:ds)  acc = conj1 c  ds (ALnam dn:acc)
>         conj1   (ALneg cn:cs)  d                acc = conj1 cs d  (ALneg cn:acc)
>         conj1 c                  (ALneg dn:ds)  acc = conj1 c  ds (ALneg dn:acc)
>         conj1 c@(ALall r rc:_) d@(ALall s sc:_) acc = conjRc r rc s sc c d acc
>         conj1 c@(ALall r rc:_) d@(ALany s:_)    acc = conjRe r rc s c d acc
>         conj1 c@(ALany r:_)    d@(ALall s sc:_) acc = conjRe s sc r d c acc
>         conj1 c@(ALany r:_)    d@(ALany s:_)    acc = conjEq r s c d acc
>         -- Conjoin similar atomic concepts: if same name, one is dropped
>         conjEq cn dn c@(c1:cs) d@(d1:ds) acc | cn == dn  = conj1 cs ds (c1:acc)
>                                              | cn <  dn  = conj1 cs d  (c1:acc)
>                                              | otherwise = conj1 c  ds (d1:acc)
>         -- Conjoin complementary atomic concepts: same names cancel to bottom
>         conjNe cn dn c@(c1:cs) d@(d1:ds) acc | cn == dn  = ALbot
>                                              | cn <  dn  = conj1 cs d  (c1:acc)
>                                              | otherwise = conj1 c  ds (d1:acc)
>         -- Conjoin 'All' and 'Any' role restrictions: Any and All bottom cancel
>         -- to bottom, otherwise sort All before Any (see comment below).
>         -- 'r' is 'All' restriction role name, 's' is for 'Any' restriction
>         conjRe r rc s c@(c1:cs) d@(d1:ds) acc | r == s && rc == ALbot = ALbot
>                                               | r <= s    = conj1 cs d  (c1:acc)
>                                               | otherwise = conj1 c  ds (d1:acc)
>         -- Conjoin 'All' role restrictions:  if same role name then make a single
>         -- restriction to the conjunction of class restrictions
>         conjRc r rc s sc c@(c1:cs) d@(d1:ds) acc | r == s    = conj1 cs ds (ALall r (conj rc sc):acc)
>                                                  | r <  s    = conj1 cs d  (c1:acc)
>                                                  | otherwise = conj1 c  ds (d1:acc)

Sorting 'All' restrictions before 'Any' restrictions in the normalization code means
that intersecting 'All' restrictions that result in a restriction to bottom are
processed before possible cancellation with existential role restrictions.

Subsumption testing works by first normalizing the expressions (above), then comparing
the resulting sorted expressions.  Essentially, C is subsumed by d if for every conjuct
term in d there is a term in c that is at least as constrained.

> isALSubsumedBy :: ALConcept -> ALConcept -> Bool
> isALSubsumedBy c d = sub (normalizeAL c) (normalizeAL d)
>     where
>         sub ALbot _     = True
>         sub _     ALtop = True
>         sub _     ALbot = False
>         sub ALtop _     = False
>         sub (ALconj cs) (ALconj ds) = sub1 cs ds
>         -- sub1 relies on sorting in the normalized conjunction:
>         sub1 _                []               = True
>         sub1 []               _                = False
>         sub1 c@(ALall r rc:_) d@(ALall s sc:_) = subRc r rc s sc c d
>         sub1 c                d                = subAt c d
>         -- Subsumption test atomic concepts
>         -- (including negations, existential role restrictions, etc.)
>         subAt c@(c1:cs) d@(d1:ds) | c1 == d1  = sub1 cs ds
>                                   | otherwise = sub1 cs d
>         -- Subsumption test 'All' role restructions.  If role names are equal
>         -- then subsumption requires subsumption between the class restrictions.
>         subRc r rc s sc c@(_:cs) d@(d1:ds) | r == s    = sub rc sc && sub1 cs ds
>                                            | otherwise = sub1 cs d

It is also sometimes desired to calculate the least common subsumer (or greatest common
subsumed) class for two or more given class expressions.  The result of such a
computation is a new class description that subsumes (or is subsumed by) each of
the original descriptions.  The above structural subsumption test is easily modified
to construct such a class description, but it is not clear to me whether such a
computation is easily done for other description logics.


2.3.1.1 Subsumption examples

Any concept subsumes itself:

> trySub2311a = isALSubsumedBy (ALAtomic "Person") (ALAtomic "Person")

But not its negation:

> trySub2311b = isALSubsumedBy (ALAtomic "Person") (ALNegate "Person")
> trySub2311c = isALSubsumedBy (ALNegate "Person") (ALAtomic "Person")

Nor by a different atomic concept:

> trySub2311d = isALSubsumedBy (ALAtomic "Person") (ALAtomic "Dog")

A conjunct is subsumed by any of its components:

> trySub2311e = isALSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>     (ALAtomic "Person")
> trySub2311f = isALSubsumedBy
>     (ALIntersect (ALIntersect (ALAtomic "Dog") (ALNegate "Female"))
>                  (ALAtomic "Person"))
>     (ALIntersect (ALAtomic "Person") (ALNegate "Female"))

Treat existential role restruction as an atomic concept:

> trySub2311g = isALSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasParent"))
> trySub2311h = isALSubsumedBy
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>                  (ALExistsAny "hasChild"))
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))

Finally, note that role restriction to a concept depends on subsumption of
the restricting concept

> trySub2311i = isALSubsumedBy
>     (ALIntersect (ALAtomic "Person")
>                  (ALAll "hasChild" (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))))
>     (ALIntersect (ALAtomic "Person") (ALAll "hasChild" (ALAtomic "Female")))
> trySub2311j = isALSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALAll "hasChild" (ALAtomic "Female")))
>     (ALIntersect (ALAtomic "Person")
>                  (ALAll "hasChild" (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))))

Collected subsumption examples:

> ex2311 = and
>     [trySub2311a==True, trySub2311b==False,trySub2311c==False,trySub2311d==False
>     ,trySub2311e==True, trySub2311f==True
>     ,trySub2311g==False,trySub2311h==True
>     ,trySub2311i==True, trySub2311j==False
>     ]


2.3.2 Inferences about individuals

Inferences that one might wish to perform using a specific world-view
described by an ABox include:
- is a specific assertion entailed by the ABox:
  A |= R(a,b) or A |= C(a)
  The latter reduces to non-satisfiability of A and (not C(a))
- enumerate the values of a such that C(a)
- enumerate the values of (a,b) such that C(a,b)
- find the most specific concept(s) C such that A |= C(a), for
  a given individual

Many common inference problems are formulated by creating a description
of some desired concept, then enumerating individuals satisfying that
concept.  However, to perform a query that returns tuples of such
individuals seems less easy to do, absent some kind of tuple-forming
operation in the language.

This is the ABox from section 2.2.1 (exABox221), extended to include
some additional concepts from the TBox from section 2.1.1 (exTBox211):

> exABox232 :: ALABox
> exABox232 =
>     ( [ (ALAtomic "Female","imary")
>       , (ALAtomic "Person","ipeter")
>       , (ALAtomic "Person","ipaul")
>       , (ALAtomic "Person","imary")
>       , (ALAtomic "Person","iharry")
>       , (ALAtomic "Woman", "imary")
>       , (ALAtomic "Man",   "ipeter")
>       , (ALAtomic "Man",   "ipaul")
>       , (ALAtomic "Man",   "iharry")
>       , (ALAtomic "Parent","imary")
>       , (ALAtomic "Parent","ipater")
>       ]
>     , [ ("hasChild","imary", "ipaul")
>       , ("hasChild","ipeter","ipaul")
>       ]
>     )

Some concepts we may wish to explore might be:

> exMother = ALIntersect (ALAtomic "Parent") (ALAtomic "Female")
> exFather = ALIntersect (ALAtomic "Parent") (ALNegate "Female")
> exNobody = ALIntersect (ALAtomic "Female") (ALNegate "Female")


2.3.3 Eliminating TBox definitions

Subsequent reasoning operations are facilitated by reducing concept
expressions to equivalents that are not dependent on a particular TBox.

If the TBox definitions are acyclic, this is easily achieved by replacing
TBox concept names with their equivalent expressions.  (But this can
result in the resulting expressions being rather larger.)

For cyclic TBox definitions, this substition cannot be performed, but
tableau algorithms used for more expressive description logics can be
adapted to handle these cases.


3. Generalizing to other Description Logics
===========================================

So far, a single Description Logic (AL) has been considered.  My next step
is to generalize the function interface to a collection of type classes
that can handle arbitrary description logics.  The basic ideas of concepts,
roles and interpretations are common to all description logics, so these
are used as defined above.  It is the concept descriptions, role descriptions
and associated operations that need to be further abstracted:

- class (Eq c, Show c) => ConceptExpr c where
-     iConcept :: Ord a => TInterpretation a -> c -> Set a

> class (Eq r, Show r) => RoleExpr r where
>     iRole    :: Ord a => TInterpretation a -> r -> Set (a,a)

(The full and final definition of ConceptExpr is given later, in section 3.3.)

Note that some description logics allow role expressions as well as concept
expressions, where AL allows only atomic role names, so a new type class is
introduced here for role expressions.  The method iRole will replace iR in
situations where iR is used to interpret atomic roles in AL expressions.


3.1 Generalizing the Tbox
-------------------------

The following type synonyms are parameterized with a type that is
an instance of ConceptExpr (c):

> type Definition c = (AtomicConcept,c)
> type TBox c       = [Definition c]
>
> simpleTBox defs     = defs
> emptyTBox           = []

Then the function to test if an interpretation is a Model of a Tbox is
parameterized by the ConceptExpr instances upon which the Tbox is based:

> isTBoxModel :: (Ord a, ConceptExpr c)
>     => TBox c -> TInterpretation a -> Bool
> isTBoxModel tbox i =
>     isValidTInterpretation i && all conceptMatch tbox
>     where
>         conceptMatch (ac,c) = iConcept i c == iC i ac

This is almost identical to the function given earlier for AL, except that
the concept interpretation function iAL has been replaced by class method
iConcept.

Declare AtomicConcept and AtomicRole as instances of ConceptExpr and RoleExpr
(AtomicRole is used by AL, and including AtomicConcept here for completeness).

> instance ConceptExpr AtomicConcept where
>     iConcept = iC
>
> instance RoleExpr AtomicRole where
>     iRole = iR

Finally, define ALConcept as an instance of ConceptExpr:

- instance ConceptExpr ALConcept where
-     iConcept = iAL

(The full definition is later, in section 3.3)


3.1.1 Example: Generalized Tbox for AL

Using the first example from section 2.1.1, but expressed as an
instance of ConceptExpr:

> exTBox311 :: TBox ALConcept
> exTBox311 = simpleTBox exTBox211
>
> exTInt311 :: TInterpretation String
> exTInt311 = exTInt211

Try it:

> tryTInt311 = isTBoxModel exTBox311 exTInt311

Collect test cases:

> ex311 = and
>     [tryTInt311==True]


3.2 Generalizing the Abox
-------------------------

The following type synonyms are parameterized with types that are
an instance of ConceptExpr (c) or RoleExpr (r):

> type ConceptAssertion c = (c,Individual)
> type RoleAssertion    r = (r,Individual,Individual)
> type ABox r c           = ([ConceptAssertion c],[RoleAssertion r])

And the function to test if an interpretation is a Model of an Abox is
parameterized by the ConceptExpr and RoleExpr instances upon which the
Abox is based:

> isABoxModel :: (Ord a, ConceptExpr c, RoleExpr r)
>     => ABox r c -> Interpretation a -> Bool
> isABoxModel abox i@(it,ia) =
>     isValidInterpretation it ia &&
>     all isValidConceptAssertion (fst abox) &&
>     all isValidRoleAssertion    (snd abox)
>     where
>         isValidConceptAssertion (c,a) = iA ia a `justElementOf` iConcept it c
>         isValidRoleAssertion (r,a,b)  = pairSwapM (iA ia a,iA ia b) `justElementOf` iRole it r

Then the function to test if an interpretation is a model of an Abox with respect
to a given Tbox is:

> isModel :: (Ord a, ConceptExpr c, RoleExpr r)
>     => TBox c -> ABox r c -> Interpretation a -> Bool
> isModel tbox abox i@(it,_) = isABoxModel abox i && isTBoxModel tbox it


3.2.1 Example: Generalized Abox for AL

Continuing the example from section 3.1.1 (using the example data from
sections 2.1.1 ans 2.2.1):

> exABox321 :: ABox AtomicRole ALConcept
> exABox321 = exABox221
>
> exAInt321 :: AInterpretation String
> exAInt321 = exAInt221
>
> exInt321 :: Interpretation String
> exInt321 = (exTInt311,exAInt321)

Try it:

> tryInt321 = isModel exTBox311 exABox321 exInt321

Collect test cases:

> ex321 = and
>     [tryInt321==True]


3.3 Generalizing inference
--------------------------

As observed previously (section 2.3.1), satsifiability can be expressed
in terms of subsumption.  Alternatively, subsumption can be expressed in
terms of satisfiability, and tableau algorithms for working with advanced
description logics use a satisfiability test as the basis for computing
subsumtion.  Thus, a generalized inference interface must allow the full
range of inferences to be defined in terms of either of these.

  c <= d = not satisfiable ( c /\ �d )

Further, the knowledge base upon which the inferences are based may be
non-definitorial.  That is, it may be not possible to replace references
in an expression to classes constrained in the knowledge base so that
only base concepts remain.  Thus, inference may need to be performed with
respect to a given knowledge base.

The class interface for concept expressions is therefore defined in two
parts, dealing with basic concept values and advanced inference testing
(the latter possibly taking some knowledge base into account):

> class (Eq c, Show c) => ConceptExpr c where
>     iConcept          :: Ord a => TInterpretation a -> c -> Set a
>     emptyClass        :: c -> c
>     complementClass   :: c -> c
>     intersectClass    :: c -> c -> c
>     -- Class expression testing.
>     -- Repeated application of tableau expansion rules are required to
>     -- evenutally yield primitive class expressions, for which clashing
>     -- combinations can be detected by 'classMerge'.  'isPrimitive' is
>     -- an optimization to avoid performing futile merge tests.
>     isPrimitiveClass  :: c -> Bool
>     classMerge        :: c -> c -> Maybe [c]  -- recognizes primitive classes
>
> class (ConceptExpr c) => ConceptInferrable c where
>     isSatisfiable     :: c -> Bool
>     isSatisfiable c = not (isSubsumedBy c (emptyClass c))
>     isSubsumedBy      :: c -> c -> Bool
>     isSubsumedBy c d =
>         not $ isSatisfiable (intersectClass c (complementClass d))

To express these default relationships, the logic used must include a
generalized negation, intersection and an empty class value.
For logics that do not have expressions for these concepts, the
corresponding function must be defined explicitly.
In instances that do not support inference with respect to a given
knowledge base, the tests should fail if the supplied Tbox is non-empty.

<aside>
Equivalence can also be expressed as a satisfaction test, but as the
following analysis shows, the class expression to be satisfied must
include a disjunction.  Disjunction is a source of non-determinism
in some satisfaction tests, which can lead to poor performance.

c == d = (not (satisfiable (�c /\ d))) && (not (satisfiable (c /\ �d)))
       = not (satisfiable (�c /\ d) || satisfiable (c /\ �d))
       = not (satisfiable ((�c /\  d) \/ (c  /\ �d)))
       = not (satisfiable ((�c \/  c) /\ (�c \/ �d) /\ (d  \/ c) /\ (d /\ �d)))
       = not (satisfiable ((�c \/ �d) /\ (d  \/  c)))
</aside>

Finally, define ALConcept as an instance of ConceptExpr:

> instance ConceptExpr ALConcept where
>     iConcept        = iAL
>     emptyClass _    = ALBottom
>     complementClass = error "No general class complement in AL"
>     intersectClass  = ALIntersect
>     isPrimitiveClass (ALBottom)    = True
>     isPrimitiveClass (ALUniversal) = True
>     isPrimitiveClass (ALAtomic _)  = True
>     isPrimitiveClass (ALNegate _)  = True
>     isPrimitiveClass  _            = False
>     classMerge _                    (ALBottom)                = Nothing
>     classMerge    (ALBottom)     _                            = Nothing
>     classMerge c1                   (ALUniversal)             = Just [c1]
>     classMerge    (ALUniversal)  c2                           = Just [c2]
>     classMerge c1@(ALAtomic i1)     (ALAtomic i2) | i1 == i2  = Just [c1]
>     classMerge    (ALAtomic i1)     (ALNegate i2) | i1 == i2  = Nothing
>     classMerge    (ALNegate i1)     (ALAtomic i2) | i1 == i2  = Nothing
>     classMerge c1@(ALNegate i1)     (ALNegate i2) | i1 == i2  = Just [c1]
>     classMerge c1                c2                           = Just [c1,c2]
>
> instance ConceptInferrable ALConcept where
>     isSubsumedBy             = isALSubsumedBy
>     isSatisfiable            = isALSatisfiable


3.3.1 Example: Generalized concept inference for AL

Here is a re-casting of the inference examples from section 2.3.1.1

Any concept subsumes itself:

> trySub331a = isSubsumedBy (ALAtomic "Person") (ALAtomic "Person")

But not its negation (and using the abbreviated function for the remaining
examples):

> trySub331b = isSubsumedBy (ALAtomic "Person") (ALNegate "Person")
> trySub331c = isSubsumedBy (ALNegate "Person") (ALAtomic "Person")

Nor by a different atomic concept:

> trySub331d = isSubsumedBy (ALAtomic "Person") (ALAtomic "Dog")

A conjunct is subsumed by any of its components:

> trySub331e = isSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>     (ALAtomic "Person")
> trySub331f = isSubsumedBy
>     (ALIntersect (ALIntersect (ALAtomic "Dog") (ALNegate "Female"))
>                  (ALAtomic "Person"))
>     (ALIntersect (ALAtomic "Person") (ALNegate "Female"))

Treat existential role restruction as an atomic concept:

> trySub331g = isSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasParent"))
> trySub331h = isSubsumedBy
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>                  (ALExistsAny "hasChild"))
>     (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))

Finally, note that role restriction to a concept depends on subsumption of
the restricting concept

> trySub331i = isSubsumedBy
>     (ALIntersect (ALAtomic "Person")
>                  (ALAll "hasChild" (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))))
>     (ALIntersect (ALAtomic "Person") (ALAll "hasChild" (ALAtomic "Female")))
> trySub331j = isSubsumedBy
>     (ALIntersect (ALAtomic "Person") (ALAll "hasChild" (ALAtomic "Female")))
>     (ALIntersect (ALAtomic "Person")
>                  (ALAll "hasChild" (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))))

Collected subsumption examples:

> ex331 = and
>     [trySub331a==True, trySub331b==False,trySub331c==False,trySub331d==False
>     ,trySub331e==True, trySub331f==True
>     ,trySub331g==False,trySub331h==True
>     ,trySub331i==True, trySub331j==False
>     ]


4. Tableau reasoning for generalized description logics
=======================================================

Unlike structural reasoning, tableau based reasoning for description logics
hinges on a satisfaction algorithm that proceeds thus:  assume the existence
of a value satisfying a concept, and then use a set of expansion rules based
on the logic concerned to infer new values until (a) a complete set of implied
values needed for x to satisfy the given concept have been found, or (b) an
"obvious" contradiction is revealed - in our case, inferring that a value is a
member of some class and also of its complement.

The expansion rules used do depend on the description logic used, but the
basic tableau representation is not.  A tableau is a graph whose nodes represent
values and whose edges represent relations between the values:

A complete tableau describes a set of values that are part of an interpretation
of a concept expression, and the role relationbships between those values.
In describing tableaux and operations on tableaux, it is sometimes useful to
talk of 'role successors'.  A 'role successor' v1 of a value v0 is a value
that is related to v0 by some role relation.  An 'r-successor' of v0 is a value
related to v0 by the specific role r.

[[[
TODO:  need to reconsider index structures for roles here, to focus on
efficient discovery of successor, and maybe predecessor, values.
]]]

> data {- ConceptExpr c, RoleExpr r) => -} Tableau r c = Tableau
>     { tableauValues :: Map ValueId [c]
>     , tableauRoles  :: Map (ValueId,ValueId) [r]
>     , nextValueId   :: ValueId
>     } deriving Show
> type ValueId        = Int     -- arbitrary identifier for implied values

Define also a null tableau value and a helper function for creating new
tableau values:

> nullTableau = Tableau
>     { tableauValues = Map.empty
>     , tableauRoles  = Map.empty
>     , nextValueId   = 0
>     }
>
> makeTableau :: [(ValueId,[c])] -> [((ValueId,ValueId),[r])] -> ValueId -> Tableau r c
> makeTableau vs rs vid = Tableau
>     { tableauValues = Map.fromList vs
>     , tableauRoles  = Map.fromList rs
>     , nextValueId   = vid
>     }

For use in conjunction with this, we define a tableau expansion rule

> type TableauExpansionRule r c = Tableau r c -> [Tableau r c]

The rule returns an empty list if no expansion of the tableau can be performed
using this rule, or a list of values corresponding to alternative possible
extensions of the tableau using this rule.  The return values contain new
class and role assertions that are to be added to the supplied tableau, and an
updated value identifier to be used for further evaluation of the tableau
containing that extension.  Clash detection is performed when the new values
are merged into the existing tableau:

> -- Tableau extension merging function:  takes a base tableau and a list of
> -- alternative extensions generated by some rule, and returns:
> --   Just []  if there are no new tableaux generated by the extensions given,
> --   Just ts  a non-empty list of generated tableaux for which no clash is detected
> --   Nothing  if all of the generated tableax can be detected as containing a clash
> --
> -- Note that when a rule provides any extensions, at least one of them must lead to
> -- a model of the expression under test.
> --
> tableauMerge :: (ConceptExpr c, RoleExpr r) =>
>     Tableau r c -> [Tableau r c] -> Maybe [Tableau r c]
> tableauMerge oldt []    = Just []
> tableauMerge oldt newts = listOrNothing $ catMaybes $ map (tableauMerge1 oldt) newts
>     where
>         listOrNothing [] = Nothing
>         listOrNothing as = Just as
>
> -- tableauMerge helper, merges a pair of tableau values:
> tableauMerge1 :: (ConceptExpr c, RoleExpr r) =>
>     Tableau r c -> Tableau r c -> Maybe (Tableau r c)
> -- tableauMerge1 t1 t2
> --     | seq (traceShow "tableauMerge1:t1 " t1) $
> --       seq (traceShow "              t2 " t2) $ False = undefined
> tableauMerge1 (Tableau oldv oldr oldi) (Tableau newv newr newi) =
>     do  { updv <- Map.unionWithM mergeVal oldv newv
>         ; updr <- Just $ Map.union oldr newr
>         ; return $ -- traceShow "tableauMerge1:-> " $
>                    Tableau updv updr newi
>         }
>     where
>         -- mergeVal cs1 cs2
>         --     | seq (traceShow "mergeVal cs1 " cs1) $
>         --       seq (traceShow "         cs2 " cs2) $ False = undefined
>         mergeVal cs1 cs2 = case mergeClasses cp1 cp2 of
>             Nothing -> Nothing
>             Just cp -> Just (cp++cc1++cc2)
>             where
>                 (cp1,cc1) = partition isPrimitiveClass cs1
>                 (cp2,cc2) = partition isPrimitiveClass cs2
>         -- mergeClasses cs1 cs2
>         --     | seq (traceShow "mergeClasses cs1 " cs1) $
>         --       seq (traceShow "             cs2 " cs2) $ False = undefined
>         mergeClasses cs1 cs2 = -- traceShow "mergeClasses --> " $
>                                foldM mergeClass1 cs1 cs2
>                                -- foldM :: (Monad m) => (a->b->m a) -> a -> [b] -> m a
>         mergeClass1 cs1 c2 = -- traceShow "mergeClass1 --> " $
>                              liftM (const (c2:cs1)) $ sequence $ map (classMerge c2) cs1
>                              -- liftM :: (Monad m) => (a -> b) -> (m a -> m b)

Then satisfiability testing of a concept expression is performed with respect to a
set of tableau rules:

> -- Entry function, tests for satisfiability of a concept expression
> isSatisfiableUsingTableau :: (ConceptExpr c, RoleExpr r) =>
>     [TableauExpansionRule r c] -> c -> Bool
> isSatisfiableUsingTableau rules cexpr =
>     -- Try merging with self to pick up case of unsatisfiable
>     -- primitive class
>     case tableauMerge1 initab initab of
>         Just _  -> isSatisfiableTableau rules initab
>         Nothing -> False
>     where
>         initab = initTableau cexpr
>
> initTableau :: RoleExpr r => c -> Tableau r c
> initTableau cexpr = Tableau
>             { tableauValues = Map.single 0 [cexpr]
>             , tableauRoles  = Map.empty
>             , nextValueId   = 1
>             }
>
> -- Worker function, tests for satisfiability of a given tableau by using the
> -- rules to expand it, and recursively testing for satisfiability of the
> -- new tableaux thereby generated.
> isSatisfiableTableau :: (ConceptExpr c, RoleExpr r) =>
>     [TableauExpansionRule r c] -> Tableau r c -> Bool
> isSatisfiableTableau rules tableau =
>     case tableauMerge tableau (apprule tableau) of
>         Nothing -> False              -- All possible expansions have detected clash
>         Just [] -> True               -- No further expansion: have model
>         Just ts -> or (map (isSatisfiableTableau rules) ts)
>     where
>         --  Find a rule that generates an expansion
>         apprule t = -- traceShow "++ Expand tableau with:\n" $
>                     -- firstNotNull . map ($t) $ rules
>                     firstNotNull $ apprules t
>         apprules t = -- traceShow "++ Possible expand tableau with:\n" $
>                     map ($t) $ rules
>
> -- Helper function returns the first non-null entry in a list of lists, or
> -- an empty list of all entryes are null.  'foldr const []' is like head,
> -- except that it returns [] if the list is empty.
> firstNotNull :: [[a]] -> [a]
> firstNotNull = foldr const [] . filter (not . null)

So that is the tableau algorithm.

To use this function, we need to define some tableau expansion rules.

A typical expansion rule matches a class restriction for some value in the
tableau, and generates new tableau entries, so we define some helper
functions to scan the tableau value classes.  'forSomeTableauValueClass'
takes a function that accepts a tableau, a single value entry from the tableau,
and a single class value from that entry, and returns a tableau value containing
new entries to be merged into the original, or an empty list if the function
does not define any new expansion of the tableau.  Note that the supplied function
is required to test that it is actually adding new information to the tableau,
otherwise the tableau expension may get stuck in a loop.

Recall:  type TableauExpansionRule r c = Tableau r c -> [Tableau r c]

> forSomeTableauValueClass ::
>     (Tableau r c -> (ValueId,[c]) -> c -> [Tableau r c])
>     -> TableauExpansionRule r c
> forSomeTableauValueClass = forSomeTableauValue . forSomeValueClass
>
> forSomeTableauValue ::
>     (Tableau r c -> (ValueId,[c]) -> [Tableau r c])
>     -> TableauExpansionRule r c
> forSomeTableauValue f t = firstNotNull . map (f t) . Map.toList $ tableauValues t
>
> forSomeValueClass ::
>     (Tableau r c -> (ValueId,[c]) -> c -> [Tableau r c])
>     -> Tableau r c -> (ValueId,[c]) -> [Tableau r c]
> forSomeValueClass f t (v,cs) =
>     firstNotNull . map (f t (v,cs)) $ cs

Here are some other general helper functions that are used for defining
tableau expansion rules:

> -- Test if supplied class is a further restruction on a list of classes
> -- that restrict a value
> -- (also handles primitive subsumption cases, ala 'classMerge')
> inClassSet :: ConceptExpr c => c -> [c] -> Bool
> inClassSet c = any (match c)
>     where
>         match c vc = (c==vc) || classMerge c vc == Just [vc]
>
> -- Retrieve all classes from the tableau entry for a given value, or []
> valueClasses :: Tableau r c -> ValueId -> [c]
> valueClasses t v = Map.findWithDefault [] v (tableauValues t)
>
> -- Test if the tableau asserts the identified value is in the specified class
> valueInClass :: ConceptExpr c =>
>     Tableau r c -> c -> ValueId -> Bool
> valueInClass t c v = c `inClassSet` valueClasses t v
>
> -- Test for given class in the tableau entry for a given value
> hasClass :: ConceptExpr c =>
>     Tableau r c -> c -> ValueId -> Bool
> hasClass t c v = c `inClassSet` valueClasses t v
>
> -- Find an r-successor for v in supplied tableau role entry
> findRoleSucc :: RoleExpr r =>
>     ValueId -> r -> ((ValueId,ValueId),[r]) -> Maybe ValueId
> findRoleSucc v r ((vp,vs),rs)
>     | (v == vp) && (r `elem` rs) = Just vs
>     | otherwise                  = Nothing
>
> -- Find all role r successors of v
> findAllRoleSucc :: RoleExpr r => Tableau r c -> ValueId -> r -> [ValueId]
> findAllRoleSucc t v r =
>     catMaybes $ map (findRoleSucc v r) (Map.toList $ tableauRoles t)
>
> -- Find a role r successor of v that does not include a given class
> findNewRoleSucc :: (ConceptExpr c, RoleExpr r) =>
>     Tableau r c -> ValueId -> r -> c -> Maybe ValueId
> findNewRoleSucc t v r c =
>     case filter (not . hasClass t c) (findAllRoleSucc t v r) of
>         (c1:_) -> Just c1
>         _      -> Nothing
>
> -- Test if role has successor value that is in the supplied class
> -- (or successor value that is primitive-subsumed by the supplied class:
> -- supply a primitive universal class to test for any successor value)
> hasRoleSucc ::  (ConceptExpr c, RoleExpr r) =>
>     Tableau r c -> ValueId -> r -> c -> Bool
> hasRoleSucc t v r c = any (valueInClass t c) (findAllRoleSucc t v r)


4.1 Tableau reasoning for AL
----------------------------

Using the above helper functions, we can define tableau expansion rules for AL.

When comparing with the expansion rules from the Description Logic Handbook [2],
section 9.3.2.1, note that:
(a) the rules given here are for language AL, not ALC,
(b) the first condition for each of the rules is governed by a pattern match
    for the concept (first) parameter, and additional conditions are handled
    by expression guards.

> type TableauAL              = Tableau AtomicRole ALConcept
> type TableauExpansionRuleAL = TableauExpansionRule AtomicRole ALConcept
>
> tableauExpansionRulesAL :: [TableauExpansionRule AtomicRole ALConcept]
> tableauExpansionRulesAL =
>     [ forSomeTableauValueClass intersectRuleAL
>     , forSomeTableauValueClass existsRuleAL
>     , forSomeTableauValueClass allRuleAL
>     ]
>
> -- This type applies to all three functions below
> intersectRuleAL ::
>     Tableau AtomicRole ALConcept -> (ValueId,[ALConcept]) -> ALConcept
>     -> [Tableau AtomicRole ALConcept]
>
> intersectRuleAL t (v,cs) (ALIntersect c1 c2)
>     | not $ null cnew = [makeTableau [(v,cnew)] [] (nextValueId t)]
>     where
>         cnew = filter (not . (`inClassSet` cs)) [c1,c2]
> intersectRuleAL _ _ _ = []
>
> existsRuleAL t (v,cs) (ALExistsAny r)
>     | not $ hasRoleSucc t v r ALUniversal =
>         [makeTableau [(vs,[ALUniversal])] [((v,vs),[r])] (vs+1)]
>     where
>         vs = nextValueId t
> existsRuleAL _ _ _ = []
>
> allRuleAL t (v,_) (ALAll r c) = case findNewRoleSucc t v r c of
>     Just vs   -> [makeTableau [(vs,[c])] [] (nextValueId t)]
>     otherwise -> []
> allRuleAL _ _ _ = []

And finally, a test for satisfiability of an AL concept expression.

> isSatisfiableInAL :: ALConcept -> Bool
> isSatisfiableInAL = isSatisfiableUsingTableau tableauExpansionRulesAL


4.1.1 Example: concept satisfaction for AL

Note that, in the case of the language AL, we cannot use this to perform subsumption
tests because there is no construct in AL for general negation of a concept.
So we restrict ourselves here to tests of satisfiability of AL expressions:

First, some basic tests to exercise all the basic expression forms:

> ex411a = False == isSatisfiableInAL (ALBottom)
> ex411b = True  == isSatisfiableInAL (ALUniversal)
> ex411c = True  == isSatisfiableInAL (ALAtomic "a")
> ex411d = True  == isSatisfiableInAL (ALNegate "a")
> ex411e = False == isSatisfiableInAL (ALIntersect (ALAtomic "a") ALBottom)
> ex411f = True  == isSatisfiableInAL (ALIntersect (ALAtomic "a") ALUniversal)
> ex411g = False == isSatisfiableInAL (ALIntersect ALBottom       (ALNegate "a"))
> ex411h = True  == isSatisfiableInAL (ALIntersect ALUniversal    (ALNegate "a"))
> ex411i = True  == isSatisfiableInAL (ALIntersect (ALAtomic "a") (ALAtomic "a"))
> ex411j = False == isSatisfiableInAL (ALIntersect (ALAtomic "a") (ALNegate "a"))
> ex411k = True  == isSatisfiableInAL (ALIntersect (ALNegate "a") (ALAtomic "b"))
> ex411l = True  == isSatisfiableInAL (ALIntersect (ALNegate "a") (ALNegate "b"))
> ex411m = True  == isSatisfiableInAL (ALAll       "r"            ALUniversal)
> ex411n = True  == isSatisfiableInAL (ALAll       "r"            ALBottom)
> ex411o = True  == isSatisfiableInAL (ALAll       "r"            (ALAtomic "a"))
> ex411p = True  == isSatisfiableInAL (ALExistsAny "r")

And some more complex test cases, adapted from those section 2.3.1.1 which can be
expressed in terms of concept satisfiability in AL:

> ex411q = False == isSatisfiableInAL
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALAtomic "Female"))
>                  (ALNegate "Person") )

Handling of role restrictions:

> ex411r = False == isSatisfiableInAL
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>                  (ALNegate "Person") )
> ex411s = True == isSatisfiableInAL
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>                  (ALNegate "Animal") )
> ex411t = False == isSatisfiableInAL
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>                  (ALAll "hasChild" ALBottom))
> ex411u = False == isSatisfiableInAL
>     (ALIntersect (ALAll "hasChild" ALBottom)
>                  (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild")))
> ex411v = False == isSatisfiableInAL
>     (ALIntersect (ALIntersect (ALAtomic "Person") (ALExistsAny "hasChild"))
>                  (ALAll "hasChild" (ALIntersect (ALAtomic "a") (ALNegate "a"))))

Evaluate all the test cases:

> ex411 = and
>     [ ex411a, ex411b, ex411c, ex411d
>     , ex411e, ex411f, ex411g, ex411h
>     , ex411i, ex411j, ex411k, ex411l
>     , ex411m, ex411n, ex411o, ex411p
>     , ex411q, ex411r, ex411s, ex411t
>     , ex411u
>     ]


4.2 Representing more expressive description logics

Having generalized the functions that process description logic expressions,
I now turn to the expressions themselves.

One approach would be to define a new representation for each description logic,
which would embody the allowable forms of expression.  I propose to take a
slightly different approach that defined a single framework for representation of
expressions from a range of description logics, and then to provide checking and
tableau expansion rule functions that can be applied selectively according to the
particular DL used.  In this way, I aim for much of the executable code to be
shareable by reasoners for different description logics.

> data DLConcept = DLAtomic AtomicConcept
>                | DLUniversal
>                | DLBottom
>                | DLNegate DLConcept
>                | DLIntersect DLConcept DLConcept
>                | DLUnion DLConcept DLConcept
>                | DLAll DLRole DLConcept
>                | DLMin DLRole DLConcept Int
>                | DLMax DLRole DLConcept Int
>     deriving (Show, Eq)
>
> data DLRole = DLAtomicR AtomicRole
>             | DLUniversalR
>             | DLEmptyR
>             | DLIntersectR DLRole DLRole
>             | DLUnionR     DLRole DLRole
>             | DLNegateR    DLRole
>             | DLCompose    DLRole DLRole
>             | DLInverse    DLRole
>             | DLClosure    DLRole
>     deriving (Show, Eq)

The concept expressions are extended to provide for:
(a) concept union (U)
(b) full existential quantification (E) (a specified class for a role successor)
(c) numeric restrictions on role successors (N)
(d) general negation (C)
(e) qualification of number restrictions (Q)

Further, role expressions are allowed in addition to atomic roles.

[[[
Note:  Role value map and [dis]agreement constructors are not (yet?)
included here.  Nominals are also omitted these being expressible as
atomic concepts.
]]]

Starting from AL, more expressive languages are sometimes described by appending
the letter for the corresponding feature.  Not all languages thus expressible are
distinct, e.g.,

    ALU == ALC == ALE == ALUCE

The terms ALC and ALCN are commonly used for languages that can express general
negation with and without numeric restrictions on role successors.
(Note: an existential role restriction is expressed by a DLMin expression
with a numeric value of 1.)

Define an interpretation function for class expressions:

> iDLC :: Ord a => TInterpretation a -> DLConcept -> Set a
> iDLC i (DLAtomic c)       = iC i c
> iDLC i DLUniversal        = iDom i
> iDLC _ DLBottom           = Set.empty
> iDLC i (DLNegate c)       = iDom i `Set.difference` (iDLC i c)
> iDLC i (DLIntersect c d)  = iDLC i c `Set.intersection` iDLC i d
> iDLC i (DLUnion c d)      = iDLC i c `Set.union` iDLC i d
> iDLC i (DLAll r c)        = Set.fromDistinctAscList
>                                 [ a | (a,bs) <- iSuccessors (iDLR i r)
>                                 ,     bs `subsetOf` cs
>                                 ]
>                                 where cs = iDLC i c
> iDLC i (DLMin r c 0)      = iDom i    -- >=0 is pretty pointless, really
> iDLC i (DLMin r c n)      = Set.fromDistinctAscList
>                                 [ a | (a,bs) <- iSuccessors (iDLR i r)
>                                 ,     Set.size (bs `Set.intersection` cs) >= n
>                                 ]
>                                 where cs = iDLC i c
> iDLC i (DLMax r c n)      = Set.fromDistinctAscList
>                                 [ a | (a,bs) <- Map.toAscList ams
>                                 ,     Set.size (bs `Set.intersection` cs) <= n
>                                 ]
>     where
>         cs  = iDLC i c
>         ads = Map.fromDistinctAscList $ zip (Set.toAscList $ iDom i) (repeat Set.empty)
>         ars = iSuccessorMap (iDLR i r)
>         ams = Map.union ars ads       -- 1st arg takes precedence

Define an interpretation function for role expressions:

> iDLR :: Ord a => TInterpretation a -> DLRole -> Set (a,a)
> iDLR i (DLAtomicR r)        = iR i r
> iDLR i DLUniversalR         = Set.fromDistinctAscList
>                                   [ (a,b) | a <- ds, b <- ds
>                                   ]
>                                   where ds = Set.toAscList (iDom i)
> iDLR _ DLEmptyR             = Set.empty
> iDLR i (DLIntersectR r1 r2) = Set.intersection (iDLR i r1) (iDLR i r2)
> iDLR i (DLUnionR r1 r2)     = Set.union (iDLR i r1) (iDLR i r2)
> iDLR i (DLNegateR r)        = Set.difference (iDLR i DLUniversalR) (iDLR i r)
> iDLR i (DLCompose r1 r2)    = Set.fromDistinctAscList
>     [ (a,c) | (a,bs) <- iSuccessors (iDLR i r1)
>     ,         b <- Set.toAscList bs
>     ,         Just cs <- [Map.lookup b r2m]
>     ,         c <- Set.toAscList cs
>     ]
>     where
>         r2m = iSuccessorMap (iDLR i r2)
> iDLR i (DLInverse r)        = Set.fromList . map swap . Set.toList $ iDLR i r
>     where
>         swap (a,b) = (b,a)
> iDLR i (DLClosure r)        = Set.fromDistinctAscList
>     [ (a,c) | (a,bs) <- rs
>     ,         c <- Set.toAscList $ setClosure (mapSet rm) bs
>     ]
>     where
>         rs = iSuccessors (iDLR i r)
>         rm = Map.fromDistinctAscList rs

Helper function to map a set of values to a new set using a supplied
value-to-set map:

> mapSet :: Ord a => Map a (Set a) -> Set a -> Set a
> mapSet m as = Set.unions
>     [ bs | a <- Set.toAscList as
>     ,      Just bs <- [Map.lookup a m]
>     ]

Helper function to calculate the (non-reflexive) transitive closure of
a set of values under some mapping function:

> setClosure :: Ord a => (Set a -> Set a) -> Set a -> Set a
> setClosure ms as =
>     fst . head . dropWhile (not . Set.isEmpty . snd) $ closure1 ms (as,as)
>     where
>         -- Generate sequence of pairs, where each pair consists of:
>         --   1. the closure so far
>         --   2. new values from last iteration
>         closure1 :: Ord a => (Set a -> Set a) -> (Set a,Set a) -> [(Set a,Set a)]
>         closure1 ms aps = iterate (closure2 ms) aps
>         closure2 :: Ord a => (Set a -> Set a) -> (Set a,Set a) -> (Set a,Set a)
>         closure2 ms (aold,atry) = (aall,anew)
>             where
>                 agen = ms atry
>                 anew = agen `Set.difference` aold
>                 aall = aold `Set.union` anew

Now we can define ConceptExpr and RoleExpr class instances for
DLConcept and DLRole:

> instance ConceptExpr DLConcept where
>     iConcept        = iDLC
>     isPrimitiveClass (DLBottom)              = True
>     isPrimitiveClass (DLUniversal)           = True
>     isPrimitiveClass (DLAtomic _)            = True
>     isPrimitiveClass (DLNegate (DLAtomic _)) = True
>     isPrimitiveClass  _                      = False
>     -- Preferrably, test for primitive classes before calling merge function,
>     -- otherwise, may be called with complex negated expression.
>     classMerge _                    (DLBottom)                = Nothing
>     classMerge    (DLBottom)     _                            = Nothing
>     classMerge c1                   (DLUniversal)             = Just [c1]
>     classMerge    (DLUniversal)  c2                           = Just [c2]
>     classMerge c1@(DLAtomic i1)     (DLAtomic i2) | i1 == i2  = Just [c1]
>     classMerge c1@(DLAtomic i1)     (DLNegate i2) | c1 == i2  = Nothing
>     classMerge    (DLNegate i1)  c2@(DLAtomic i2) | i1 == c2  = Nothing
>     classMerge c1@(DLNegate i1)     (DLNegate i2) | i1 == i2  = Just [c1]
>     classMerge c1                c2                           = Just [c1,c2]
>
> instance RoleExpr DLRole where
>     iRole = iDLR


4.2.1 Example interpretations for more general description logics

Using this enterpretation:

> exTInt421 :: TInterpretation String
> exTInt421 =
>     ( mkSet ["Peter","Paul","Mary","Harry"
>             ,"Spot","Rover","Lassie","Thumper","Bouncer"]
>     , aConcepts
>     , aRoles ) where
>         aConcepts =
>             [ ("Female", mkSet ["Mary","Lassie","Bouncer"])
>             , ("Person", mkSet ["Peter","Paul","Mary","Harry"])
>             , ("Dog"   , mkSet ["Spot","Rover","Lassie"])
>             , ("Rabbit", mkSet ["Thumper","Bouncer"])
>             , ("Woman" , mkSet ["Mary"])
>             , ("Man"   , mkSet ["Peter","Paul","Harry"])
>             ]
>         aRoles =
>             [ ("likes" , mkSet [ ("Mary","Peter")
>                                , ("Peter","Paul")
>                                , ("Paul","Harry")
>                                , ("Harry","Peter")
>                                , ("Rover","Spot")
>                                , ("Spot","Lassie")
>                                , ("Thumper","Bouncer")
>                                ])
>             , ("hasPet", mkSet [ ("Peter","Spot")
>                                , ("Peter","Rover")
>                                , ("Peter","Lassie")
>                                , ("Paul","Spot")
>                                , ("Mary","Thumper")
>                                , ("Mary","Bouncer")
>                                ])
>             ]
>
> i421C = iDLC exTInt421
> i421R = iDLR exTInt421
>
> dom421 = [ "Peter","Paul","Mary","Harry"
>          , "Spot","Rover","Lassie","Thumper","Bouncer"
>          ]

Evaluate some class expressions:

> ex421a = i421C (DLAtomic "Dog") == mkSet ["Spot","Rover","Lassie"]
>
> ex421b = i421C (DLUniversal)    == mkSet dom421
>
> ex421c = i421C (DLBottom)       == Set.empty
>
> cl421d = (DLIntersect (DLAtomic "Person") (DLNegate (DLAtomic "Female")))
> ex421d = i421C cl421d           == mkSet ["Peter","Paul","Harry"]
>
> cl421e = (DLUnion (DLAtomic "Dog") (DLAtomic "Rabbit"))
> ex421e = i421C cl421e           == mkSet ["Spot","Rover","Lassie","Thumper","Bouncer"]
>
> cl421f = (DLAll (DLAtomicR "hasPet") (DLAtomic "Dog"))
> ex421f = i421C cl421f           == mkSet ["Peter","Paul"]
>
> cl421g = (DLAll (DLAtomicR "hasPet") (DLAtomic "Dog"))
> ex421g = i421C cl421g           == mkSet ["Peter","Paul"]
>
> cl421h = (DLMin (DLAtomicR "hasPet") (DLUniversal) 2)
> ex421h = i421C cl421h           == mkSet ["Peter","Mary"]
>
> cl421i = (DLMin (DLAtomicR "hasPet") (DLNegate (DLAtomic "Female")) 2)
> ex421i = i421C cl421i           == mkSet ["Peter"]
>
> cl421j = (DLMax (DLAtomicR "hasPet") (DLUniversal) 1)
> ex421j = i421C cl421j           ==
>     mkSet ["Paul","Harry","Spot","Rover","Lassie","Thumper","Bouncer"]

And some role expressions:

> rl421n = (DLAtomicR "hasPet")
> ri421n = mkSet [ ("Peter","Spot")
>                , ("Peter","Rover")
>                , ("Peter","Lassie")
>                , ("Paul","Spot")
>                , ("Mary","Thumper")
>                , ("Mary","Bouncer")
>                ]
> ex421n = i421R rl421n == ri421n
>
> rl421o = (DLUniversalR)
> ri421o = mkSet [ (a,b) | a <- dom421, b <- dom421 ]
> ex421o = i421R rl421o == ri421o
>
> rl421p = (DLEmptyR)
> ri421p = Set.empty
> ex421p = i421R rl421p == ri421p
>
> rl421q = (DLUnionR (DLAtomicR "hasPet") (DLAtomicR "likes") )
> ri421q = mkSet [ ("Peter","Spot")
>                , ("Peter","Rover")
>                , ("Peter","Lassie")
>                , ("Paul","Spot")
>                , ("Mary","Thumper")
>                , ("Mary","Bouncer")
>                , ("Mary","Peter")
>                , ("Peter","Paul")
>                , ("Paul","Harry")
>                , ("Harry","Peter")
>                , ("Rover","Spot")
>                , ("Spot","Lassie")
>                , ("Thumper","Bouncer")
>                ]
> ex421q = i421R rl421q == ri421q
>
> rl421r = (DLIntersectR rl421q (DLAtomicR "likes"))
> ri421r = mkSet [ ("Mary","Peter")
>                , ("Peter","Paul")
>                , ("Paul","Harry")
>                , ("Harry","Peter")
>                , ("Rover","Spot")
>                , ("Spot","Lassie")
>                , ("Thumper","Bouncer")
>                ]
> ex421r = i421R rl421r == ri421r
>
> rl421s = (DLIntersectR rl421q (DLNegateR (DLAtomicR "likes")))
> ri421s = mkSet [ ("Peter","Spot")
>                , ("Peter","Rover")
>                , ("Peter","Lassie")
>                , ("Paul","Spot")
>                , ("Mary","Thumper")
>                , ("Mary","Bouncer")
>                ]
> ex421s = i421R rl421s == ri421s
>
> rl421t = (DLCompose (DLAtomicR "likes") (DLAtomicR "hasPet"))
> ri421t = mkSet [ ("Mary","Spot")
>                , ("Mary","Rover")
>                , ("Mary","Lassie")
>                , ("Harry","Spot")
>                , ("Harry","Rover")
>                , ("Harry","Lassie")
>                , ("Peter","Spot")
>                ]
> ex421t = i421R rl421t == ri421t
>
> rl421u = (DLInverse rl421t)
> ri421u = mkSet [ ("Spot"  ,"Mary")
>                , ("Rover" ,"Mary")
>                , ("Lassie","Mary")
>                , ("Spot"  ,"Harry")
>                , ("Rover" ,"Harry")
>                , ("Lassie","Harry")
>                , ("Spot"  ,"Peter")
>                ]
> ex421u = i421R rl421u == ri421u
>
> rl421v = (DLClosure (DLAtomicR "likes"))
> ri421v = mkSet [ ("Mary","Peter")
>                , ("Mary","Paul")
>                , ("Mary","Harry")
>                , ("Peter","Paul")
>                , ("Peter","Harry")
>                , ("Peter","Peter")
>                , ("Paul","Harry")
>                , ("Paul","Peter")
>                , ("Paul","Paul")
>                , ("Harry","Peter")
>                , ("Harry","Paul")
>                , ("Harry","Harry")
>                , ("Rover","Spot")
>                , ("Rover","Lassie")
>                , ("Spot","Lassie")
>                , ("Thumper","Bouncer")
>                ]
> ex421v = i421R rl421v == ri421v

And finally, a more complex class expression.  Let's try one for
"people who have a female pet or who are liked by someone all of
whose pets are dogs".

> rl421w = (DLUnion
>            (DLMin (DLAtomicR "hasPet") (DLAtomic "Female") 1)
>            (DLMin (DLInverse (DLAtomicR "likes"))
>                   (DLAll (DLAtomicR "hasPet") (DLAtomic "Dog"))
>                   1))
> ri421w = mkSet ["Harry","Mary","Paul","Peter"]
> ex421w = i421C rl421w == ri421w

Collect all examples together:

> ex421 = and
>     [ ex421a, ex421b, ex421c, ex421d, ex421e, ex421f, ex421g, ex421h
>     , ex421i, ex421j
>     , ex421n, ex421o, ex421p, ex421q, ex421r, ex421s, ex421t , ex421u
>     , ex421v, ex421w
>     ]


4.3 Multiple description logics using a common expression
---------------------------------------------------------

To allow a common expression to support multiple description logics,
we first define a wrapper type:

> data Wrapper c d = Wrap c d
>     deriving (Eq,Show)
>
> unwrap :: Wrapper c d -> c
> unwrap (Wrap c _) = c
>
> wmap :: (c->c2) -> Wrapper c d -> Wrapper c2 d
> wmap f (Wrap c d) = (Wrap (f c) d)
>
> wmap2 :: (c->c->c2) -> Wrapper c d -> Wrapper c d -> Wrapper c2 d
> wmap2 f (Wrap c1 d) (Wrap c2 _) = (Wrap (f c1 c2) d)
>
> applyd :: (d->c->c2) -> Wrapper c d -> c2
> applyd f (Wrap c d) = (f d c)
>
> wmap2M :: (Monad m1, Monad m2) =>
>     (c->c->m1 (m2 c2)) -> Wrapper c d -> Wrapper c d -> m1 (m2 (Wrapper c2 d))
> wmap2M f (Wrap c1 d) (Wrap c2 _) = f c1 c2 >>= return . liftM (flip Wrap d)

[[[NOTE:
Currently, the wrapper is fixed as a pairing with some additional data.
I was hoping to abstract this, maybe to being a reader monad, but
got caught up with overlapping class instances.
]]]

4.4 Defining a specific Description Logic
-----------------------------------------

A description logic with all of the above features is amost certainly
undecideable, and it is often desired to restrict expressions to those
that are decideable (even though the decision process may be somewhat
intractable).  To achieve this, a function may be defined on
DL concept expressions that determines whether it satisfies some
conditions, and a corresponding set of tableau expansion rules may be
provided.

The following declarations create a framework for defining description logic
processing based on the above data type declarations for description logic
expressions.

> type DLTableauExpansionRule = TableauExpansionRule DLRole DLConcept
>
> data DLDescription = DL
>     { dlName            :: String
>     , dlValidateConcept :: DLConcept -> Bool
>     , dlValidateRole    :: DLRole    -> Bool
>     , dlRules           :: [DLTableauExpansionRule]
>     }
>
> instance Eq DLDescription where
>     d1 == d2 = dlName d1 == dlName d2
>
> instance Show DLDescription where
>     show = dlName
>
> instance ConceptExpr (Wrapper DLConcept DLDescription) where
>     iConcept i        = iDLC i . unwrap
>     emptyClass        = wmap (const DLBottom)
>     complementClass   = wmap DLNegate
>     intersectClass    = wmap2 DLIntersect
>     isPrimitiveClass  = isPrimitiveClass . unwrap
>     classMerge        = wmap2M classMerge
>
> instance ConceptInferrable (Wrapper DLConcept DLDescription) where
>     isSatisfiable = applyd (isSatisfiableUsingTableau . dlRules)
>
> instance RoleExpr (Wrapper DLRole DLDescription) where
>     iRole i = iDLR i . unwrap


4.5 Tableau rules for more expressive description logics
--------------------------------------------------------













(how to implement blocking?)

(optimizations)



X. Extension to N-ary role predicates
=====================================

[[[
Explore N-ary role predicate extensions in what are otherwise fully
tractable DLs.  Also explore tableau expansion starting with a given
role expression:  is it possible to deduce relations that satisfy said
role, particularly in the face of Abox assertions.  Can these be used
to bridge the gap to problems otherwise solved using rules?
]]]


Y. Additional thoughts about tableau reasoning
==============================================

The tableau approach can be extended from simply performing a satisfiability
test to actually deducing the consequences of a value being a member of some
class.  To access these consequences requires that the final tableau be
accessible.  The graph in a resulting tableau indicates relationships and
class memberships that are a consequence of the original class membership
assertion.  But remember that in the face is disjunctions, all alternative
tableaux must be preserved, since one particular expanded tableau is not
necessarily the only consequence.  (Is this an aspect of class-based
reasoning that is not captured by Horn rules?)

A basic tableau expansion is in terms of named values, not denotations.
But datatype-aware consequences depend on known relations between denoted
values (e.g. 2+2=4).  By attaching denotations to a tableau, it may be
possible to use additional tableau expansion rules as a basis for
datatype-aware inferences.  Maybe this is more efficient that other
approaches tried so far?

A tableau reasoner can also be used to test the satisfiability of an
arbitrary expression, simply by initializing the tableau with that
expression.  Put another way, the normal tableau reasoning starts from
an assertion like:
  _:x rdf:type some:Class .
but there is no reason it cannot start from some completely different
expression.  (See also, the comment above about role assertions.)

Is it possible to optimize tableau expansion processing by organizing
the tableau expansion rules into a rete-type network?  If the tableau
expansion rules are presented as CWM-style rules, then maybe try using
Pychinko to evaluate them?

Is it possible to use a tableau algorithm to derive an *expression* for
a least common subsumer of two DL expressions?


Z. Check all examples
=====================

> test = ( "Quick test: 2nd value should be True"
>        , and [ex211,ex221,ex2311,ex311,ex321,ex331,ex411,ex421])

Other values for debugging

> x411a :: TableauAL
> x411a = initTableau (ALBottom)
> x411b :: Maybe TableauAL
> x411b = tableauMerge1 x411a x411a

> traceShow :: Show a => String -> a -> a
> traceShow msg x = trace (msg ++ show x) x
> traceVal :: Show a => String -> a -> b -> b
> traceVal msg x y = trace (msg ++ show x) y


--------------------------------------------------------------------------------
$Log: DLExploration.lhs,v $
Revision 1.10  2004/11/23 16:27:19  graham
Coded basic framework for generalized DL handling.

Revision 1.9  2004/11/19 20:59:13  graham
General DL structures and interpretation function working.

Revision 1.8  2004/11/16 12:59:17  graham
Started work on general DL expression and tableau reasoner

Revision 1.7  2004/11/12 19:34:17  graham
Tableau satisfiability tested for simple expressions in AL

Revision 1.6  2004/11/11 22:44:47  graham
Initial tableau satisfaction test nearly done.

Revision 1.5  2004/11/05 19:58:02  graham
Added class for generic concept expressions.

Revision 1.4  2004/08/21 20:47:30  graham
Minor spelling corrections.

Revision 1.3  2004/08/11 11:16:25  graham
Up to structural subsumption in /AL/

Revision 1.2  2004/07/27 13:49:30  graham
Completed to working structural subsumption for AL.

