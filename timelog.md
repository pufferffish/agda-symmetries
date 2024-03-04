* 19/08/2023 [2 hours]
Meeting with Dr. Vikraman Choudhury to discuss general scope of the project

* 15/09/2023 [2 hours]
Meeting with Dr. Vikraman Choudhury to answer some questions I have about Cubical Agda, 
and begin work on proving elementary theorems on free monoids as practice

* 16/09/2023 [2 hours]
Attempt to prove theorems about homomorphism on free monoids

* 16/09/2023 [4 hours]
Draft implementation and theorems on List

* 17/09/2023 [2 hours]
Investigate theorems about homomorphism on free monoids

* 18/09/2023 [4 hours]
Meeting with Dr. Vikraman Choudhury to discuss questions about category theory and theorems
involving trunated types, the `freeMonEquiv` theorem, potential plans to expand the project's
scope to general free structures

* 21/09/2023 [5 hours]
Prove `freeMonEquivLemma`

* 22/09/2023 [3 hours]
Complete proof for `freeMonEquiv`

* 22/09/2023 [1 hours]
Complete proof for `listMonIsEquiv`

* 25/09/2023 [3 hours]
Meeting with Dr. Vikraman Choudhury to discuss formalizing universal algebra to refactor existing code
under the new univeral algebra framework

* 27/09/2023 [30 minutes]
Meeting with Dr. Vikraman Choudhury and Dr. Simon Gay to discuss general progress of the project, and
setting some deadlines with experiments with universal algebra formalization

* 29/09/2023 [3 hours]
Implement `Tree` and prove `Tree`'s universal property

* 30/09/2023 [1 hour]
Minor experimentation with defining `Free` with quotients

* 01/10/2023 [2 hours]
Minor experimentation with defining `Free`'s algebraic structures

* 02/10/2023 [3 hours]
Meeting with Dr. Vikraman Choudhury to finalize the universal algebra framework, and agree on tasks to do
for the week

* 03/10/2023 [3 hours]
Setting up CI, patching up the universal algebra framework

* 04/10/2023 [3 hours]
Proving theorems about homomorphisms and defining trees in the new universal algebra framework, meeting
with Dr. Simon Gay to report progress

* 05/10/2023 [1 hours]
Minor asethetics changes to the framework from according to feedbacks by Dr. Vikraman Choudhury

* 06/10/2023 [2 hours]
Begin work on formalizing free monoids in the new framework

* 07/10/2023 [7 hours]
Formalizing free monoids with the new universal algebra framework, fixing issues with the framework

* 08/10/2023 [2 hours]
Attempt to generalize the framework to all h-levels

* 09/10/2023 [2 hours]
Meeting with Dr. Vikraman Choudhury to discuss tasks for the week

* 11/10/2023 [2 hours]
Another attempt to generalize the framework to all h-levels, gave up and just proved Tree's h-level instead,
also work on defining some commutative monoids

* 12/10/2023 [5 hours]
Complete work on defining SList, CList, FreeCMon, and prove they are all free commutative monoids

* 16/10/2023 [2 hours]
Meeting with Dr. Vikraman Choudhury to discuss tasks for the week

* 17/10/2023 [5 hours]
Refactoring the lemmas for Free structures

* 18/10/2023 [3 hours]
Experimentation with SList for groupoids, meeting with Dr. Vikraman Choudhury and Dr. Simon Gay to catch up on progress

* 19/10/2023 [4 hours]
Define and prove PList is a free comm monoid, experimentation with free comm monoid as an analytic functor

* 20/10/2023 [4 hours]
Prove Array's monoidal properties, generalize PList to any relations

* 21/10/2023 [8 hours]
Prove Array is a free monoid and generalize QList to QFreeMon

* 22/10/2023 [5 hours]
Refactor PList in terms of QFreeMon, defining symmetric action on array and attempt to prove it satisfies permutation relation

* 23/10/2023 [4 hours]
Prove all lemmas needed to show SymmAction is a permutation relation except `f-≅ₚ`, got stuck on `f-≅ₚ`

* 24/10/2023 [2 hours]
Experiments with Lehmer Codes to attempt to prove `f-≅ₚ`

* 25/10/2023 [6 hours]
Meeting with Dr. Vikraman Choudhury to discuss tasks for the week, and also the `f-≅ₚ` proof

* 26/10/2023 [2 hours]
Prove Array is isomorphic to List

* 27/10/2023 [2 hours]
Transport List's Free proof to Array by isomorphism and create experiments to see if Agda can compute it

* 28/10/2023 [3 hours]
Clean up Array's proof to make it more translatable to paper

* 30/10/2023 [6 hours]
Meeting with Dr. Vikraman Choudhury to discuss strategies to prove SymmAction is a permutation relation, clean up and simplify the existing proofs in Bag

* 31/10/2023 [6 hours]
Prove `f-≅ₚ` when `aut 0 = 0`, also experiment with Lehmer Codes

* 01/11/2023 [6 hours]
Get rid of Lehmer Codes, refactor `permuteInvariant`, worked out a strategy to prove cases where `aut 0 != 0`, and defined `swapAut`

* 02/11/2023 [6 hours]
Refactor, simplify, and complete `permuteInvariant`. Also minor clean up in the rest of `Bag`

* 03/11/2023 [3 hours]
Refactor `Bag` lemmas to use existing helper lemmas instead, attempt to define isomorphism from `Bag` to `CList`

* 04/11/2023 [4 hours]
Prove some trivial theorems about algebras with no structures, prove two free objects on the same set are isomorphic

* 05/11/2023 [30 minutes]
Slight refactor on the free object isomorphism proof

* 06/11/2023 [10 minutes]
Another slight refactor on the free object isomorphism proof

* 13/11/2023 [3 hours]
Meeting with Dr. Vikraman Choudhury to discuss strategies to prove direct isomorphism from Bag to CList

* 14/11/2023 [3 hours]
Some work on proving direct isomorphism from Bag to CList

* 15/11/2023 [4 hours]
Meeting with Dr. Vikraman Choudhury to discuss strategies to prove direct isomorphism from Bag to CList,
then meeting with Dr. Simon Gay, also some work on the proof in terms of punchIn/punchOut relations

* 16/11/2023 [1 hours]
Prove some lemmas for Bag to CList isomorphism

* 18/11/2023 [3 hours]
Complete the definition of `toCList : Bag -> CList`

* 20/11/2023 [2 hours]
Start work on `fromCList : CList -> Bag`

* 21/11/2023 [2 hours]
Meeting with Dr. Simon Gay and Dr. Vikraman Choudhury, experimenting with ways to deal with
Agda getting stuck

* 22/11/2023 [2 hours]
Work on some necessary lemmas about array to list isomorphism being a homomorphism.
Went to SPLS where Dr. Vikraman Choudhury did a talk on the project (this is not counted towards the time)

* 23/11/2023 [2 hours]
Prove lemmas about array to list isomorphism being a homomorphism, and completing the entire Bag to CList
isomorphism proof

* 25/11/2023 [30 minutes]
Minor cleanup on Bag to CList isomorphism proof

* 29/11/2023 [30 minutes]
Meeting with Dr. Simon Gay and Dr. Vikraman Choudhury, some discussion on what to do next

* 30/11/2023 [4 hours]
Begin work on formalizing sort functions, refactor SList, add lemmas about SList, experimentation with different sorted list representations

* 1/12/2023 [4 hours]
Showed sort cannot be a homomorphism (contrary to what we assumed in the SPLS talk), proved some axioms of total orders

* 2/12/2023 [4 hours]
Proved least-choice under decidable equality assumption, experimentation with different constructions of total order to see if transitivity can be derived

* 3/12/2023 [3 hours]
Formalizing membership proofs of List and SList by their universal property, removed decidable equality assumption in least-choice

* 4/12/2023 [2 hours]
Experimentation in trying to prove transitivity

* 10/12/2023 [2 hours]
Reduced the proof for transitivity down to least-removed

* 3/1/2024 [2 hours]
Meeting with Dr. Vikraman Choudhury to discuss how sorting relates to axiom of choice

* 10/1/2024 [2 hours]
Define sort function under decidable total order

* 14/1/2024 [1 hours]
Some experimentations with total order

* 15/1/2024 [4 hours]
Try to prove least-removed, meeting with Dr. Vikraman Choudhury to discuss abstract for HoTT/UF workshop

* 16/1/2024 [1 hour]
Some draft on the abstract

* 17/1/2024 [2 hour]
Meeting with Dr. Simon Gay to catch up on progress, add proof sketch on total order can be constructed to abstract

* 18/1/2024 [1 hour]
Add explanation of the framework for universal algebra to abstract

* 19/1/2024 [2 hours]
Show transitivity cannot be proven without extra assumptions, proved transitivity under new assumption,
added explanation on transitivity to abstract

* 20/1/2024 [2 hours]
Work with Dr. Vikraman Choudhury to write the abstract for HoTT/UF workshop

* 21/1/2024 [3 hours]
Fix insertion sort definition to `SList -> List`

* 22/1/2024 [2 hours]
Prove order can be used to construct section, section can be used to reconstruct the same order

* 24/1/2024 [2 hours]
Some work on proving reconstructing a section by section -> order -> section

* 26/1/2024 [1 hour]
Some more work on proving reconstructing a section by section -> order -> section

* 27/1/2024 [30 minutes]
Clean up and merge progress into main branch

* 30/1/2024 [2 hours]
Meeting with Dr. Vikraman Choudhury to discuss overall status of the project, and potentially extending the proof to relationship with axiom of choice

* 31/1/2024 [30 minutes]
Meeting with Dr. Simon Gay to discuss potentially submitting to ICFP

* 2/2/2024 [1 hour]
Explore other possible potential axioms of sorting

* 3/2/2024 [3 hours]
Meeting with Dr. Vikraman Choudhury to discuss overall status of the project, cleaned up the proof

* 4/2/2024 [2 hours]
Add second axiom of sorting to complete the full equivlence of total order and sorting proof

* 8/2/2024 [2 hours]
Meeting with Dr. Simon Gay to catch up on progress, add counterexample that satifies is-head-least but not is-tail-sort, and formalize the proof for seely isomorphism

* 9/2/2024 [1 hours]
Start draft on PLUG talk slides

* 10/2/2024 [3 hours]
Add HIT intro to the slides

* 11/2/2024 [3 hours]
Add h-level explanation to the slides, collaboration with Dr. Vikraman Choudhury on some aesthetics of the slide

* 12/2/2024 [3 hours]
Work with Dr. Vikraman Choudhury on the slides, add explanation on universal algebra

* 13/2/2024 [3 hours]
Work with Dr. Vikraman Choudhury on the slides, add explanation on sorting

* 14/2/2024 [3 hours]
Meeting with Dr. Vikraman Choudhury to discuss the slides and do a practice talk, then a talk on the project in PLUG

* 15/2/2024 [30 minutes]
Meeting with Dr. Simon Gay to catch up on progress and also get some advice on thesis

* 18/2/2024 [30 minutes]
Move HTML rendering of the code from GitHub Pages to Netlify 

* 19/2/2024 [3 hours]
Fix CI where Everything.agda is not generated and meeting with Dr. Vikraman Choudhury to discuss the ICFP paper

* 20/2/2024 [2 hours]
Begin work on the ICFP paper and some cleanup on the HoTT/UF abstract

* 21/2/2024 [4 hours]
Meeting with Dr. Simon Gay to discuss the ICFP paper and also work on the paper, work out the rough outline

* 22/2/2024 [1 hours]
Work on the ICFP paper introduction

* 23/2/2024 [2 hours]
Meeting with Dr. Vikraman Choudhury to work on the ICFP paper, organize the latex files and assign work

* 24/2/2024 [5 hours]
Work on the free monoid section

* 25/2/2024 [4 hours]
More work on the free monoid section, begin the free commutative monoid section

* 26/2/2024 [7 hours]
Meeting with Dr. Vikraman Choudhury to work on the ICFP paper, clean up the free monoid and free commutative monoid sections, begin work on the combinatoric section

* 27/2/2024 [9 hours]
Meeting with Dr.Simon Gay and Dr. Vikraman Choudhury to discuss the ICFP paper, start writing the sorting section

* 28/2/2024 [7 hours]
Meeting with Dr.Simon Gay to discuss the ICFP paper, wrote a better introduction and some work on the sorting section

* 29/2/2024 [4 hours]
Meeting with Dr. Vikraman Choudhury to work on the ICFP paper and submit it

* 1/3/2024 [30 minutes]
Fix some slight mistakes on the paper

* 2/3/2024 [30 minutes]
Migrate the HTML rendering of the code from netlify
