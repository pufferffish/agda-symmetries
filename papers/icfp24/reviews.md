ICFP 2024 Paper #59 Reviews and Comments
===========================================================================
Paper #59 Symmetries in Sorting


Review #59A
===========================================================================

Overall merit
-------------
C. Weak paper, though I will not fight strongly against it

Reviewer Expertise
------------------
Y. I am knowledgeable in this area, but not an expert

Reviewer Confidence
-------------------
3. Good: I am reasonably sure of my assessment

Paper summary
-------------
This paper explores the relation between sorting algorithms and orderings. Given an ordering on a set A, this induces a sorting algorithm on lists of A. The implication in the other direction is less obvious -- especially as not every endomorphism on lists is a sorting function; not every relation on A is an order. This paper establishes how the two defining properties of sorting functions and orderings can be connected formally using HoTT / Cubical Agda as the metalanguage to bridge the gap.

Assessment of the paper
-----------------------
This paper gradually builds up to the main result, connecting ordering of elements and sorting of lists. The paper gives a tour of universal algebra, (free) monoids, (free) commutative monoids, monoid homomorphisms and how to define these concepts mathematically and (when relevant) formalise them in type theory. Most of these topics are well studied elsewhere and I appreciate the effort that has gone into making the paper relatively accessible.

Having said that, however, it takes almost twenty pages to introduce the problem and provide the background mathematics -- before the question from the introduction is finally tackled. Even then, I consider the power-to-weight ratio between the methods used and the results these deliver to be rather poor. The key insight -- we can define an ordering between two elements by sorting a two-element list -- does not strike me as particularly deep, despite the pages of mathematics that precede it. The main technical hurdles seem to be establishing transitivity: which relies on the head of a sorted list being a minimal element. I may be overlooking something here -- but I can't help but feel underwhelmed by the time I'd finished reading the paper.

I really do appreciate that formalisation is not easy, especially in evolving systems such as Cubical Agda, yet I struggle to identify re-usable insights or techniques that deserve wider recognition in the FP community.

Questions for authors’ response
-------------------------------
* How essential is the use of Cubical Agda here? Proving that the sorting specification (permutation + order) uniquely determines the behaviour of any sorting function is possible in vanilla Agda. From the description, I assume most of these constructions -- defining a sorting algorithm parametrised by an ordering, defining an ordering given a sorting algorithm, etc. -- can be done without HoTT. The quotient types and HITs, used for SLists and Bags, do require Cubical Agda -- but there are perfectly reasonable definitions of both these notions that do not rely on these features.

* Are there any re-usable insights that could have wider applications beyond the development presented?

Comments for authors
--------------------
* Why do the figures on the first page use different brackets? I would expect the sorted and unsorted sequences to use the same brackets (and possibly, the three colours to use set braces).

* line 132 - 'logical and.. logical ord' -> perhaps 'conjunction' and 'disjunction' is more clear?

* line 333 - these formulas confused me at first, until I realised that there are two different zero's at play here. The zero drawn from the set of natural numbers and the that from Fin 1.

* line 463 - THe -> The

* line 471 - I didn't found this example particularly helpful, as it does not mention union or ++.

* Line 540 - why choose this notion of permutation? This works well for bubble sort, but not for other sorting algorithms...

* Line 610 - List(A) is a set assuming A is a set -- I understand what you mean, but the paper assumes quite some prior knowledge about homotopy type theory (using terms like 'propositional truncation'), but then spends quite some time spelling out the definition of very simple structures such as monoids. I can't help but wonder if the presentation would be better if the explanation over these topics was distributed otherwise.

* Line 1010 - the proposition uses 'image-respects-pair' before this has been defined. Perhaps it would make sense to swap these two.

* Proposition 25 seems trivial as it is formulated now. Why does the current formulation rule out choosing s = t by construction?

* line 1150 - this is almost unreadable as the 'code font' and text font are so similar that it becomes very hard to parse.

* line 1159 - I did not understand the citations from my (printed) copy of the submission.



Review #59B
===========================================================================

Overall merit
-------------
D. Reject

Reviewer Expertise
------------------
X. I am an expert in this area

Reviewer Confidence
-------------------
4. High: I am very sure of my assessment

Paper summary
-------------
This paper contributes a characterisation of *sorting function*, an extensional view of sorting algorithm, independent from a choice of total order as a section of the (canonical) projection from the free monoid $\mathcal{L}A$ to the free commutative monoid $\mathcal{M}A$ satisfying two additional properties $\textsf{image{-}respects-pair}$ and $\textsf{image-can-induct}$ (Definition 7.6). Moreover, it is shown that the set of decidable total orders $A$ is equivalent to the set of sorting functions on $A$ with a decidable equality (Theorem 7.7).

In detail, a section $s\colon \mathcal{M}A \to \mathcal{L}A$ of the projection $q\colon \mathcal{L}A \to \mathcal{M}A$ can be understood as a function from lists $\mathit{xs}$ of $A$ to lists $s(\mathit{xs})$ of $A$ such that any permutation $\mathit{ys}$ of $\mathit{xs}$ must produce the same list $s(\mathit{xs})$ and that $q(s(\mathit{xs})) = \mathit{xs}$ since any permutation of $\mathit{xs}$ belongs to the same equivalence class in $\mathcal{M}A$ and that $s$ is a section of $q$. It means that $s(\mathit{xs})$ can only pick some *permutation* of $\mathit{xs}$. This permutation-invariant property is obviously satisfied by the function defined by any sorting algorithm for some given ordering. Starting from sections, one would need to ensure that $s$ picks the permutation uniformly for every two and more elements.

The characterisation then starts from the observation that a section also defines a relation, which is very close to a total order but without transitivity, and the induced relation coincides with the given ordering if the section is defined by a sorting algorithm. They further refine this set of functions with additional constraints until they are uniquely determined by the induced total order.

Their characterisation is not tied to any specific representation of free monoids, so it works for any possible representations such as lists and arrays (as functions from $\mathsf{Fin}\;n$ to $A$). Similarly, common operations on free (commutative) monoids are given in this level of generality.

In addition to the main contribution, this paper reviews some elements of universal algebra in terms of category theory and claims to prove every result formally in Cubical Agda.

Assessment of the paper
-----------------------
The main contribution (Definition 7.6 and Theorem 7.7) is cute, providing a fresh take on what sorting is extensionally. However, the paper unnecessarily takes too much space on well-established notions in universal algebra from Sections 3 to 5. The operations in Section 6 are straightforward to define if working with the free (commutative) monoids defined inductively by singletons and unions subject to unit laws, associative laws, (commutativity), and set truncator, using higher inductive type.

Some technical issues are not sufficiently explored, either.
- The paper briefly mentions there are notions of total order and decidable total order, and they chose to work with decidable total order, making me wonder why this stronger version was chosen. In contrast, Frumin et al. (2018) study finite sets, free commutative monoids that are idempotent, in HoTT with two notions of equality: decidable equality and decidable mere equality. It is also not clear how essential univalence is in this paper.
- This paper also discusses the recent work by Kupke et al. (2023) on the construction of free commutative monoid as fresh lists without the use of quotient type and argues that their representation is reasonable. This paragraph made me wonder why one needs to work in HoTT at all and if we can establish the correspondence in this paper in their setting.

As the paper emphasises the use of HoTT, I'd like to see some discussion specific to HoTT.

Apart from falling short of significance, the writing can be improved:

- The introduction does not clearly state and explain the main result (Theorem 7.7).
- It is not clear what the targeted audience is. While many rudimentary developments in universal algebra are presented in length, more advanced notions (such as coequaliser, projective, algebraic-freeness, Seely isomorphism, and Riesz refinement property) are mentioned without explanation.
- The main focus of this paper is unclear—alternative representations of free (commutative) monoids are presented but not needed for later development; a general construction of free algebras is briefly discussed at the end of Section 3 with the conclusion that it will not be used in subsequent sections.
- Each section is loosely connected, and I have no difficulty starting from Section 7 without reading prior sections first.

The technical contribution of this paper might not be very interesting to the ICFP audience. The total order is usually given in practice and thus uniquely determines the *extensional* behaviour of the sorting algorithm. How could Theorem 7.7 be used? Having at least a use case of Theorem 7.7 would make the contribution more convincing.

In short, the technical contribution is cute but not significant enough; the writing can be improved; the technical contribution as it is does not seem appealing for ICFP. Unfortunately, I'd argue that this paper should be rejected.

Comments for authors
--------------------
Based on its contributions, I believe this paper is more suitable for CPP or specialised conferences in theoretical computer science after resolving aforementioned issues.



Review #59C
===========================================================================

Overall merit
-------------
D. Reject

Reviewer Expertise
------------------
X. I am an expert in this area

Reviewer Confidence
-------------------
4. High: I am very sure of my assessment

Paper summary
-------------
The paper claims to provide a novel axiomatization of sorting
functions.

Assessment of the paper
-----------------------
Strengths:

· The submission has the *potential* for a nice tutorial paper on free
  structures and their use in program verification.  (It doesn't
  succeed in its present form: too much category-theory and
  type-theory lingo; no practical examples—is the ``new''
  axiomatization of sorting algorithms helpful for program
  verification e.g. to establish the correctness of a solution to the
  Dutch National Flag Problem?  A mix of Agda and traditional
  mathematical reasoning—you may want to provide Agda proofs of the
  theorems?  The axioms are pulled out of the hat; a more attractive
  approach would try to derive them.)

Weaknesses:

· Lack of focus: It is not clear what the goal of the paper is.  The
  abstract says ``Our first main contribution is a new axiomatization
  of correct sorting algorithms''.  Now, the axiomatization is only
  discussed on Page 20! (That's a long build-up; you certainly don't
  want to keep the reader waiting that long.)  I don't understand
  ``Our second main contribution is a formlization of the informal
  intuition that commutative monoids are unordered lists.''  Is the
  qualifier *free* missing here? (Typo: formlization.)

· Lack of discussion of related work: Fritz Henglein's in-depth
  treatise ``What is a sorting function?'' is not even mentioned
  (Available online 10 March 2009).  Henglein answers the question
  ``What is a sorting function—not a sorting function for a given
  ordering relation, but a sorting function with nothing given?''  His
  work is more general than the present submission in that he
  considers preorders, not orders.  He also discusses *stable* sorting
  functions and considers both comparison-based and key-based sorting
  (of which the Dutch National Flag Problem is an instance).

· Lack of originality: As far as I can tell, all of the material is
  completely standard: there are many papers on free structures;
  Henglein's work encompasses the ``first main contribution''.

Overall, this seems like a clear reject. That said, I would encourage
you to consider turning the submission into a tutorial paper on free
structures and their use in program verification (see above).

