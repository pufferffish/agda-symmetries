We thank the reviewers for their thoughtful and detailed feedback.

It is very embarrassing that we did not know about the work of Henglein (2009), since under the assumption of decidable
equality, theorem 7.5 in that paper already is equivalent to our main result. Even though we gave several talks about
this work before the submission, no one had pointed this out to us. After studying the literature ourselves, we only
found a connection to a proof in a paper by Henglein and Hinze (2013), which we mentioned on line 1187.

In light of this, there is essentially nothing new in the paper other than a restatement in a categorical framework and
a formalization in Agda. Therefore, we have decided to withdraw the paper. We apologize for the oversight, and thank the
reviewers and program committee for their time. We will continue thinking about the problem and studying the work of
Henglein, to relate it to our framework and axioms for sorting:

Use of HoTT:
===
The main result can be formalized without HoTT/Cubical, of course, in any framework for constructive type theory -- the
use of HoTT is to make the proof conceptually clear, and closer to the informal mathematics, without requiring
engineering tricks (like setoids, quotient containers, etc). We believe that the use of HoTT is justified because we
work in a representation-independent way, using categorical universal properties (free algebras), and we use tools like
univalence, effective quotients, for example, to show that the map q : L(A) -> M(A) is surjective (which is hard to do
with a concrete representation like SList, but obvious for a quotient representation of M(A)). Partly, the purpose of
the submission was also to show to the ICFP community how these tools are useful in practice, as applied to verified
programming and proving.