algos
=====

 ἔνθ᾽ οἵ γ᾽ ἄλγε᾽ ἔχοντες ὑπὸ χθονὶ ναιετάοντες
 εἵατ᾽ ἐπ᾽ ἐσχατιῇ, μεγάλης ἐν πείρασι γαίης,
 δηθὰ μάλ᾽ ἀχνύμενοι, κραδίῃ μέγα πένθος ἔχοντες. 

 and he made them live beneath the wide-pathed earth,
 where they were afflicted, being set to dwell under the ground,
 at the end of the earth, at its great borders,
 in bitter anguish for a long time and with great grief at heart.
 Hesiod, Theogony, 620

=====

Algebraic arithmetization of boolean algebra and its OCaml implementation.

To compile:

ocamlbuild main.native

----

A different kind of SAT solver, boolean formulas are represented as algebraic expressions.

For example:

a → b ≡ (1 + −a + (a × b))

The solver performs cancellation, idempotency reductions, x^2 = x holds in this algebra, and so on and so forth, until either a fully reduced algebraic expression in sum of product forms is found; or 0, or 1.  Reduction to 1 is a tautology, 0 a contradiction, and anything else a satisfiable expression.

The ``interpreter'' accepts unicode (∨, →, ¬, etc.), in addition to the usual ascii representations of the logical formulae (\/, ->, ~, etc.)

