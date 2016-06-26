# Regular Expression Derivatives

Formalization of regular expression derivatives in Coq. A good reference with the basic definitions and a matcher based on derivatives comes from [Matt Might](http://matt.might.net/articles/implementation-of-regular-expression-matching-in-scheme-with-derivatives/). This formalization was inspired by [Nick Foster's presentation from OPLSS 2016](https://www.cs.cornell.edu/~jnfoster/oplss16/2016-06-oplss-3.pdf) (page 69), but only the terms "observation map" and "continuation map" come from that reference, the rest is fairly universal.

In this development we define regular expressions, give them a denotation as a
predicate over strings, define a continuation map over the syntax as well as a
much simpler, denotational derivative, and then prove that for all regexes, the
denotation of the continuation map of the syntatic derivative is the derivative
of the denotation of the regex (`continuation_map_denotes_derivative`).
