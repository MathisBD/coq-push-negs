# Description

This is an implementation in Coq of a Lean tactic called "push_neg" :
https://leanprover-community.github.io/mathlib4_docs//Mathlib/Tactic/PushNeg.html

To push negations in a formula [f] of type [Prop], the main idea is to reify [f] into an inductive type [form] that captures just enough of the first-order structure of [f]. We then implement push_neg on [form]s, and also define a function [eval] that does the inverse of reification (i.e. lowers a [form] into a [Prop]). Finally we use a bit of Ltac to glue all of this together.

This tactic is tricky to implement because it is required to preserve variable names.
For instance, a naive implementation would transform [~ forall long_name, long_name = 0] into [exists x, x <> 0], whereas we want to get [exists long_name, long_name <> 0]. The trick I used to accomplish this is described in the code. 

# Running 

This project uses MetaCoq. To run the Coq file, you will need Coq 8.19.1 and coq-metacoq-template 1.3.1+8.19.