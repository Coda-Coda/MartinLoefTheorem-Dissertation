(** printing Falsum $\bot$ *)
(** printing False $\bot$ *)
(** printing ◊ $\Diamond$ *)
(** printing (◊ $(\Diamond$ *)
(** printing ⇒ $\Rightarrow$ *)
(** printing ∧ $\wedge$ *)
(** printing ∨ $\vee$ *)
(** printing ⊥ $\bot$ *)
(** printing ¬ $\lnot$ *)
(** printing (¬ $(\lnot$ *)
(** printing □ $\square$ *)

(** %\chapter{Open Questions}% *)

(** * Double negation elimination and the Martin-%\Loef{}% Theorem *)

(** In chapter 4, double negation elimination was considered with regards to the completeness theorems. [( ~ ~ q -> q)] also has interesting considerations in relation to the Martin-%\Loef{}% Theorem. %\\%
For instance, Martin-%\Loef{}% claims that "it is impossible to find a counterexample to the law of the excluded middle in its positive formulation"%~\cite[p.~14]{ml}%. If we consider %$$%[( ~ ~ q -> q) \/ ( ~ ( ~ ~ q -> q))]%$$% we would think this must not be true, since neither disjunct is provable intuitionistically. However this would then count as "a counterexample to the law of the excluded middle in its positive formulation". %\\%
What then resolves this? A possible answer is that the reasoning used to justify that neither disjunct is provable intuitionistically is not itself intuitionistic reasoning. That is, analysing the axioms of intuitionistic logic to conclude that [( ~ ~ q -> q)] is not intuitionistically provable does not give us a canonical proof of [False] from [( ~ ~ q -> q)]. This means that although we _know_ neither disjunct is provable we do not know this intuitionistically and thus we do not have "a counterexample to the law of the excluded middle in its positive formulation" after all. %\\%
Nevertheless, this example does show that care needs to be taken when interpreting the implications of the Martin-%\Loef{}% Theorem. *)

(** * Simplifying the axioms in the CS4 + Int formalisation *)

(** In the proof of Martin-%\Loef{}%'s Theorem in chapter 5, both Fact 2 and Fact 4 are added as axioms. It may be possible however to derive these facts from more fundamental rules for intuitionistic logic, in a similar way to how this is done in the intuitionistic logic formalisation in chapter 6. %\\%
The advantage of this would be that the trustworthiness of the proof of the Martin-%\Loef{}% Theorem would rest upon the fundamental rules rather than the correctness of Fact 2 and Fact 4. However both Fact 2 and Fact 4 (shown below) are fairly primitive axioms so this is not too great a concern. *)

(** [[
Axiom fact_2 : forall A B, (True A /\ True B) <-> True (A ∧ B).
Axiom fact_4 : forall A, ~ (True (A ∧ (¬ A))).
]] 
*)

(** * Implications of the `Non-strictly positive occurrence' error in the intuitionistic logic formalisation *)

(** In the definition of what constitutes a proof in the intuitionistic logic embedding in chapter 6 the most natural definition for the proof rule for implication results in the Coq error `Non strictly positive occurrence of "Proof" in
 "[forall p q : proposition, (Proof p -> Proof q) -> Proof (Implies p q)]" '. A shorter example of a definition that gives the same error is shown below. From further reading%~\cite{vilhelm, stackoverflowPositive}% it does unfortunately seem that that circumventing the error as done in the intuitionistic logic formalisation is very likely to enable [False] to be provable. Further work would be needed to ensure this is the case and to check whether a slightly altered definition for [implies_ev] might be able to avoid the issue. Also, the proofs in the chapter (as far as I am aware) do not make use of the flaw that is introduced and so it is possible that the reasoning in the chapter is still useful. *)

(* begin hide *)
Inductive Atoms := 
  | a : Atoms
  | S : Atoms -> Atoms.

Inductive proposition :=
  | Atom : Atoms -> proposition
  | Implies : proposition -> proposition -> proposition
  | Or : proposition -> proposition -> proposition
  | And : proposition -> proposition -> proposition
  | Falsum : proposition
  | Not : proposition -> proposition
  | K : proposition -> proposition.
(* end hide *)
(** [[
Inductive Proof : proposition -> Prop :=
  | implies_ev : forall (p q : proposition), (Proof p -> Proof q) -> (Proof (Implies p q)).
]]
 *)