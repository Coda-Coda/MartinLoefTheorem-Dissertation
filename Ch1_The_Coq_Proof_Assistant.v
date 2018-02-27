(** %\chapter{The Coq Proof Assistant}% *)

(** This chapter is an introduction to and overview of the proof techniques relating to the Coq Proof assistant%~\cite{coq}% that are used in this dissertation. *)

(** * Interactively viewing proofs *)
(** %
\urlstyle{same}
The entire text of this dissertation is comprised of Coq source files which include all the proofs given. The reader is recommended to download CoqIde from \begin{center}\url{https://coq.inria.fr/download}\end{center} and use the Coq source files available from \begin{center}\url{https://github.com/Coda-Coda/MartinLoefTheorem-Dissertation/releases/tag/submission}\end{center} This will allow the reader to step through any of the proofs in this dissertation interactively.
% *)

(** * A typical Coq Proof *)
(** Because of the nature of the topic covered by this dissertation, some of the proof techniques used are not entirely standard (for instance [Axiom]s are often used) but most of the same elements are still used. Below is an annotated fairly standard Coq proof that highlights some of the ways Coq is used to assist with proofs in this dissertation. *)

Inductive boolean :=
 | true
 | false.

(** Above a data type, [boolean], is defined which can have either of the values listed. Data type definitions of this kind will be used to define propositional or modal formulas as their own type. *)

Definition not (x:boolean) : boolean :=
match x with
 | true => false
 | false => true
end.

(** Above a function [not] is defined with the type signature [boolean -> boolean]. Very few function definitions of this kind are used in this dissertation. *)

Lemma example_lemma : forall (b:boolean), b = not (not b).
Proof.
destruct b.
 - (** Case [b = true] *)
   reflexivity.
 - (** Case [b = false] *)
   reflexivity.
Qed.

(** Above is an example of a Coq proof. The statement of the proof appears first, followed by the `proof script' which instructs Coq as to which steps to take to prove the statement. Each step involves using a [tactic] which can be a basic step or be a complex semi-automated step. This dissertation involves many proofs and also defines some [tactic]s in order to aid with proofs. *)

(** A Coq proof can be stepped through interactively [tactic] by [tactic]. At each stage Coq will show the remaining [goal] that needs to be proven at that stage. *)

(** * An overview of relevant tactics *)

(** In general, Coq does not automatically prove statements. Rather, the process is guided by the user inputting tactics which control the flow of the proof. Below are a selection of tactics that are commonly used in proofs in this dissertation. *)

(** %\begin{itemize}% *)

(** %\item% *)
(** [reflexivity] will simplify the goal and then solve a goal of the form [a=a]. *)

Example reflexivity_example : 1=1.
Proof.
reflexivity.
Qed.

(** %\item% *)
(** [simpl] will simplify a goal. *)

Example simpl_example : 1 + 2 = 3.
Proof.
simpl. (** The [goal] now is [3 = 3]. %\\% *)
reflexivity.
Qed.

(** %\item% *)
(** [intros] will typically introduce quantified variables as new arbitrary variables. Usually used with goals of the form [forall p q, ...]. *)

Example intros_example : forall n, n + 1 = n + 1.
Proof.
intros. (** The context now contains [n : nat], and the [goal] is [n + 1 = n + 1]. *)
reflexivity.
Qed.

(** %\item% *)
(** [exact] will solve a goal that looks exactly like a current hypothesis. In the example below, [p] is introduced as the hypothesis [H] and then the goal [p] can be solved with the tactic [exact H]. *)

Example exact_example : forall p, p -> p.
Proof.
intros p H.
exact H.
Qed.

(** %\item% *)
(** [unfold] will unpack a definition and rewrite the [goal] accordingly. *)

Definition double_neg (p:Prop) := ~ ~ p.

Example unfold_example : forall p:Prop, p -> double_neg p.
Proof.
intro.
unfold double_neg. (** Now the [goal] is [p -> ~ ~ p]. %\\% *)
firstorder. (** Proof automation for first order logic can complete the proof. %\\% *)
Qed.

(** %\item% *)
(** [destruct] facilitates analysing different cases. *)

Example destruct_example : forall b: boolean, b = true \/ b = false.
Proof.
destruct b.
left. reflexivity. (** Case: [b = true]. %\\% *)
right. reflexivity. (** Case: [b = false]. %\\% *)
Qed.

(** %\item% *)
(** [pose proof] can be used to bring an axiom into the context as shown below. Note how [example1] is followed by [p] and [~ q], they are then bound to [A] and [B] respectively, giving the correct instantiation of the axiom [example1]. *)

Axiom example1 : forall A B, ~ A -> A \/ B -> B.

Example pose_proof_example : forall p q, ~ p -> p \/ ~ q -> ~ q.
Proof.
intros p q.
pose proof example1 p ( ~ q) as example1_axiom.
exact example1_axiom.
Qed.

(** %\item% *)
(** [apply] will apply a theorem to the current goal, as shown below. *)

Example apply_example : forall p q, ~ p -> p \/ ~ q -> ~ q.
Proof.
intros p q.
apply example1.
Qed.

(** %\end{itemize}% *)


(** * Confidence in different types of Coq proofs *)

(** It is important to note that different ways of using Coq have important implications for how trustworthy the resulting proofs are and for which sections of code need to be checked to be trustworthy before trusting a particular proof. %\par%
When Coq is used without adding any additional assumptions and for its regular usage we can be very confident of the system's consistency and the trustworthiness of proofs. In general, if the Coq definitions used in a theorem are fully understood, the user code leading to a proof of it would not need to be manually checked to be trustworthy. %\par%
In contrast, when the code leading to a proof makes use of assumptions then it is important to carefully check that the assumptions do not lead to unintended results. For example, consider the statement below. *)

Parameter i : Type.

(** The [Parameter] keyword is an example of this. In the code above, we assume the existence of [i] and that it is a [Type]. In this case, this is a safe assumption but it is important to note that the trustworthiness of proofs in a Coq file depends on the trustworthiness of such statements. %\par%
For example, the following use of [Parameter] would make Coq's logic inconsistent: %\par%
[Parameter x: False.] %\par%
This assumes the existence of [x] of type [False], which essentially assumes the existence of a proof of [False] (which should be impossible). %\par%
A second consideration is whether the proof involves an embedding and `lifted connectives', such as is the case with the Modal Logic formalisation in a later chapter. This technically falls under the idea of being sure that "the Coq definitions used in the theorem are fully understood". Essentially, if an entire logical system has been newly defined, then any theorems proven in such a system are only as trustworthy as the definitions given in the user code.
 %\par%
These considerations are relevant to aspects of the formalisations in this dissertation, and also relevant are the standard considerations outlined on a Coq FAQ site%~\cite{coqFAQtrust}% which include trusting the integrity of the system Coq is running on and trusting the theory behind Coq. 
*)