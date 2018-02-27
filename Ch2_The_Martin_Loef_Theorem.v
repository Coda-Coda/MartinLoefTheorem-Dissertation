(** printing False $\bot$ *)

(** %\chapter{The Martin-\Loef{} Theorem}% *)

(** The Martin-%\Loef{}% Theorem is introduced in the paper Verificationism Then and Now (1995, 2013)%\cite{MartinLoef1995, ml}%. The conclusion of the paper is that, on the intuitionistic conception, there are no absolutely undecidable propositions. %\\%
A large portion of the paper involves carefully unpacking the notions of a proposition, truth, falsity, knowledge and possibility. %\\%
The purpose of this dissertation and the ongoing work in parallel to it is to formalise the proof outlined by Martin-%\Loef{}% in some sound and complete logical system as well as in a proof assistant such as Coq. *)

(** * Unpacking the key notions *)

(** For a full treatment of the key notions in the Martin %\Loef{}% Theorem see the paper Verificationism Then and Now%~\cite{ml}%. Here an overview is given. *)

(** ** Proposition *)
(** A proposition is defined by its introduction rules. For example, the proposition $ A \vee{} B $ gets its meaning from that the introduction rule for $ \vee{} $ requires either a proof for $ A $ or a proof for $ B $ in order to have a proof for $ A \vee{} B $. *)
(** ** Truth *)
(** A proposition is true if it has a proof. *)
(** ** Falsity *)
(** A proposition is false, if there exists a hypothetical proof of [False] from it. *)
(** ** Knowledge *)
(** A proposition can be known to be true if there exists a proof for it. *)
(** ** Possibility *)
(** The `if there exists' in the definition of knowledge refers to an intuitionistic understanding of these words. That is, possibility in principle. For example, in order for a statement involving a large number to be known to be true, there need not be a proof detailing every step of that proof - rather it would be sufficient to demonstrate the existence of an algorithm that would, in principle, produce the required step by step proof. *)

(** * Unpacking the Martin-%\Loef{}% Theorem *)

(** The sections below describe the informal proof of the Martin-%\Loef{}% Theorem. This content was kindly provided by Cristian Calude%~\cite{crisslides}%, with only minor alterations made by myself. *)


(** ** Objective vs. subjective mathematics *)
(** %
\begin{itemize}
\item Objective mathematics consists of the body of mathematical propositions, constructive or not, which hold true in an absolute sense. Peano Arithmetic
 or Zermelo-Fraenkel set theory are parts of it. 
\item Subjective mathematics consists of all mathematical truths {\em humanly demonstrable} (or {\em provable} or {\em knowable}),
in a constructive manner or not.
\end{itemize}
%
*)



(** ** Does objective mathematics coincide with subjective mathematics? *)

(** %
 \Godel{} \alert{accepted} Hilbert's rejection of the existence of absolutely unsolvable problems because otherwise, 
\begin{quote}
``it would mean that human reason is utterly irrational by asking questions it cannot answer, while asserting emphatically that only reason can answer them''~\cite[p.~324-325]{wang}
\end{quote}

but he found Turing's argument \alert{inconclusive}:

\begin{quote}
``Turing gives an argument which is supposed to show that mental procedures cannot go beyond mechanical procedures. However, this argument is inconclusive. What Turing disregards completely is the fact that mind, in its use, is not static, but constantly developing, i.e., we understand abstract terms more and more precisely as we go on using them \dots  though at each stage the number and precision of the abstract terms at our disposal may be finite, both \dots  may converge toward infinity \dots''~\cite[p.~306]{godel1990collected}
\end{quote}

% *)


(** %
\Godel{}'s answer (Gibbs lecture ``Some Basic Theorems on the Foundations of Mathematics and their Implications'',~\cite{Godel51}) based on his incompleteness theorem is a \alert{disjunctive conclusion}:\medskip

\begin{quote}
``Either mathematics is incompletable in this sense, that its evident axioms can never be comprised in a finite rule, that is to say, the human mind (even within the realm of pure mathematics) infinitely surpasses the powers of any finite machine, or else there exist absolutely unsolvable diophantine problems of the type specified.''
\end{quote}
%
*)

(** %
Martin-\Loef{}'s answer based on a {\em constructive} interpretation of the notions of  `true', `false' and `can be known'~\cite{MartinLoef1995}:
\begin{quote}
There are no propositions which can neither be known to be  true nor be known to be false.
\end{quote}

For the non-constructive mathematician:

\begin{quote}
No propositions can be effectively produced (i.e.~by an algorithm) of which it can be shown that they can neither be proved constructively nor disproved 
constructively. There may be absolutely unsolvable problems, but one cannot effectively produce one for which one can show that it is unsolvable.
\end{quote}

%
*)


(** ** Objective mathematics vs. subjective mathematics *)

(** %
Emil Post writes:~\cite[p.~200]{Urquhart2009, Post1943}

\begin{quote}
``A fundamental problem is the question of the existence of absolutely undecidable propositions, that is, propositions which in some a priori fashion can be said to have a determined truth-value, and yet cannot be proved or disproved by any valid logic.''
\end{quote}


\alert{We will only require that the objective mathematics contains the subjective mathematics.} \pause  \medskip 

Furthermore,
in contrast with Feferman~\cite{Feferman2006-SFEATA}, \alert{we will include in subjective mathematics all statements provable by any methods, axiomatic (dynamic, not only static), constructive, computational or by
methods currently not yet discovered.}


% *)


(** **  Martin-%\Loef{}%'s argument *)
(** %
 Constructive logical interpretations:

 \begin{itemize}
  \item The proposition $A$ can be known to be true if we have a proof for $A$.
  \item The proposition $A \vee B$ can be known to be true if we have a proof for $A$ or we have a proof for $B$.
  \item The proposition $A \wedge B$ can be known to be true if we have a proof for $A$ and we have a proof for $B$.
  \item The proposition $A \rightarrow B$ can be known to be true if we have an algorithm which converts any proof for $A$ into a proof for $B$.
  \item The proposition $\neg A$ can be known to be true if we have a proof for $A \rightarrow (0=1)$.
  
  \item The proposition $A$ \alert{can be known to be false} if we have a proof for $\neg A$.
  \item The proposition $A$ \alert{cannot be known to be true} if we have an algorithm which tests and rejects any given `proof' which purports to demonstrate $A$.
  \item If the proposition $A$ can be known to be true, then $A$ is true.
  \item Martin-\Loef{}'s notions of \alert{can be known to be true/false} are not related to any fixed formal system.
\end{itemize}
%
*)

(** %
{\bf Fact~1.} [Unknowability of truth entails knowability of falsity] {\em  If the proposition $A$ cannot be known to be true, then $A$ can be known to be false.}
\\[2ex]

{\it Proof}: To prove that $A$ can be known to be false we have to show that $\neg A$, i.e. $A \rightarrow (0=1)$ can be known to be true. To this aim we need an algorithm ${\mathcal B}$ to convert any proof of $A$ into a proof of $(0=1)$. The algorithm ${\mathcal B}$  returns anything output by  the algorithm  ${\mathcal A}$ provided by the hypothesis, i.e.~noting: vacuously, the implication holds.\\

Comment: The proof constructively produces positive information  from negative information. \\
% *)

(** %
{\bf Fact~2.} {\em If $A$ can be known to be true and $B$ can be known to be true, then $A\wedge B$ can be known to be true.}

\medskip 

{\bf Fact~3.} [Absolute consistency]  {\em The proposition $(0=1)$ cannot to be known to be true.}
\\[2ex]


{\it Proof}: The proposition $\neg (0=1)$ can be known to be true because $(0=1)\rightarrow (0=1)$ is provable using the identity algorithm, so $(0=1)$ can be known to be false, i.e.~it is false. No proof can demonstrate $(0=1)$ because otherwise it would be true: the algorithm rejects any proof candidate.

% *)
(** %\pause% *)
(** %
{\bf Fact~4.} [Law of contradiction]  {\em One and the same proposition $A$ cannot both be known to be true and  be known to be false.}
\\[2ex]


{\it Proof}: By hypothesis we have a proof demonstrating $A$ and a proof demonstrating $\neg A$, i.e. $A \rightarrow (0=1)$. Then we can demonstrate $(0=1)$, contradicting Fact~3.


\medskip

{\bf Fact~5.} [Law of excluded middle] {\em There is no proposition  which can neither be known to be true nor be known to be false, i.e.~there is no absolutely unprovable proposition.} 
\\[2ex]


{\it Proof}:  If $A$ is a proposition which cannot be known to be true, then by Fact~1, $A$ can be known to be false, a contradiction.
 % *)