(******************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Flight_Model.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

theory
  Flight_Model
imports
  "../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin

subsection\<open> Class Model \<close>

find_theorems (350) name:"Client"

text\<open>This part corresponds to the writing in Isabelle of the
code shown in \autoref{fig:code-data}.\<close>

Class Flight
  Attributes
    seats  : Integer
    "from" : String
    to     : String
End

lemma "id = (\<lambda>x. x)"
by (rule id_def)
text\<open>As remark, we are checking for example that the constant @{term id} already exists,
and that one can also use this name in the following attribute:
no conflict will happen.\<close>

Class Reservation
  Attributes
    id : Integer
    date : Week
End

Class Person
  Attributes
    name : String
End

Class Client < Person
  Attributes
    address : String
End

Class Staff < Person
End

Association passengers
  Between Person      [*]
            Role passengers
          Flight      [*]
            Role flights
End

Aggregation flights
  Between Flight      [1]
            Role flight
          Reservation [*]
            Role fl_res Sequence_
End

Association reservations
  Between Client      [1]
            Role client
          Reservation [*]
            Role cl_res
End

Association connection
  Between Reservation [0 \<bullet>\<bullet> 1]
            Role "next"
          Reservation [0 \<bullet>\<bullet> 1]
            Role prev
End

text\<open> In complement to \autoref{fig:code-data}, we define an enumeration type.\<close>
Enum Week
  [ Mon, Tue, Wed, Thu, Fri, Sat, Sun ]
End!

find_theorems (350) name:"Client"

(*
(* Illustration of a wrong model transition: *)
Instance R00 :: Reservation = [ id = 00, flight = [ F1 ], "next" = R11 ]
     and R11 :: Reservation = [ id = 11, flight = [ F1, F2 ], "next" = R00 ]
     and R22 :: Reservation = [ id = 22, "next" = [ R00, R11, R22 ] ]
     and F1 :: Flight = [ seats = 120, "from" = "Valencia", to = "Miami" ]
     and F2 :: Flight = [ seats = 370, "from" = "Miami", to = "Ottawa" ]
(*
R00 .flight = Set{ F1 }
R00 .client = Set{} // minimum constraint [1] not satisfied
R00 .prev = Set{ R11 , R22 } // maximum constraint [0 .. 1] not satisfied
R00 .next = Set{ R11 }
R11 .flight = Set{ F1 , F2 } // maximum constraint [1] not satisfied
R11 .client = Set{} // minimum constraint [1] not satisfied
R11 .prev = Set{ R00 , R22 } // maximum constraint [0 .. 1] not satisfied
R11 .next = Set{ R00 }
R22 .flight = Set{} // minimum constraint [1] not satisfied
R22 .client = Set{} // minimum constraint [1] not satisfied
R22 .prev = Set{ R22 }
R22 .next = Set{ R00 , R11 , R22 } // maximum constraint [0 .. 1] not satisfied
F1 .passengers = Set{}
F1 .fl_res = Set{ R00 , R11 }
F2 .passengers = Set{}
F2 .fl_res = Set{ R11 }
8 error(s) in multiplicity constraints
*)
*)

subsection\<open> Two State Instances of the Class Model \<close>

text\<open> The creation of (typed) object instances is performed in \HOCL
with the command $\Instance$: \<close>
Instance S1  :: Staff  = [ name = "Merlin" , flights = F1 ]
     and C1  :: Client = [ name = "Bertha" , address = "Miami" , flights = F1 , cl_res = R11 ]
     and C2  :: Client = [ name = "Arthur" , address = "Valencia" , flights = F1 , cl_res = R21 ]
     and R11 :: Reservation = [ id = 12345 , flight = F1 , date = Mon ]
     and R21 :: Reservation = [ id = 98765 , flight = F1 ]
     and F1  :: Flight = [ seats = 120 , "from" = "Valencia" , to = "Miami" ]
     and F2  :: Flight = [ seats = 370 , "from" = "Miami" , to = "Ottawa" ]
text\<open>
The notion of object instances comes before that of states.
Currently, we have only created the object instances @{const S1},
@{const C1}, @{const C2}, @{const R11}, @{const R21}, @{const F1} and @{const F2}.
They will need to be ``registered'' in a state later.
$\Instance$ verifies that all objects being created
 are respecting the multiplicities declared above in classes (in the bidirectional sense).
For example, after the type-checking stage, we have
correctly that @{term "R21 .client"} \<open>\<cong>\<close> @{term "Set{ C2 }"}, since @{const R21} appears as one reservation of
@{const C2}, and where ``\<open>X \<cong> Y\<close>''
stands as a synonym for @{term "\<forall>\<tau>. (\<tau> \<Turnstile> \<delta> X) \<longrightarrow> (\<tau> \<Turnstile> \<delta> Y) \<longrightarrow> (\<tau> \<Turnstile> (X \<triangleq> Y))"}.\footnotemark
As remark, the order of attributes and objects
declarations is not important: mutually recursive constructions become
de-facto supported. As illustration, we can include here the text displayed in the output window after evaluating
the above $\Instance$
(we have manually pasted the text from the output window in Isabelle/jEdit):
@{text [display] \<open>
S1 .flights \<cong> Set{ F1 }
C1 .flights \<cong> Set{ F1 }
C1 .cl_res \<cong> Set{ R11 }
C2 .flights \<cong> Set{ F1 }
C2 .cl_res \<cong> Set{ R21 }
R11 .flight \<cong> Set{ F1 }
R11 .client \<cong> Set{ C1 }
R11 .prev \<cong> Set{}
R11 .next \<cong> Set{}
R21 .flight \<cong> Set{ F1 }
R21 .client \<cong> Set{ C2 }
R21 .prev \<cong> Set{}
R21 .next \<cong> Set{}
F1 .passengers \<cong> Set{ S1 , C1 , C2 }
F1 .fl_res \<cong> Set{ R11 , R21 }
F2 .passengers \<cong> Set{}
F2 .fl_res \<cong> Set{}
\<close>}
\<close>
text_raw\<open>\footnotetext{
Although such rule schemata may be explicitly generated by $\Instance$ (for most \OCL expressions),
they can also not be:
at the time of writing, the complete type-checking process is at least
fully executed from an extracted \HOL function
(as one consequence, the type-checking process terminates).
This is feasible because for the moment, $\Instance$ only accepts ``grounds objects''
as arguments (the reader is referred to its syntax diagram detailed in \autoref{app:oltg-rail}).}\<close>

text\<open> We can check that @{const S1} indeed exists and has the expected \OCL type. \<close>
term "S1 ::\<cdot> Staff"

text\<open> Once objects are constructed with $\Instance$, it becomes possible to
regroup them together into a state. This is what the next command $\State$ is doing by creating
a state named \<open>\<sigma>\<^sub>1\<close>, corresponding to the pre-state of \autoref{fig:system-states}.\<close>
State \<sigma>\<^sub>1 =  [ S1, C1, C2, R11, R21, F1, F2 ]

text\<open>
This generates a number of theorems from it, \eg:
@{text [display] \<open>
\<And>\<sigma>. (\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Staff .allInstances@pre() \<triangleq> Set{S1}
\<And>\<sigma>. (\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Client .allInstances@pre() \<triangleq> Set{C1,C2}
\<And>\<sigma>. (\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Reservation .allInstances@pre() \<triangleq> Set{R11,R12}
\<And>\<sigma>. (\<sigma>\<^sub>1, \<sigma>) \<Turnstile> Flight .allInstances@pre() \<triangleq> Set{F1,F2}
\<close>}

At this point, it is not yet sure that @{text \<sigma>\<^sub>1} will be used in the pre-state or post-state.
In any case, the above command also generates the following symmetric lemmas:
@{text [display] \<open>
\<And>\<sigma>. (\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Staff .allInstances() \<triangleq> Set{S1}
\<And>\<sigma>. (\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Client .allInstances() \<triangleq> Set{C1,C2}
\<And>\<sigma>. (\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Reservation .allInstances() \<triangleq> Set{R11,R12}
\<And>\<sigma>. (\<sigma>, \<sigma>\<^sub>1) \<Turnstile> Flight .allInstances() \<triangleq> Set{F1,F2}
\<close>}

Because all these lemmas are stated under the precondition that all object instances are
defined entities, lemmas generated by $\State$ are actually proved in a particular
$\holoclthykeywordstyle\operatorname{locale}$~\cite{DBLP:journals/jar/Ballarin14,isabelle-locale} \<open>state_\<sigma>\<^sub>1\<close>.
Thus the header of \<open>state_\<sigma>\<^sub>1\<close> regroups these (mandatory) definedness assumptions,
that have to be all satisfied before being able to use the rules defined in its body.
\<close>

text\<open> The next statement illustrates \autoref{sec:focl-front-end}. It
shows for instance that object instances can also be generated
by $\State$ on the fly. Fresh variables are created meanwhile if needed, like \<open>\<sigma>\<^sub>2_object1\<close>.\<close>
State \<sigma>\<^sub>2 =
  [ S1
  , ([ C1 with_only name = "Bertha", address = "Saint-Malo" , flights = F1 , cl_res = R11 ] :: Client)
  , ([ C2 with_only name = "Arthur",address = "Valencia",flights=[F1,F2],cl_res=[self 4,self 7]]::Client)
  , R11
  , ([ R21 with_only id = 98765 , flight = F1 , "next" = self 7] :: Reservation)
  , F1
  , F2
  , ([ id = 19283 , flight = F2 ] :: Reservation) ]
text\<open>
Similarly as with $\Instance$, we can paste in the following what is currently being
displayed in the output window (where ``\<open>/*8*/\<close>'' means the object having an $\oid$ equal to
8).\footnotemark
@{text [display] \<open>
\<sigma>\<^sub>2_object1 .flights \<cong> Set{ /*8*/ }
\<sigma>\<^sub>2_object1 .cl_res \<cong> Set{ /*6*/ }
\<sigma>\<^sub>2_object2 .flights \<cong> Set{ /*8*/ , /*9*/ }
\<sigma>\<^sub>2_object2 .cl_res \<cong> Set{ \<sigma>\<^sub>2_object4 , \<sigma>\<^sub>2_object7 }
\<sigma>\<^sub>2_object4 .flight \<cong> Set{ /*8*/ }
\<sigma>\<^sub>2_object4 .client \<cong> Set{ \<sigma>\<^sub>2_object2 }
\<sigma>\<^sub>2_object4 .prev \<cong> Set{}
\<sigma>\<^sub>2_object4 .next \<cong> Set{ \<sigma>\<^sub>2_object7 }
\<sigma>\<^sub>2_object7 .flight \<cong> Set{ /*9*/ }
\<sigma>\<^sub>2_object7 .client \<cong> Set{ \<sigma>\<^sub>2_object2 }
\<sigma>\<^sub>2_object7 .prev \<cong> Set{ \<sigma>\<^sub>2_object4 }
\<sigma>\<^sub>2_object7 .next \<cong> Set{}
\<close>}

Note that there is a mechanism to reference objects via the (invented) keyword
$\greenkeywordstyle\operatorname{self}$ (it has no particular relation
with the one used in \autoref{sec:focl-front-end}),
which takes a number designating the index of a particular object instance occurring
in the list of declarations (the index starts with 0 as first position).

Similarly as for \<open>state_\<sigma>\<^sub>1\<close>, we obtain another $\holoclthykeywordstyle\operatorname{locale}$
called \<open>state_\<sigma>\<^sub>2\<close>, representing the post-state of \autoref{fig:system-states}.
\<close>
text_raw\<open>\footnotetext{As future work, it is plan for $\Instance$ to support the writing of
arbitrary \OCL expressions, including the assignment of potentially infinite collection types
(for example ``a set of sequence of bag of objects'').
In particular, besides the cardinality of the manipulated collection types,
the sole information required for checking multiplicities
appears to be the $\oid$ of objects.}\<close>

text\<open> The $\Transition$ command relates the two states together. \<close>
Transition \<sigma>\<^sub>1 \<sigma>\<^sub>2
text\<open>
The first state is intended to be understood as the pre-state,
and the second state as the post-state. In particular, we do not obtain similar proved theorems
if we write \<^theory_text>\<open>Transition \<sigma>\<^sub>1 \<sigma>\<^sub>2\<close> or \<^theory_text>\<open>Transition \<sigma>\<^sub>2 \<sigma>\<^sub>1\<close> (assuming \<open>\<sigma>\<^sub>1\<close> and \<open>\<sigma>\<^sub>2\<close>
are different). Generally, $\Transition$ establishes for a pair of a pre- and a post state
(i.e. a state transition) that a number of
crucial properties are satisfied.
For instance, the well-formedness of the two given states is proven: \<open>WFF(\<sigma>\<^sub>1, \<sigma>\<^sub>2)\<close>.

Furthermore, for each object \<open>X\<close> additional lemmas are generated to situate \<open>X\<close>
as an object existing in \<open>\<sigma>\<^sub>1\<close>, \<open>\<sigma>\<^sub>2\<close>, both, or in any permutations of
\<open>\<sigma>\<^sub>1\<close> and \<open>\<sigma>\<^sub>2\<close>.
Such lemmas typically resemble as:
  \<^item> \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Turnstile> X .oclIsNew()\<close>, or
  \<^item> \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Turnstile> X .oclIsDeleted()\<close>, or
  \<^item> \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Turnstile> X .oclIsAbsent()\<close>, or
  \<^item> \<open>(\<sigma>\<^sub>1, \<sigma>\<^sub>2) \<Turnstile> X .oclIsMaintained()\<close>

where the latter only means that the $\oid$ of \<open>X\<close> exists both in \<open>\<sigma>\<^sub>1\<close> and
\<open>\<sigma>\<^sub>2\<close>, in particular the values of the attribute fields of \<open>X\<close> have also not changed.

As completeness property, we can state the following lemma covering all disjunction case
(for any \<open>X\<close> and
\<open>\<tau>\<close>)~\cite{brucker.ea:featherweight:2014}: @{thm state_split}

Finally $\Transition$ proceeds as $\State$: it builds a new
$\holoclthykeywordstyle\operatorname{locale}$, called \<open>transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2\<close>,
 by particularly instantiating the two locales
\<open>state_\<sigma>\<^sub>1\<close> and \<open>state_\<sigma>\<^sub>2\<close>.
\<close>

text\<open> The following lemma establishes that the generated object presentations
       (like @{thm "S1_def"}, @{thm "C1_def"}, etc.) satisfy the requirements
       of the locale \<open>state_\<sigma>\<^sub>1\<close>. In particular, it has to be shown that the
       chosen object representations are defined and have distinct $\oid$s.
       Proving this lemma gives access to the already defined properties in this
       locale. \<close>
lemma \<sigma>\<^sub>1: "state_interpretation_\<sigma>\<^sub>1 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>1_def,
   standard, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text\<open> This instance proof goes analogously. \<close>

lemma \<sigma>\<^sub>2: "state_interpretation_\<sigma>\<^sub>2 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>2_def,
   standard, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text\<open> The latter proof gives access to the locale \<open>transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2\<close>. \<close>

lemma \<sigma>\<^sub>1_\<sigma>\<^sub>2: "pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2 \<tau>"
by(simp add: pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def,
   standard, simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+,
   (simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)


text\<open> For convenience, one can introduce the empty state here \<close>
definition \<sigma>\<^sub>0 :: "\<AA> state" where "\<sigma>\<^sub>0 = state.make Map.empty Map.empty"

text\<open> so that the following abbreviations can be written \<close>
definition "\<sigma>\<^sub>t\<^sub>1 = transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>t\<^sub>2 = transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid4 oid5 oid6 oid7 oid8 oid9 oid10
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>s\<^sub>1 = state_\<sigma>\<^sub>1.\<sigma>\<^sub>1 oid3 oid4 oid5 oid6 oid7 oid8 oid9
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>C2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>R21 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

definition "\<sigma>\<^sub>s\<^sub>2 = state_\<sigma>\<^sub>2.\<sigma>\<^sub>2 oid3 oid4 oid5 oid6 oid7 oid8 oid9 oid10
                  \<lceil>\<lceil>S1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>\<sigma>\<^sub>2_object2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>R11 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object4 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F1 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil> \<lceil>\<lceil>F2 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>
                  \<lceil>\<lceil>\<sigma>\<^sub>2_object7 (\<sigma>\<^sub>0, \<sigma>\<^sub>0)\<rceil>\<rceil>"

text\<open> Both formats are, fortunately, equivalent; this means that for these states, we
can access properties from both state and transition locales, in which the
object representations are ``wired'' in the same way. \<close>

lemma \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1: "\<sigma>\<^sub>t\<^sub>1 = \<sigma>\<^sub>s\<^sub>1"
unfolding \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>s\<^sub>1_def
 apply(subst transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)


lemma \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2: "\<sigma>\<^sub>t\<^sub>2 = \<sigma>\<^sub>s\<^sub>2"
unfolding \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>s\<^sub>2_def
 apply(subst transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def)
by(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def], simp)


text\<open> The next lemma becomes a shortcut of the one generated by $\Transition$,
       but explicitly instantiated. \<close>

(* TODO : this should be done at the level of states, not transitions... *)
lemma "WFF (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)"
unfolding \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1 \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2 \<sigma>\<^sub>s\<^sub>1_def \<sigma>\<^sub>s\<^sub>2_def
 apply(rule transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.basic_\<sigma>\<^sub>1_\<sigma>\<^sub>2_wff)
 apply(rule \<sigma>\<^sub>1_\<sigma>\<^sub>2[simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def])
by(simp_all add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2 pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2
      (* *)
      oid_of_\<AA>_def oid_of_ty\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def oid_of_ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      (* *)
      S1\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_def C1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def C2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def R21\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
      \<sigma>\<^sub>2_object1\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object2\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def \<sigma>\<^sub>2_object4\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def \<sigma>\<^sub>2_object7\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def)


(* TODO : the following low-level properties on the states @{term \<sigma>\<^sub>s\<^sub>1} ... should also
          be proven automatically. This is stuff from the object and state presentation that
          should be hidden away from the user. *)

lemma F1_val_seatsATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>) \<Turnstile> F1 .seats@pre \<triangleq> \<guillemotleft>120\<guillemotright>"
      proof(simp add: UML_Logic.foundation22 k_def )
         show "F1 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>) = \<lfloor>\<lfloor>120\<rfloor>\<rfloor>"
            proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
            show ?thesis
                apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def
                                F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
                apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
                apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
                by(simp add: reconst_basetype_def)
            qed
       qed

lemma F1_val_seatsATpre': "\<sigma>\<^sub>s\<^sub>1 \<Turnstile>\<^sub>p\<^sub>r\<^sub>e F1 .seats@pre \<triangleq> \<guillemotleft>120\<guillemotright>"
by(simp add: OclValid_at_pre_def F1_val_seatsATpre)

lemma F2_val_seatsATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>) \<Turnstile> F2 .seats@pre \<triangleq> \<guillemotleft>370\<guillemotright>"
      proof(simp add: UML_Logic.foundation22 k_def )
         show "F2 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>) = \<lfloor>\<lfloor>370\<rfloor>\<rfloor>"
            proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
            show ?thesis
                apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def
                                F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
                apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
                apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
                by(simp add: reconst_basetype_def)
            qed
       qed

lemma F2_val_seatsATpre': "\<sigma>\<^sub>s\<^sub>1 \<Turnstile>\<^sub>p\<^sub>r\<^sub>e F2 .seats@pre \<triangleq> \<guillemotleft>370\<guillemotright>"
by(simp add: OclValid_at_pre_def F2_val_seatsATpre)

lemma F1_val_seats: "(\<sigma>, \<sigma>\<^sub>s\<^sub>2) \<Turnstile> F1 .seats \<triangleq> \<guillemotleft>120\<guillemotright>"
proof(simp add: UML_Logic.foundation22 k_def )
   show "F1 .seats (\<sigma>, \<sigma>\<^sub>s\<^sub>2) = \<lfloor>\<lfloor>120\<rfloor>\<rfloor>"
        proof - note  S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
              show ?thesis
              apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
                              oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
              apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
              apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
              by(simp add: reconst_basetype_def)
        qed
qed

lemma F1_val_seats': "\<sigma>\<^sub>s\<^sub>2 \<Turnstile>\<^sub>p\<^sub>o\<^sub>s\<^sub>t F1 .seats \<triangleq> \<guillemotleft>120\<guillemotright>"
by(simp add: OclValid_at_post_def F1_val_seats)

lemma F2_val_seats: "(\<sigma>, \<sigma>\<^sub>s\<^sub>2) \<Turnstile> F2 .seats \<triangleq> \<guillemotleft>370\<guillemotright>"
proof(simp add: UML_Logic.foundation22 k_def )
   show   "F2 .seats (\<sigma>, \<sigma>\<^sub>s\<^sub>2) =  \<lfloor>\<lfloor>370\<rfloor>\<rfloor>"
        proof - note  S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
              show ?thesis
              apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def
                              oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
              apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
              apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
              by(simp add: reconst_basetype_def)
        qed
qed

lemma F2_val_seats': "\<sigma>\<^sub>s\<^sub>2 \<Turnstile>\<^sub>p\<^sub>o\<^sub>s\<^sub>t F2 .seats \<triangleq> \<guillemotleft>370\<guillemotright>"
by(simp add: OclValid_at_post_def F2_val_seats)

lemma C1_valid: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> (\<upsilon> C1)"
by(simp add: OclValid_def C1_def)

lemma R11_val_clientATpre: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> R11 .client@pre \<triangleq> C1"
  proof(simp add: foundation22)

  have C1_deref_val: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4 \<triangleq> C1"
    proof(simp add: foundation22)
    show "deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4 (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')"
      proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
      show ?thesis
          apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def)
          apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
          by(simp add: reconst_basetype_def C1_def)
      qed
    qed

  have C1_val: "(\<sigma>\<^sub>s\<^sub>1, \<sigma>') \<Turnstile> \<upsilon> deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4"
   apply(simp add: OclValid_def)
   apply(subst cp_valid)
   using C1_deref_val[simplified OclValid_def StrongEq_def true_def]
  by(simp, subst cp_valid[symmetric], simp add: C1_valid[simplified OclValid_def])

  show "R11 .client@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')"
  proof -  note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0, \<sigma>\<^sub>0)"]
  show ?thesis
    apply(simp add: dot\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___clientat_pre R11_def deref_oid\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def in_pre_state_def
                    R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid6_def)
    apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
    apply(simp add: deref_assocs\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___client_def deref_assocs_def oid\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_1___client_def)
    apply(subst (3) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1] map_of_list_def
          oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___flights_def oid\<^sub>S\<^sub>t\<^sub>a\<^sub>f\<^sub>f_0___flights_def oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___cl_res_def)
    apply(simp add: switch\<^sub>2_01_def switch\<^sub>2_10_def choose_0_def choose_1_def deref_assocs_list_def
                    pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2 R11_def R11\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def oid_of_ty\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n_def List.member_def)
    apply(simp add: select\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n__client_def select_object_any\<^sub>S\<^sub>e\<^sub>t_def select_object\<^sub>S\<^sub>e\<^sub>t_def)
    apply(subgoal_tac "(let s = Set{deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4} in
                        if s->size\<^sub>S\<^sub>e\<^sub>t() \<triangleq> \<zero> then null else if s->size\<^sub>S\<^sub>e\<^sub>t() \<triangleq> \<one> then s->any\<^sub>S\<^sub>e\<^sub>t() else \<bottom> endif endif) (\<sigma>\<^sub>s\<^sub>1, \<sigma>') = C1 (\<sigma>\<^sub>s\<^sub>1, \<sigma>')")
     apply(subgoal_tac "Set{deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype 4} =
             select_object Set{} UML_Set.OclIncluding id (deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t fst reconst_basetype) [4]")
      apply(simp only: Let_def)
     apply(simp add: select_object_def)
    apply(simp only: Let_def)
    apply(subst OclIf_false')
     apply(rule StrongEq_L_trans_not[OF OclSize_singleton[OF C1_val]], normalization)
    apply(subst cp_OclIf, subst OclSize_singleton[OF C1_val, simplified OclValid_def])
    using C1_deref_val[simplified OclValid_def StrongEq_def true_def]
    by(subst cp_OclIf[symmetric], simp)
  qed
qed

subsection\<open> Annotations of the Class Model in OCL \<close>

text\<open> Subsequently, we state a desired class invariant for $\mocl{Flight}$'s in the
       usual \OCL syntax: \<close>
Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .client .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"

(* TODO : the following low-level properties should also
          be proven automatically. *)

definition "Flight_A\<^sub>p\<^sub>r\<^sub>e = (\<lambda>\<sigma>. \<sigma> \<Turnstile>\<^sub>p\<^sub>r\<^sub>e Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(self|Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats@pre)))"
definition "Flight_A\<^sub>p\<^sub>o\<^sub>s\<^sub>t = (\<lambda>\<sigma>. \<sigma> \<Turnstile>\<^sub>p\<^sub>o\<^sub>s\<^sub>t Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(self|Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats)))"

(* This lemma would be highly desirable, but well ... *)
lemma Flight_A_prepost_transfer: "Flight_Aat_pre (\<sigma>, \<sigma>') = Flight_A (\<sigma>'', \<sigma>)"
oops

lemma Flight_A_prepost_transfer' : "Flight_A\<^sub>p\<^sub>o\<^sub>s\<^sub>t = Flight_A\<^sub>p\<^sub>r\<^sub>e"
unfolding Flight_A\<^sub>p\<^sub>r\<^sub>e_def Flight_A\<^sub>p\<^sub>o\<^sub>s\<^sub>t_def OclValid_at_pre_def OclValid_at_post_def
apply(rule ext, auto)
apply(erule_tac x="\<sigma>" in allE)
prefer 2
apply(erule_tac x="\<sigma>" in allE)
oops

subsection\<open> Model Analysis: A satisfiability proof of the invariants \<close>

text\<open> We wish to analyse our class model and show that the entire set of invariants can
be satisfied, \ie{} there exist legal states that satisfy all constraints imposed
by the class invariants. \<close>


lemma Flight_consistent: "\<exists> \<tau>. Flight_Aat_pre \<tau> \<and>  Flight_A \<tau>"
proof (rule_tac x="(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)" in exI, rule conjI)
       txt\<open> The following auxiliary fact establishes that @{thm OclForall_body_trivial} from the
             library is applicable since @{term "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"}
             is indeed defined. \<close>
       have  forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre() in
                            (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
             unfolding Let_def by(rule OclForall_body_trivial, rule OclAllInstances_at_pre_defined)
       show  "Flight_Aat_pre (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)"
       proof -
             have *: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F1_val_seatsATpre,
                                                                  simplified \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]],simp)
                      by(simp add: OclInt0')
             have **: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F2_val_seatsATpre,
                                                                  simplified \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]],simp)
                      by(simp add: OclInt0')

             txt\<open> Now we calculate: \<close>

             have    "((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(self|
                                         Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats@pre))) =
                      ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances@pre() \<triangleq> Set{} or
                                         Flight .allInstances@pre()->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats@pre))"
                     by(simp add: StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def],
                                                     where P = "\<lambda>x. x"])
             also
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> ((Set{F1, F2} \<triangleq> Set{}) or
                                           (Set{F1, F2}->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t  f .seats@pre))))"
                     unfolding Flight_def
                     apply(subst StrongEq_L_subst3[where x="OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"],
                           simp, simp add: \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[simplified \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>s\<^sub>1_def])
                     apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'
                                 [THEN iffD1, OF _ _ state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Flight
                                                     [OF \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def],
                                  simplified Flight_def]])
                     apply(rule OclAllInstances_at_pre_valid)
                     apply(simp add: F1_def F2_def)
                     by(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
             also
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1, F2} \<triangleq> Set{} or
                                         (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F2 .seats@pre)) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F1 .seats@pre)))"
                     apply(simp, simp add: OclValid_def, subst (1 2) cp_OclOr,
                           subst cp_OclIf, subst (1 2 3) cp_OclAnd, subst cp_OclIf)
                     by(simp add: F1_def F2_def OclIf_def)
             also
             have    "... = True"
                     by(simp,rule foundation25', simp add: foundation10' * ** )
             finally show ?thesis
                     unfolding Flight_Aat_pre_def  by simp
          qed
next
       txt\<open> Analogously for the first part, the following auxiliary fact establishes
             that @{thm OclForall_body_trivial} from the  library is applicable since
             @{term "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"}  is indeed defined. \<close>
       have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances() in
                         (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
            by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_post_defined)
       show "Flight_A (\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2)"
       proof -
             have *: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> \<zero> <\<^sub>i\<^sub>n\<^sub>t F1 .seats"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F1_val_seats,
                                                                  simplified \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[symmetric]],simp)
                      by(simp add: OclInt0')
             have**: "(\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> \<zero> <\<^sub>i\<^sub>n\<^sub>t F2 .seats"
                      apply(subst UML_Logic.StrongEq_L_subst3_rev[OF F2_val_seats,
                                                                  simplified \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[symmetric]],simp)
                      by(simp add: OclInt0')
             have    "((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(self|
                                         Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(f|\<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats))) =
                      ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Flight .allInstances() \<triangleq> Set{} or
                                         Flight .allInstances()->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t f .seats))"
                     by(simp add: StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def],
                                                    where P = "\<lambda>x. x"])
             also
             have    " ... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1,F2} \<triangleq> Set{} or
                                          Set{F1,F2}->forAll\<^sub>S\<^sub>e\<^sub>t(f| \<zero> <\<^sub>i\<^sub>n\<^sub>t  f .seats))"
                     unfolding Flight_def
                     apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"],
                           simp, simp add: \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>t\<^sub>2_\<sigma>\<^sub>s\<^sub>2[simplified \<sigma>\<^sub>t\<^sub>2_def \<sigma>\<^sub>s\<^sub>2_def])
                     apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'
                                    [THEN iffD1, OF _ _ state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_OclAllInstances_at_post_exec_Flight
                                                [OF \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def],
                                    simplified Flight_def]])
                     apply(rule OclAllInstances_at_post_valid)
                     apply(simp add: F1_def F2_def)
                     by(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
             also
             have    "... = ((\<sigma>\<^sub>t\<^sub>1, \<sigma>\<^sub>t\<^sub>2) \<Turnstile> Set{F1, F2} \<triangleq> Set{} or
                                          (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F2 .seats)) and (\<zero> <\<^sub>i\<^sub>n\<^sub>t  (F1 .seats)))"
                     apply(simp, simp add: OclValid_def, subst (1 2) cp_OclOr,
                           subst cp_OclIf, subst (1 2 3) cp_OclAnd, subst cp_OclIf)
                     by(simp add: F1_def F2_def OclIf_def)
             also
             have   "... = True"
                       by(simp,rule foundation25', simp add: foundation10' * ** )
             finally show ?thesis
                     unfolding Flight_A_def  by simp
       qed
qed

lemma Flight_consistent': "(\<exists> \<sigma>\<^sub>p\<^sub>r\<^sub>e. Flight_A\<^sub>p\<^sub>r\<^sub>e \<sigma>\<^sub>p\<^sub>r\<^sub>e) \<and> (\<exists> \<sigma>\<^sub>p\<^sub>o\<^sub>s\<^sub>t. Flight_A\<^sub>p\<^sub>o\<^sub>s\<^sub>t \<sigma>\<^sub>p\<^sub>o\<^sub>s\<^sub>t)"
oops

Context r: Reservation
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (r .id)"
  Inv B : "r .next <> null implies (r .flight .to \<doteq> r .next .flight .from)"
  Inv C : "r .next <> null implies (r .client \<doteq> r .next .client)"


Context Client :: book (f : Flight)
  Pre : "f .passengers ->excludes\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person))
         and (f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() <\<^sub>i\<^sub>n\<^sub>t (f .seats))"
  Post: "f .passengers \<doteq> (f .passengers@pre ->including\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person)))
         and (let r = self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(r | r .flight \<doteq> f)->any\<^sub>S\<^sub>e\<^sub>t() in
              (r .oclIsNew())
              and (r .prev \<doteq> null)
              and (r .next \<doteq> null))"

Context Client :: booknext (f : Flight, r : Reservation)
  Pre : "f .passengers ->excludes\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person))
         and (f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() <\<^sub>i\<^sub>n\<^sub>t (f .seats))
         and (r .client \<doteq> self)
         and (f .from \<doteq> (r .flight .to))"
  Post: "f .passengers \<doteq> (f .passengers@pre ->including\<^sub>S\<^sub>e\<^sub>t(self .oclAsType(Person)))
         and (let r = self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(r | r .flight \<doteq> f)->any\<^sub>S\<^sub>e\<^sub>t() in
              (r .oclIsNew())
              and (r .prev \<doteq> r)
              and (r .next \<doteq> null))"


Context Client :: cancel (r : Reservation)
  Pre : "r .client \<doteq> self"
  Post: "self .cl_res ->select\<^sub>S\<^sub>e\<^sub>t(res | res .flight \<doteq> r .flight@pre)
                      ->isEmpty\<^sub>S\<^sub>e\<^sub>t()"

(* example for a recursive query *)
Context Reservation :: connections () : Set(Integer)
  Post : "result \<triangleq> if (self .next \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   else (self .next .connections()->including\<^sub>S\<^sub>e\<^sub>t(self .id))
                   endif"
  Pre  : "true"

subsection\<open> Proving the Implementability of Operations \<close>
text\<open> An operation contract is said to be non-blocking, if and only if there exist input and input
       states where the pre-condition is satisfied.
       Moreover, a contract is said to be implementable, if and only if for all inputs satisfying the
       pre-condition output data exists that satisfies the post-condition.
\<close>


definition cancel\<^sub>p\<^sub>r\<^sub>e :: "(\<cdot>Client) \<Rightarrow> (\<cdot>Reservation) \<Rightarrow> \<cdot>Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e"
where     "cancel\<^sub>p\<^sub>r\<^sub>e  self r \<equiv> (r .client@pre) \<doteq> self"

definition cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t :: "(\<cdot>Client) \<Rightarrow> (\<cdot>Reservation) \<Rightarrow> (\<cdot>Void\<^sub>b\<^sub>a\<^sub>s\<^sub>e) \<Rightarrow> \<cdot>Boolean\<^sub>b\<^sub>a\<^sub>s\<^sub>e"
where     "cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t  self r result \<equiv> self .cl_res->select\<^sub>S\<^sub>e\<^sub>t(res|res .flight \<doteq> r .flight@pre)->isEmpty\<^sub>S\<^sub>e\<^sub>t()"

lemma cancel\<^sub>n\<^sub>o\<^sub>n\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>i\<^sub>n\<^sub>g : "\<exists> self r \<sigma>.  (\<sigma>, \<sigma>') \<Turnstile> (cancel\<^sub>p\<^sub>r\<^sub>e  self r)"
 apply(rule exI[where x = "C1"], rule exI[where x = "R11"], rule exI[where x = "\<sigma>\<^sub>t\<^sub>1"])
 using R11_val_clientATpre[simplified OclValid_def StrongEq_def true_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric], of \<sigma>']
 apply(simp add: cancel\<^sub>p\<^sub>r\<^sub>e_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def)
by(subst cp_valid, simp, subst cp_valid[symmetric],
   simp add: C1_valid[simplified OclValid_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]])

lemma cancel\<^sub>n\<^sub>o\<^sub>n\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k\<^sub>i\<^sub>n\<^sub>g_\<^sub>p\<^sub>r\<^sub>e : "\<exists> self r \<sigma>.  \<sigma> \<Turnstile>\<^sub>p\<^sub>r\<^sub>e (cancel\<^sub>p\<^sub>r\<^sub>e  self r)"
 apply(rule exI[where x = "C1"], rule exI[where x = "R11"], rule exI[where x = "\<sigma>\<^sub>t\<^sub>1"])
 apply(simp add: OclValid_at_pre_def, intro allI)
 proof - fix \<sigma>' show "(\<sigma>\<^sub>t\<^sub>1, \<sigma>') \<Turnstile> cancel\<^sub>p\<^sub>r\<^sub>e C1 R11"
 using R11_val_clientATpre[simplified OclValid_def StrongEq_def true_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric], of \<sigma>']
  apply(simp add: cancel\<^sub>p\<^sub>r\<^sub>e_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_\<^sub>R\<^sub>e\<^sub>s\<^sub>e\<^sub>r\<^sub>v\<^sub>a\<^sub>t\<^sub>i\<^sub>o\<^sub>n StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_at_pre_def OclValid_def)
 by(subst cp_valid, simp, subst cp_valid[symmetric],
    simp add: C1_valid[simplified OclValid_def \<sigma>\<^sub>t\<^sub>1_\<sigma>\<^sub>s\<^sub>1[symmetric]])
qed

lemma cancel\<^sub>i\<^sub>m\<^sub>p\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>a\<^sub>b\<^sub>l\<^sub>e :
 assumes pre_satisfied: "\<sigma> \<Turnstile>\<^sub>p\<^sub>r\<^sub>e (cancel\<^sub>p\<^sub>r\<^sub>e  self r)"
 shows                  "\<exists> \<sigma>' result. ((\<sigma>, \<sigma>') \<Turnstile> \<delta> self) \<longrightarrow>
                                      ((\<sigma>, \<sigma>') \<Turnstile> \<upsilon> r) \<longrightarrow>
                                      ((\<sigma>, \<sigma>') \<Turnstile> (cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t  self r result))"
proof -
  define \<sigma>'' where "\<sigma>'' \<equiv> \<lparr> heap = K \<lfloor>in\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t 0 None) None)\<rfloor>
                          , assocs = Map.empty (oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___cl_res \<mapsto> []) \<rparr>"

 have self_definition: "\<And>\<tau>. \<tau> \<Turnstile> \<delta> self \<Longrightarrow> \<exists>ta xa x. self \<tau> = \<lfloor>\<lfloor>mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ta xa) x\<rfloor>\<rfloor>"
  apply(simp add:OclValid_def defined_def true_def false_def split: if_split_asm)
  proof - fix \<tau> show "self \<tau> \<noteq> \<bottom> \<tau> \<and> self \<tau> \<noteq> null \<tau> \<Longrightarrow>
         \<exists>ta xa x. self \<tau> = \<lfloor>\<lfloor>mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ta xa) x\<rfloor>\<rfloor>"
  apply(case_tac "self \<tau>", simp add: bot_option_def bot_fun_def, simp)
  proof - fix a show "\<lfloor>a\<rfloor> \<noteq> \<bottom> \<tau> \<and> \<lfloor>a\<rfloor> \<noteq> null \<tau> \<Longrightarrow>
         self \<tau> = \<lfloor>a\<rfloor> \<Longrightarrow> \<exists>ta xa x. a = \<lfloor>mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ta xa) x\<rfloor>"
  apply(case_tac "a", simp add: null_fun_def null_option_def bot_option_def, simp)
  proof - fix aa show " \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<noteq> \<bottom> \<tau> \<and> \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<noteq> null \<tau> \<Longrightarrow>
          self \<tau> = \<lfloor>\<lfloor>aa\<rfloor>\<rfloor> \<Longrightarrow>
          a = \<lfloor>aa\<rfloor> \<Longrightarrow> \<exists>ta xa x. aa = mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t (mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ta xa) x"
  apply(case_tac aa, simp)
  proof - fix x1 x2 show " self \<tau> = \<lfloor>\<lfloor>mk\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t x1 x2\<rfloor>\<rfloor> \<Longrightarrow> \<exists>ta xa. x1 = mk\<E>\<X>\<T>\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t ta xa"
  by(case_tac x1, simp)
  qed qed qed qed

 have self_empty: "(\<sigma>, \<sigma>'') \<Turnstile> \<delta> self \<Longrightarrow> (\<sigma>, \<sigma>'') \<Turnstile> (self .cl_res \<triangleq> Set{})"
  apply(drule self_definition, elim exE)
  apply(simp add: OclValid_def StrongEq_def dot\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___cl_res)
  apply(simp add: deref_oid\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def in_post_state_def, subst (8) \<sigma>''_def)
  apply(simp add: Let_def K_def oid_of_option_def deref_assocs\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_0___cl_res_def deref_assocs_def)
  apply(subst (3) \<sigma>''_def, simp add: select\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t__cl_res_def)
  by(simp add: oid_of_ty\<^sub>C\<^sub>l\<^sub>i\<^sub>e\<^sub>n\<^sub>t_def deref_assocs_list_def switch\<^sub>2_01_def select_object\<^sub>S\<^sub>e\<^sub>t_def select_object_def)

 show "?thesis"
  apply(rule exI[where x = \<sigma>''], rule exI[where x = "null"], intro impI)
  apply(simp add: cancel\<^sub>p\<^sub>o\<^sub>s\<^sub>t_def)
  apply(subst StrongEq_L_subst3[OF _ self_empty])
    apply(rule UML_Set.cp_intro''\<^sub>S\<^sub>e\<^sub>t(2))
    apply(simp only: cp_def)
    apply(rule exI[where x = "\<lambda>X \<tau>. (\<lambda>_. X)->select\<^sub>S\<^sub>e\<^sub>t(res|StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t res .flight r .flight@pre) \<tau>"],
          subst cp_OclSelect, simp)
 by(simp+)
qed
text\<open> As remark, the pre-condition @{term "\<sigma> \<Turnstile>\<^sub>p\<^sub>r\<^sub>e (cancel\<^sub>p\<^sub>r\<^sub>e  self r)"} has not been used;
 in the special case of the
operation ``cancel'', the post-condition is satisfiable for \<^emph>\<open>arbitrary\<close> defined and valid input,
even input that does not satisfy the pre-condition. \<close>


lemmas [simp,code_unfold] = dot_accessor

end
