(******************************************************************************
 * HOL-OCL
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
  Flight_Model_compact
imports
  "../../src/UML_OCL"
  (* separate compilation : UML_OCL *)
begin

subsection\<open> Class Model \<close>

text\<open>This part corresponds to the writing in Isabelle of the
code shown in \autoref{fig:code-data}.\<close>

Class Flight
  Attributes
    seats : Integer
    "from" : String
    to : String
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

locale TRANSITION_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin
lemma \<sigma>\<^sub>1: "state_interpretation_\<sigma>\<^sub>1 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>1_def,
   standard,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text\<open> This instance proof goes analogously. \<close>

lemma \<sigma>\<^sub>2: "state_interpretation_\<sigma>\<^sub>2 \<tau>"
by(simp add: state_interpretation_\<sigma>\<^sub>2_def,
   standard,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
   (simp add: pp_object_\<sigma>\<^sub>1_\<sigma>\<^sub>2)+)

text\<open> The latter proof gives access to the locale \<open>transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2\<close>. \<close>

lemma \<sigma>\<^sub>1_\<sigma>\<^sub>2: "pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2 \<tau>"
by(simp add: pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def,
   standard,
   simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2,
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

end


section{* Annotations of the Class Model in OCL *}

text{* Subsequently, we state a desired class invariant for \verb$Flight$'s in the usual
OCL syntax: *}
Context f: Flight
  Inv A : "\<zero> <\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv B : "f .fl_res ->size\<^sub>S\<^sub>e\<^sub>q() \<le>\<^sub>i\<^sub>n\<^sub>t (f .seats)"
  Inv C : "f .passengers ->select\<^sub>S\<^sub>e\<^sub>t(p | p .oclIsTypeOf(Client))
                          \<doteq> ((f .fl_res)->collect\<^sub>S\<^sub>e\<^sub>q(c | c .client .oclAsType(Person))->asSet\<^sub>S\<^sub>e\<^sub>q())"



section{* Model Analysis I: A satisfiability proof of the invariants. *}

text{* We wish to analyse our class model and show that the entire set of invariants can
be satisfied, \ie{} there exists legal states that satisfy all constraints imposed
by the class invariants. *}

context transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin

lemma Flight_at_pre_sat: "let \<tau> = (\<sigma>\<^sub>1,\<sigma>\<^sub>2) in
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))) \<longrightarrow>
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))) \<longrightarrow>
                           Flight_Aat_pre \<tau>"
proof -
 have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre() in
                       (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
 by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_pre_defined)
 show ?thesis
  apply(simp add: Let_def, intro impI)
  apply(simp add: Flight_Aat_pre_def StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], where P = "\<lambda>x. x"])
  apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances@pre()"], simp, simp add: \<sigma>\<^sub>1_def)
   apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'[THEN iffD1, OF _ _ state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_OclAllInstances_at_pre_exec_Flight[OF \<sigma>\<^sub>1, simplified Flight_def]])
            apply(rule OclAllInstances_at_pre_valid)
           apply(simp add: F1_def F2_def)
  apply(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
  apply(simp add: OclValid_def, subst cp_OclOr, subst cp_OclIf, subst (1 2) cp_OclAnd, subst cp_OclIf)
 by(simp add: F1_def F2_def OclIf_def, fold true_def, simp add: OclOr_true2)
qed

lemma Flight_at_pre_sat': "\<exists> \<tau>.
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats@pre))) \<longrightarrow>
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats@pre))) \<longrightarrow>
                        Flight_Aat_pre \<tau>"
by(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], rule Flight_at_pre_sat[simplified Let_def])

lemma Flight_at_post_sat: "let \<tau> = (\<sigma>\<^sub>1,\<sigma>\<^sub>2) in
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats))) \<longrightarrow>
                           (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats))) \<longrightarrow>
                           Flight_A \<tau>"
proof -
 have forall_trivial: "\<And>\<tau> P. let S = OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances() in
                       (\<tau> \<Turnstile> (S->forAll\<^sub>S\<^sub>e\<^sub>t(X|P) \<triangleq> (S \<triangleq> Set{} or P)))"
 by(simp add: Let_def, rule OclForall_body_trivial, rule OclAllInstances_at_post_defined)
 show ?thesis
  apply(simp add: Let_def, intro impI)
  apply(simp add: Flight_A_def StrongEq_L_subst3[OF _ forall_trivial[simplified Let_def], where P = "\<lambda>x. x"])
  apply(subst StrongEq_L_subst3[where x = "OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA> .allInstances()"], simp, simp add: \<sigma>\<^sub>2_def)
   apply(rule StrictRefEq\<^sub>S\<^sub>e\<^sub>t.StrictRefEq_vs_StrongEq'[THEN iffD1, OF _ _ state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_OclAllInstances_at_post_exec_Flight[OF \<sigma>\<^sub>2, simplified Flight_def]])
            apply(rule OclAllInstances_at_post_valid)
           apply(simp add: F1_def F2_def)
  apply(simp add: OclAsType\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_\<AA>_def)+
  apply(simp add: OclValid_def, subst cp_OclOr, subst cp_OclIf, subst (1 2) cp_OclAnd, subst cp_OclIf)
 by(simp add: F1_def F2_def OclIf_def, fold true_def, simp add: OclOr_true2)
qed

lemma Flight_at_post_sat': "\<exists> \<tau>.
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F1 .seats))) \<longrightarrow>
                        (\<tau> \<Turnstile> (\<zero> <\<^sub>i\<^sub>n\<^sub>t (F2 .seats))) \<longrightarrow>
                        Flight_A \<tau>"
by(rule exI[where x = "(\<sigma>\<^sub>1,\<sigma>\<^sub>2)"], rule Flight_at_post_sat[simplified Let_def])

end

context TRANSITION_\<sigma>\<^sub>1_\<sigma>\<^sub>2
begin
lemma Flight_at_pre_sat: "\<exists> \<tau>. Flight_Aat_pre \<tau>"
proof -
 note S1 = \<sigma>\<^sub>1[simplified state_interpretation_\<sigma>\<^sub>1_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
 note PP = \<sigma>\<^sub>1_\<sigma>\<^sub>2[of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)", simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def]

 have F1_val: "F1 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2) = (\<lambda>_. \<lfloor>\<lfloor>120\<rfloor>\<rfloor>) (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 have F2_val: "F2 .seats@pre (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2) = (\<lambda>_. \<lfloor>\<lfloor>370\<rfloor>\<rfloor>) (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seatsat_pre F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_pre_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid9_def)
  apply(subst (8) \<sigma>\<^sub>s\<^sub>1_def, simp add: state_\<sigma>\<^sub>1.\<sigma>\<^sub>1_def[OF S1], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 show ?thesis
  apply(rule exI[where x = "(\<sigma>\<^sub>t\<^sub>1,\<sigma>\<^sub>t\<^sub>2)"], simp add: \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>t\<^sub>2_def)
  apply(rule transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_pre_sat[OF PP, simplified Let_def, THEN mp, THEN mp])
   apply(simp add: transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold \<sigma>\<^sub>s\<^sub>1_def, fold \<sigma>\<^sub>s\<^sub>2_def)
   apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F1_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)

  apply(simp add: transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold \<sigma>\<^sub>s\<^sub>1_def, fold \<sigma>\<^sub>s\<^sub>2_def)
  apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F2_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)
 done
qed

lemma Flight_at_post_sat: "\<exists> \<tau>. Flight_A \<tau>"
proof -
 note S2 = \<sigma>\<^sub>2[simplified state_interpretation_\<sigma>\<^sub>2_def, of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)"]
 note PP = \<sigma>\<^sub>1_\<sigma>\<^sub>2[of "(\<sigma>\<^sub>0,\<sigma>\<^sub>0)", simplified pp_\<sigma>\<^sub>1_\<sigma>\<^sub>2_def]

 have F1_val: "F1 .seats (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2) = (\<lambda>_. \<lfloor>\<lfloor>120\<rfloor>\<rfloor>) (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F1_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F1_def F1\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 have F2_val: "F2 .seats (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2) = (\<lambda>_. \<lfloor>\<lfloor>370\<rfloor>\<rfloor>) (\<sigma>\<^sub>s\<^sub>1, \<sigma>\<^sub>s\<^sub>2)"
  apply(simp add: dot\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats F2_def deref_oid\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def in_post_state_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid_of_ty\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def oid8_def)
  apply(subst (8) \<sigma>\<^sub>s\<^sub>2_def, simp add: state_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF S2], simp add: pp_oid_\<sigma>\<^sub>1_\<sigma>\<^sub>2)
  apply(simp add: select\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t__seats_def F2_def F2\<^sub>F\<^sub>l\<^sub>i\<^sub>g\<^sub>h\<^sub>t_def)
 by(simp add: reconst_basetype_def)

 show ?thesis
  apply(rule exI[where x = "(\<sigma>\<^sub>t\<^sub>1,\<sigma>\<^sub>t\<^sub>2)"], simp add: \<sigma>\<^sub>t\<^sub>1_def \<sigma>\<^sub>t\<^sub>2_def)
  apply(rule transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_post_sat[OF PP, simplified Let_def, THEN mp, THEN mp])
   apply(simp add: transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold \<sigma>\<^sub>s\<^sub>1_def, fold \<sigma>\<^sub>s\<^sub>2_def)
   apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F1_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)

  apply(simp add: transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>1_def[OF PP] transition_\<sigma>\<^sub>1_\<sigma>\<^sub>2.\<sigma>\<^sub>2_def[OF PP], fold \<sigma>\<^sub>s\<^sub>1_def, fold \<sigma>\<^sub>s\<^sub>2_def)
  apply(simp add: OclValid_def)
  apply(subst OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r.cp0, simp add: F2_val OclInt0_def OclLess\<^sub>I\<^sub>n\<^sub>t\<^sub>e\<^sub>g\<^sub>e\<^sub>r_def)
 done
qed
end

thm TRANSITION_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_pre_sat[simplified Flight_Aat_pre_def]
thm TRANSITION_\<sigma>\<^sub>1_\<sigma>\<^sub>2.Flight_at_post_sat[simplified Flight_A_def]

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

find_theorems (350) name:"Client"
lemmas [simp,code_unfold] = dot_accessor

end
