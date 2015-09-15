(*****************************************************************************
 * A Meta-Model for the Isabelle API
 *
 * Copyright (c) 2013-2015 Université Paris-Saclay, Univ Paris Sud, France
 *               2013-2015 IRT SystemX, France
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
(* $Id:$ *)

section{* Example: A Class Model Converted into a Theory File *}
subsection{* Introduction *}

theory
  Design_deep
imports
  "../embedding/Generator_dynamic"
begin
ML_file "~~/src/Doc/antiquote_setup.ML"

text{*
In this example, we configure our package to generate \verb|.thy| files,
without executing the associated generated code
(c.f. @{file "Design_shallow.thy"} for a direct evaluation).
This mode is particularly relevant for debugging purposes:
while by default no evaluation occurs, 
the generated files (and their proofs!) can be executed on
a step by step basis, depending on how we interact with the output window
(by selectively clicking on what is generated).

After clicking on the generated content, the newly inserted content could depend on some theories
which are not loaded by this current one.
In this case, it is necessary to manually add all the needed dependencies above after the 
keyword @{keyword "imports"}.
One should compare this current theory with @{file "Design_shallow.thy"}
to see the differences of imported theories, and which ones to manually import
(whenever an error happens).
*}

generation_syntax [ deep
                      (generation_semantics [ design (*, oid_start 10*) ])
                      (THEORY Design_generated)
                      (IMPORTS ["../Toy_Library", "../Toy_Library_Static"]
                               "../embedding/Generator_dynamic")
                      SECTION
                      (*SORRY*) (*no_dirty*)
                      [ (* in Haskell *)
                        (* in OCaml module_name M *)
                        (* in Scala module_name M *)
                        in SML module_name M ]
                      (output_directory "../document_generated")
                  (*, syntax_print*) ]
text{* 
While in theory it is possible to set the @{keyword "deep"} mode
for generating in all target languages, i.e. by writing 
@{text "[ in Haskell, in OCaml module_name M, in Scala module_name M, in SML module_name M ]"},
usually using only one target is enough,
since the task of all target is to generate the same Isabelle content.
However in case one language takes too much time to setup,
we recommend to try the generation with another target language,
because all optimizations are currently not (yet) seemingly implemented for all target languages,
or differently activated. *}

subsection{* Designing Class Models (I): Basics *}

text{*
The following example shows the definitions of a set of classes, 
called the ``universe'' of classes.
Instead of providing a single command for building all the complete universe of classes
directly in one block, 
we are constructing classes one by one.
So globally the universe describing all classes is partial, it
will only be fully constructed when all classes will be finished to be defined.

This allows to define classes without having to follow a particular order of definitions.
Here @{text Atom} is defined before the one of @{text Molecule}
(@{text Molecule} will come after):
*}

Class Atom < Molecule
  Attributes size : Integer
End

text{* The ``blue'' color of @{command End} indicates that
@{command End} is not a ``green'' keyword. 
@{command End} and @{command Class} are in fact similar, they belong to the group of meta-commands
(all meta-commands are defined in @{theory Generator_dynamic}).
At run-time and in @{keyword "deep"} mode, the semantics of all meta-commands are 
approximately similar: all meta-commands displays some quantity of Isabelle code
in the output window (as long as they are syntactically correct).
However each meta-command is unique because what is displayed
in the output window depends on the sequence of all meta-commands already encountered before
(and also depends on arguments given to the meta-commands). *}

text{* 
One particularity of @{command End} is to behave as the identity function when 
@{command End} is called without arguments.
As example, here we are calling lots of @{command End} without arguments,
and no Isabelle code is generated. *}
       End End End 
text{*
We remark that, like any meta-commands, @{command End} could have been written anywhere
in this theory, for example before @{command Class} or before @{command generation_syntax}...
Something does not have to be specially opened before using an @{command End}.
*}

Class Molecule < Person
text{* As example, here no @{command End} is written. *}

text{*
The semantics of @{command End} is further precised here. 
We earlier mentioned that the universe of classes is partially constructed, but one can still
examine what is partially constructed, and one possibility is to use @{command End} for doing so.

@{command End} can be seen as a lazy meta-command: 
\begin{itemize}
\item without parameters, no code is generated,
\item with some parameters (e.g., the symbol \verb|!|), it forces the generation of the computation
of the universe, by considering all already encountered classes. 
Then a partial representation of the universe can be interactively inspected.
\end{itemize}
*}

Class Galaxy
  Attributes wormhole : UnlimitedNatural
             is_sound : Void
End!

text{* At this position, in the output window, 
we can observe for the first time some generated Isabelle code,
corresponding to the partial universe of classes being constructed.

Note: By default, @{text "Atom"} and @{text "Molecule"} are not (yet) present in the shown universe
because @{text "Person"} has not been defined in a separate line (unlike @{text "Galaxy"} above). *}

Class Person < Galaxy
  Attributes salary : Integer
             boss : Person
             is_meta_thinking: Boolean

text{* 
There is not only @{command End} which forces the computation of the universe, for example
@{command Instance} declares a set of objects belonging to the classes earlier defined, 
but the entire universe is needed as knowledge, so there is no choice than forcing
the generation of the universe.
*}

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 ]

text{*
Here we will call @{command Instance} again to show that the universe will not be computed again
since it was already computed in the previous @{command Instance}.
*}

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = [ salary = 1 ]

text{* However at any time, the universe can (or will) automatically be recomputed,
whenever we are adding meanwhile another class:
\begin{verbatim}
(* Class Big_Bang < Atom (* This will force the creation of a new universe. *) *)
\end{verbatim}

As remark, not only the universe is recomputed, but 
the recomputation takes also into account all meta-commands already encountered. 
So in the new setting, @{text "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1"}, @{text "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2"} and @{text "X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3"} 
will be resurrected... after the @{text Big_Bang}.
*}

subsection{* Designing Class Models (II): Jumping to Another Semantic Floor *}

text{*
Until now, meta-commands was used to generate lines of code, and
these lines belong to the Isabelle language.
One particularity of meta-commands is to generate pieces of code containing not only Isabelle code
but also arbitrary meta-commands. 
In @{keyword "deep"} mode, this is particularly not a danger 
for meta-commands to generate themselves.

In this case, such meta-commands must automatically generate the appropriate call to
@{command generation_syntax} beforehand. 
However this is not enough, the compiling environment (comprising the
history of meta-commands) are changing throughout the interactive evaluations,
so the environment must also be taken into account and propagated when meta-commands
are generating themselves.
For example, the environment is needed for consultation whenever resurrecting objects,
recomputing the universe or accessing the hierarchy of classes being
defined.

As a consequence, in the next example we add after @{command generation_syntax}
a line @{command setup} which bootstraps the state of the compiling environment.
*}

State \<sigma>\<^sub>1 =
  [ ([ salary = 1000 , boss = self 1 ] :: Person)
  , ([ salary = 1200 ] :: Person)
  (* *)
  , ([ salary = 2600 , boss = self 3 ] :: Person)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
  , ([ salary = 2300 , boss = self 2 ] :: Person)
  (* *)
  (* *)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]

State \<sigma>\<^sub>1' =
  [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 ]

PrePost \<sigma>\<^sub>1 \<sigma>\<^sub>1'

text{*
The generation of meta-commands allows to perform various extensions
on the Toy language being embedded, without altering the semantics of a particular command.
The semantics of @{command PrePost} was hence extended to mimic the support of @{text "\<zeta>-reduction"}
in its arguments:
\begin{verbatim}
(* PrePost \<sigma>\<^sub>1 [ ([ salary = 1000 , boss = self 1 ] :: Person) ] *)
\end{verbatim}
This will rewrite to a preliminary call to @{command State}
(and the name @{text "WFF_10_post"} was automatically generated):
\begin{verbatim}
(* State WFF_10_post = [ ([ "salary" = 1000, "boss" = self 1 ] :: Person) ]
   PrePost[shallow] \<sigma>\<^sub>1 WFF_10_post *)
\end{verbatim}
then the rewriting of the above @{command State} terminates 
with a final call to @{command Instance}.
*}

subsection{* Designing Class Models (III): Interaction with (Pure) Term *}

text{*
Meta-commands are obviously not restricted to manipulate expressions in the Outer Syntax level.
It is possible to build meta-commands so that Inner Syntax expressions are directly parsed.
However the dependencies of this theory have been minimized so that experimentations
and debugging can easily occur in @{keyword "deep"} mode. 
Since the Inner Syntax expressions would not be well-typed (due to missing dependencies), 
it can be desirable to consider the Inner Syntax container as a string and leave the parsing 
for subsequent semantic floors.

This is what is implemented here:
*}

Context Person :: content ()
  Post "\<close>\<open>"

text{*
Here the expression @{text "\<close>\<open>"} is not well-typed in Isabelle, but an error is not raised
because the above expression is not (yet) parsed as an Inner Syntax element.

However, this is not the same for the resulting generated meta-command:
\begin{verbatim}
(* Context [shallow] Person :: content () 
   Post : "(\<lambda> result self. (\<close>\<open>))" 
*)
\end{verbatim}
and an error is immediately raised because the parsing of Inner Syntax expressions
is activated in this case.
*}

text{* For example, one can put the mouse, with the CTRL gesture,
over the variable @{term "a"}, @{term "b"} or @{term "c"}
to be convinced that they are free variables compared with above: *}

Context[shallow] Person :: content () 
  Post : "a + b = c"

subsection{* Designing Class Models (IV): Conclusion: Saving the Generated to File *}

text{*
The experimentations usually finish by saving all the universe 
and generated Isabelle theory to the hard disk:
\begin{verbatim}
(* generation_syntax deep flush_all *)
\end{verbatim}
*}

end
