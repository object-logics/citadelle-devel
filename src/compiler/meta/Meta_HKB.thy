(******************************************************************************
 * Haskabelle --- Converting Haskell Source Files to Isabelle/HOL Theories.
 *                http://isabelle.in.tum.de/repos/haskabelle
 *
 * Copyright (c) 2007-2015 Technische Universität München, Germany
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

section\<open>Isabelle Meta-Model aka. AST definition of Isabelle\<close>

theory Meta_HKB
imports "../../compiler_generic/Init"
begin
 
section \<open>Isa.hs\<close>

(* Author: Tobias C. Rittweiler, TU Muenchen

Abstract representation of Isar/HOL theory.
*)

datatype ThyName = ThyName string
 
datatype Name = QName ThyName string
              | Name string
 
type_synonym Sort = "Name list"
 
datatype Type = Type Name "Type list"
              | Func Type Type
              | TVar Name
              | NoType
 
datatype Literal = Int nat (*FIXME 'int' to be supported instead of 'nat'*)
                 (*(*To be supported*)| Char char*)
                 | String string
 
datatype Term = Literal Literal
              | Const Name
              | Abs Name Term
              | App Term Term
              | If Term Term Term
              | Let "(Term * Term) list" Term
              | Case Term "(Term * Term) list"
              | ListCompr Term "ListComprFragment list"
              | RecConstr Name "(Name * Term) list"
              | RecUpdate Term "(Name * Term) list"
              | DoBlock string "DoBlockFragment list" string
              | Parenthesized Term
and      ListComprFragment = Generator "Term * Term"
                           | Guard Term
and      DoBlockFragment = DoGenerator Term Term
                         | DoQualifier Term
                         | DoLetStmt "(Term * Term) list"
 
type_synonym Pat = Term
 
datatype TypeSpec = TypeSpec "Name list" Name
 
datatype TypeSign = TypeSign Name "(Name * Sort) list" Type
 
datatype Function_Kind = Definition
                       | Primrec
                       | Fun
                       | Function_Sorry
 
datatype Function_Stmt = Function_Stmt Function_Kind "TypeSign list" "((Name * (Pat list)) * Term) list"
 
datatype Stmt = Datatype "(TypeSpec * ((Name * (Type list)) list)) list"
              | Record TypeSpec "(Name * Type) list"
              | TypeSynonym "(TypeSpec * Type) list"
              | Function Function_Stmt
              | Class Name "Name list" "TypeSign list"
              | Instance Name Name "(Name * Sort) list" "Function_Stmt list"
              | Comment string
              | SML Function_Stmt
 
datatype Module = Module ThyName "ThyName list" "Stmt list" bool

section \<open>Convert.hs\<close>

(* Author: Tobias C. Rittweiler, TU Muenchen

Conversion from abstract Haskell code to abstract Isar/HOL theory.
*)

datatype IsaUnit = IsaUnit "bool (* true: generate with 'old_datatype' instead of 'datatype' *) \<times> nat (* 0: full datatype, \<ge> 1: more atomic *)" (* FIXME add a generic meta-command 'generation_syntax_params' to parameterize at any interleaving place the generating mode (i.e. datatype or old_datatype) *)
                           "(string (* old prefix name to replace *) \<times> string option (* new substitute (or none to remove the prefix) *)) list"
                           string (* name of the current theory *) (* FIXME move that 'static value' to the global environment. In principle, each meta-command is evaluated within one "own" theory name, following the hierarchy of children theories... *)
                           "(Module list \<times> bool (* true: treat as most the list as a single module *))"

end
