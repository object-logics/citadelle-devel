(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * Toy_Library.thy --- OCL Contracts and an Example.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2013-2015 Université Paris-Sud, France
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

chapter{* Part ... *}

theory Toy_Library
imports (* As example, we are importing (arbitrary) theories which take some time to import.
           This is to situate ourself in the middle of a work, which needs at this point
           more developped meta-tactics to continue further,
           then we will continue here with the meta-compiler. *)
        (*"~~/src/HOL/Multivariate_Analysis/ex/Approximations"*)
        Main
begin

section\<open>...\<close>

type_notation option ("\<langle>_\<rangle>\<^sub>\<bottom>") (* NOTE: "_\<^sub>\<bottom>" also works *)
notation Some ("\<lfloor>(_)\<rfloor>")

fun    drop :: "'\<alpha> option \<Rightarrow> '\<alpha>" ("\<lceil>(_)\<rceil>")
where  drop_lift[simp]: "\<lceil>\<lfloor>v\<rfloor>\<rceil> = v"

section\<open>...\<close>

type_synonym oid = nat

type_synonym '\<alpha> val' = "unit \<Rightarrow> '\<alpha>"
type_notation val' ("\<cdot>(_)")

record ('\<AA>)state =
             heap   :: "oid \<rightharpoonup> '\<AA> "
             assocs :: "oid \<rightharpoonup> ((oid list) list) list"

lemmas [simp,code_unfold] = state.defs

end