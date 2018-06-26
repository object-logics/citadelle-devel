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

chapter{* Part ... *}

theory
  Analysis_shallow
imports
  "../../src/UML_Main"
  "../../src/compiler/Static"
  "../../src/compiler/Generator_dynamic_sequential"
begin

generation_syntax [ shallow (generation_semantics [ analysis ])
                            (*SORRY*) (*no_dirty*)
                  (*, syntax_print*) ]

Class Person < Planet
  Attributes salary : Integer (*\<acute>int\<acute>*)
End

Association boss
  Between Person [*]
          Person [0 \<bullet>\<bullet> 1] Role boss
End

Class Planet < Galaxy
  Attributes wormhole : UnlimitedNatural
             weight : Integer
End

Class Galaxy
  Attributes sound : Void
             moving : Boolean
             outer_world : Set(Sequence(Planet))
End

Instance X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 :: Person = [ salary = 1300 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 :: Person = [ salary = 1800 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3 :: Person = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 :: Person = [ salary = 2900 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5 :: Person = [ salary = 3500 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 :: Person = [ salary = 2500 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ]
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7           = ([ salary = 3200 , boss = X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7 ] :: Person) \<rightarrow>oclAsType( OclAny )
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8 :: OclAny = []
     and X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 :: Person = [ salary = 0 ]
     and X0 :: Person = [ outer_world = [ [ P1 ] ] ]
     and P1 :: Planet = [ outer_world = [ [ P1 ] , [ self 10 ] ] ]

State \<sigma>\<^sub>1 =
  [ ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1 with_only salary = 1000 , boss = self 1 ] :: Person)
  , ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2 with_only salary = 1200 ] :: Person)
  (* *)
  , ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4 with_only salary = 2600 , boss = self 3 ] :: Person)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n5
  , ([ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6 with_only salary = 2300 , boss = self 2 ] :: Person)
  (* *)
  (* *)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ]

State \<sigma>\<^sub>1' =
  [ X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n1
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n2
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n3
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n4
  (* *)
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n6
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n7
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n8
  , X\<^sub>P\<^sub>e\<^sub>r\<^sub>s\<^sub>o\<^sub>n9 ]

(*State \<sigma>\<^sub>0 = []*)

Transition \<sigma>\<^sub>1 \<sigma>\<^sub>1'

Context Person :: contents () : Set(Integer)
  Post : "result \<triangleq> if (self .boss \<doteq> null)
                   then (Set{}->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   else (self .boss .contents()->including\<^sub>S\<^sub>e\<^sub>t(self .salary))
                   endif"
  Post : "true"
  Pre  : "false"

Context Person
  Inv a: "self .boss <> null implies (self .salary  \<triangleq>  ((self .boss) .salary))"

Context Planet
  Inv A : "true and (self .weight \<le>\<^sub>i\<^sub>n\<^sub>t \<zero>)"

(*BaseType [ 1000, 1200, 1300, 1800, 2600, 2900, 3200, 3500
            , 3.14159265
            , "abc", "\<AA>\<BB>\<CC>\<DD>\<EE>\<FF>" ]*)

lemmas [simp,code_unfold] = dot_accessor

end
