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
  Bank_Model
imports
  "../src/UML_OCL"
begin

Class Bank
  Attributes name : String

Class Client
  Attributes clientname : String
             address : String
             age : Integer

term id

Class Account
  Attributes id : Integer
             balance : Currency

Association clients
  Between Bank [1 \<bullet>\<bullet> *] Role banks
          Client [1 \<bullet>\<bullet> *] Role clients

Association owner
  Between Account [1 \<bullet>\<bullet> *] Role c_accounts
          Client [1] Role owner

Association bank
  Between Account [1 \<bullet>\<bullet> *] Role b_accounts
          Bank [1] Role bank

term max

Class Savings < Account
  Attributes max : Currency

Class Current < Account
  Attributes overdraft : Currency

Class Currency = Real

Instance Saving1 = ([ max = 2000 ] :: Savings) \<rightarrow> oclAsType( Account )
     and Client1 :: Client = [ c_accounts = Saving1 , banks = Bank1 ]
     and Account1 :: Account = [ id = 250 , owner = Client1 ]
     and Bank1 :: Bank = [ b_accounts = [ Saving1 , Account1 ], name = "\<infinity>\<heartsuit> \<Longleftrightarrow> \<infinity>\<epsilon>" (* (* TODO latex *) \<euro> *) ]

State \<sigma>\<^sub>1' =
  [ Account1, Client1, Bank1, Saving1 ]

State ss = []

Transition ss \<sigma>\<^sub>1'

BaseType [ 25, 250.0 ]

Context c: Savings
  Inv "\<zero>.\<zero> <\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max)"
  Inv "c .balance \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .max) and \<zero>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l (c .balance)"

Context c: Current
  Inv "\<two>\<five> \<le>\<^sub>i\<^sub>n\<^sub>t (c .owner .age) implies (c .overdraft \<doteq> \<two>\<five>\<zero>.\<zero>)"
  Inv "c .owner .age <\<^sub>i\<^sub>n\<^sub>t \<two>\<five>   implies (c .overdraft \<doteq> \<zero>.\<zero>)"

Context c: Client
  Inv "c .banks ->forAll\<^sub>S\<^sub>e\<^sub>t(b | b .b_accounts ->select\<^sub>S\<^sub>e\<^sub>t(a | (a .owner \<doteq> c) and
                                                                  (a .oclIsTypeOf(Current)))
                                             ->size\<^sub>S\<^sub>e\<^sub>t() \<le>\<^sub>i\<^sub>n\<^sub>t \<one>)"

Context Bank :: create_client (clientname : String, age : Integer, bank : Bank) : Integer
  Pre  "bank .clients ->forAll\<^sub>S\<^sub>e\<^sub>t(c | c .clientname <> clientname or (c .age <> age))"
  Post "bank .clients ->exists\<^sub>S\<^sub>e\<^sub>t(c | c .clientname \<doteq> clientname and (c .age \<doteq> age))"


Context Account :: get_balance (c : String, no : Integer) : Real
  Pre  "self .id \<doteq> no and ((self .owner .clientname) \<doteq> c)"
  Post "result \<doteq> (self .balance)"

Context Account :: deposit (c : String, no : Integer, amount:Real) : Real
  Pre  "self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)"
  Post "self .balance \<doteq> (self .balance@pre +\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)"

Context Account :: withdraw (c : String, no : Integer, amount:Real) : Real
  Pre  "self .id \<doteq> no and ((self .owner .clientname) \<doteq> c) and (\<zero>.\<zero>  \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)"
  Post "self .balance \<doteq> (self .balance@pre -\<^sub>r\<^sub>e\<^sub>a\<^sub>l amount)"


(*generation_syntax deep flush_all*)

lemmas [simp,code_unfold] = dot_accessor

end
