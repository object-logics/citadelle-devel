(******************************************************************************
 * Language.C
 * https://hackage.haskell.org/package/language-c
 *
 * Copyright (c) 1999-2017 Manuel M T Chakravarty
 *                         Duncan Coutts
 *                         Benedikt Huber
 * Portions Copyright (c) 1989,1990 James A. Roskind
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Language.C.Comments
 * https://hackage.haskell.org/package/language-c-comments
 *
 * Copyright (c) 2010-2014 Geoff Hulette
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
 *
 * Securify & Orca
 *
 * Copyright (c) 2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *  *
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

section \<open>Acknowledgements\<close>

theory C_Model_core
  imports "$HASKABELLE_HOME_USER/default/Prelude"
          "../src/UML_Main"
          "../src/compiler/Generator_dynamic_parallel"
          C_Model_init
begin

subsection \<open>\<^file>\<open>$HASKABELLE_HOME/ex/language-c/AUTHORS.c2hs\<close>\<close>
text \<open>
  Manuel M T Chakravarty	<chak@cse.unsw.edu.au>
  Duncan Coutts		<duncan@haskell.org>
  
  with contributions from (alphabetical order)
  
  Bertram Felgenhauer	<int-e@gmx.de>
  Ian Lynagh		<igloo@earth.li>
  André Pang		<ozone@algorithm.com.au>
  Jens-Ulrik Petersen	<petersen@haskell.org>
  Armin Sander		<armin@mindwalker.org>
  Sean Seefried		<sseefried@cse.unsw.edu.au>
  Udo Stenzel		<u.stenzel@web.de>
  Axel Simon              <A.Simon@ukc.ac.uk>
  Michael Weber		<michaelw@debian.org>
  
  Thanks for comments and suggestions to 
  
  Roman Leshchinskiy	<rl@cs.tu-berlin.de>
  Jan Kort		<kort@science.uva.nl>
  Seth Kurtzberg		<seth@cql.com>
  Simon Marlow		<simonmar@microsoft.com>
  Matthias Neubauer	<neubauer@informatik.uni-freiburg.de>
  Sven Panne		<sven.panne@aedion.de>
  Simon L. Peyton Jones	<simonpj@microsoft.com>
  Volker Wysk		<post@volker-wysk.de>
\<close>

subsection \<open>\<^file>\<open>$HASKABELLE_HOME/ex/language-c/AUTHORS\<close>\<close>
text \<open>
  Benedikt Huber          <benedikt.huber@gmail.com>
  Manuel M T Chakravarty  <chak@cse.unsw.edu.au>
  Duncan Coutts           <duncan@haskell.org>
  Bertram Felgenhauer     <int-e@gmx.de>
  
  with code contributions and patches from
  
  Iavor Diatchki          <iavor.diatchki@gmail.com>
  Kevin Charter           <kcharter@gmail.com>
  Aleksey Kliger
  
  This project originated from the C parser component of c2hs,
  for many additional contributors see AUTHORS.c2hs.
  
  Special thanks for their great support, comments and suggestions to:
  
  Duncan Coutts           <duncan@haskell.org>
  Iavor Diatchki          <iavor.diatchki@gmail.com>
  Don Steward             <dons@galois.com>
\<close>

section \<open>Initialization of the generator\<close>

declare [[syntax_ambiguity_warning = false]]

generation_syntax [ deep
                      (THEORY Meta_C_generated)
                      (IMPORTS ["../src/UML_Main", "../src/compiler/Static", "../examples/C_Model_init"]
                               "../src/compiler/Generator_dynamic_parallel")
                      SECTION
                      SORRY
                      [ in self ]
                      (output_directory "../doc")
                  , shallow SORRY ]

section \<open>Type definition\<close>

End!

text \<open> \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Name.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Position.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Node.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Data/Ident.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Ops.hs\<close>
       \<^file>\<open>$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/Constants.hs\<close> \<close>

Haskell_file datatype_old_atomic try_import only_types concat_modules
             base_path "$HASKABELLE_HOME/ex/language-c/src"
             [Prelude \<rightharpoonup> C_Model_init, Int, String, Option \<rightharpoonup> C_Model_init]
             (**)
             "$HASKABELLE_HOME/ex/language-c/src/Language/C/Syntax/AST.hs"

text \<open>@{typ CTranslUnit}\<close>

datatype CommentFormat = SingleLine | MultiLine
datatype Comment = Comment Position string CommentFormat

section \<open>Garbage Collection of Notations\<close>

hide_type (open) int
hide_type (open) string

end
