(******************************************************************************
 * Language.C
 * https://hackage.haskell.org/package/language-c
 *
 * Copyright (c) 1999-2017 Manuel M T Chakravarty
 *                         Duncan Coutts
 *                         Benedikt Huber
 * Portions Copyright (c) 1989,1990  James A. Roskind
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

theory C_Model
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

section \<open>Initialization of the parsing code\<close>

meta_language C
  base_path "../src/compiler_generic/isabelle_home/contrib/haskabelle"
  [Prelude \<rightharpoonup> C_Model_init, Option \<rightharpoonup> C_Model_init]
  where imports \<open>Language.C\<close>
          (load \<open>Importer.Conversion.Haskell\<close>)
          (load \<open>Importer.Conversion.Haskell.C\<close>)
  where defines \<open>\s -> do { (r, acc) <- parseC' (inputStreamFromString s) ; return (gshows r "", acc) }\<close>

ML \<open>val String = META.Stringa\<close>

section \<open>Parsing\<close>

language increment_method :: C where \<open>/* ASSUMES \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<close> */ f () {
  int x = 0;
  /* INVAR \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0 \<and> \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u &x\<close>
     VRT \<open>(measure o Rep_uexpr) (\<guillemotleft>a\<guillemotright> - &x)\<close> */
  while (x < a) {
    x = x + 1;
  }
} /* ENSURES \<open>\<guillemotleft>a\<guillemotright> =\<^sub>u &x\<close> */\<close>

language even_count_gen :: C where \<open>/* ASSUMES \<open>\<guillemotleft>a\<guillemotright> >\<^sub>u 0\<close> */ f () {
  int i = 0;
  int j = 0;
  /* INVAR \<open>&j =\<^sub>u (&i + 1) div \<guillemotleft>2\<guillemotright> \<and> &i \<le>\<^sub>u \<guillemotleft>a\<guillemotright>\<close>
     VRT \<open>measure (nat o (Rep_uexpr (\<guillemotleft>a\<guillemotright> - &i)))\<close> */
  while (i < a) {
    if (i % 2 == 0) {
      j = j + 1;
    } else skip;
    i = i + 1;
  }
} /* ENSURES \<open>&j =\<^sub>u (\<guillemotleft>a\<guillemotright> + 1)div \<guillemotleft>2\<guillemotright>\<close> */\<close>

language max_program_correct :: C where \<open>/* ASSUMES \<open>uop length \<guillemotleft>a\<guillemotright> \<ge>\<^sub>u1 \<and> &i =\<^sub>u 1 \<and> &r =\<^sub>u bop nth \<guillemotleft>a:: int list\<guillemotright> 0\<close> */ f () {
  /* INVAR \<open>0 <\<^sub>u &i \<and> &i \<le>\<^sub>u uop length \<guillemotleft>a\<guillemotright> \<and> &r =\<^sub>u uop Max (uop set (bop take (&i) \<guillemotleft>a\<guillemotright>))\<close>
     VRT \<open>measure (Rep_uexpr (uop length \<guillemotleft>a\<guillemotright> - (&i)))\<close> */
  while (! (i < length(a))) {
    if (r < nth(a, i)) {
      r = nth(a, i);
    } else skip;
    i = i + 1;
  }
} /* ENSURES \<open>&r =\<^sub>u uop Max (uop set \<guillemotleft>a\<guillemotright>)\<close> */\<close>

section \<open>Garbage Collection of Notations\<close>

hide_type (open) int
hide_type (open) string

end
