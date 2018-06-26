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

theory   Clocks_Lib_Model
imports
  "../src/UML_OCL"
begin

Class Clock
  Attributes created_at : Real
  Operations after(c : Clock) : Boolean
  Operations equal(c : Clock) : Boolean

Class WorldClock < Clock
  Operations elapse()
             Pre : "true"

Class DiscreteClock < Clock
  Operations create\<^sub>D\<^sub>i\<^sub>s\<^sub>c\<^sub>r\<^sub>e\<^sub>t\<^sub>e()
             Post: "self .oclIsNew() and
                    (self .created_at \<doteq> (WorldClock .allInstances() ->any\<^sub>S\<^sub>e\<^sub>t() .created_at))"
  Operations get_time\<^sub>D\<^sub>i\<^sub>s\<^sub>c\<^sub>r\<^sub>e\<^sub>t\<^sub>e() : Integer
             Post: "result \<doteq> (WorldClock .allInstances() ->any\<^sub>S\<^sub>e\<^sub>t() .created_at ->oclAsType\<^sub>R\<^sub>e\<^sub>a\<^sub>l(Integer))
                               -\<^sub>i\<^sub>n\<^sub>t
                               (self .created_at ->oclAsType\<^sub>R\<^sub>e\<^sub>a\<^sub>l(Integer))"

Class PeriodicDiscreteClock < DiscreteClock
  Attributes period\<^sub>D\<^sub>i\<^sub>s\<^sub>c\<^sub>r\<^sub>e\<^sub>t\<^sub>e : Integer
  Operations create_period_clock\<^sub>D\<^sub>i\<^sub>s\<^sub>c\<^sub>r\<^sub>e\<^sub>t\<^sub>e(p : Integer)
             Pre : "\<zero> \<le>\<^sub>i\<^sub>n\<^sub>t p"
             Post: "self .period\<^sub>D\<^sub>i\<^sub>s\<^sub>c\<^sub>r\<^sub>e\<^sub>t\<^sub>e \<doteq> p"

Class ContClock < Clock
  Operations create\<^sub>C\<^sub>o\<^sub>n\<^sub>t()
             Post: "self .oclIsNew() and
                    (self .created_at \<doteq> (WorldClock .allInstances() ->any\<^sub>S\<^sub>e\<^sub>t() .created_at))"
  Operations get_time\<^sub>C\<^sub>o\<^sub>n\<^sub>t() : Real
             Post: "result \<doteq> (WorldClock .allInstances() ->any\<^sub>S\<^sub>e\<^sub>t() .created_at)
                               -\<^sub>r\<^sub>e\<^sub>a\<^sub>l
                               (self .created_at)"

Class PeriodicContClock < Clock
  Attributes period\<^sub>C\<^sub>o\<^sub>n\<^sub>t : Real
  Operations create_period_clock\<^sub>C\<^sub>o\<^sub>n\<^sub>t(p : Real)
             Pre : "\<zero>.\<zero> \<le>\<^sub>r\<^sub>e\<^sub>a\<^sub>l p"
             Post: "self .period\<^sub>C\<^sub>o\<^sub>n\<^sub>t \<doteq> p"

End!



Context c: Clock
  Inv "(Clock .allInstances()) ->size\<^sub>S\<^sub>e\<^sub>t() \<doteq> \<one>"



lemmas [simp,code_unfold] = dot_accessor

end
