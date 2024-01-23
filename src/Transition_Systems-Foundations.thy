(*
  Copyright 2021–2024 Input Output Global Inc.

  Licensed under the Apache License, Version 2.0 (the “License”); you may not use this file except
  in compliance with the License. You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software distributed under the License
  is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
  or implied. See the License for the specific language governing permissions and limitations under
  the License.
*)

section \<open>Foundations\<close>

theory "Transition_Systems-Foundations"
  imports
    Main
begin

subsection \<open>Repeated Composition\<close>

text \<open>
  This applies in particular to functions and relations.
\<close>

notation compower (\<open>(_\<^bsup>_\<^esup>)\<close> [1000, 0] 1000)

subsection \<open>Relations\<close>

type_synonym 'p relation = "'p \<Rightarrow> 'p \<Rightarrow> bool"

definition
  chain :: "
    ('p relation \<Rightarrow> 'p relation) \<Rightarrow>
    ('p relation \<Rightarrow> 'p relation) \<Rightarrow>
    ('p relation \<Rightarrow> 'p relation)"
  (infixr \<open>\<frown>\<close> 75)
where
  [simp]: "\<F> \<frown> \<G> = (\<lambda>K. \<F> K OO \<G> K)"

definition
  dual :: "('p relation \<Rightarrow> 'p relation) \<Rightarrow> ('p relation \<Rightarrow> 'p relation)"
  ("_\<^sup>\<dagger>" [1000] 1000)
where
  [simp]: "\<F>\<^sup>\<dagger> = (\<lambda>K. (\<F> K\<inverse>\<inverse>)\<inverse>\<inverse>)"

end
