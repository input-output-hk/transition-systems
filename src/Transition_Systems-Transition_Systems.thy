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

section \<open>Transition Systems\<close>

theory "Transition_Systems-Transition_Systems"
  imports
    "Transition_Systems-Simulation_Systems"
begin

locale transition_system =
  simulation_system \<open>transition\<close> \<open>transition\<close>
  for transition :: "'a \<Rightarrow> 'p relation" (\<open>'(\<rightarrow>\<lparr>_\<rparr>')\<close>)
begin

abbreviation transition_std :: "'p \<Rightarrow> 'a \<Rightarrow> 'p \<Rightarrow> bool" (\<open>(_ \<rightarrow>\<lparr>_\<rparr>/ _)\<close> [51, 0, 51] 50) where
  "p \<rightarrow>\<lparr>\<alpha>\<rparr> q \<equiv> (\<rightarrow>\<lparr>\<alpha>\<rparr>) p q"

subsection \<open>Simulations and Bisimulations\<close>

notation unilateral_progression (infix \<open>\<hookrightarrow>\<close> 50)

notation bilateral_progression (infix \<open>\<mapsto>\<close> 50)

notation simulation (\<open>sim\<close>)

notation bisimulation (\<open>bisim\<close>)

lemma equality_is_simulation:
  shows "sim (=)"
  by (simp add: eq_OO OO_eq)

lemma relation_composition_is_simulation:
  assumes "sim K" and "sim L"
  shows "sim (K OO L)"
proof -
  have "(K OO L)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) \<le> (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (K OO L)\<inverse>\<inverse>" for \<alpha>
  proof -
    have "(K OO L)\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) = L\<inverse>\<inverse> OO K\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>)"
      by blast
    also from \<open>sim K\<close> have "\<dots> \<le> L\<inverse>\<inverse> OO (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO K\<inverse>\<inverse>"
      by (simp add: relcompp_mono)
    also from \<open>sim L\<close> have "\<dots> \<le> (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO L\<inverse>\<inverse> OO K\<inverse>\<inverse>"
      by fastforce
    also have "\<dots> = (\<rightarrow>\<lparr>\<alpha>\<rparr>) OO (K OO L)\<inverse>\<inverse>"
      by blast
    finally show ?thesis .
  qed
  then show ?thesis
    by simp
qed

lemma equality_is_bisimulation:
  shows "bisim (=)"
  using equality_is_simulation
  by simp

lemma relation_composition_is_bisimulation:
  assumes "bisim K" and "bisim L"
  shows "bisim (K OO L)"
  using relation_composition_is_simulation and assms
  by (simp only: simulation_def bisimulation_def bilateral_progression_def converse_relcompp)

subsection \<open>Bisimilarity\<close>

notation bisimilarity (infix \<open>\<sim>\<close> 50)

lemma bisimilarity_reflexivity_rule [iff]:
  shows "p \<sim> p"
  by (coinduction arbitrary: p) blast

lemma bisimilarity_reflexivity:
  shows "reflp (\<sim>)"
  using bisimilarity_reflexivity_rule ..

lemma bisimilarity_transitivity_rule [trans]:
  assumes "p \<sim> q" and "q \<sim> r"
  shows "p \<sim> r"
  using assms by (coinduction arbitrary: p q r) (auto; elim bisimilarity.cases, blast)

lemma bisimilarity_transitivity:
  shows "transp (\<sim>)"
  using bisimilarity_transitivity_rule ..

theorem bisimilarity_is_equivalence:
  shows "equivp (\<sim>)"
  using bisimilarity_reflexivity and bisimilarity_symmetry and bisimilarity_transitivity
  by (fact equivpI)

subsection \<open>Respectful Functions\<close>

notation shortcut_progression (infix \<open>\<leadsto>\<close> 50)

notation constant_bisimilarity (\<open>[\<sim>]\<close>)

lemma relation_composition_shortcut_progression:
  assumes "K\<^sub>1 \<leadsto> L\<^sub>1" and "K\<^sub>2 \<leadsto> L\<^sub>2"
  shows "K\<^sub>1 OO K\<^sub>2 \<leadsto> L\<^sub>1 OO L\<^sub>2"
  using assms by (simp, blast)

lemma chain_is_respectful [respectful]:
  assumes "respectful \<F>" and "respectful \<G>"
  shows "respectful (\<F> \<frown> \<G>)"
proof -
  have "(\<F> \<frown> \<G>) K \<leadsto> (\<F> \<frown> \<G>) L" if "K \<leadsto> L" for K and L
  proof -
    from \<open>respectful \<F>\<close> and \<open>respectful \<G>\<close> and \<open>K \<leadsto> L\<close> have "\<F> K \<leadsto> \<F> L" and "\<G> K \<leadsto> \<G> L"
      by simp_all
    then show ?thesis
      unfolding chain_def
      by (fact relation_composition_shortcut_progression)
  qed
  then show ?thesis
    by simp
qed

subsection \<open>``Up to'' Methods\<close>

notation simulation_up_to (\<open>sim\<^bsub>_\<^esub>\<close>)

notation bisimulation_up_to (\<open>bisim\<^bsub>_\<^esub>\<close>)

end

end
