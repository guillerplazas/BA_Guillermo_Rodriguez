section \<open>Absolute Module\<close>

theory abs_module
  imports 
 "Compositional_Structures/Basic_Modules/Component_Types/Elimination_Module"
 "Compositional_Structures/Basic_Modules/eliminate_least_score"
 "Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Profile"
 "Compositional_Structures/Basic_Modules/Defer_Module"
 "Compositional_Structures/Basic_Modules/Drop_Module"



begin


subsection \<open>Definition Eliminator\<close>

subsection \<open>Functions absolute module\<close>

(*Mover a Profile*)
definition abs_winner_aux :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "abs_winner_aux A p a =
  (finite_profile A p \<and> a \<in> A \<and> (win_count p a > ( length p div 2)))"

definition abs_winner :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a \<Rightarrow> bool" where
  "abs_winner A p a = (win_count p a > ( length p div 2))"

fun abs_score :: "'a Evaluation_Function" where
  "abs_score x A p =
    (if (abs_winner A p x) then 1 else 0)"


fun absolute:: "'a Electoral_Module" where
  "absolute A p = (if (\<exists> x \<in> A . abs_winner A p x) then ( max_eliminator abs_score A p) else defer_module A p)"



lemma at_most_one_top:
  assumes "finite_profile A p" and "A \<noteq> {}"
  shows "\<forall>i < length p. \<exists>!x. x \<in> A \<and> above (p!i) x = {x}"
proof -
  {
    fix i assume "i < length p"
    then have "\<exists>!x. x \<in> A \<and> above (p!i) x = {x}"
      using assms
      using above_one profile_def by blast 
  }
  then show ?thesis by blast
qed





lemma absolute_win_unique:
  assumes "finite_profile A p"
    and "\<exists>x \<in> A. abs_winner A p x"
  shows "(\<exists>!x \<in> A. abs_winner A p x)"
  sorry

lemma absolute_well_formed:
  assumes "finite_profile A p"
  shows "well_formed A ( absolute A p)"
proof -
  have h1: "\<forall> A p. finite_profile A p \<longrightarrow> well_formed A (max_eliminator abs_score A p)"
    using max_elim_sound
    using par_comp_result_sound by blast
  have h2: "\<forall> A p. finite_profile A p \<longrightarrow> well_formed A (defer_module A p)"
    using def_mod_sound by (simp add: electoral_module_def)
  show ?thesis
    by (metis absolute.elims assms h1 h2)
qed
    

lemma absoulte_sound:
  shows "electoral_module absolute" using absolute_well_formed
  using electoral_modI by blast

lemma absoulte_non_elect_step:
  assumes "finite_profile A p"
  shows "elect absolute A p = {}"  
proof (cases "\<exists> x \<in> A. abs_winner A p x")
    case True
    then have "absolute A p = max_eliminator abs_score A p"
      by simp
    then show ?thesis 
      using max_elim_non_electing \<open>finite_profile A p\<close> non_electing_def by auto
  next
    case False
    then have "absolute A p = defer_module A p"
      by simp
    then show ?thesis 
      by simp
  qed

lemma absolute_non_electing:
  shows "non_electing absolute" using absoulte_non_elect_step
  using absoulte_sound non_electing_def by blast 

lemma max_in_zero_one:
  assumes "S \<subseteq> {0::nat, 1}" "1 \<in> S"
  shows "Max S = 1"
using assms
proof -
  have "finite S" using assms(1)
    by (simp add: finite_subset) 
  then show ?thesis using assms
    by (metis Max.boundedE Max.subset_imp Max_eqI Max_insert Max_singleton empty_iff finite.emptyI finite.insertI insert_not_empty max_0_1(1)) 
qed

lemma min_in_zero_one:
  assumes "S \<subseteq> {0::nat, 1}" "0 \<in> S"
  shows "Min S = 0"
using assms
proof -
  have "finite S" using assms(1)
    by (simp add: finite_subset) 
  then show ?thesis using assms
    using Min_eqI by auto
qed

lemma max_eliminator_card_defer:
  assumes "finite_profile A p"
    and "abs_winner A p a"
    and "a \<in> A"
  shows "defer_r (max_eliminator abs_score A p) = {a}"
  sorry


theorem absolute_imp_cond:
  assumes "finite_profile A p"
    and "card A > 2"
    and "{a} = defer absolute A p"
  shows "abs_winner A p a" 
proof-
  have "\<exists> x \<in> A. abs_winner A p x" 
  proof (rule ccontr)
    assume "\<not>(\<exists> x \<in> A. abs_winner A p x)"
    then have "absolute A p = defer_module A p" 
      by simp
    then have "defer absolute A p = defer defer_module A p" 
      by simp
    then have "{a} = A" 
      using assms(3) by simp
    then have "card A = 1"
      by auto 
    then show False using assms(2) 
      by simp
  qed
  then have "absolute A p = max_eliminator abs_score A p"
    by simp
  obtain e r d where abs_def: "absolute A p = (e, r, d)"
    by (cases "absolute A p")
  then have "{a} = d"
    using assms(3) by simp
  then have "r=A-{a}"
    by (metis Diff_empty \<open>absolute A p = max_eliminator abs_score A p\<close> abs_def absoulte_non_elect_step assms(1) fstI max_elim_sound reject_not_elec_or_def snd_eqD)
  then have "reject_r (defer_module A p)  ={}"
    by simp
  show ?thesis
    by (metis \<open>\<exists>x\<in>A. abs_winner A p x\<close> \<open>absolute A p = max_eliminator abs_score A p\<close> assms(1) assms(3) max_eliminator_card_defer the_elem_eq) 
qed



end