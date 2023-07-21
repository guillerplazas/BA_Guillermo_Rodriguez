section \<open>Eliminate leas score\<close>

theory eliminate_least_score
  imports 
 "Component_Types/Elimination_Module"
 "Component_Types/Social_Choice_Types/Profile"
 "Defer_Module"
 "Drop_Module"



begin


subsection \<open>Definition Eliminator\<close>



fun eliminate_least_old :: "'a Evaluation_Function \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "eliminate_least_old e r A p =
    (if A = {} then ({}, {}, {})
     else
        (if card A = 1 then defer_module A p  
        else
          let scores = {e x A p | x. x \<in> A};
              min_score = Min scores;
              candidates_with_min_score = {x \<in> A. e x A p = min_score}
          in
            if candidates_with_min_score = {} then ({}, {}, A)
            else 
              if card candidates_with_min_score = 1 then ({}, candidates_with_min_score, A-candidates_with_min_score)
              else
                let (_, to_eliminate, _) = drop_module 1 r candidates_with_min_score p
                in
                  if to_eliminate = {} then ({},{},A)
                  else ({}, to_eliminate, A - to_eliminate)))"


fun eliminate_least_score :: "'a Evaluation_Function \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "eliminate_least_score e r A p =
   (if card A = 1 then defer_module A p  
        else
          let  cand_with_min_score = {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}
          in
              if card cand_with_min_score = 1 then ({}, cand_with_min_score, A-cand_with_min_score)
              else
                let to_eliminate = {a \<in> cand_with_min_score. card(above (limit cand_with_min_score r) a) \<le> 1}
                in
                   ({}, to_eliminate, A - to_eliminate))"





subsection \<open>Branch Proofs\<close>

lemma eliminate_least_score_branch_A_1:
  assumes "finite_profile A p" 
    and "card A = 1"
  shows "eliminate_least_score e r A p=defer_module A p"
proof -
  from assms obtain c where "A = {c}"
    by (auto simp: card_Suc_eq)

  have elim_res: "eliminate_least_score e r A p = ({}, {}, A)"
    using `A = {c}` assms(1) assms(2) by simp
  show "eliminate_least_score e r A p=defer_module A p"
    using elim_res by auto
qed


lemma eliminate_least_score_branch_cwms_1:
  assumes 
    "finite_profile A p" 
    "card A \<noteq> 1"
    "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 1"
  shows 
    "eliminate_least_score e r A p = ({}, {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}, A - {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}})"
proof -
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  have "eliminate_least_score e r A p = ({}, ?candidates_with_min_score, A - ?candidates_with_min_score)"
    unfolding eliminate_least_score.simps 
    using assms(2) assms(3) by (auto simp add: Let_def)
  then show ?thesis by simp
qed



lemma eliminate_least_score_branch_cwms_not_1:
  assumes 
    "finite_profile A p"
    "card A \<noteq> 1"
    "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} \<noteq> 1"
  shows 
    "eliminate_least_score e r A p = ({}, {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}, A - {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1})"
proof-
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  let ?to_eliminate = "{a \<in> ?candidates_with_min_score. card(above (limit ?candidates_with_min_score r) a) \<le> 1}"
  have "eliminate_least_score e r A p = ({}, ?to_eliminate, A - ?to_eliminate)"
    unfolding eliminate_least_score.simps 
    using assms(2) assms(3) by (auto simp add: Let_def)
  then show ?thesis by simp
qed




subsection \<open>Soundness Proofs \<close>


lemma eliminate_least_score_well_formed:
  assumes finite: "finite_profile A p"
  shows "well_formed A  (eliminate_least_score e r A p)"
proof (cases "card A = 1")
  case A_eq_1: True
  then have res_A_eq_1: "eliminate_least_score e r A p = defer_module A p"
    using eliminate_least_score_branch_A_1 finite A_eq_1 by simp
  then show ?thesis 
    using def_mod_sound res_A_eq_1 set_equals_partition.simps by auto 
next
  case A_neq_1: False
  then show ?thesis
  proof (cases "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 1")
    case card_cwms_eq_1: True
    then have res_branch_cwms_1: "eliminate_least_score e r A p = ({}, {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}, A - {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}})"
      using eliminate_least_score_branch_cwms_1 finite A_neq_1 by blast 
    then show ?thesis 
      using set_equals_partition.simps res_branch_cwms_1 by auto 
  next
    case card_cwms_neq_1: False
    then have res_branch_cwms_neq_1: "eliminate_least_score e r A p = ({}, {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}, A - {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1})"
      using eliminate_least_score_branch_cwms_not_1 finite card_cwms_neq_1 A_neq_1 by blast
    then show ?thesis
      using set_equals_partition.simps res_branch_cwms_neq_1 by auto
  qed
qed



lemma eliminate_least_score_soundness:
  shows "electoral_module (eliminate_least_score e r)" using eliminate_least_score_well_formed 
  by (metis electoral_module_def)




subsection \<open>Non-Electing Proofs\<close>


lemma eliminate_least_score_empty_elect:
  assumes "finite_profile A p"
  shows "elect (eliminate_least_score e r) A p = {}" using finite eliminate_least_score_branch_A_1 eliminate_least_score_branch_cwms_1 eliminate_least_score_branch_cwms_not_1
          assms
  by (smt (verit, ccfv_SIG) defer_module.simps fst_conv)

lemma eliminate_least_score_non_electing:
  shows "non_electing (eliminate_least_score e r)" using  eliminate_least_score_empty_elect
  by (metis eliminate_least_score_soundness non_electing_def)





subsection \<open>Cardinality Eliminations\<close>

lemma eliminate_least_score_branch_A_1_card:
  assumes "finite_profile A p" 
    and "card A = 1"
  shows  "card (reject_r (eliminate_least_score e r A p)) \<le> 1"
proof -
  have "eliminate_least_score e r A p = defer_module A p"  using assms by auto
  have "card (reject_r (defer_module A p)) =  0"
    by simp
  show ?thesis
    by (simp add: assms(2)) 
qed

lemma eliminate_least_score_branch_cwms_1_card:
  assumes 
    "finite_profile A p" 
    "card A \<noteq> 1"
    "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 1"
  shows 
    "card (reject_r (eliminate_least_score e r A p)) \<le> 1"
proof -
  let ?candidates_with_min_score = "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}"
  have "eliminate_least_score e r A p = ({}, ?candidates_with_min_score, A - ?candidates_with_min_score)"
    unfolding eliminate_least_score.simps 
    using assms(2) assms(3) by (auto simp add: Let_def)
  have reject_r_def: "reject_r (eliminate_least_score e r A p) = ?candidates_with_min_score"
    using \<open>eliminate_least_score e r A p = ({}, {x \<in> A. e x A p = Min {e x A p |x. x \<in> A}}, A - {x \<in> A. e x A p = Min {e x A p |x. x \<in> A}})\<close> by auto
  then have "card ?candidates_with_min_score =1 "
    by (simp add: assms(3))
 
  show ?thesis using reject_r_def `card ?candidates_with_min_score =1`
    by simp 
qed

lemma eliminate_least_score_A_eq_0:
assumes
"finite_profile A p"
"card A = 0"
shows
"card (reject_r (eliminate_least_score e r A p)) = 0"
proof-
  have "A = {}"
    using assms(2)
  by (simp add: assms(1)) 
  then have "eliminate_least_score e r A p = ({}, {}, A)"
    by simp
  hence "reject_r (eliminate_least_score e r A p) = {}"
    by simp
  thus "card (reject_r (eliminate_least_score e r A p)) = 0"
    by simp
qed

lemma eliminate_least_score_A_cwms_0:
  assumes
    "finite_profile A p"
    "card A\<noteq>1"
    "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}=0"
  shows
    "card (reject_r (eliminate_least_score e r A p)) = 0"
  proof(cases "card A =0")
    case A_empty: True 
    then show ?thesis using eliminate_least_score_A_eq_0
      by (metis assms(1))
  next
    case A_non_empty: False
    have "A \<noteq> {}"
      using assms(2) A_non_empty
      by auto 
    have empty_res: "{x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = {}"
      using assms(1) assms(3) by auto
    have result: "eliminate_least_score e r A p=({}, {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}, A - {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1})" 
    using eliminate_least_score_branch_cwms_not_1
    by (simp add: \<open>{x \<in> A. e x A p = Min {e x A p |x. x \<in> A}} = {}\<close>)
    have "reject_r(eliminate_least_score e r A p) = {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}" 
      using result by simp
    then have "reject_r(eliminate_least_score e r A p) = {a \<in> {}. card(above (limit {} r) a) \<le> 1}"
      using empty_res by simp
    then have "reject_r(eliminate_least_score e r A p) = {}"
      by simp
    then show ?thesis
      by simp
  qed

lemma step_wrong:
  assumes "linear_order_on A r"
    and "S \<subseteq> A"
  shows " card{a \<in> S. card(above (limit S r) a) \<le> n}\<le>1"
  sorry


lemma eliminate_least_score_branch_cwms_not_1_card:
  assumes 
    "finite_profile A p"
    "card A \<noteq> 1"
    "linear_order_on A r"
    "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} \<noteq> 1"
  shows 
    "card (reject_r (eliminate_least_score e r A p)) \<le>  1"
proof (cases "card A = 0")
  case True
  then show ?thesis using eliminate_least_score_A_eq_0
    by (metis assms(1) linordered_nonzero_semiring_class.zero_le_one)
next
  case A_neq_0: False
  then have "A \<noteq> {}"
    using assms(2) by auto
  then have "card (reject_r (eliminate_least_score e r A p)) \<le>  1"
  proof (cases "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 0")
    case True 
    then show ?thesis using eliminate_least_score_A_cwms_0 assms(2) True
      by (metis (mono_tags, lifting) assms(1) le_zero_eq linorder_le_cases)   
  next
    case cwms_neq_0: False
    have impli: "eliminate_least_score e r A p = ({}, {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}, A - {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1})"
      using assms eliminate_least_score_branch_cwms_not_1 by blast
    then have "reject_r (eliminate_least_score e r A p) = {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}"
      by simp 
    have " {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} \<subseteq> A"
      by simp
    then have "card {a \<in> {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}}. card(above (limit {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} r) a) \<le> 1}\<le>1" 
      using step_wrong  assms(3) by blast
    then show ?thesis
      using \<open>reject (eliminate_least_score e r) A p = {a \<in> {x \<in> A. e x A p = Min {e x A p |x. x \<in> A}}. card (above (limit {x \<in> A. e x A p = Min {e x A p |x. x \<in> A}} r) a) \<le> 1}\<close> by presburger
  qed
  show ?thesis
    using \<open>card (reject (eliminate_least_score e r) A p) \<le> 1\<close> by blast 
qed



theorem eliminate_least_score_card:
  assumes "finite_profile A p"
and "linear_order_on A r"
  shows "card (reject_r (eliminate_least_score e r A p))\<le> 1"
proof(cases "card A = 1")
  case True
  then show ?thesis 
    using eliminate_least_score_branch_A_1_card assms by simp
next
  case False
  then show ?thesis 
  proof (cases "card {x \<in> A. e x A p = Min {e x A p | x. x \<in> A}} = 1")
    case True
    then show ?thesis
      using eliminate_least_score_branch_cwms_1_card False assms
      by blast 
  next
    case False
    then show ?thesis
      using eliminate_least_score_branch_cwms_not_1_card False `card A \<noteq> 1` assms
      by blast
  qed
qed

end