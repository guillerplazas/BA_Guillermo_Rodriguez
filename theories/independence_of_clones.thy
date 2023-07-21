section \<open>independence_of_clones\<close>

theory independence_of_clones
  imports 
        "abs_module"
        "IRV_Rule"
      
begin

subsection \<open>Definitions \<close>
definition is_clone_set :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "is_clone_set A p \<equiv> \<forall>r \<in> set p. \<forall>a \<in> A. \<forall>b \<in> A. a \<noteq> b \<longrightarrow> ((a, b) \<in> r \<longleftrightarrow> (b, a) \<in> r)"


definition dir_pref_in_ballot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a Preference_Relation \<Rightarrow> bool" where
  "dir_pref_in_ballot a c r \<equiv> 
    a \<noteq> c \<and> (a, c) \<in> r \<and> (\<forall>b. (b \<noteq> a \<and> b \<noteq> c) \<longrightarrow> \<not> ((a, b) \<in> r \<and> (b, c) \<in> r))"


fun clones_exist_in_A :: "'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
"clones_exist_in_A A p = 
  (\<exists>a\<in>A. \<exists>b\<in>A. a \<noteq> b \<and> 
    (\<forall>r \<in> set p. (dir_pref_in_ballot a b r) \<or> (dir_pref_in_ballot b a r)))"


definition introduces_clone_in_candidate :: "'a \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> bool" where
  "introduces_clone_in_candidate a c A p Ac pc \<equiv> 
   a \<in> A \<and> a \<noteq> c \<and> c \<notin> A \<and> c\<in>Ac \<and> a\<in>Ac  \<and> finite_profile A p \<and> finite_profile Ac pc \<and> Ac = A \<union> {c} \<and>
    (\<forall>r \<in> set pc. (dir_pref_in_ballot a c r) \<or> (dir_pref_in_ballot c a r)) \<and>
    (\<forall>r \<in> set p. \<forall>r' \<in> set pc. 
        (\<forall>b d. b \<noteq> a \<and> b \<noteq> c \<and> d \<noteq> a \<and> d \<noteq> c \<longrightarrow> ((b, d) \<in> r \<longleftrightarrow> (b, d) \<in> r')) \<and>
        (\<forall>b. b \<noteq> a \<and> b \<noteq> c \<longrightarrow> ((b, a) \<in> r \<longrightarrow> ((b, a) \<in> r' \<and> (b, c) \<in> r'))) \<and>
        (\<forall>d. d \<noteq> a \<and> d \<noteq> c \<longrightarrow> ((a, d) \<in> r \<longrightarrow> ((a, d) \<in> r' \<and> (c, d) \<in> r'))))"



definition independence_of_clones_win :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones_win em \<equiv> 
    \<forall>A p Ac pc. (\<forall> a \<in> elect em A p. \<exists>c. c \<notin> A \<and> 
      introduces_clone_in_candidate a c A p Ac pc 
      \<longrightarrow> ( a \<in> (elect_r (em Ac pc)) \<or>  c \<in> (elect_r (em Ac pc))))"

definition independence_of_clones_loose :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones_loose em \<equiv> 
    \<forall>A p Ac pc. (\<forall> a \<in> reject em A p. \<exists>c. c \<notin> A \<and> 
      introduces_clone_in_candidate a c A p Ac pc 
      \<longrightarrow> ( a \<in> (reject_r (em Ac pc)) \<and>  c \<in> (reject_r (em Ac pc))))"

definition independence_of_clones:: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones em \<equiv> (independence_of_clones_win em) \<and> (independence_of_clones_loose em)"

definition independence_of_clones_deff :: "'a Electoral_Module \<Rightarrow> bool" where
  "independence_of_clones_deff em \<equiv> 
    \<forall>A p Ac pc. (\<forall> a \<in> defer em A p. \<exists>c. c \<notin> A \<and> 
      introduces_clone_in_candidate a c A p Ac pc 
      \<longrightarrow> ( a \<in> (defer_r (em Ac pc)) \<or>  c \<in> (defer_r (em Ac pc))))"



subsection \<open>Basic Lemmas\<close>

lemma prof_fin_A:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "finite_profile A p" 
  using assms unfolding introduces_clone_in_candidate_def by auto

lemma prof_fin_Ac:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "finite_profile Ac pc" 
  using assms unfolding introduces_clone_in_candidate_def by auto

lemma ac_union_property:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "Ac = A \<union> {c}"
  using assms unfolding introduces_clone_in_candidate_def by blast

lemma ac_union_minus:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "A =Ac- {c}"
  using assms unfolding introduces_clone_in_candidate_def
  by blast 
 

lemma dir_pref_excludes_inverse:
  assumes "dir_pref_in_ballot a b r" 
    and "linear_order_on A r" 
    and "a \<in> A" 
    and "b \<in> A"
  shows "\<not>(b, a) \<in> r"
proof
  assume "(b, a) \<in> r"
  moreover have "(a, b) \<in> r" 
    using assms(1) unfolding dir_pref_in_ballot_def by simp
  moreover have "a \<noteq> b" 
    using assms(1) unfolding dir_pref_in_ballot_def by simp
  ultimately show False 
    using assms(2) unfolding linear_order_on_def partial_order_on_def 
    by (metis antisym_def)
qed

lemma introduces_clone_implies_dir_pref:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "\<forall>r \<in> set pc. dir_pref_in_ballot a c r \<or> dir_pref_in_ballot c a r"
  using assms
  unfolding introduces_clone_in_candidate_def
  by simp


lemma b_preferred_over_a:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
    and "b \<noteq> a"
    and "b \<noteq> c"
  shows "\<forall>r \<in> set p. \<forall>r' \<in> set pc.(a,b)\<in>r\<longrightarrow>((a,b)\<in>r')"  
  using assms(1) assms(2) assms(3) unfolding introduces_clone_in_candidate_def
  by blast

lemma b_preferred_over_c:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
    and "b \<noteq> a"
    and "b \<noteq> c"
    and "a \<noteq> c"
  shows "\<forall>r \<in> set p. \<forall>r' \<in> set pc.(a,b)\<in>r\<longrightarrow>((c,b)\<in>r')"
  using assms(1) assms(2) assms(3) assms(4)  unfolding introduces_clone_in_candidate_def
  by simp


lemma b_preferred_over_a_c:
assumes "introduces_clone_in_candidate a c A p Ac pc"
    and "finite_profile A p"
    and "finite_profile Ac pc"
    and "a \<in> A"
    and "b \<in> A"
    and "b \<noteq> a"
    and "b \<noteq> c"
    and "c \<noteq> a"
shows "\<forall>r \<in> set p. \<forall>r' \<in> set pc.(a,b)\<in>r\<longrightarrow>((c,b)\<in>r'\<and>(a,b)\<in>r')" unfolding introduces_clone_in_candidate_def dir_pref_in_ballot_def
  using b_preferred_over_a  b_preferred_over_c assms(1) assms(6) assms(7) by fastforce



subsection \<open> \<close>

lemma vote_distribution:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
      and "abs_winner A p a"
    shows "(abs_winner Ap pc a)\<or>(abs_winner Ac pc c)\<or>\<not>(\<exists>b \<in> Ac. b\<noteq>a \<and>b\<noteq>c\<and> abs_winner Ac pc b)"
  sorry


lemma absolute_no_elim:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
    and "{a} = defer absolute A p"
    and "card A > 2"
    and "finite_profile A p"
  shows "\<not>({a,c} \<subseteq> reject absolute Ac pc)"
proof-
   have "abs_winner A p a" using assms(2) absolute_imp_cond assms(3) assms(4)
     by metis
   then have "(a \<in> defer absolute Ac pc \<and> c \<in> reject absolute Ac pc)\<or>(c \<in> defer absolute Ac pc \<and> a \<in> reject absolute Ac pc)\<or> (a \<in> defer absolute Ac pc \<and> c \<in> defer absolute Ac pc)"
  proof (cases "abs_winner Ac pc a")
    case a_win: True
    have "(a \<in> defer absolute Ac pc \<and> c \<in> reject absolute Ac pc)" 
    proof-
      have "abs_winner Ac pc a" using a_win
        by simp
      then have "defer_r (absolute Ac pc) = {a}"
        by (metis (no_types, lifting) UnI1 UnI2 absolute.elims absoulte_sound ac_union_property assms(1) assms(2) assms(4) insertI1 max_eliminator_card_defer prof_fin_Ac result_presv_alts)  
       then show ?thesis
         by (metis (no_types, opaque_lifting) Diff_iff Un_insert_right absolute_non_electing ac_union_property ac_union_minus assms(1) assms(2) assms(4) elec_and_def_not_rej insertI1 non_electing_def prof_fin_Ac)
     qed
       then show ?thesis  by simp
  next
    case a_n_win:False
    have "(c \<in> defer absolute Ac pc \<and> a \<in> reject absolute Ac pc)\<or> (a \<in> defer absolute Ac pc \<and> c \<in> defer absolute Ac pc)"
    proof (cases "abs_winner Ac pc c")
      case c_win: True
      have "(c \<in> defer absolute Ac pc \<and> a \<in> reject absolute Ac pc)" unfolding  absolute.simps
        using a_n_win
        by (smt (verit) Diff_empty Un_iff absolute.elims absoulte_non_elect_step ac_union_property ac_union_minus assms(1) assms(2) assms(4) c_win def_mod_non_electing insertCI max_elim_sound max_eliminator_card_defer non_electing_def prof_fin_Ac reject_not_elec_or_def result_presv_alts) 
      then show ?thesis by simp
    next
      case no_win: False
      have "\<not>(abs_winner Ac pc c) \<and> \<not>(abs_winner Ac pc c)" using no_win
        by simp
    hence "a \<in> defer absolute Ac pc \<and> c \<in> defer absolute Ac pc"
      using no_win absolute.simps vote_distribution
      by (metis (no_types, lifting) Un_iff \<open>abs_winner A p a\<close> a_n_win absoulte_sound ac_union_property assms(1) assms(2) assms(4) defer_module.simps result_presv_alts singletonI snd_conv)
    then show ?thesis by blast
  qed
  then show ?thesis
    by simp
qed
  then show ?thesis
    by (metis (no_types, lifting) Int_iff absoulte_sound assms(1) insert_absorb insert_not_empty insert_subset prof_fin_Ac result_disj)
qed


lemma implication_intro_clone:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "{a,c} \<subseteq> Ac"
proof -
  have "a \<in> Ac \<and> c \<in> Ac"
    using assms
    by (simp add: introduces_clone_in_candidate_def) 
  then show ?thesis
    by blast
qed



lemma implication_intro_clone_card:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
  shows "card {a,c} = 2"
proof -
  have "a \<noteq> c"
    using assms
    by (simp add: introduces_clone_in_candidate_def)
  then have "{a, c} = {c, a}"
    by (simp add: doubleton_eq_iff)
  then show ?thesis
    using \<open>a \<noteq> c\<close> by auto
qed

lemma IRV_step_2_no_elim:
  assumes "introduces_clone_in_candidate a c A p Ac pc"
    and "a \<in> defer_r (IRV_step_2 r A p)"
    and "linear_order_on A r"
    and "linear_order_on Ac rc"
    and "finite_profile A p"
    and "finite_profile Ac pc"
  shows "\<not>({a,c} \<subseteq> reject_r (IRV_step_2 rc Ac pc))"
proof (rule ccontr)
  assume "\<not> \<not>({a,c} \<subseteq> reject_r (IRV_step_2 rc Ac pc))"
  then have ac_in_reject_r: "{a,c} \<subseteq> reject_r (IRV_step_2 rc Ac pc)"
    by simp
  then have "reject_r (IRV_step_2 rc Ac pc) \<noteq> {}"
    by blast
  then have "card (reject_r (IRV_step_2 rc Ac pc)) \<le> 1"
    using assms(4) assms(6) eliminate_least_score_card IRV_step_2.simps
    by metis
  moreover have "card {a, c} = 2"
  proof-
    have "a \<noteq> c"
      using assms  by (simp add: introduces_clone_in_candidate_def)
 then have "{a, c} = {c, a}"
    by (simp add: doubleton_eq_iff)
  then show ?thesis
    using \<open>a \<noteq> c\<close> by auto
qed
  have "finite Ac " using assms(5)
    by (simp add: assms(6))
  have "reject_r (IRV_step_2 rc Ac pc) =  reject_r ( eliminate_least_score IRV_score rc Ac pc) "
    by simp
  have " finite(reject_r ( eliminate_least_score IRV_score rc Ac pc))" using eliminate_least_score_well_formed
    by (metis assms(6) finite_subset reject_subset)
  have "reject_r ( eliminate_least_score IRV_score rc Ac pc) \<subseteq>Ac"
    using assms(6) eliminate_least_score_soundness reject_in_alts by blast
  have "finite(reject_r (IRV_step_2 rc Ac pc)) "
    using \<open>finite (reject (eliminate_least_score IRV_score rc) Ac pc)\<close> by auto
  have "reject_r (IRV_step_2 rc Ac pc)\<subseteq>Ac" using eliminate_least_score_well_formed
    using \<open>reject (eliminate_least_score IRV_score rc) Ac pc \<subseteq> Ac\<close> by auto
   then have "2 \<le> card (reject_r (IRV_step_2 rc Ac pc))"
    using `card {a, c} = 2` ac_in_reject_r card_mono
    by (metis \<open>finite (reject (IRV_step_2 rc) Ac pc)\<close>) 
  ultimately show False
    using `card (reject_r (IRV_step_2 rc Ac pc)) \<le> 1` by simp
qed






