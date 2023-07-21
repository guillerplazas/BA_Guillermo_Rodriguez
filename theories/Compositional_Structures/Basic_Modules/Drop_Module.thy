(*  File:       Drop_Module.thy
    Copyright   2021  Karlsruhe Institute of Technology (KIT)
*)
\<^marker>\<open>creator "Karsten Diekhoff, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Jonas Kraemer, Karlsruhe Institute of Technology (KIT)"\<close>
\<^marker>\<open>contributor "Michael Kirsten, Karlsruhe Institute of Technology (KIT)"\<close>

section \<open>Drop Module\<close>

theory Drop_Module
  imports "Component_Types/Electoral_Module"
begin

text \<open>
  This is a family of electoral modules. For a natural number n and a
  lexicon (linear order) r of all alternatives, the according drop module
  rejects the lexicographically first n alternatives (from A) and
  defers the rest.
  It is primarily used as counterpart to the pass module in a
  parallel composition, in order to segment the alternatives into
  two groups.
\<close>

subsection \<open>Definition\<close>

fun drop_module :: "nat \<Rightarrow> 'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "drop_module n r A p =
    ({},
    {a \<in> A. card(above (limit A r) a) \<le> n},
    {a \<in> A. card(above (limit A r) a) > n})"

subsection \<open>Soundness\<close>

theorem drop_mod_sound[simp]: "electoral_module (drop_module n r)"
proof (intro electoral_modI)
  fix
    A :: "'a set" and
    p :: "'a Profile"
  let ?mod = "drop_module n r"
  have
    "(\<forall> a \<in> A. a \<in> {x \<in> A. card(above (limit A r) x) \<le> n} \<or>
        a \<in> {x \<in> A. card(above (limit A r) x) > n})"
    by auto
  hence
    "{a \<in> A. card(above (limit A r) a) \<le> n} \<union>
        {a \<in> A. card(above (limit A r) a) > n} = A"
    by blast
  hence 0: "set_equals_partition A (drop_module n r A p)"
    by simp
  have
    "(\<forall> a \<in> A. \<not>(a \<in> {x \<in> A. card(above (limit A r) x) \<le> n} \<and>
        a \<in> {x \<in> A. card(above (limit A r) x) > n}))"
    by auto
  hence
    "{a \<in> A. card(above (limit A r) a) \<le> n} \<inter>
        {a \<in> A. card(above (limit A r) a) > n} = {}"
    by blast
  hence 1: "disjoint3 (?mod A p)"
    by simp
  from 0 1 show "well_formed A (?mod A p)"
    by simp
qed

subsection \<open>Non-Electing\<close>

text \<open>
  The drop module is non-electing.
\<close>

theorem drop_mod_non_electing[simp]:
  assumes "linear_order r"
  shows "non_electing (drop_module n r)"
  unfolding non_electing_def
  using assms
  by simp

subsection \<open>Properties\<close>

text \<open>
  The drop module is strictly defer-monotone.
\<close>

theorem drop_mod_def_lift_inv[simp]:
  assumes "linear_order r"
  shows "defer_lift_invariance (drop_module n r)"
  unfolding defer_lift_invariance_def
  using assms
  by simp

(*
lemma limit_above_card:
  assumes "linear_order_on A r"
  assumes "A \<noteq> {}"
  assumes "finite A"
  shows "card {a \<in> A. card (above (limit A r) a) \<le> 1} \<le> 1"
proof -
  let ?limit_r = "limit A r"
  let ?above_set = "{a \<in> A. card (above ?limit_r a) \<le> 1}"
  {
    fix a assume "a \<in> ?above_set"
    then have "card (above ?limit_r a) \<le> 1" by simp
    hence "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      by (simp add: le_Suc_eq)
    have "finite (above ?limit_r a)"
      using assms(3) above_presv_limit finite_subset
      by metis 
    hence "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      using \<open>card (above (limit A r) a) = 0 \<or> card (above (limit A r) a) = 1\<close> by auto
      
  }
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
    by blast
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) \<le> 1"
    by simp
  have "card ?above_set \<le> 1"
  proof (cases "card ?above_set > 1")
    assume "card ?above_set > 1"
    then obtain x y where "x \<in> ?above_set" and "y \<in> ?above_set" and "x \<noteq> y"
      by (metis One_nat_def Suc_1 card_eq_0_iff not_less_eq_eq numeral_2_eq_2)
    have "card (above ?limit_r x) \<le> 1" and "card (above ?limit_r y) \<le> 1"
      using \<open>x \<in> ?above_set\<close> \<open>y \<in> ?above_set\<close> by simp
    have "connex A (limit A r)"
      using assms(1) assms(2) connex_def limit_presv_lin_ord by blast
    hence "x \<preceq>\<^sub>(limit A r) y \<or> y \<preceq>\<^sub>(limit A r) x"
      using \<open>x \<in> ?above_set\<close> \<open>y \<in> ?above_set\<close> connex_def by auto
    then show "card ?above_set \<le> 1"
    proof
      assume "x \<preceq>\<^sub>(limit A r) y"
      then have "y \<in> above ?limit_r x"
        unfolding above_def by simp
      then have "card (above ?limit_r x) = 1"
        using assms(3) card_ge_0_finite above_presv_limit by auto
      hence "above ?limit_r x = {y}"
        using card_1_singletonE by auto
      then have "card (above ?limit_r x) > 1"
        using \<open>x \<noteq> y\<close> \<open>y \<in> above ?limit_r x\<close> \<open>connex A (limit A r)\<close> above_connex by fastforce
      hence False
        using \<open>card (above ?limit_r x) \<le> 1\<close> by auto
      then show "card ?above_set \<le> 1" by simp
    next
      assume "y \<preceq>\<^sub>(limit A r) x"
      then have "x \<in> above ?limit_r y"
        unfolding above_def by (metis pref_imp_in_above)
      then have "card (above ?limit_r y) = 1"
        using assms(3) card_ge_0_finite above_presv_limit by auto
      hence "above ?limit_r y = {x}"
        using card_1_singletonE by auto
      then have "card (above ?limit_r y) > 1"
        using \<open>x \<noteq> y\<close> \<open>x \<in> above ?limit_r y\<close> \<open>connex A (limit A r)\<close> above_connex by fastforce
      hence False
        using \<open>card (above ?limit_r y) \<le> 1\<close> by auto
      then show "card ?above_set \<le> 1" by simp
    qed
  next
    assume "\<not>card ?above_set > 1"
    then show "card ?above_set \<le> 1" by simp
  qed
  thus "card ?above_set \<le> 1" by simp
qed


lemma limit_above_card:
  assumes "linear_order_on A r"
  assumes "A \<noteq> {}"
  assumes "finite A"
  shows "card {a \<in> A. card (above (limit A r) a) \<le> 1} \<le> 1"
proof -
  let ?limit_r = "limit A r"
  let ?above_set = "{a \<in> A. card (above ?limit_r a) \<le> 1}"
  {
    fix a assume "a \<in> ?above_set"
    then have "card (above ?limit_r a) \<le> 1" by simp
    hence "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
    
      by (simp add: le_Suc_eq)
    have "finite A"
      by (simp add: assms(3))
    moreover have "finite (above ?limit_r a)"
      by (meson above_presv_limit calculation rev_finite_subset) 

    ultimately have "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      using \<open>card (above (limit A r) a) = 0 \<or> card (above (limit A r) a) = 1\<close> by auto
    moreover have "above ?limit_r a \<subseteq> A"
      by (meson above_presv_limit)
    hence "finite (above ?limit_r a)"
      using assms(1) finite_subset
      using \<open>finite (above (limit A r) a)\<close> by auto 
    ultimately have "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      by auto
  }
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
    by blast
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) \<le> 1"
    by simp
  have  "card ?above_set \<le> 1"
  proof (cases "card ?above_set > 1")
    assume "card ?above_set > 1"
    then obtain x y where "x \<in> ?above_set" and "y \<in> ?above_set" and "x \<noteq> y"
      by (smt (verit) card.empty is_singletonI' is_singleton_altdef less_numeral_extra(1) order_less_imp_not_less)
    hence "card (above ?limit_r x) \<le> 1" and "card (above ?limit_r y) \<le> 1"
    proof -
      show "card (above (limit A r) x) \<le> 1"
        by (meson \<open>\<forall>a\<in>{a \<in> A. card (above (limit A r) a) \<le> 1}. card (above (limit A r) a) \<le> 1\<close> \<open>x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}\<close>)
    next

    have "connex A (limit A r)"
      using assms(1) assms(2) connex_def limit_presv_lin_ord
      by (metis limit_presv_prefs1 limit_to_limits lin_ord_imp_connex) 
    hence "x \<preceq>\<^sub>(limit A r) y \<or> y \<preceq>\<^sub>(limit A r) x"
      by (metis \<open>x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}\<close> \<open>y \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}\<close> connex_def mem_Collect_eq)
      
    have "card ?above_set \<le> 1"
    proof-
      assume "x \<preceq>\<^sub>(limit A r) y"
      then have "y \<in> above ?limit_r x"
        unfolding above_def by simp
      then have "card (above ?limit_r x) = 1"
        using card_ge_0_finite above_presv_limit assms(3)
        by (metis (mono_tags, lifting) \<open>\<And>a. a \<in> {a \<in> A. card (above (limit A r) a) \<le> 1} \<Longrightarrow> card (above (limit A r) a) = 0 \<or> card (above (limit A r) a) = 1\<close> \<open>x \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}\<close> card_gt_0_iff empty_iff finite_subset less_numeral_extra(3)) 
      hence "above ?limit_r x = {y}"
        using card_1_singletonE
        by (metis \<open>y \<in> above (limit A r) x\<close> empty_iff insertE) 
      then have "card (above ?limit_r x) > 1"
        using `x \<noteq> y` `y \<in> above ?limit_r x` `connex A (limit A r)` above_connex
        using \<open>x \<preceq>\<^sub>(limit A r) y\<close> by fastforce 
      hence False
        using \<open>card (above (limit A r) x) = 1\<close> by auto
      then have "card ?above_set \<le> 1" by simp
    next
      assume "y \<preceq>\<^sub>(limit A r) x"
      then have "x \<in> above ?limit_r y"
        unfolding above_def
        by simp 
      then have "card (above ?limit_r y) = 1"
        using card_ge_0_finite above_presv_limit assms(3)
        by (metis (mono_tags, lifting) \<open>\<And>a. a \<in> {a \<in> A. card (above (limit A r) a) \<le> 1} \<Longrightarrow> card (above (limit A r) a) = 0 \<or> card (above (limit A r) a) = 1\<close> \<open>y \<in> {a \<in> A. card (above (limit A r) a) \<le> 1}\<close> card_gt_0_iff empty_iff finite_subset less_numeral_extra(3)) 
      hence "above ?limit_r y = {x}"
        using card_1_singletonE
        by (metis \<open>x \<in> above (limit A r) y\<close> empty_iff insertE) 
      then have "card (above ?limit_r y) > 1"
        by (metis \<open>connex A (limit A r)\<close> \<open>x \<noteq> y\<close> \<open>y \<preceq>\<^sub>(limit A r) x\<close> above_connex limit_to_limits limited_dest singletonD)
      hence False
        using \<open>card (above (limit A r) y) = 1\<close> by linarith
      then have "card ?above_set \<le> 1" by simp
    
  next
    assume "\<not>card ?above_set > 1"
    then have "card ?above_set \<le> 1" by simp

  thus "card ?above_set \<le> 1" by simp
qed

lemma limit_above_card:
  assumes "linear_order_on A r"
  assumes "{a \<in> A. card (above (limit A r) a) \<le> 1} \<noteq> {}"
  assumes "A \<noteq> {}"
  assumes "finite A"
  shows "card {a \<in> A. card (above (limit A r) a) \<le> 1} \<le> 1"
proof -
  let ?limit_r = "limit A r"
  let ?above_set = "{a \<in> A. card (above ?limit_r a) \<le> 1}"
  {
    fix a assume "a \<in> ?above_set"
    then have "card (above ?limit_r a) \<le> 1" by simp
    hence "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
    
      by (simp add: le_Suc_eq)
    have "finite A"
      by (simp add: assms(4))
    moreover have "finite (above ?limit_r a)"
      by (meson above_presv_limit calculation rev_finite_subset) 

    ultimately have "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      using \<open>card (above (limit A r) a) = 0 \<or> card (above (limit A r) a) = 1\<close> by auto
    moreover have "above ?limit_r a \<subseteq> A"
      by (meson above_presv_limit)
    hence "finite (above ?limit_r a)"
      using assms(1) finite_subset
      using \<open>finite (above (limit A r) a)\<close> by auto 
    ultimately have "card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
      by auto
  }
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) = 0 \<or> card (above ?limit_r a) = 1"
    by blast
  hence "\<forall>a \<in> ?above_set. card (above ?limit_r a) \<le> 1"
    by simp
moreover have "?above_set \<subseteq> A"
  by blast
 hence "card ?above_set \<le> 1"  using assms(3) card_mono finite_subset card_le_1_iff_card_eq_0_or_1   by fastforce 
    by (simp add: card_le_1_iff_card_0_or_card_1 ?above_set)
 hence "card ?above_set \<le> 1" 
 
  ultimately show ?thesis
    by (simp add: card_mono)
qed


  hence "card (?above_set) \<le> 1" using  assms(2) card_1_singletonE finite_subset le_0_eq
    by (metis assms(2) card_1_singletonE finite_subset le_0_eq)
  thus "card {a \<in> A. card (above (limit A r) a) \<le> 1} \<le> 1"
    by simp
qed


lemma limit_above_card:
  assumes "linear_order_on A r"
  assumes "A\<noteq>{}"
  shows "card {a \<in> A. card(above (limit A r) a) \<le> 1}\<le>1"


theorem drop_module_cardinality:
  assumes "finite_profile A p"
  assumes "linear_order r"
  and "linear_order_on A r"
  shows "card (reject_r (drop_module 1 r A p)) < 2"
proof -
  have soundness: "electoral_module (drop_module 1 r)"
    using drop_mod_sound by simp

  let ?rejected = "{a \<in> A. card(above (limit A r) a) \<le> 1}"

  have reject_eq: "reject_r (drop_module 1 r A p) = ?rejected"
    by simp

  have "?rejected \<subseteq> A" 
    using soundness electoral_module_def reject_eq
    by auto

  have "card ?rejected \<le> 1"
  proof (rule ccontr)
    assume "\<not> card ?rejected \<le> 1"
    hence "card ?rejected \<ge> 2" by simp

    obtain x y where "{x,y} \<subseteq> ?rejected" 
      using `card ?rejected \<ge> 2`  card_le_Suc0_iff_eq le_SucI numeral_2_eq_2
      by (smt (verit, del_insts) \<open>\<not> card {a \<in> A. card (above (limit A r) a) \<le> 1} \<le> 1\<close> card_eq_0_iff empty_subsetI equals0I insert_subset le0) 

    have connex_limit: "connex A (limit A r)"
      using limit_presv_lin_ord assms(3) `linear_order r` by (metis dual_order.refl lin_ord_imp_connex)

    have derive_contradiction: "\<And>w z. w \<preceq>\<^sub>(limit A r) z \<Longrightarrow> False"
    proof -
      fix w z
      assume "w \<preceq>\<^sub>(limit A r) z"
      hence "z \<in> above (limit A r) w" using above_def by force
     
      have "card (above (limit A r) w) = 1"
        using `w \<in> ?rejected` card_ge_0_finite above_presv_limit assms(1) by fastforce
      hence "above (limit A r) w = {z}"
        by (metis `z \<in> above (limit A r) w` card_1_singletonE)
      then have "card (above (limit A r) w) > 1"
        using `w \<preceq>\<^sub>(limit A r) z` `w \<in> ?rejected` `z \<in> ?rejected` `w \<noteq> z` above_connex connex_limit by fastforce
      thus "False" using `card (above (limit A r) w) = 1` by auto
    qed

    show "False"
      using `x \<preceq>\<^sub>(limit A r) y \<or> y \<preceq>\<^sub>(limit A r) x` connex_limit `x \<in> ?rejected` `y \<in> ?rejected` connex_def
      by (meson `x \<noteq> y` `?rejected \<subseteq> A` derive_contradiction subset_eq)
  qed

  thus ?thesis using reject_eq by auto
qed


theorem drop_module_cardinality_2:
  assumes "linear_order r"
  and "linear_order_on A r"
  shows "card (reject_r (drop_module 1 r A p)) < 2"
proof -
  have soundness: "electoral_module (drop_module 1 r)"
    using drop_mod_sound by simp

  let ?rejected = "{a \<in> A. card(above (limit A r) a) \<le> 1}"

  have reject_eq: "reject_r (drop_module 1 r A p) = ?rejected"
    by simp

  have "well_formed A (drop_module 1 r A p)"
    using assms soundness electoral_module_def by blast

  have "?rejected \<subseteq> A" 
    using `well_formed A (drop_module 1 r A p)` set_equals_partition.elims(2) reject_eq by fastforce

  have "card ?rejected \<le> 1"
  proof (rule ccontr)
    assume "\<not> card ?rejected \<le> 1"
    hence "card ?rejected \<ge> 2" by simp

    from this have "\<exists> x y. x \<in> ?rejected \<and> y \<in> ?rejected \<and> x \<noteq> y" using
        One_nat_def Suc_1 card_eq_0_iff not_less_eq_eq numeral_2_eq_2
      by (metis (no_types, lifting) card_le_Suc0_iff_eq le_SucI)
    then obtain x y where x_prop: "x \<in> ?rejected" and y_prop: "y \<in> ?rejected" and "x \<noteq> y"
      by blast

    have "card (above (limit A r) x) \<le> 1" and "card (above (limit A r) y) \<le> 1"
      using x_prop y_prop by auto

    have "linear_order_on A r"
      by (simp add: assms(2))
    then have "connex A (limit A r)"
      using limit_presv_lin_ord `linear_order r` by (metis dual_order.refl lin_ord_imp_connex)
    then have "x \<preceq>\<^sub>(limit A r) y \<or> y \<preceq>\<^sub>(limit A r) x"
      using x_prop y_prop connex_def by (metis (no_types, lifting) \<open>?rejected \<subseteq> A\<close> subset_eq)

    then show "False"
    proof (rule disjE)
      assume "x \<preceq>\<^sub>(limit A r) y"
    then have "y \<in> above (limit A r) x"
      using above_def by force
    then have "card (above (limit A r) x) = 1"
      using  card_ge_0_finite
      by (metis \<open>card (above (limit A r) x) \<le> 1\<close> above_presv_limit assms(1) card_eq_0_iff empty_iff le_neq_implies_less less_one rev_finite_subset)
    (* Here, we can't necessarily find another z that is different from y *)
    then have "above (limit A r) x = {y}"
      by (metis \<open>y \<in> above (limit A r) x\<close> card_1_singletonE empty_iff insertE)
      
    (* This means that there is no other element in the above set of x other than y, and since y is above x, there must be at least one more alternative above x, creating a contradiction *)
    then have "card (above (limit A r) x) > 1"
      using `x \<preceq>\<^sub>(limit A r) y`
      using \<open>connex A (limit A r)\<close> \<open>x \<noteq> y\<close> above_connex by fastforce
    then show "False"
      using `card (above (limit A r) x) \<le> 1` by auto
  next
    assume "y \<preceq>\<^sub>(limit A r) x"
    then have "x \<in> above (limit A r) y"
      using above_def by (metis pref_imp_in_above)
    then have "card (above (limit A r) y) = 1"
      using card_ge_0_finite
      by (metis \<open>card (above (limit A r) y) \<le> 1\<close> above_presv_limit assms(1) card_eq_0_iff empty_iff le_neq_implies_less less_one rev_finite_subset)
    (* Similarly for y *)
    then have "above (limit A r) y = {x}"
      by (metis \<open>x \<in> above (limit A r) y\<close> card_1_singletonE empty_iff insertE)
    then have "card (above (limit A r) y) > 1"
      using `y \<preceq>\<^sub>(limit A r) x`
      using \<open>connex A (limit A r)\<close> \<open>x \<noteq> y\<close> above_connex by fastforce 
    then show "False"
      using `card (above (limit A r) y) \<le> 1` by auto
    qed
  qed

  then show ?thesis using reject_eq by auto
qed
*)
end
