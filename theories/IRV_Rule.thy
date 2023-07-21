section \<open>IRV_Rule\<close>

theory IRV_Rule
  imports "abs_module"
          "Compositional_Structures/Defer_One_Loop_Composition"
          "Compositional_Structures/Basic_Modules/drop_module"
begin

fun IRV_score :: "'a Evaluation_Function" where
  "IRV_score x A p = win_count p x"

fun IRV_step_2:: "'a Preference_Relation \<Rightarrow>'a Electoral_Module" where
  "IRV_step_2 r A p =  eliminate_least_score IRV_score r A p"


fun IRV_rule_drop :: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "IRV_rule_drop r A p= (((absolute \<triangleright> ( IRV_step_2 r) )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d)\<triangleright> elect_module) A p"

fun IRV_loop:: "'a Preference_Relation \<Rightarrow> 'a Electoral_Module" where
  "IRV_loop r A p= ((absolute \<triangleright> ( IRV_step_2 r) )\<circlearrowleft>\<^sub>\<exists>\<^sub>!\<^sub>d) A p"



end
