section \<open>Test Case 1\<close>

theory test_case_1
  imports "../IRV_Rule"
begin

text \<open>A={}\<close>

definition A_empty :: "char set" where  "A_empty = {}"
definition p_empty :: "char Profile" where  "p_empty = []"
definition r_empty :: "char Preference_Relation" where "r_empty = {}"

value "IRV_rule_drop r_empty A_empty p_empty "

end