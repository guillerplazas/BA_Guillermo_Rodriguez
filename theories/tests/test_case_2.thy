section \<open>Test Case 2\<close>

theory test_case_2
  imports "../IRV_Rule"
begin

text \<open>A={a}\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition A_1 :: "char set" where  "A_1 = {canA}"
definition r_1 :: "char Preference_Relation" where "r_1 = {(canA, canA)}"


definition voter1_1 :: "(char \<times> char) set" where "voter1_1 = set [(canA, canA)]"
definition voter2_1 :: "(char \<times> char) set" where "voter2_1 = set [(canA, canA)]"
definition voter3_1 :: "(char \<times> char) set" where "voter3_1 = set [(canA, canA)]"


definition p_1 :: "char Profile" where  "p_1 = [voter1_1, voter2_1,voter3_1]"

value "IRV_rule_drop r_1 A_1 p_1 "

end