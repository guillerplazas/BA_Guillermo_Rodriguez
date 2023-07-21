section \<open>Test Case 3\<close>

theory test_case_3
  imports "../IRV_Rule"
begin

text \<open>
Case 3: A wins first round
Ballot: Bottom [...] Top
Voter 1: [c,b,a]
Voter 2: [b,c,a]
Voter 2: [c,b,a]
\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"

definition A :: "char set" where  "A = {canA, canB, canC}"
definition A_test :: "char set" where  "A_test = {canA}"

definition r :: "char Preference_Relation" where
  "r = {(canB, canA), (canC, canA), (canC, canB), (canA, canA), (canB, canB), (canC, canC)}"

definition voter1_test  :: "(char \<times> char) set" where "voter1_test = set [(canA, canA)]"
definition voter1_pref1 :: "(char \<times> char) set" where "voter1_pref1 = set [(canC, canB), (canB, canA),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"
definition voter2_pref1 :: "(char \<times> char) set" where "voter2_pref1 = set [(canB, canC), (canC, canA),(canB, canA),(canA, canA),(canB, canB),(canC, canC)]"
definition voter3_pref1 :: "(char \<times> char) set" where "voter3_pref1 = set [(canC, canB), (canB, canA),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"

definition p1 :: "char Profile" where  "p1 = [voter1_pref1, voter2_pref1,voter3_pref1]"
definition p_test :: "char Profile" where  "p_test = [voter1_test]"


value "IRV_rule_drop r A p1 "

end