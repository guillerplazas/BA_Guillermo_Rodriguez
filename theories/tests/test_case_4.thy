section \<open>Test Case 4\<close>

theory test_case_4  
  imports "../IRV_Rule"
begin



text \<open>
Case 4: C eliminated first, then A wins
Ballot: Bottom [...] Top
Voter 1:  [c,b,a]
Voter 2:  [c,a,b]
Voter 3:  [b,a,c]
"
\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"

definition A :: "char set" where  "A = {canA, canB, canC}"

definition r :: "char Preference_Relation" where
  "r = {(canB, canA), (canC, canA), (canC, canB), (canA, canA), (canB, canB), (canC, canC)}"

definition voter1_pref2 :: "(char \<times> char) set" where "voter1_pref2 = set [(canB, canA), (canC, canA),(canC, canB),(canA, canA),(canB, canB),(canC, canC)]"
definition voter2_pref2 :: "(char \<times> char) set" where "voter2_pref2 = set [(canA, canB), (canC, canB),(canC, canA),(canA, canA),(canB, canB),(canC, canC)]"
definition voter3_pref2 :: "(char \<times> char) set" where "voter3_pref2 = set [(canA, canC), (canB, canC),(canB, canA),(canA, canA),(canB, canB),(canC, canC)]"


definition p2 :: "char Profile" where  "p2 = [voter1_pref2, voter2_pref2,voter3_pref2]"

value "IRV_rule_drop r A p2" 



end