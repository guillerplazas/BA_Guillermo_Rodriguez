section \<open>test_case_5\<close>

theory test_case_5
  imports "../IRV_Rule"
          
begin


text \<open>
Case 5
code:
a and c are clones
bottom[...]top 
[b,a,c]
[b,a,c]
[b,c,a]
[b,c,a]
[c,a,b]
[c,a,b]
[c,a,b]
\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"


definition A3 :: "char set" where  "A3 = {canA, canB, canC}"

definition r3 :: "char Preference_Relation" where
  "r3 = {(canB, canA), (canC, canA), (canC, canB), (canA, canA), (canB, canB), (canC, canC)}"


definition voter1_pref3 :: "(char \<times> char) set" where
  "voter1_pref3 = set [(canB, canA), (canB, canC), (canA, canC), (canA, canA), (canB, canB), (canC, canC)]"

definition voter2_pref3 :: "(char \<times> char) set" where
  "voter2_pref3 = set [(canB, canA), (canB, canC), (canA, canC), (canA, canA), (canB, canB), (canC, canC)]"

definition voter3_pref3 :: "(char \<times> char) set" where
  "voter3_pref3 = set [(canB, canC), (canB, canA), (canC, canA), (canA, canA), (canB, canB), (canC, canC)]"

definition voter4_pref3 :: "(char \<times> char) set" where
  "voter4_pref3 = set [(canB, canC), (canB, canA), (canC, canA), (canA, canA), (canB, canB), (canC, canC)]"

definition voter5_pref3 :: "(char \<times> char) set" where
  "voter5_pref3 = set [(canC, canA), (canC, canB), (canA, canB), (canA, canA), (canB, canB), (canC, canC)]"

definition voter6_pref3 :: "(char \<times> char) set" where
  "voter6_pref3 = set [(canC, canA), (canC, canB), (canA, canB), (canA, canA), (canB, canB), (canC, canC)]"

definition voter7_pref3 :: "(char \<times> char) set" where
  "voter7_pref3 = set [(canC, canA), (canC, canB), (canA, canB), (canA, canA), (canB, canB), (canC, canC)]"

definition p3 :: "char Profile" where  
  "p3 = [voter1_pref3, voter2_pref3, voter3_pref3, voter4_pref3, voter5_pref3, voter6_pref3,voter7_pref3]"



value "IRV_rule_drop r3 A3 p3"


end