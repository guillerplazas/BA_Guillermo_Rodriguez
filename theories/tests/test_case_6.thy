section \<open>test_case_6\<close>

theory test_case_6
  imports "../IRV_Rule"
          
begin

text \<open>
Case 6:
Ballot: Bottom [...] Top
Voter 1: [e,d,a,c,b]
Voter 2: [e,b,d,a,c]
Voter 3: [e,a,c,d,b]
Voter 4: [b,e,a,c,d]
Voter 5: [d,c,a,e,b]
Voter 6: [c,b,d,a,e]
\<close>

definition canA :: "char" where "canA = CHR ''a''"
definition canB :: "char" where "canB = CHR ''b''"
definition canC :: "char" where "canC = CHR ''c''"
definition canD :: "char" where "canD = CHR ''d''"
definition canE :: "char" where "canE = CHR ''e''"

definition A :: "char set" where  "A = {canA, canB, canC, canD ,canE}"
definition r :: "char Preference_Relation" where
  "r =  {
    (canA, canA), (canB, canA), (canC, canA), (canD, canA), (canE, canA),
    (canB, canB), (canC, canB), (canD, canB), (canE, canB),
    (canC, canC), (canD, canC), (canE, canC),
    (canD, canD), (canE, canD),
    (canE, canE)
  }"


definition voter1_pref2 :: "(char \<times> char) set" where
  "voter1_pref2 = set [(canE, canD), (canE, canA), (canE, canC), (canE, canB), (canD, canA), (canD, canC), (canD, canB), (canA, canC), (canA, canB), (canC, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter2_pref2 :: "(char \<times> char) set" where
  "voter2_pref2 = set [(canE, canB), (canE, canD), (canE, canA), (canE, canC), (canB, canD), (canB, canA), (canB, canC), (canD, canA), (canD, canC), (canA, canC),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter3_pref2 :: "(char \<times> char) set" where
  "voter3_pref2 = set [(canE, canA), (canE, canC), (canE, canD), (canE, canB), (canA, canC), (canA, canD), (canA, canB), (canC, canD), (canC, canB), (canD, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter4_pref2 :: "(char \<times> char) set" where
  "voter4_pref2 = set [(canB, canE), (canB, canA), (canB, canC), (canB, canD), (canE, canA), (canE, canC), (canE, canD), (canA, canC), (canA, canD), (canC, canD),
  (canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter5_pref2 :: "(char \<times> char) set" where
  "voter5_pref2 = set [(canD, canC), (canD, canA), (canD, canE), (canD, canB), (canC, canA), (canC, canE), (canC, canB), (canA, canE), (canA, canB), (canE, canB),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition voter6_pref2 :: "(char \<times> char) set" where
  "voter6_pref2 = set [(canC, canB), (canC, canD), (canC, canA), (canC, canE), (canB, canD), (canB, canA), (canB, canE), (canD, canA), (canD, canE), (canA, canE),
(canA, canA), (canB, canB) ,(canC, canC),(canD, canD),(canE, canE)]"

definition p1 :: "char Profile" where  "p1 = [voter1_pref2, voter2_pref2,voter3_pref2,voter4_pref2,voter5_pref2,voter6_pref2]"



value "IRV_rule_drop r A p1"

end