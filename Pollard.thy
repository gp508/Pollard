theory Pollard
  imports Main
  "HOL-Library.Code_Target_Numeral" 
  "HOL-Computational_Algebra.Primes"
  "HOL.GCD"

begin                                        

fun g :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g n x = (x^2+1) mod n"

fun getQ :: "nat list \<Rightarrow> nat" where
  "getQ [] = 1"|
  "getQ [x] = 1"|
  "getQ (x # y # xs) = (y - x) * getQ (xs)"

fun getd :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "getd n xs = (let Q = getQ xs mod n in
  gcd Q n)"

(*function for full factorisation*)
function Cycle_full :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "Cycle_full i n (x#y#xs) = 
  (let d = (getd n (x#y#xs)) mod n in
  let p = n div d in
  if i > 1000 then xs else

  if 1 < d \<and> d < n then
 (if prime p \<and> prime d then [d,n div d]
  else if prime p then p # Cycle_full (i+1) d [2,4]
  else if prime d then d # Cycle_full (i+1) p [2,4]
  else Cycle_full (i+1) d [2, 4] @  Cycle_full (i+1) p [2,4])

  else Cycle_full (i + 1) n (g n x # g n (g n y) # []))"
  | "Cycle_full i n [] = []"
  | "Cycle_full i n [_] = []"
  by pat_completeness auto

(*Simplified function*)
function Cycle:: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "Cycle i n (x#y#xs) = 
  (let d = (getd n (x#y#xs)) mod n in
  if i > 1000 then 1 else

  if 1 < d \<and> d < n then d

  else Cycle (i + 1) n (g n x # g n (g n y) # []))"
  | "Cycle i n [] = 1"
  | "Cycle i n [_] = 1"
  by pat_completeness auto


termination Cycle
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

termination Cycle_full
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun Rho :: "nat \<Rightarrow> nat" where
  "Rho x = (if prime(x) then x
   else Cycle 1 x [2,5])"

value "Rho (10457*12789)"
value "Cycle_full 1  (10457*10559) [2,2]"
(*Helper lemmas*)

lemma getd_dvd: assumes "getd n xs = p" shows "p dvd n"
proof -
  have "getd n xs = gcd (getQ xs mod n) n" by auto
  have "... dvd n" using gcd_dvd2 by blast
  show ?thesis using assms by auto
qed



lemma Cycle_dvd: assumes "Cycle 1 n [2,2] = p" shows "p dvd n"
proof(cases "p=1")
  case True
  then show ?thesis by simp
  case False
  

(*Main lemmas*)

lemma Correct: assumes "Rho n = p" shows "p dvd n"



end