theory Pollard
  imports Main
  "HOL-Library.Code_Target_Numeral" 
  "HOL-Computational_Algebra.Primes"

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


function Cycle :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "Cycle i n (x#y#xs) = 
  (let d = (getd n (x#y#xs)) mod n in
  let p = n div d in
  if i > 1000 then xs else

  if 1 < d \<and> d < n then
 (if prime p \<and> prime d then [d,n div d]
  else if prime p then p # Cycle (i+1) d [2,4]
  else if prime d then d # Cycle (i+1) p [2,4]
  else Cycle (i+1) d [2, 4] @  Cycle (i+1) p [2,4])

  else Cycle (i + 1) n (g n x # g n (g n y) # []))"
  | "Cycle i n [] = []"
  | "Cycle i n [_] = []"
  by pat_completeness auto


termination Cycle      
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun factorise :: "nat list \<Rightarrow> nat list" where
  "factorise (x#xs) =  (Cycle 1 x [2,4])@factorise xs"|
  "factorise [] = []"

fun Rho :: "nat \<Rightarrow> nat list" where
  "Rho x = (if prime(x) then [x]
   else factorise [x])"

(*Helper lemmas*)

lemma prime_rho: "prime n \<Longrightarrow> set (Rho n) = set([n])"
  by simp

lemma set_element: "x \<in> set [n] \<Longrightarrow> x = n"
  by simp

lemma Cycle_prime_help: assumes "d = getd n [2,4]" and "p = n div d" and "x \<in> set (Cycle 1 n [2,4])" shows "prime x"
proof(insert assms, cases "prime p \<and> prime d")
  case True
  have "Cycle 1 n [2,4] = d # Cycle (i+1) p [2,4]" by (auto)


lemma Cycle_prime: assumes "x \<in> set (Cycle 1 n [2,4])" shows "prime x"
proof(insert assms)
  obtain "d = getd n [2,4]" by auto
  then show ?thesis sorry
  

value "Rho 4278335778"

(*Main lemmas*)

lemma Correct: assumes "prime p" and "prime q" and "n = p * q" and "p \<noteq> q" shows "p \<in> set(Rho n)"
proof (insert assms,cases "n=0")
  case True
  then have "p=0" using assms(2) assms(3) by auto 
  then show ?thesis using assms(1) by auto
next
  case False
  then show ?thesis
qed


end