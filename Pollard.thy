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


termination Cycle_full
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

(*Simplified function*)
fun Cycle:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "Cycle i n x y = 
  (let d = (getd n [x,y]) mod n in
  if i = 0 then 1 else

  if 1 < d \<and> d < n then d

  else Cycle (i - 1) n (g n x) (g n (g n y)))"

fun Rho :: "nat \<Rightarrow> nat" where
  "Rho n = (if prime(n) then n
   else Cycle 1000 n 2 2)"

(*Helper lemmas*)

lemma getd_dvd: assumes "getd n xs = p" shows "p dvd n"
proof -
  have "getd n xs = gcd (getQ xs mod n) n" by auto
  then have "... dvd n" using gcd_dvd2 by blast
  then show ?thesis using assms by auto
qed

lemma Cycle_dvd:  assumes "Cycle i n x y = p" and "0 < n" shows "p dvd n"
proof(insert assms, induction i arbitrary: x y)
  case 0
  then show ?case by(auto)
next
  case (Suc i)
  then show ?case 
  proof(cases "let d = (getd n [x,y]) mod n in 1 < d \<and> d < n")
    case True
    then show ?thesis 
      using Suc.prems apply(simp add:Let_def) 
      using getd_dvd by (metis gcd_dvd2 gcd_le2_nat less_nat_zero_code mod_less mod_self order_le_less) 
  next
    case False
    then show ?thesis 
      using Suc by(simp add:Let_def) 
  qed
qed

(*Main lemmas*)


lemma Correct: assumes "Rho n = p" shows "p dvd n"
proof(cases "prime n")
  case True
  then show ?thesis using assms by auto
next
  case False
  then have "Rho n = Cycle 1000 n 2 2" by simp
  then show ?thesis using Cycle_dvd
    by (metis assms gcd_nat.extremum gr0I)
qed
end