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
  else if prime p then p # Cycle (i+1) d [2, g d 2]
  else if prime d then d # Cycle (i+1) p [2, g p 2]
  else Cycle (i+1) d [2, g d 2] @  Cycle (i+1) p [2, g p 2])

  else Cycle (i + 1) n (g n x # g n (g n y) # []))"
  | "Cycle i n [] = []"
  | "Cycle i n [_] = []"
  by pat_completeness auto


termination Cycle      
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun factorise :: "nat list \<Rightarrow> nat list" where
  "factorise (x#xs) = (if prime x then x#factorise xs else Cycle 1 x [2,g x 2])@factorise xs"|
  "factorise [] = []"

fun Rho :: "nat \<Rightarrow> nat list" where
  "Rho x = (if prime(x) then [x]
   else factorise [x])"

value "Rho 8051"

end