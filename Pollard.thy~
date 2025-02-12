theory Pollard
  imports Main
  "HOL-Library.Code_Target_Numeral" 
  "HOL-Computational_Algebra.Primes"

begin
definition primeset :: "nat set" where
  "primeset = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293}"

fun Prime :: "nat \<Rightarrow> bool" where
  "Prime x = (if x \<in> primeset then True else False)"
                                        

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

 (if Prime p \<and> prime d then [d,n div d]
  else if Prime p then p # Cycle (i+1) d [2, g d 2]
  else if Prime d then d # Cycle (i+1) p [2, g p 2]
  else Cycle (i+1) d [2, g d 2] @  Cycle (i+1) p [2, g p 2])

  else Cycle (i + 1) n (g n x # g n (g n y) # []))"
  | "Cycle i n [] = []"
  | "Cycle i n [_] = []"
  by pat_completeness auto


termination Cycle      
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun factorise :: "nat list \<Rightarrow> nat list" where
  "factorise (x#xs) = (if Prime x then x#factorise xs else Cycle 1 x [2,g x 2])@factorise xs"|
  "factorise [] = []"

fun Rho :: "nat \<Rightarrow> nat list" where
  "Rho x = (if Prime(x) then [x]
   else factorise [x])"

value "Rho 6567"

export_code g getQ getd Cycle factorise Rho in SML

end