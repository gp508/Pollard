theory Pollard
  imports Main
begin
fun Prime :: "nat \<Rightarrow> bool" where
  "Prime x = (if x = 2 then True else if x = 3 then True else if x = 5 then True else False)"
                                        

fun g :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g n x = x^2+1 mod n"

fun getQ :: "nat list \<Rightarrow> nat" where
  "getQ [] = 1"|
  "getQ [x] = 1"|
  "getQ (x # y # xs) = (y - x) * getQ (xs)"

fun getd :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "getd n xs = (let Q = getQ xs in
  gcd Q n)"


function Cycle :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "Cycle i n (x#y#xs) = 
  (let d = (getd n (x#y#xs)) mod n in
  if i > 1000 then xs else
  if 1 < d \<and> d < n then [d,n div d]
  else Cycle (i + 1) n (g n x # g n (g n y) # x # y # []))"
  | "Cycle i n [] = []"
  | "Cycle i n [_] = []"
  by pat_completeness auto


termination Cycle
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun factorise :: "nat list \<Rightarrow> nat list" where
  "factorise (x#xs) = (if Prime x then x#factorise xs else Cycle 1 x [2,g x 2])"|
  "factorise [] = []"

fun Rho :: "nat \<Rightarrow> nat list" where
  "Rho x = (if Prime(x) then [x]
   else factorise [x])"


value "getd 16 [2,5]"
value "getQ [2,5]"
value "Rho 21"

end