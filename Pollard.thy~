theory Pollard
  imports Main
begin
fun Prime :: "nat \<Rightarrow> bool" where
  "Prime x = (if x = 2 then True else if x = 3 then True else False)"
                                        

fun g :: "nat \<Rightarrow> nat" where
  "g x = x^2+1"

fun getQ :: "nat list \<Rightarrow> nat" where
  "getQ [] = 1"|
  "getQ [x] = 1"|
  "getQ (x # y # xs) = (y - x) * getQ (y # xs)"

fun getd :: "nat \<Rightarrow> nat list \<Rightarrow> nat" where
  "getd n xs = (let Q = getQ xs in
  gcd Q n)"


function Cycle :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "Cycle i n (x#y#xs) = 
  (let d = (getd n xs) mod n in
  if i > 1000 then xs else
  if i < d \<and> d < n then [d,n div d]
  else Cycle (i + 1) n (g x # g (g x) # x # y # []))"
  | "Cycle i n [] = []"
  | "Cycle i n [_] = []"
  by pat_completeness auto


termination Cycle
proof (relation "measure (\<lambda>(i, xs). 1001 - i)")
qed auto

fun checkQ :: "nat list \<Rightarrow> nat list" where
  "checkQ (n#xs) =
     (let z = gcd (getQ xs) n in
      if 1 < z \<and> z < n then [z] else xs)"

fun factorise :: "nat list \<Rightarrow> nat list" where
  "factorise (x#xs) = (if Prime x then x#factorise xs else Cycle 1 x [2,2])"|
  "factorise [] = []"

fun Rho :: "nat \<Rightarrow> nat list" where
  "Rho x = (if Prime(x) then [x]
   else factorise [x])"


value "Rho 12"

end