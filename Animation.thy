theory Animation

imports Main

begin


inductive append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "append [] ys ys" |
  "append xs ys zs \<Longrightarrow> append (x#xs) ys (x#zs)"


code_pred append .

values "{(xs, ys). append xs ys [1::nat,2,3,4,5]}"


inductive append' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "append' xs ys (xs @ ys)"


inductive clz :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "clz k (replicate k false)" |  (* all 0 *)
  "clz k (replicate k false @ [true] @ bs)"  (* leading 0s followed by 1 and something else *)

inductive clz' :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "bs = replicate k false \<Longrightarrow> clz' k bs" |
  "bs = replicate k false @ [true] @ bs' \<Longrightarrow> clz' k bs"


inductive sat_u :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> bool" where
  "i < 0 \<Longrightarrow> sat_u N i 0" |
  "i > 2^N - 1 \<Longrightarrow> sat_u N i (2^N - 1)" |
  "i \<ge> 0 \<Longrightarrow> i \<le> 2^N - 1 \<Longrightarrow> sat_u N i (nat i)"


end
