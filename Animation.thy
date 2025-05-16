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

value "[3 .. 0]"




inductive zip_ind :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> bool" where
  "zip_ind [] _ []" |
  "zip_ind _ [] []" |
  "zip_ind xs ys zs \<Longrightarrow> zip_ind (x#xs) (y#ys) ((x,y)#zs)"

inductive fold_ind :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "fold_ind f [] acc0 acc0" |
  "fold_ind f xs (f x acc) res \<Longrightarrow> fold_ind f (x#xs) acc res"

inductive fold_ind' :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
  "fold_ind' f [] acc0 acc0" |
  "fold_ind' f xs acc res' \<Longrightarrow> fold_ind' f (xs@[x]) acc (f x res')"


lemma fold_ind_eqv: "fold_ind f xs acc0 (fold f xs acc0)"
proof (induction xs arbitrary: f acc0)
  case Nil
  then show ?case using fold.simps(1) fold_ind.simps(1) by fastforce
next
  case (Cons x xs)
  thus ?case by (simp add: fold_ind.intros(2))
qed


lemma fold_ind'_eqv: "fold_ind' f xs acc0 (fold f xs acc0)"
proof (induction xs arbitrary: f acc0 rule: rev_induct) 
  case Nil
  thus ?case using fold.simps(1) fold_ind'.simps(1) by fastforce
next
  case (snoc x xs)
  thus ?case by (simp add: fold_ind'.intros(2))
qed


inductive ibits :: "nat \<Rightarrow> int \<Rightarrow> bool list \<Rightarrow> bool" where
  "is = reverse [0 .. (int N-1)] \<Longrightarrow>
   ids = zip is ds \<Longrightarrow>
   i = fold (\<lambda>(idx, d) acc. (if d then acc + 2^idx else acc)) ids 0 \<Longrightarrow>
   ibits N i ds"

inductive ishr_u :: "nat \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> bool" where
  "i2 \<le> 2^N - 1 \<Longrightarrow>
   ibits N i1 ((replicate (N - k) d1) @ (replicate k d2)) \<Longrightarrow>
   k = i2 mod N \<Longrightarrow>
   ibits N n (replicate k False @ replicate (N - k) d1) \<Longrightarrow>
   ishr_u N i1 i2 n"



end
