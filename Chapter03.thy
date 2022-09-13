theory Chapter03
  imports Main
begin

declare [[names_short]]

section "Chapter 3"

datatype t = 
  TTrue
  | FFalse
  | Zero 
  | Succ t
  | Pred t
  | IsZero t
  | IfElse t t t ("If _ Then _ Else _" [85,85,85] 80)

(* 3.2.5 *)
fun terms :: "nat \<Rightarrow> t set" where
"terms 0 = {}" |
"terms (Suc n) = 
  {TTrue,FFalse,Zero}
  \<union> {Succ t | t. t \<in> terms n} \<union> {Pred t | t. t \<in> terms n} \<union> {IsZero t | t. t \<in> terms n}
  \<union> {IfElse t1 t2 t3 | t1 t2 t3. let termsn = terms n in t1 \<in> termsn \<and> t2 \<in> termsn \<and> t3 \<in> termsn}"

lemma succ: "Succ t \<in> terms (Suc n) \<longleftrightarrow> t \<in> terms n" 
  by (induction n) auto

lemma pred: "Pred t \<in> terms (Suc n) \<longleftrightarrow> t \<in> terms n" 
  by (induction n) auto

lemma iszero: "IsZero t \<in> terms (Suc n) \<longleftrightarrow> t \<in> terms n" 
  by (induction n) auto

lemma ifelse: "IfElse t1 t2 t3 \<in> terms (Suc n) \<longleftrightarrow> t1 \<in> terms n \<and> t2 \<in> terms n \<and> t3 \<in> terms n" 
  by (induction n) auto
thm terms.simps
lemma "terms n \<subseteq> terms (Suc n)"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "t \<in> terms (Suc n) \<Longrightarrow> t \<in> terms (Suc (Suc n))" for t
  proof (induction t)
    case (Succ t)
    then show ?case
      using Suc.IH
      by (meson in_mono succ) 
  next
    case (Pred t)
    then show ?case 
      using Suc.IH
      by (meson in_mono pred) 
  next
    case (IsZero t)
    then show ?case 
      using Suc.IH
      by (meson in_mono iszero) 
  next
    case (IfElse t1 t2 t3)
    then show ?case 
      using Suc.IH
      by (meson in_mono ifelse) 
  qed auto
  then show ?case 
    by blast
qed

(* 3.3.1 *)
fun Consts :: "t \<Rightarrow> t set" where
"Consts TTrue = {TTrue}" |
"Consts FFalse = {FFalse}" |
"Consts Zero = {Zero}" |
"Consts (Succ t1) = Consts t1" |
"Consts (Pred t1) = Consts t1" |
"Consts (IsZero t1) = Consts t1" |
"Consts (IfElse t1 t2 t3) = Consts t1 \<union> Consts t2 \<union> Consts t3" 

(* 3.3.2 *)
fun size :: "t \<Rightarrow> nat" where
"size TTrue = 1" |
"size FFalse = 1" |
"size Zero = 1" |
"size (Succ t1) = 1 + size t1" |
"size (Pred t1) = 1 + size t1" |
"size (IsZero t1) = 1 + size t1" |
"size (IfElse t1 t2 t3) = 1 + size t1 + size t2 + size t3" 

lemma size_not_zero: "size t > 0"
  by (cases t) auto

fun depth :: "t \<Rightarrow> nat" where
"depth TTrue = 1" |
"depth FFalse = 1" |
"depth Zero = 1" |
"depth (Succ t1) = 1 + depth t1" |
"depth (Pred t1) = 1 + depth t1" |
"depth (IsZero t1) = 1 + depth t1" |
"depth (IfElse t1 t2 t3) = Max {depth t1, depth t2, depth t3}" 

lemma depth_not_zero: "depth t > 0"
  by (induction t) auto

(* 3.3.3 *)
lemma "card (Consts t) \<le> size t"
proof (induction t)
  case (IfElse t1 t2 t3)
  have "card (Consts (IfElse t1 t2 t3)) = card (Consts t1 \<union> Consts t2 \<union> Consts t3)" 
    by simp
  also have "\<dots> \<le> card (Consts t1) + card (Consts t2) + card (Consts t3)"
    by (metis add_mono_thms_linordered_semiring(3) card_Un_le order_trans) 
  also have "\<dots> \<le> size t1 + size t2 + size t3" 
    using IfElse.IH by (simp add: add_mono)
  also have "\<dots> \<le> size (IfElse t1 t2 t3)" 
    by simp
  finally show ?case .
qed auto

(* 3.3.4 *)
lemma raw_induct[case_names TTrue FFalse Zero Succ Pred IsZero IfElse]: 
  assumes "P TTrue" 
    and "P FFalse"
    and "P Zero"
    and "\<And>t. P (Succ t)"
    and "\<And>t. P (Pred t)" 
    and "\<And>t. P (IsZero t)"
    and "\<And>t1 t2 t3. P (IfElse t1 t2 t3)"
  shows "P t"
  using assms
  by (cases t) auto

lemma depth_induct: 
  "(\<And>r::t. depth r < depth s \<Longrightarrow> P r) \<Longrightarrow> P s"
  sorry

lemma size_induct: 
  "(\<And>r::t. size r < size s \<Longrightarrow> P r) \<Longrightarrow> P s"
  sorry

end