theory Chapter03
  imports Main
begin

declare [[names_short]]

section "Chapter 3"

datatype t = 
  TTrue
  | FFalse
  | Zero ("0")
  | Succ t
  | Pred t
  | IsZero t
  | IfElse t t t ("If _ Then _ Else _" [85,85,85] 80)

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

fun depth :: "t \<Rightarrow> nat" where
"depth TTrue = 1" |
"depth FFalse = 1" |
"depth Zero = 1" |
"depth (Succ t1) = 1 + size t1" |
"depth (Pred t1) = 1 + size t1" |
"depth (IsZero t1) = 1 + size t1" |
"depth (IfElse t1 t2 t3) = Max {depth t1, depth t2, depth t3}" 

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

(* TODO: 3.3.4 *)

end