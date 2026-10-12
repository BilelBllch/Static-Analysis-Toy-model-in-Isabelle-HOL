theory san
imports Main  "~~/src/HOL/Library/Code_Target_Int" "set"
begin

(* Types des expressions, conditions et programmes (statement) *)
datatype expression= Constant int | Variable string | Sum expression expression | Sub expression expression

datatype condition= Eq expression expression

datatype statement= Seq statement statement | 
                    Aff string expression | 
                    Read string | 
                    Print expression | 
                    Exec expression | 
                    If condition statement statement |
                    Skip
(* Un exemple d'expression *)

(* expr1= (x-10) *)
definition "expr1= (Sub (Variable ''x'') (Constant 10))"


(* Des exemples de programmes *)

(* p1= exec(0) *)
definition "p1= Exec (Constant 0)"

(* p2= {
        print(10)
        exec(0+0)
       }
*)

definition "p2= (Seq (Print (Constant 10)) (Exec (Sum (Constant 0) (Constant 0))))"

(* p3= {
         x:=0
         exec(x)
       }
*)

definition "p3= (Seq (Aff ''x'' (Constant 0)) (Exec (Variable ''x'')))"

(* p4= {
         read(x)
         print(x+1)
       }
*)
definition "p4= (Seq (Read ''x'') (Print (Sum (Variable ''x'') (Constant 1))))"


(* Le type des evenements soit X: execute, soit P: print *)
datatype event= X int | P int

(* les flux de sortie, d'entree et les tables de symboles *)

type_synonym outchan= "event list"
definition "el1= [X 1, P 10, X 0, P 20]"                   (* Un exemple de flux de sortie *)

type_synonym inchan= "int list"           
definition "il1= [1,-2,10]"                                (* Un exemple de flux d'entree [1,-2,10]              *)

type_synonym symTable= "(string * int) list"

(* La fonction (partielle) de recherche dans une liste de couple, par exemple une table de symbole *)
(*datatype 'a option= None | Some 'a*)

fun assoc:: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option"
where
"assoc _ [] = None" |
"assoc x1 ((x,y)#xs)= (if x=x1 then Some(y) else (assoc x1 xs))"

(* Exemples de recherche dans une table de symboles *)

value "assoc ''x'' st1"     (* quand la variable est dans la table st1 *)
value "assoc ''z'' st1"     (* quand la variable n'est pas dans la table st1 *)


(* Evaluation des expressions par rapport a une table de symboles *)
fun evalE:: "expression \<Rightarrow> symTable \<Rightarrow> int"
where
"evalE (Constant s) e = s" |
"evalE (Variable s) e= (case (assoc s e) of None \<Rightarrow> -1 | Some(y) \<Rightarrow> y)" |
"evalE (Sum e1 e2) e= ((evalE e1 e) + (evalE e2 e))" |
"evalE (Sub e1 e2) e= ((evalE e1 e) - (evalE e2 e))" 

(* Exemple d'évaluation d'expression *)

value "evalE expr1 st1"

(* Evaluation des conditions par rapport a une table de symboles *)
fun evalC:: "condition \<Rightarrow> symTable \<Rightarrow> bool"
where
"evalC (Eq e1 e2) t= ((evalE e1 t) = (evalE e2 t))"

(* Evaluation d'un programme par rapport a une table des symboles, a un flux d'entree et un flux de sortie. 
   Rend un triplet: nouvelle table des symboles, nouveaux flux d'entree et sortie *)
fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"
where
"evalS Skip x=x" |
"evalS (Aff s e)  (t,inch,outch)=  (((s,(evalE e t))#t),inch,outch)" |
"evalS (If c s1 s2)  (t,inch,outch)=  (if (evalC c t) then (evalS s1 (t,inch,outch)) else (evalS s2 (t,inch,outch)))" |
"evalS (Seq s1 s2) (t,inch,outch)= 
    (let (t2,inch2,outch2)= (evalS s1 (t,inch,outch)) in
        evalS s2 (t2,inch2,outch2))" |
"evalS (Read _) (t,[],outch)= (t,[],outch)" |
"evalS (Read s) (t,(x#xs),outch)= (((s,x)#t),xs,outch)" |
"evalS (Print e) (t,inch,outch)= (t,inch,((P (evalE e t))#outch))" |
"evalS (Exec e) (t,inch,outch)= 
  (let res= evalE e t in
   (t,inch,((X res)#outch)))"



(* Exemples d'évaluation de programmes *)
(* Les programmes p1, p2, p3, p4 ont été définis plus haut *)
(* p1= exec(0) *)

value "evalS p1 ([],[],[])"

(* ------------------------------------ *)
(* p2= {
        print(10)
        exec(0+0)
       }
*)

value "evalS p2 ([],[],[])"

(* ------------------------------------ *)
(* p3= {
         x:=0
         exec(x)
       }
*)

value "evalS p3 ([],[],[])"

(* ------------------------------------ *)
(* p4= {
         read(x)
         print(x+1)
       }
*)

value "evalS p4 ([],[10],[])"


definition "bad1= (Exec (Constant 0))"
definition "bad2= (Exec (Sub (Constant 2) (Constant 2)))"
definition "bad3= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x'')) (Exec (Sub (Variable ''x'') (Constant 1)))))"
definition "bad4= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) Skip (Aff ''y'' (Constant 1))) (Exec (Sum (Variable ''y'') (Constant 1)))))"
definition "bad5= (Seq (Read ''x'') (Seq (Aff ''y'' (Sum (Variable ''x'') (Constant 2))) (Seq (If (Eq (Variable ''x'') (Sub (Constant 0) (Constant 1))) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x'')))) (Seq (Aff ''x'' (Sub (Variable ''x'') (Constant 2))) (Aff ''y'' (Sub (Variable ''y'') (Variable ''x''))))) (Exec (Variable ''y'')))))"
definition "bad6= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 1)) (Aff ''z'' (Constant 0))) (Exec (Variable ''z''))))"
definition "bad7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 1))) (Exec (Variable ''z''))))"
definition "bad8= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Variable ''x'') (Variable ''y'')) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "bad9= (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 2))) (If (Eq (Variable ''x'') (Variable ''z'')) (Exec (Constant 1)) (Exec (Constant 0))))))"

definition "ok0= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Print (Sum (Variable ''y'') (Variable ''x'')))
(Print (Variable ''x''))
) (Print (Variable ''y''))
) (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 2)) (Seq (Print (Variable ''x''))
 (Seq (Aff ''x'' (Constant 3)) (Seq (Print (Variable ''x''))
 (Seq (Read ''y'') (Seq (If (Eq (Variable ''y'') (Constant 0)) (Aff ''z'' (Sum (Variable ''x'') (Variable ''x''))) (Aff ''z'' (Sub (Variable ''x'') (Variable ''y'')))) (Print (Variable ''z''))
)))))))))))"
definition "ok1= (Seq (Aff ''x'' (Constant 1)) (Seq (Print (Sum (Variable ''x'') (Variable ''x'')))
 (Seq (Exec (Constant 10)) (Seq (Read ''y'') (If (Eq (Variable ''y'') (Constant 0)) (Exec (Constant 1)) (Exec (Constant 2)))))))"
definition "ok2= (Exec (Variable ''y''))"
definition "ok3= (Seq (Read ''x'') (Exec (Sum (Variable ''y'') (Constant 2))))"
definition "ok4= (Seq (Aff ''x'' (Constant 0)) (Seq (Aff ''x'' (Sum (Variable ''x'') (Constant 20))) (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''z'' (Constant 0)) (Aff ''z'' (Constant 4))) (Seq (Exec (Variable ''z'')) (Exec (Variable ''x''))))))"
definition "ok5= (Seq (Read ''x'') (Seq (Aff ''x'' (Constant 4)) (Exec (Variable ''x''))))"
definition "ok6= (Seq (If (Eq (Constant 1) (Constant 2)) (Aff ''x'' (Constant 0)) (Aff ''x'' (Constant 1))) (Exec (Variable ''x'')))"
definition "ok7= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (If (Eq (Variable ''x'') (Constant 4)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 1)))) (Exec (Variable ''x''))))"
definition "ok8= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Constant 1)) (Aff ''x'' (Constant 2))) (Exec (Sub (Variable ''x'') (Constant 3)))))"
definition "ok9= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok10= (Seq (Read ''x'') (If (Eq (Variable ''x'') (Constant 0)) (Exec (Constant 1)) (Exec (Variable ''x''))))"
definition "ok11= (Seq (Read ''x'') (Seq (If (Eq (Variable ''x'') (Constant 0)) (Aff ''x'' (Sum (Variable ''x'') (Constant 1))) Skip) (Exec (Variable ''x''))))"
definition "ok12= (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''z'') (If (Eq (Variable ''z'') (Constant 0)) (Exec (Variable ''y'')) (Exec (Variable ''z'')))))"
definition "ok13= (Seq (Aff ''z'' (Constant 4)) (Seq (Aff ''x'' (Constant 1)) (Seq (Read ''y'') (Seq (Aff ''x'' (Sum (Variable ''x'') (Sum (Variable ''z'') (Variable ''x'')))) (Seq (Aff ''z'' (Sum (Variable ''z'') (Variable ''x''))) (Seq (If (Eq (Variable ''y'') (Constant 1)) (Aff ''x'' (Sub (Variable ''x'') (Variable ''y''))) Skip) (Seq (If (Eq (Variable ''y'') (Constant 0)) (Seq (Aff ''y'' (Sum (Variable ''y'') (Constant 1))) (Exec (Variable ''x''))) Skip) (Exec (Variable ''y'')))))))))"
definition "ok14= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"
definition "ok15= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Constant 0)) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Sum (Variable ''y'') (Sum (Variable ''y'') (Variable ''x''))))))))"
definition "ok16= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Variable ''x'') (Variable ''y'')) (Sum (Variable ''y'') (Variable ''x''))) (Exec (Constant 1)) (Exec (Constant 0)))))"
definition "ok17= (Seq (Read ''x'') (Seq (Read ''y'') (If (Eq (Sum (Constant 10) (Sub (Sum (Variable ''x'') (Variable ''y'')) (Constant 3))) (Sub (Sum (Variable ''y'') (Variable ''x'')) (Sub (Variable ''x'') (Sum (Variable ''x'') (Constant 7))))) (Exec (Constant 1)) (Exec (Sum (Variable ''x'') (Variable ''y''))))))"

(* Le TP commence ici! *)
(* TODO: BAD, san_Inter0, lemme de correction *)

fun BAD::"(symTable * inchan * outchan) \<Rightarrow> bool"
  where
"BAD (_, _, outs) = (List.member outs (X 0))"


(* Si san_Inter accepte un programme alors son évaluation, quelles que soient les entrées utilisateur (inchan)
   ne provoquera pas d'exec(0) *)
fun san_Inter0::"statement \<Rightarrow> bool"
  where
"san_Inter0 (Exec _) = False" |
"san_Inter0 (Seq s1 s2) = (san_Inter0 s1 \<and> san_Inter0 s2)" |
"san_Inter0 (If c st sf) = (san_Inter0 st \<and> san_Inter0 sf)" |
"san_Inter0 _ = True"

lemma rw:"s = k \<longrightarrow> san_Inter0 s = san_Inter0 k"
  apply auto
  done

(*fun evalS:: "statement \<Rightarrow> (symTable * inchan * outchan) \<Rightarrow> (symTable * inchan * outchan)"*)
lemma correction_seq0: "s=(Seq s1 s2) \<longrightarrow> san_Inter0 s \<longrightarrow> (\<forall> sytable. \<forall> ins.  \<not>(BAD (evalS s (sytable, ins, []))))"
  
  sorry

lemma correction_aff0: "s=(Aff  s1 s2) \<longrightarrow> san_Inter0 s \<longrightarrow> (\<forall> sytable. \<forall> ins.  \<not>(BAD (evalS s (sytable, ins, []))))"
  sorry

lemma correction0: "san_Inter0 s \<longrightarrow> (\<forall> sytable. \<forall> ins.  \<not>(BAD (evalS s (sytable, ins, []))))"
  apply (case_tac "s")
  
  using correction_seq0 apply auto[1]
  using correction_aff0 apply auto[1]
  sorry
  
  

fun san_Inter1::"statement \<Rightarrow> bool"
  where
"san_Inter1 (Exec (Constant x)) = (x\<noteq>0)" |
"san_Inter1 (Exec _) = False" |
"san_Inter1 (Seq s1 s2) = ((san_Inter1 s1) \<and> (san_Inter1 s2))" |
"san_Inter1 (If c st sf) = ((san_Inter1 st) \<and> (san_Inter1 sf))" |
"san_Inter1 _ = True"


lemma correction1: "san_Inter1 s \<longrightarrow> (\<forall> sytable. \<forall> ins.  \<not>(BAD (evalS s (sytable, ins, []))))"
  (*nitpick[timeout=120]
  quickcheck[tester=narrowing,size=5,timeout=120]*)
  apply (case_tac "s")
  sorry

(* 
Isabelle fournit un type Interval que je vais me permettre d'utiliser
https://isabelle.in.tum.de/library/HOL/HOL-Real_Asymp/HOL-Library.Interval.html
*)(* ========== Domaine abstrait : Intervalles ========== *)

datatype absExpr_Inter = Interval int int | TopEval

fun contains_zero :: "absExpr_Inter \<Rightarrow> bool"
where
"contains_zero (Interval low high) = (low \<le> 0 \<and> 0 \<le> high)" |
"contains_zero TopEval = True"

fun interval_add :: "absExpr_Inter \<Rightarrow> absExpr_Inter \<Rightarrow> absExpr_Inter"
where
"interval_add TopEval _ = TopEval" |
"interval_add _ TopEval = TopEval" |
"interval_add (Interval l1 h1) (Interval l2 h2) = Interval (l1 + l2) (h1 + h2)"

fun interval_sub :: "absExpr_Inter \<Rightarrow> absExpr_Inter \<Rightarrow> absExpr_Inter"
where
"interval_sub TopEval _ = TopEval" |
"interval_sub _ TopEval = TopEval" |
"interval_sub (Interval l1 h1) (Interval l2 h2) = Interval (l1 - h2) (h1 - l2)"

fun union_absExpr_Inter :: "absExpr_Inter \<Rightarrow> absExpr_Inter \<Rightarrow> absExpr_Inter"
where
"union_absExpr_Inter TopEval _ = TopEval" |
"union_absExpr_Inter _ TopEval = TopEval" |
"union_absExpr_Inter (Interval l1 h1) (Interval l2 h2) = Interval (min l1 l2) (max h1 h2)"

type_synonym absSymTable = "(string * absExpr_Inter) list"

fun absSymTable_assoc_Inter :: "string \<Rightarrow> absSymTable \<Rightarrow> absExpr_Inter"
where
"absSymTable_assoc_Inter _ [] = Interval (-1) (-1)" |  (* Valeur par défaut : -1 *)
"absSymTable_assoc_Inter x1 ((x,y)#xs) = (if x = x1 then y else (absSymTable_assoc_Inter x1 xs))"

fun abstract_evalE_Inter :: "expression \<Rightarrow> absSymTable \<Rightarrow> absExpr_Inter"
where
"abstract_evalE_Inter (Constant x) _ = Interval x x" |
"abstract_evalE_Inter (Variable var) absST = absSymTable_assoc_Inter var absST" |
"abstract_evalE_Inter (expression.Sum e1 e2) absST = 
   interval_add (abstract_evalE_Inter e1 absST) (abstract_evalE_Inter e2 absST)" |
"abstract_evalE_Inter (expression.Sub e1 e2) absST = 
   interval_sub (abstract_evalE_Inter e1 absST) (abstract_evalE_Inter e2 absST)"

datatype absCondition = AbsTrue | AbsFalse | TopCondition

fun intervals_equal :: "absExpr_Inter \<Rightarrow> absExpr_Inter \<Rightarrow> bool"
where
"intervals_equal (Interval l1 h1) (Interval l2 h2) = 
   (l1 = h1 \<and> l2 = h2 \<and> l1 = l2)" |
"intervals_equal _ _ = False"

fun intervals_differ :: "absExpr_Inter \<Rightarrow> absExpr_Inter \<Rightarrow> bool"
where
"intervals_differ TopEval _ = False" |
"intervals_differ _ TopEval = False" |
"intervals_differ (Interval l1 h1) (Interval l2 h2) = (h1 < l2 \<or> h2 < l1)"

fun abstract_evalC_Inter :: "condition \<Rightarrow> absSymTable \<Rightarrow> absCondition"
where
"abstract_evalC_Inter (Eq e1 e2) absST = (
       if intervals_equal (abstract_evalE_Inter e1 absST) (abstract_evalE_Inter e2 absST)
         then AbsTrue
       else (
        if intervals_differ (abstract_evalE_Inter e1 absST) (abstract_evalE_Inter e2 absST)
           then AbsFalse
         else TopCondition
       )
     )"

fun get_vars_inbranches :: "absSymTable \<Rightarrow> absSymTable \<Rightarrow> string list"
where
"get_vars_inbranches env1 env2 = clean (map fst env1 @ map fst env2)"

fun branch_absSymTable :: "absSymTable \<Rightarrow> absSymTable \<Rightarrow> absSymTable"
where
"branch_absSymTable env1 env2 = 
   map (\<lambda>v. (v, union_absExpr_Inter (absSymTable_assoc_Inter v env1) (absSymTable_assoc_Inter v env2))) 
       (get_vars_inbranches env1 env2)"

fun absSymTable_record_Inter :: "statement \<Rightarrow> absSymTable \<Rightarrow> absSymTable"
where
"absSymTable_record_Inter (Exec _) absST = absST" |
"absSymTable_record_Inter (Seq s1 s2) absST = 
   absSymTable_record_Inter s2 (absSymTable_record_Inter s1 absST)" |
"absSymTable_record_Inter (Aff v x) absST = (v, abstract_evalE_Inter x absST) # absST" |
"absSymTable_record_Inter (Read v) absST = (v, TopEval) # absST" |
"absSymTable_record_Inter (statement.If c s1 s2) absST = 
   (case abstract_evalC_Inter c absST of 
      AbsTrue \<Rightarrow> absSymTable_record_Inter s1 absST 
    | AbsFalse \<Rightarrow> absSymTable_record_Inter s2 absST
    | TopCondition \<Rightarrow> branch_absSymTable (absSymTable_record_Inter s1 absST) 
                                       (absSymTable_record_Inter s2 absST))" |
"absSymTable_record_Inter (Print v) absST = absST" |
"absSymTable_record_Inter Skip absST = absST"
(* ========== Analyseur statique ========== *)

(* Vérification récursive *)
fun san_rec_Inter :: "statement \<Rightarrow> absSymTable \<Rightarrow> bool"
where
"san_rec_Inter (Exec exp) absST = (\<not>contains_zero (abstract_evalE_Inter exp absST))" |
"san_rec_Inter (Seq s1 s2) absST =  
   (san_rec_Inter s1 absST \<and> san_rec_Inter s2 (absSymTable_record_Inter s1 absST))" |
"san_rec_Inter (Aff v x) absST = True" |
"san_rec_Inter (Read v) absST = True" |
"san_rec_Inter (Print v) absST = True" |
"san_rec_Inter (statement.If c s1 s2) absST = 
   (san_rec_Inter s1 absST \<and> san_rec_Inter s2 absST)" |
"san_rec_Inter Skip absST = True"

(* Point d'entrée de l'analyseur *)
fun san :: "statement \<Rightarrow> bool"
where
"san prog = san_rec_Inter prog []"

(* ----- Restriction de l'export Scala (Isabelle 2023) -------*)
(* ! ! !  NE PAS MODIFIER ! ! ! *)
(* Suppression de l'export des abstract datatypes (Isabelle 2023) *)
code_reserved Scala
  expression condition statement 
code_printing
   type_constructor expression \<rightharpoonup> (Scala) "expression"
  | constant Constant \<rightharpoonup> (Scala) "Constant"
  | constant Variable \<rightharpoonup> (Scala) "Variable"
  | constant Sum \<rightharpoonup> (Scala) "Sum"
  | constant Sub \<rightharpoonup> (Scala) "Sub"  

  | type_constructor condition \<rightharpoonup> (Scala) "condition"
  | constant Eq \<rightharpoonup> (Scala) "Eq"

  | type_constructor statement \<rightharpoonup> (Scala) "statement"
  | constant Seq \<rightharpoonup> (Scala) "Seq"
  | constant Aff \<rightharpoonup> (Scala) "Aff"
  | constant Read \<rightharpoonup> (Scala) "Read"
  | constant Print \<rightharpoonup> (Scala) "Print"
  | constant Exec \<rightharpoonup> (Scala) "Exec"
  | constant If \<rightharpoonup> (Scala) "If"
  | constant Skip \<rightharpoonup> (Scala) "Skip"
  | code_module "" \<rightharpoonup> (Scala) 
\<open>// Code generated by Isabelle
package tp67

import utilities.Datatype._
// automatic conversion of utilities.Datatype.Int.int to Int.int
object AutomaticConversion {
  implicit def int2int(i: utilities.Datatype.Int.int): Int.int =
    i match {
      case utilities.Datatype.Int.int_of_integer(i) => Int.int_of_integer(i)
    }

  def bit_cut_integer(k: BigInt): (BigInt, Boolean) =
    (if (k == BigInt(0)) (BigInt(0), false)
     else {
       val (r, s): (BigInt, BigInt) =
         (
             (k: BigInt) =>
               (l: BigInt) =>
                 if (l == 0) (BigInt(0), k)
                 else
                   (k.abs /% l.abs)
         ).apply(k).apply(BigInt(2));
       ((if (BigInt(0) < k) r else (-r) - s), s == BigInt(1))
     })

  def char_of_integer(k: BigInt): Str.char = {
    val (q0, b0): (BigInt, Boolean) = bit_cut_integer(k)
    val (q1, b1): (BigInt, Boolean) = bit_cut_integer(q0)
    val (q2, b2): (BigInt, Boolean) = bit_cut_integer(q1)
    val (q3, b3): (BigInt, Boolean) = bit_cut_integer(q2)
    val (q4, b4): (BigInt, Boolean) = bit_cut_integer(q3)
    val (q5, b5): (BigInt, Boolean) = bit_cut_integer(q4)
    val (q6, b6): (BigInt, Boolean) = bit_cut_integer(q5)
    val a: (BigInt, Boolean) = bit_cut_integer(q6)
    val (_, aa): (BigInt, Boolean) = a;
    Str.Chara(b0, b1, b2, b3, b4, b5, b6, aa)
  }

  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil)     => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

  def explodeList(l: List[Char]): List[Str.char] = {
    (l.map(c => {
      val k: Int = c.toInt;
      if (k < 128) BigInt(k) else sys.error("Non-ASCII character in literal")
    }))
      .map(a => char_of_integer(a))
  }

  def explode(s: String): List[Str.char] = {
    explodeList(s.toCharArray.toList)
  }

  // conversion from Scala String to HOL string
  implicit def string2charList(s: String): List[Str.char] = explode(s)

  // conversion from Scala List[Char] to HOL List[Str.char]
  implicit def charList2charList(l: List[Char]): List[Str.char] =
    explodeList(l)
  // conversion of a pair with a Scala List[String] on the first position
  // to an HOL pair with an HOL List[Str.char] on first position
  implicit def tupleString2tupleString[T](
      t: (List[Char], T)
  ): (List[Str.char], T) = t match {
    case (e1, e2) => (charList2charList(e1), e2)
  }

  // conversion from Isabelle Int.int to Project Int.int
  implicit def int2dataint(i: Int.int): utilities.Datatype.Int.int =
    i match {
      case Int.int_of_integer(i) => utilities.Datatype.Int.int_of_integer(i)
    }

  def stringChar2char(x: Str.char): Char = {
    x match {
      case Str.Chara(x1, x2, x3, x4, x5, x6, x7, x8) => {
        var n = 0;
        n = if (x8) 2 * n + 1 else 2 * n;
        n = if (x7) 2 * n + 1 else 2 * n;
        n = if (x6) 2 * n + 1 else 2 * n;
        n = if (x5) 2 * n + 1 else 2 * n;
        n = if (x4) 2 * n + 1 else 2 * n;
        n = if (x3) 2 * n + 1 else 2 * n;
        n = if (x2) 2 * n + 1 else 2 * n;
        n = if (x1) 2 * n + 1 else 2 * n;
        n.toChar
      }
    }
  }

  // conversion from Isabelle String to Lists of Chars
  implicit def charList2String(l: List[Str.char]): List[Char] = {
    l.map(stringChar2char(_))
  }
}

import AutomaticConversion._
\<close>


(* Directive pour l'exportation de l'analyseur *)
export_code san in Scala (case_insensitive)

(* file "~/workspace/TP67/src/tp67/san_Inter.scala"   (* à adapter en fonction du chemin de votre projet TP67 *)
*)

end
