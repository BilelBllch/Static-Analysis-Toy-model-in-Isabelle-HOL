theory set
  imports Main
begin


(*CONSTRUCTION DES ENSEMBLES*)

(*1*)
fun isSet::"'a list \<Rightarrow> bool" where
  "isSet Nil = True" | 
  "isSet (x#xs) = (\<not>(List.member xs x) \<and> isSet xs)"

value "isSet [0::nat]"
value "isSet [0::nat, 0, 0]"
value "isSet  [0::nat, 1, 2]"
value "isSet  [0::nat, 1, 0]"
value "isSet  [0::nat, 1, 2, 1]"

(*2*)
fun clean::"'a list \<Rightarrow> 'a list" where
  "clean Nil = Nil" |
  "clean (x#xs) = (if (List.member xs x) then (clean xs) else x#(clean xs))"

value "clean [0::nat]"
value "clean [0::nat, 1, 2]"
value "clean [0::nat, 1, 2, 0]"
value "clean [0::nat, 1, 1, 2]"
value "clean [0::nat, 0, 0, 0]"
value "clean [0::nat, 1, 2, 3, 3,3, 4, 5, 6, 1]"

(*3*)
lemma member_clean_impl: "List.member (clean L) e \<longrightarrow> List.member L e"
  apply (induct L)
   apply simp
   apply (simp add: member_rec(1))
  done

lemma member_clean_recip: " List.member L e \<longrightarrow> List.member (clean L) e"
  apply (induct L)
   apply simp
   apply (simp add: member_rec(1))
  done

lemma member_clean:"List.member (clean L) e = List.member L e"
   apply auto
   apply (simp add:member_clean_impl)
   apply (simp add:member_clean_recip)
  done

(*4*)
lemma isSet_clean: "isSet (clean l)"
  apply (induct l)
   apply simp
  using member_clean_impl by fastforce

(*SUPPRESSION D'UN ELEMENT*)
(*5*)
(*fun delete::"'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "delete Nil _  = Nil" |
  "delete (x#xs) e = (if x = e then xs else x#(delete xs e))"*)

fun delete::"'a list \<Rightarrow> 'a \<Rightarrow>'a list" where
  "delete Nil _ = Nil" |
  "delete (x#xs) e = (if x=e then delete xs e else x#(delete xs e))"
  


value "delete [0::nat, 1, 2, 3] 2"
value "delete [0::nat] 0"
value "delete [0::nat, 1, 2, 3] 10"
value "delete [0::nat, 1, 2, 0] 0"

value "delete [0::nat, 1, 2, 3] 1"
value "\<not>(List.member (delete [0::nat, 1, 2, 3] 1) 1)"


(*6*)

(*Supprimer un element d'un set \<Rightarrow> cet element n'est plus un element de la liste representant
  le set*)
lemma member_delete:"\<not>(List.member (delete L x) x)"
  apply auto
  apply (induction L)
   apply (simp add:List.member_def)
  by (metis delete.simps(2)  member_rec(1))


(* Supprimer un element qui n'est pas dans l'ensemble laisse invariant l'ensemble*)

lemma delete_invariant_impl:"\<not>(List.member L x) \<longrightarrow> (delete L x = L)"
  apply (induction L)
   apply (simp add:List.member_def)
   by (simp add: member_rec(1))

lemma delete_invariant_recip:"(delete L x = L) \<longrightarrow> \<not>(List.member L x)"
  apply (induction L)
   apply (simp add:List.member_def)
   by (metis member_delete)
    

lemma delete_invariant:"\<not>(List.member L x) \<longleftrightarrow> (delete L x = L)"
  apply auto
   apply (simp add:delete_invariant_impl)
  apply (simp add:delete_invariant_recip)
  done


(*INTERSECTION*)
(*7*)
fun intersection::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersection Nil _ = Nil" |
  "intersection (x#xs) ys = (if (List.member ys x) then (x#intersection xs ys) else intersection xs ys)"

value "intersection [0::nat] [0::nat]"
value "intersection [0::nat, 2, 4, 6] [1::nat, 3, 5]"
value "intersection [0::nat, 2, 4, 6] [0::nat, 2, 4, 6]"
value "intersection [0::nat, 2, 3, 13, 12, 19] [0::nat,1, 32, 3, 13]"
value "intersection [0::nat, 1, 2] [0::nat, 1, 2]"
value "intersection [0::nat, 1, 2] [0::nat, 1, 2, 3, 4]"
value "intersection [0::nat, 1, 2,3 ,4] [0::nat, 1, 2]"


(*8*)
lemma intersection_ensembliste_impl:"(List.member L1 x \<and> List.member L2 x) \<longrightarrow> List.member (intersection L1 L2) x"
  apply (induct L1)
   apply simp
   apply (case_tac "a=x")
    apply (simp add: member_rec(1))
    apply (simp add: member_rec(1))
  done

lemma intersection_ensembliste_recip:"List.member (intersection L1 L2) x \<longrightarrow> (List.member L1 x \<and> List.member L2 x)"
  apply (induct L1)
   apply simp
   apply (case_tac "a=x")
    apply (simp add:List.member_def)
    apply (simp add:List.member_def)
    by (metis intersection.simps(2) member_rec(1))
    
   

lemma intersection_ensembliste:"(List.member L1 x \<and> List.member L2 x) \<longleftrightarrow> List.member (intersection L1 L2) x "
  sorry

(*9*)
lemma intersection_isSet:"isSet L1 \<and> isSet L2 \<longrightarrow> isSet(intersection L1 L2)"
  apply (induct L1)
   apply simp
   by (metis intersection.simps(2) intersection_ensembliste isSet.simps(2))


(*UNION*)
(*10*)
fun union::"'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "union Nil ys = ys" |
  "union (x#xs) ys = clean (x # (union xs ys))"

value "union [1::nat, 2, 3] [3, 4, 5]"
value "union [1::nat, 1, 2] [2, 3, 3]"
value "union ([]::nat list) [1,2,3]"
value "union [1::nat,2,3] []"
value "union ([]::nat list) ([]::nat list)"
value "union [0::nat, 1, 2, 5] [10, 9, 5]"

(*11*)
lemma union_ensembliste:"List.member (union xs ys) a \<longleftrightarrow> List.member xs a \<or> List.member ys a"
  apply (induct xs)
   apply (simp add: member_rec(2))
  apply (case_tac "aa=a")
   apply (simp add: member_clean member_rec(1))
   by (simp add: member_clean member_rec(1))
   
   
  
(*12*)
lemma union_isSet:"isSet xs \<and> isSet ys \<longrightarrow> isSet (union xs ys)"
   apply (induct xs)
   apply simp
   by (metis isSet_clean union.simps(2))

  
(*EGALITE*)
fun subset:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "subset [] _ = True" |
  "subset (x#xs) ys = (if List.member ys x then subset xs ys else False)" 

value "subset [1, 2::nat, 9] [1, 2, 3, 4]"

lemma subset_ensembliste_impl:"(subset L1 L2) \<longrightarrow> (\<forall>x. (List.member L1 x) \<longrightarrow> (List.member L2 x))" 
  apply (induct L1)
   apply (simp add: member_rec(2))
  by (metis member_rec(1) subset.simps(2))
   

lemma subset_ensembliste_recip:" (\<forall>x. (List.member L1 x) \<longrightarrow> (List.member L2 x)) \<longrightarrow> (subset L1 L2)" 
  apply (induct L1)
   apply (simp add: member_rec(2))
   by (metis member_rec(1) subset.simps(2))

lemma subset_ensembliste:"(subset L1 L2) \<longleftrightarrow> (\<forall> x. (List.member L1 x) \<longrightarrow> (List.member L2 x))" 
  apply auto
  apply (simp add:subset_ensembliste_impl)
  apply (simp add:subset_ensembliste_recip)
  done

  
     
  

fun setequal:: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "setequal xs ys = ((subset xs ys) \<and>(subset ys xs))"

lemma setequal_ensembliste:" ( (\<forall>x.(List.member l1 x = List.member l2 x)) = (setequal l1 l2))"
  using subset_ensembliste by auto


lemma setequal_subsets: "((subset L1 L2) \<and> (subset L2 L1)) = (setequal L1 L2)"
  apply simp
  done

value "setequal [1::nat, 2, 3] [3, 2, 1]"
value "setequal [1::nat, 2, 2, 3] [1, 2, 3]"
value "setequal [1::nat, 2, 3] [1, 2, 3, 4]"
value "setequal ([]::nat list) []"
value "setequal ([]::nat list) [1]"
value "setequal [1::nat, 2] [2, 3]"



fun setDiff:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"setDiff [] _ = []" |
"setDiff (x#xs) ys = (if List.member ys x then (setDiff xs ys) else (x#(setDiff xs ys)))"
   

lemma setDiff_complementaire:"List.member (setDiff L1 L2) x \<longrightarrow> List.member L1 x"
  apply (induct L1)
   apply (simp add: member_rec(2))
  by (simp add: member_rec(1))

lemma setDiff_complementaire2:
  "(List.member L1 x) \<and> \<not>(List.member L2 x) \<longleftrightarrow> List.member (setDiff L1 L2) x"
  apply (induct L1)
   apply (simp add: member_rec(2))
  by (metis setDiff.simps(2) member_rec(1))
   

lemma setDiff_ensembliste:"(List.member L2 x) \<longrightarrow> \<not>(List.member (setDiff L1 L2) x)"
  apply (induct L1)
   apply (simp add: member_rec(2))
  by (metis setDiff.simps(2) member_def set_ConsD)
    
 
lemma setDiff_isSet: "isSet L1 \<longrightarrow> isSet (setDiff L1 L2)"
  apply (induct L1)
   apply simp
  using setDiff_complementaire by force
 


end
