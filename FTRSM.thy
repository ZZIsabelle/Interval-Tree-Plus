theory FTRSM 
  imports
  "FRMA"
begin
type_synonym 'a information ="'a ivl"
type_synonym 'a Mul_information = "'a ivl list" 
type_synonym 'a database = "'a Mul_information list" 
type_synonym 'a C_information = "'a ivl list"
type_synonym 'a Mul_ivlTree = "'a RBs_ivl_tree list"
type_synonym 'a Sub_database = "'a database"

fun Cdimension_infor::"nat \<Rightarrow>'a database \<Rightarrow> 'a C_information"where
"Cdimension_infor n [] = []"|
"Cdimension_infor n (x#xs) = (x!n)#Cdimension_infor n xs"

fun Cdimension_infors::"nat \<Rightarrow>'a Sub_database list\<Rightarrow>'a ivl list"where
"Cdimension_infors n [] = []"|
"Cdimension_infors n (x#xs) = (Cdimension_infor n x)@(Cdimension_infors n xs)"

fun Achievement::"'a::{linorder,order_bot} ivl list
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"
  where"Achievement [] t = t"|
       "Achievement (x#xs) t = Achievement xs (insert_IntervalT x t)"

fun C_Achievement::"nat \<Rightarrow>'a::{linorder,order_bot} database
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"where
"C_Achievement n DB t = Achievement (Cdimension_infor n DB) t"

fun Mul_Achievements::"nat list\<Rightarrow>'a::{linorder,order_bot} database
                              \<Rightarrow>'a Mul_ivlTree\<Rightarrow>'a Mul_ivlTree"where
"Mul_Achievements [] _ _ = []"|
"Mul_Achievements _ _ [] = []"|
"Mul_Achievements (n#ns) DB (t#ts) = (C_Achievement n DB t)#(Mul_Achievements ns DB ts)"

fun Deletes::"'a::{linorder,order_bot} information list
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"
  where"Deletes [] t = t"|
       "Deletes (x#xs) t = Deletes xs (delete_IntervalT x t)"

fun Mul_Delete::"nat \<Rightarrow> 'a::{linorder,order_bot} Mul_information
                              =>'a Mul_ivlTree \<Rightarrow> 'a Mul_ivlTree"
  where"Mul_Delete n info t = (let m = (Deletes info (t!n)) 
                                       in (list_update t n m) )"

fun Mul_db_delete::"nat list\<Rightarrow>'a::{linorder,order_bot} database
                              \<Rightarrow>'a Mul_ivlTree\<Rightarrow>'a Mul_ivlTree"where
"Mul_db_delete [] _ _ = []"|
"Mul_db_delete _ [] _ = []"|
"Mul_db_delete (n#ns) (db#dbs) t = (Mul_Delete n db t)@(Mul_db_delete ns dbs t)"

fun Mul_Search ::"'a Mul_ivlTree \<Rightarrow>'a::{linorder,order_bot} Mul_information \<Rightarrow> bool" 
  where"Mul_Search Mtree [] =True "|
       "Mul_Search Mtree (m#ms) = (search (hd(Mtree)) m \<and> (Mul_Search (tl(Mtree)) ms))"

fun find_overlap::"'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a ivl => ('a \<times>'a) list"where
"find_overlap Leaf x = []"|
"find_overlap (Node l ((a,_),_) r) x = 
 (if overlap x a then (Rep_ivl a)#(find_overlap l x)@(find_overlap r x) 
                                   else (find_overlap l x)@(find_overlap r x))"

fun Minfo_overlap::"'a::{linorder,order_bot} Mul_ivlTree \<Rightarrow> 'a Mul_information => ('a \<times>'a) list list"
  where"Minfo_overlap (t#ts) (r#rs) = (find_overlap t r)#Minfo_overlap ts rs"

fun is_overlap ::"('a \<times>'a) list list \<Rightarrow>('a \<times>'a) list \<Rightarrow> bool "where
"is_overlap m (x#xs) = (x\<in>set(hd m) \<and>(is_overlap (tl m) xs))"

fun AbstoReps::"'a::{linorder,order_bot} Mul_information\<Rightarrow>('a\<times>'a) list"where
"AbstoReps [] = []"|
"AbstoReps (x#xs) = (Rep_ivl x) # (AbstoReps xs) "

fun DB_AbstoReps::"'a::{linorder,order_bot} database \<Rightarrow>('a\<times>'a) list list"where
"DB_AbstoReps [] = []"|
"DB_AbstoReps (x#xs) = (AbstoReps x) # (DB_AbstoReps xs) "

definition onlys ::
    "nat list
     \<Rightarrow> 'a::{linorder,order_bot}database \<Rightarrow>'a Mul_ivlTree \<Rightarrow> 'a Mul_information \<Rightarrow>'a Mul_information \<Rightarrow> bool" where
"onlys n DB t info Mulinfo\<equiv> 
(\<exists>Mulinfo.(is_overlap(Minfo_overlap(Mul_Achievements n DB t) info) (AbstoReps Mulinfo)))
            \<and>(((AbstoReps Mulinfo)\<in>set(DB_AbstoReps DB)))"
                                         
fun Mul_Match ::
    "nat list
     \<Rightarrow> 'a::{linorder,order_bot} database
        \<Rightarrow> 'a Mul_ivlTree \<Rightarrow> 'a Mul_information \<Rightarrow>'a Mul_information \<Rightarrow> bool" 
where"Mul_Match n DB t info Mulinfo= (((Mul_Search (Mul_Achievements n DB t) info) 
                                           \<and>(onlys n DB t info Mulinfo)))"

fun FMRSA ::
    "nat list
     \<Rightarrow> 'a::{linorder,order_bot} database
        \<Rightarrow> 'a Mul_ivlTree \<Rightarrow> 'a database \<Rightarrow>'a Mul_information \<Rightarrow> bool" 
 where"FMRSA n DB t [] Mulinfo= False"|
"FMRSA n DB t (info#infos) Mulinfo = 
                     (Mul_Match n DB t info Mulinfo\<or> FMRSA n DB t infos Mulinfo)"

fun sets :: "'a list => 'a set" where
  "sets [] = {}"
| "sets (x # xs) = insert x (sets xs)"

fun all_has_overlap where
"all_has_overlap (x#xs)(y#ys) =((has_overlap(set_tree x) y)\<and>all_has_overlap xs ys)"

lemma M_Search:" \<forall>s. (s\<in>sets(x) \<and> invar_BItree s) \<Longrightarrow>Mul_Search x y = all_has_overlap x y"
  apply(simp add:invar_BItree_def)
  by (metis inv_baliL invh.simps(2) n_not_Suc_n)

lemma M_Achievement:" \<forall>t. t\<in>sets ts \<and> invar_BItree t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(Mul_Achievements n xl ts)\<and>invar_BItree x"
  apply(auto simp add:invar_BItree_def)
  by (metis add.right_neutral add_eq_if bheight_baliR bheight_paint_Red n_not_Suc_n nat.distinct(1) paininvh_node)

lemma M_Delete:" \<forall>t. t\<in>sets ts \<and> invar_BItree t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(Mul_Delete n xl ts)\<and> invar_BItree x"
  apply(auto simp add:invar_BItree_def)
proof -
  fix x :: "(('a ivl \<times> 'a) \<times> color) tree" and n :: nat and xl :: "'a ivl list"
  assume "\<forall>t. t \<in> sets ts \<and> inv_max_hi t \<and> inv_bst t \<and> invc t \<and> invh t \<and> interval_color t = Black"
  then have f1: "\<forall>t. bheight (paint Red (t::(('a ivl \<times> _) \<times> color) tree)) = bheight t - 1"
    by (smt (z3) bheight_paint_Red)
  then have f2: "\<forall>t p. bheight t = bheight (paint Red (baliR t (p::'a ivl \<times> _) t))"
    by (simp add: bheight_baliR)
  then have "\<forall>t p. bheight (paint Red (paint Red (baliR t (p::'a ivl \<times> _) t))) = bheight t - 1"
    using f1 by (smt (z3))
  then have False
    using f2 f1 by (metis bheight_baliR n_not_Suc_n paininvh_node)
  then show "x \<in> sets (ts[n := Deletes xl (ts ! n)])"
    by (smt (z3))
qed

lemma M_Match_correct:" \<forall>s. (s\<in>sets((Mul_Achievements n DB t)) \<and> invar_BItree s)
   \<Longrightarrow> Mul_Match n DB t Mulinfo info = all_has_overlap (Mul_Achievements n DB t) Mulinfo \<and>(onlys n DB t Mulinfo info)"
  apply(simp add:invar_BItree_def onlys_def )
  by (metis bheight_baliR invh.simps(2) n_not_Suc_n)

locale M_Region_Match = Region_Match +
  fixes overlaps::"'tl \<Rightarrow>'MR \<Rightarrow> bool"
  fixes to_set::"'tl \<Rightarrow> 'a set"
  fixes MD_Search ::"'tl \<Rightarrow> 'MR \<Rightarrow> bool"
  fixes MR_Ach::"nat list\<Rightarrow>'MS \<Rightarrow>'tl\<Rightarrow>'tl"
  fixes MR_Del::"nat \<Rightarrow>'il \<Rightarrow>'tl\<Rightarrow>'tl"
  fixes MD_Match::"nat list \<Rightarrow> 'MS \<Rightarrow>'tl \<Rightarrow> 'MR \<Rightarrow>'MR \<Rightarrow>bool"
  fixes M_only::"nat list \<Rightarrow>'MS \<Rightarrow>'tl \<Rightarrow>'MR\<Rightarrow>'MR \<Rightarrow> bool"
 assumes M_Serach__correct:"(\<forall>s. s\<in>(to_set ss) \<and> invar s) 
                                 \<Longrightarrow> MD_Search ss y= overlaps ss y"

 assumes Mul_Ach_correct:"\<forall>t. (t\<in>(to_set ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. x\<in>to_set(MR_Ach n xl ts)\<and>invar x"

 assumes Mul_Del_correct:"\<forall>t. (t\<in>(to_set ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. (x\<in>to_set(MR_Del n xl ts)\<and>invar x)"

 assumes M_Match_correct:"\<forall>x. (x\<in>to_set((MR_Ach n MS t)) \<and> invar x)
   \<Longrightarrow> (MD_Match n MS t MO MR) = overlaps (MR_Ach n MS t) MO \<and>(M_only n MS t MO MR)"



interpretation FTRSM:M_Region_Match
where empty = Leaf and insert = insert_IntervalT and delete = delete_IntervalT
  and isin = isin_IntervalT and set = set_tree  and Search = search
  and invar =invar_BItree and match = Match 
  and X_overlap = X_has_overlap and Y_overlap = Y_has_overlap and Judge = judge 
  and MR_Ach = Mul_Achievements and MR_Del = Mul_Delete and M_only = onlys 
  and MD_Match = Mul_Match and MD_Search = Mul_Search and to_set = sets 
  and overlaps = all_has_overlap
proof (standard, goal_cases)
  case (1 ss y)
  then show ?case
    by (simp add: M_Search) 
next
  case (2 ts)
  then show ?case
    using M_Achievement by blast 
next
  case (3 ts)
  then show ?case
    using M_Delete by blast
next
  case (4 n DB t Mulinfo info)
  then show ?case
    using M_Match_correct by blast 
qed


(*
locale Tree = 
fixes empty :: "'s"
fixes insert :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes delete :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes isin :: "'s \<Rightarrow> 'a \<Rightarrow> bool"
fixes set :: "'s \<Rightarrow> 'a set"
fixes invar :: "'s \<Rightarrow> bool"
assumes set_empty:    "set empty = {}"
assumes set_isin:     "invar s \<Longrightarrow> isin s x = (x \<in> set s)"
assumes set_insert:   "invar s \<Longrightarrow> set(insert x s) = set s \<union> {x}"
assumes set_delete:   "invar s \<Longrightarrow> set(delete x s) = set s - {x}"
assumes invar_empty:  "invar empty"
assumes invar_insert: "invar s \<Longrightarrow> invar(insert x s)"
assumes invar_delete: "invar s \<Longrightarrow> invar(delete x s)"
locale M_Search = Region_Match +
fixes Mul_Search ::"'a Mul_ivlTree \<Rightarrow>'a::{linorder,order_bot} Mul_information \<Rightarrow> bool"
fixes Mul_Ach::"nat list\<Rightarrow>'a::{linorder,order_bot} database 
                                            \<Rightarrow>'a Mul_ivlTree\<Rightarrow>'a Mul_ivlTree"
fixes Mul_Del::"nat \<Rightarrow> 'a::{linorder,order_bot} information list
                         =>'a Mul_ivlTree \<Rightarrow> 'a Mul_ivlTree"
fixes onlys::"nat list\<Rightarrow>'a::{linorder,order_bot}database 
                         \<Rightarrow>'a Mul_ivlTree \<Rightarrow> 'a Mul_information \<Rightarrow>'a Mul_information \<Rightarrow> bool"
fixes Mul_Match::"nat list \<Rightarrow> 'a::{linorder,order_bot} database
                        \<Rightarrow> 'a Mul_ivlTree \<Rightarrow> 'a Mul_information \<Rightarrow>'a Mul_information \<Rightarrow> bool"

  assumes Mul_search_correct:"(\<forall>s. s\<in>(sets ss) \<and> invar s) 
                                 \<Longrightarrow> Mul_Search ss y= all_has_overlap ss y"
  assumes Mul_Ach_correct:"\<forall>t. (t\<in>(sets ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. x\<in>sets(Mul_Ach n xl ts)\<and>invar x"

  assumes Mul_Del_correct:" \<forall>t. t\<in>sets ts \<and> invar t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(Mul_Del n xl ts)\<and>invar x"
  assumes M_Match_correct:" \<forall>s. (s\<in>sets((Mul_Ach n DB t)) \<and> invar s)
  \<Longrightarrow> Mul_Match n DB t Mulinfo info = 
            all_has_overlap (Mul_Ach n DB t) Mulinfo \<and>(onlys n DB t Mulinfo info)"
interpretation FMRSA:M_Search
where empty = Leaf and insert = insert_IntervalT and delete = delete_IntervalT
  and isin = isin_IntervalT and set = set_tree  and Search = search
  and invar =invar_BItree and match = Match 
  and X_overlap = X_has_overlap and Y_overlap = Y_has_overlap and Judge = judge 
  and Mul_Ach = Mul_Achievements and Mul_Del = Mul_Delete and onlys = onlys 
  and Mul_Match = Mul_Match and Mul_Search = Mul_Search
proof (standard, goal_cases)
  case (1 ss y)
  then show ?case
    by (simp add: M_Search) 
next
  case (2 ts)
  then show ?case
    using M_Achievement by blast 
next
  case (3 ts)
  then show ?case
    using M_Delete by blast
next
  case (4 n DB t Mulinfo info)
  then show ?case
    using M_Match_correct by blast 
qed
*)


 







