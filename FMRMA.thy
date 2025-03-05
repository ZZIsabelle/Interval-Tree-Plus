theory FMRMA
  imports   
  "FRMA"
begin 
type_synonym 'a M_Region ="'a ivl list"
type_synonym 'a M_Publication = "'a M_Region list"
type_synonym 'a M_Order = "'a M_Region list"
type_synonym 'a M_System = "'a M_Publication \<times> 'a M_Order"

fun Map_Publication::"'a M_System \<Rightarrow> 'a M_Publication"where
"Map_Publication MS = fst MS"

fun Certain_dimension::"nat \<Rightarrow>'a M_Publication \<Rightarrow> 'a ivl list"where
"Certain_dimension n [] = []"|
"Certain_dimension n (x#xs) = (x!n)#Certain_dimension n xs"

fun MStoMR::"nat \<Rightarrow> 'a M_System \<Rightarrow> 'a M_Region"where
"MStoMR n MS = Certain_dimension n (Map_Publication MS)"

fun MR_Achievement::"nat \<Rightarrow>'a::{linorder,order_bot} M_System
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"where
"MR_Achievement n MS t = P_Achievement (MStoMR n MS) t"

fun sets :: "'a list => 'a set" where
  "sets [] = {}"
| "sets (x # xs) = insert x (sets xs)"

lemma MInv_ach:"invar_BItree t \<Longrightarrow> inv_max_hi (P_Achievement (MStoMR n MS) t)"
  by (simp add: Inv_ach)

lemma MInv_bst:" invar_BItree t \<Longrightarrow> inv_bst (P_Achievement (MStoMR n MS) t)"
  by (simp add: Inv_bst)

lemma MInv_invc:" invar_BItree t \<Longrightarrow> invc (P_Achievement (MStoMR n MS) t)"
  by (simp add: Inv_invc)

lemma MInv_invh:" invar_BItree t \<Longrightarrow> invh (P_Achievement (MStoMR n MS) t)"
  by (simp add: Inv_invh)

lemma MInv_color:"invar_BItree t \<Longrightarrow>interval_color (P_Achievement (MStoMR n MS) t) = Black"
  by (simp add: Inv_color)

theorem MInv_Achieve:"invar_BItree t \<Longrightarrow>invar_BItree (P_Achievement (MStoMR n MS) t)"
  by (simp add: Inv_Achieve)

fun MR_Achievements::"nat list\<Rightarrow>'a::{linorder,order_bot} M_System
                              \<Rightarrow>'a RBs_ivl_tree list\<Rightarrow> 'a RBs_ivl_tree list"where
"MR_Achievements [] _ _ = []"|
"MR_Achievements _ _ [] = []"|
"MR_Achievements (n#ns) MS (t#ts) = (MR_Achievement n MS t)#(MR_Achievements ns MS ts)"

theorem M_Achievement:" \<forall>t. t\<in>sets ts \<and> invar_BItree t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(MR_Achievements n xl ts)\<and>invar_BItree x"
  apply(auto simp add:invar_BItree_def) 
  using interval_color.simps(2) neq_Red by blast

fun MR_Delete::"nat \<Rightarrow> 'a::{linorder,order_bot} ivl list  
                              =>'a RBs_ivl_tree list\<Rightarrow> 'a RBs_ivl_tree list"
  where"MR_Delete n xl t = (let m = (P_Delete xl (t!n)) in (list_update t n m) )"
 
fun MR_Search :: 
"'a::{linorder,order_bot} RBs_ivl_tree list \<Rightarrow> 'a ivl list \<Rightarrow> bool" where
"MR_Search MRtree [] =True "|
"MR_Search MRtree (m#ms) = (search (hd(MRtree)) m \<and> (MR_Search (tl(MRtree)) ms))"

lemma correct1:"\<forall>x. x\<in>(set MRtree)\<and>(invar_BItree x)
                   \<Longrightarrow>(search (hd(MRtree)) m) = has_overlap(set_tree (hd(MRtree))) m"
  apply(simp add:invar_BItree_def)
  apply auto
  by (simp add: inv_bst_def search_correct)+

theorem MR_Correct:"\<forall>x. (x\<in>(sets MRtree)\<and>(invar_BItree x))
                   \<Longrightarrow>(search x m) = has_overlap (set_tree x) m"
  apply(induct MRtree arbitrary:x m)
  apply(auto simp add:invar_BItree_def)
  by(metis (no_types, opaque_lifting) bheight_paint_Red 
           diff_Suc_1 inv_baliL n_not_Suc_n paininvh_node)+

(****************Match**********************)
fun find_overlap::"'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a ivl => ('a \<times>'a) list"where
"find_overlap Leaf x = []"|
"find_overlap (Node l ((a,_),_) r) x = 
 (if overlap x a then (Rep_ivl a)#(find_overlap l x)@(find_overlap r x) 
                                   else (find_overlap l x)@(find_overlap r x))"

fun DM_overlap::"'a::{linorder,order_bot} RBs_ivl_tree list \<Rightarrow> 'a M_Region => ('a \<times>'a) list list"
  where"DM_overlap (t#ts) (r#rs) = (find_overlap t r)#DM_overlap ts rs"

fun AbstoReps::"'a::{linorder,order_bot} M_Region\<Rightarrow>('a\<times>'a) list"where
"AbstoReps [] = []"|
"AbstoReps (x#xs) = (Rep_ivl x) # (AbstoReps xs) "

fun P_AbstoReps::"'a::{linorder,order_bot} M_Publication \<Rightarrow>('a\<times>'a) list list"where
"P_AbstoReps [] = []"|
"P_AbstoReps (x#xs) = (AbstoReps x) # (P_AbstoReps xs) "

fun overlap_region ::"('a \<times>'a) list list \<Rightarrow>('a \<times>'a) list \<Rightarrow> bool "where
"overlap_region m (x#xs) = (x\<in>set(hd m) \<and>(overlap_region (tl m) xs))"

fun judge_empty where
"judge_empty [] = True"|
"judge_empty (x#xs) = (if x=[] then False else True \<and> judge_empty xs)"

definition only where
"only n MS t MO MR \<equiv> 
(\<exists>MR.(overlap_region (DM_overlap(MR_Achievements n MS t) MO) (AbstoReps MR)))
            \<and>(((AbstoReps MR)\<in>set(P_AbstoReps (fst MS))))"

fun M_Match
  where"M_Match n MS t MO MR= (((MR_Search (MR_Achievements n MS t) MO) 
              \<and>(only n MS t MO MR )))"

fun all_has_overlap where
"all_has_overlap (x#xs)(y#ys) =((has_overlap(set_tree x) y)\<and>all_has_overlap xs ys)"

theorem M_Search:" \<forall>s. (s\<in>sets(x) \<and> invar_BItree s) \<Longrightarrow>MR_Search x y = all_has_overlap x y"
  apply(simp add:invar_BItree_def)
  apply auto
  using interval_color.simps(2) neq_Red apply blast
  by (metis add.right_neutral add_eq_if bheight_paint_Red inv_baliR 
                   n_not_Suc_n nat.discI paininvh_node)


theorem MR_Achievements_correct:"\<forall>t. t\<in>set ts \<and> invar_BItree t 
                        \<Longrightarrow> \<forall>x. x\<in>set(MR_Achievements ns MS ts)\<and>invar_BItree x "
  apply(auto simp add:invar_BItree_def)
  by (metis (no_types, opaque_lifting) bheight_baliL bheight_paint_Red diff_Suc_1 
              n_not_Suc_n paininvh_node)
theorem MR_Delete_correct:" \<forall>t. t\<in>sets ts \<and>invar_BItree t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(MR_Delete n xl ts)\<and>invar_BItree x"
  apply(auto simp add:invar_BItree_def)
  by (metis (no_types, opaque_lifting) bheight_baliR bheight_paint_Red diff_Suc_1 
        n_not_Suc_n paininvh_node)
theorem M_Match_correct:" \<forall>s. (s\<in>sets((MR_Achievements n MS t)) \<and>invar_BItree s)
   \<Longrightarrow> M_Match n MS t MO MR = all_has_overlap (MR_Achievements n MS t) MO \<and>(only n MS t MO MR) "
  apply(simp add:invar_BItree_def only_def )
  by (metis bheight.simps(1) bheight_baliL invh.simps(2) nat.distinct(1))


fun FMRMA ::
    "nat list
     \<Rightarrow> 'a::{linorder,order_bot} M_System \<Rightarrow> 'a RBs_ivl_tree list \<Rightarrow> 'a M_Region \<Rightarrow> 'a M_Order \<Rightarrow> bool" 
where"FMRMA n MS t MO [] = False"|
"FMRMA n MS t MO (MR#MRS) = (M_Match n MS t MO MR \<or> FMRMA n MS t MO MRS)"

theorem M_Matchs:"\<exists>c. c\<in>sets C \<and> M_Match n MS t MO c \<Longrightarrow> FMRMA n MS t MO C"
  apply(induct C arbitrary:n MS t MO)
   apply simp
  by fastforce

locale M_Region_Match = Region_Match +
  fixes overlaps::"'tl \<Rightarrow>'MR \<Rightarrow> bool"
  fixes to_set::"'tl \<Rightarrow> 'a set"
  fixes MD_Search ::"'tl \<Rightarrow> 'MR \<Rightarrow> bool"
  fixes MR_Ach::"nat list\<Rightarrow>'MS \<Rightarrow>'tl\<Rightarrow>'tl"
  fixes MR_Del::"nat \<Rightarrow>'il \<Rightarrow>'tl\<Rightarrow>'tl"
  fixes MD_Match::"nat list \<Rightarrow> 'MS \<Rightarrow>'tl \<Rightarrow> 'MR \<Rightarrow>'MR \<Rightarrow>bool"
  fixes M_only::"nat list \<Rightarrow>'MS \<Rightarrow>'tl \<Rightarrow>'MR\<Rightarrow>'MR \<Rightarrow> bool"
 assumes M_Search_correct:"(\<forall>s. s\<in>(to_set ss) \<and> invar s) 
                                 \<Longrightarrow> MD_Search ss y= overlaps ss y"

 assumes Mul_Ach_correct:"\<forall>t. (t\<in>(to_set ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. x\<in>to_set(MR_Ach n xl ts)\<and>invar x"

 assumes Mul_Del_correct:"\<forall>t. (t\<in>(to_set ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. (x\<in>to_set(MR_Del n xl ts)\<and>invar x)"

 assumes M_Match_correct:"\<forall>x. (x\<in>to_set((MR_Ach n MS t)) \<and> invar x)
   \<Longrightarrow> (MD_Match n MS t MO MR) = overlaps (MR_Ach n MS t) MO \<and>(M_only n MS t MO MR)"


interpretation FMRMA :M_Region_Match
 where empty = Leaf and insert = insert_IntervalT and delete = delete_IntervalT
  and Search = search and  isin = isin_IntervalT and set = set_tree 
  and invar =invar_BItree and match = Match 
  and X_overlap = X_has_overlap and Y_overlap = Y_has_overlap and Judge = judge 
  and MD_Search = MR_Search and MR_Ach = MR_Achievements 
  and MD_Match = M_Match and M_only = only and MR_Del = MR_Delete and to_set = sets
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
    using MR_Delete_correct by blast  
next
  case (4 n MS t MO MR)
  then show ?case
    using M_Match_correct by blast
qed


(*
locale M_Region_Match = Region_Match +
  fixes MD_Search ::"'a::{linorder} RBs_ivl_tree list \<Rightarrow> 'a::linorder ivl list \<Rightarrow> bool"
  fixes MR_Ach::"nat list\<Rightarrow>'a::{linorder} M_System                         
                              \<Rightarrow>'a RBs_ivl_tree list\<Rightarrow> 'a RBs_ivl_tree list"
  fixes MR_Del::"nat \<Rightarrow>'a::{linorder} ivl list  
                              =>'a RBs_ivl_tree list\<Rightarrow> 'a RBs_ivl_tree list"
  fixes MD_Match::"nat list \<Rightarrow> 'a::{linorder} M_System
        \<Rightarrow> 'a RBs_ivl_tree list \<Rightarrow> 'a M_Region  \<Rightarrow> 'a M_Region \<Rightarrow> bool"
  fixes M_only::"nat list \<Rightarrow> 'a::{linorder} M_System
        \<Rightarrow> 'a RBs_ivl_tree list \<Rightarrow> 'a M_Region  \<Rightarrow> 'a M_Region \<Rightarrow> bool"
  assumes M_search_correct:"(\<forall>s. s\<in>(sets ss) \<and> invar s) 
                                 \<Longrightarrow> MD_Search ss y= all_has_overlap ss y"

  assumes Mul_Ach_correct:"\<forall>t. (t\<in>(sets ts)\<and>(invar t)) \<Longrightarrow>
                   \<forall>x n xl. x\<in>sets(MR_Ach n xl ts)\<and>invar x"

  assumes MR_Del_correct:" \<forall>t. t\<in>sets ts \<and> invar t \<Longrightarrow>
                         \<forall>x n xl. x\<in>sets(MR_Del n xl ts)\<and> invar x"

  assumes M_Match_correct:"\<forall>x. (x\<in>sets((MR_Ach n MS t)) \<and> invar x)
   \<Longrightarrow> (MD_Match n MS t MO MR) = all_has_overlap (MR_Ach n MS t) MO \<and>(M_only n MS t MO MR)"

interpretation FMRMA :M_Region_Match
 where empty = Leaf and insert = insert_IntervalT and delete = delete_IntervalT
  and Search = search and  isin = isin_IntervalT and set = set_tree 
  and invar =invar_BItree and match = Match 
  and X_overlap = X_has_overlap and Y_overlap = Y_has_overlap and Judge = judge 
  and MD_Search = MR_Search and MR_Ach = MR_Achievements 
  and MD_Match = M_Match and M_only = only and MR_Del = MR_Delete
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
    using MR_Delete_correct by blast  
next
  case (4 n MS t MO MR)
  then show ?case
    using M_Match_correct by blast
qed
 *)

end