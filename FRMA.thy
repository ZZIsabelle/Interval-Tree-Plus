theory FRMA 
  imports   
  "IntervalTreeplus"
begin 
(*****************Achievement************************)
type_synonym 'a Region ="'a ivl \<times> 'a ivl"
type_synonym 'a Publication = "'a Region list"
type_synonym 'a Order = "'a Region list"
type_synonym 'a Coordinate_System = "'a Publication \<times> 'a Order"

definition map_Publication::"'a Coordinate_System \<Rightarrow> 'a Publication"where
"map_Publication CS \<equiv> fst CS"

definition X_Dimension::"'a Coordinate_System \<Rightarrow>'a ivl list"
  where"X_Dimension CS \<equiv> map fst (map_Publication CS)"

definition Y_Dimension::"'a Coordinate_System \<Rightarrow>'a ivl list"
  where"Y_Dimension CS \<equiv> map snd (map_Publication CS)"

fun P_Achievement::"'a::{linorder,order_bot} ivl list
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"
  where"P_Achievement [] t = t"|
       "P_Achievement (x#xs) t = P_Achievement xs (insert_IntervalT x t)"

fun P_Delete::"'a::{linorder,order_bot} ivl list
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"
  where"P_Delete [] t = t"|
       "P_Delete (x#xs) t = P_Delete xs (delete_IntervalT x t)"

definition X_P_Achievements::"'a::{linorder,order_bot} Coordinate_System
                              =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"where
"X_P_Achievements x t = P_Achievement (X_Dimension x) t"

definition Y_P_Achievements::"'a::{linorder,order_bot} Coordinate_System
                       =>'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"where
"Y_P_Achievements y t = P_Achievement (Y_Dimension y) t"

(****************Match**********************)
fun find_overlap::"'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a ivl => ('a \<times>'a) list"where
"find_overlap Leaf x = []"|
"find_overlap (Node l ((a,_),_) r) x = 
 (if overlap x a then (Rep_ivl a)#(find_overlap l x)@(find_overlap r x) 
                                   else (find_overlap l x)@(find_overlap r x))"

lemma"Rep_ivl(Abs_ivl (16::nat, 28::nat)) = (16,28)"
  by(simp add:Abs_ivl_inverse)
 
lemma"(find_overlap (B \<langle>\<rangle> (Abs_ivl (5::nat, 12::nat), 28::nat) (R \<langle>\<rangle> (Abs_ivl (16::nat, 28::nat), 28::nat) \<langle>\<rangle>)) (Abs_ivl (14::nat, 21::nat))) = [(16::nat, 28::nat)]"
  apply (auto simp add:overlap_def  low_def high_def)
  by(auto simp add:Abs_ivl_inverse)
lemma"(find_overlap (B \<langle>\<rangle> (Abs_ivl (10::nat, 22::nat), 22::nat) (R \<langle>\<rangle> (Abs_ivl (14::nat, 20::nat), 20::nat) \<langle>\<rangle>)) (Abs_ivl (6::nat, 16::nat)))
           = [(10::nat, 22::nat), (14::nat, 20::nat)]"
   apply (auto simp add:overlap_def  low_def high_def)
  by(auto simp add:Abs_ivl_inverse)

fun finds_list::"('a \<times>'a) list \<Rightarrow> ('a \<times>'a) \<Rightarrow> ((('a \<times>'a)) \<times>(('a \<times>'a))) list"where
"finds_list [] y = []"|
"finds_list (x#xs) y =(x,y)#finds_list xs y"

fun find::"('a \<times>'a) list => ('a \<times>'a) list \<Rightarrow>((('a \<times>'a)) \<times>('a \<times>'a)) list"where
"find xs [] = []"|
"find xs (y#ys) =finds_list xs y @ (find xs ys)"

lemma"find [(16::nat, 28::nat)] [ (10::nat, 22::nat), (14::nat, 20::nat)]
   = [((16::nat, 28::nat), (10::nat, 22::nat)),( (16::nat, 28::nat), (14::nat, 20::nat))]"
  by auto

definition CS::"nat Coordinate_System" where
"CS \<equiv> ([(Abs_ivl (5::nat,12::nat),Abs_ivl(10::nat,22::nat)),(Abs_ivl (16,28),Abs_ivl(14,20))] ,
         [(Abs_ivl (14::nat,21::nat),Abs_ivl(6::nat,16::nat)),(Abs_ivl (26,34),Abs_ivl(4,12))])"

fun AbstoRep::"('a::linorder ivl \<times> 'a::linorder ivl) list\<Rightarrow>(('a \<times>'a)\<times>('a\<times>'a)) list"where
"AbstoRep [] = []"|
"AbstoRep (x#xs) = (Rep_ivl (fst x),Rep_ivl (snd x)) # (AbstoRep xs) "
  
definition judge where
"judge cs t r = 
(\<exists>x.(x\<in>set(find(find_overlap(X_P_Achievements cs t) (fst r))
             (find_overlap(Y_P_Achievements cs t) (snd r)))
                    \<and> x\<in>set(AbstoRep(fst cs))))"

lemma test0:"judge CS Leaf (Abs_ivl (14::nat,21::nat),Abs_ivl(6::nat,16::nat)) = True"
  apply(simp add:CS_def judge_def)
  apply(simp add:X_P_Achievements_def Y_P_Achievements_def X_Dimension_def Y_Dimension_def map_Publication_def)
  apply(simp add:insert_IntervalT_def overlap_def low_def high_def ivl_less Abs_ivl_inverse)
  by auto 

lemma test1:"(judge CS Leaf (Abs_ivl (26::nat,34::nat),Abs_ivl(4::nat,12::nat))) \<Longrightarrow> False  "
  apply(simp add:CS_def judge_def)
  apply(simp add:X_P_Achievements_def Y_P_Achievements_def X_Dimension_def Y_Dimension_def map_Publication_def)
  by(simp add:insert_IntervalT_def overlap_def low_def high_def ivl_less  Abs_ivl_inverse )
 
definition Match::"'a Coordinate_System \<Rightarrow>
                        'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a Region \<Rightarrow>bool"
 where"Match cs t r \<equiv> (search (X_P_Achievements cs t) (fst r))
                  \<and>(search (Y_P_Achievements cs t) (snd r)) \<and> judge cs t r"
                                          
fun FRMA::"'a Coordinate_System \<Rightarrow>
                    'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> 'a Order \<Rightarrow>bool"
  where"FRMA cs t [] = False"|
       "FRMA cs t (y#ys) = (Match cs t y \<or> FRMA cs t ys)"

lemma Inv_ach:" inv_rb_it t \<Longrightarrow> inv_max_hi (P_Achievement x t)"
  apply(induct x arbitrary:t)
   apply(auto simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)
  by (meson inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_insert)

lemma Inv_bst:" inv_rb_it t \<Longrightarrow> inv_bst (P_Achievement x t)"
  apply(induct x arbitrary:t)
   apply(auto simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)
  by (meson inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_insert)

lemma Inv_invc:" inv_rb_it t \<Longrightarrow> invc (P_Achievement x t)"
  apply(induct x arbitrary:t)
   apply(auto simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)
  by (meson inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_insert)

lemma Inv_invh:" inv_rb_it t \<Longrightarrow> invh (P_Achievement x t)"
  apply(induct x arbitrary:t)
   apply(auto simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)
  by (meson inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_insert)

lemma Inv_color:" inv_rb_it t \<Longrightarrow>interval_color (P_Achievement x t) = Black"
  apply(induct x arbitrary:t)
   apply(auto simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)
  by (meson inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_insert)

lemma Inv_X_Achieve:"inv_rb_it t \<Longrightarrow> inv_rb_it (P_Achievement (X_Dimension x) t)"
  apply(induct x arbitrary:t)
 apply(simp add:X_P_Achievements_def X_Dimension_def inv_rb_it_def  map_Publication_def)+
by (auto simp add: Inv_ach Inv_bst Inv_invc Inv_invh Inv_color inv_rb_it_def)

lemma Inv_Y_Achieve:"inv_rb_it t \<Longrightarrow> inv_rb_it (P_Achievement (Y_Dimension y) t)"
   apply(induct y arbitrary:t)
  apply(simp add:Y_P_Achievements_def Y_Dimension_def inv_rb_it_def)+
  apply auto
by (auto simp add: Inv_ach Inv_bst Inv_invc Inv_invh Inv_color inv_rb_it_def)

theorem Inv_Achieve:"inv_rb_it t \<Longrightarrow>inv_rb_it (P_Achievement xs t)"
  apply(induct xs arbitrary:t)
   apply(simp add:inv_rb_it_def)+
  by (metis Inv_ach Inv_bst Inv_color Inv_invc Inv_invh inv_color.elims(3) inv_rb_it_def rbt_insert)
 

lemma Inv_X_Delete:"inv_rb_it (P_Achievement (X_Dimension x) t)
          \<Longrightarrow> inv_rb_it (P_Delete xs ((P_Achievement (X_Dimension x) t)))"
  apply(induct xs arbitrary:t x)
   apply(simp add:inv_rb_it_def X_P_Achievements_def X_Dimension_def)+
  apply auto
  by (metis P_Achievement.simps(1) fstI inv_color.simps inv_rb_it_def list.simps(8) map_Publication_def rbt_delete)+
 
lemma Inv_Y_Delete:"inv_rb_it (P_Achievement (Y_Dimension x) t)
          \<Longrightarrow> inv_rb_it (P_Delete xs ((P_Achievement (Y_Dimension x) t)))"
  apply(induct xs arbitrary:t x)
  apply(simp add:inv_rb_it_def Y_P_Achievements_def Y_Dimension_def)+
  apply auto
by (metis P_Achievement.simps(1) fstI inv_rb_it_def list.simps(8) map_Publication_def rbt_delete inv_color.simps)+

theorem Inv_Delete:"inv_rb_it t \<Longrightarrow> inv_rb_it (P_Delete xs t)"
  apply(induct xs arbitrary:t)
  apply(simp add:inv_rb_it_def)+
  by (metis inv_color.elims(2) inv_color.elims(3) inv_rb_it_def rbt_delete)

lemma Inv_X_Search:"inv_rb_it t\<Longrightarrow>(search (X_P_Achievements CS t) (fst r)) 
                         = has_overlap(set_tree(X_P_Achievements CS t)) (fst r)"
  apply(induct CS arbitrary:t r)
  apply(auto simp : X_P_Achievements_def X_Dimension_def inv_rb_it_def)
  apply (simp add: has_overlap_def overlap_def search_correct inv_bst_def)
  apply (metis Inv_Achieve has_overlap_def inv_bst_def inv_color.elims(3) inv_rb_it_def overlap_def rbt_search)
  by (meson Inv_Achieve inv_color.elims(3) inv_rb_it_def rbt_search)

lemma Inv_Y_Search:"inv_rb_it t\<Longrightarrow>(search (Y_P_Achievements CS t) (snd r)) 
                         = has_overlap(set_tree(Y_P_Achievements CS t)) (snd r)"
  apply(induct CS arbitrary:t r)
  apply(auto simp : Y_P_Achievements_def Y_Dimension_def inv_rb_it_def)
  by (meson Inv_Achieve inv_color.elims(3) inv_rb_it_def rbt_search)+

definition X_has_overlap::"'a Coordinate_System \<Rightarrow>'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a Region \<Rightarrow> bool" where
"X_has_overlap cs t r \<equiv> has_overlap(set_tree(X_P_Achievements cs t)) (fst r)"

definition Y_has_overlap::"'a Coordinate_System \<Rightarrow>'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow>'a Region \<Rightarrow> bool" where
"Y_has_overlap cs t r \<equiv>has_overlap(set_tree(Y_P_Achievements cs t)) (snd r)"

theorem match_correct:"inv_rb_it t\<Longrightarrow> Match cs t r =
                           (X_has_overlap cs t r \<and> Y_has_overlap cs t r \<and> judge cs t r)"
  apply(simp add:X_has_overlap_def Y_has_overlap_def Match_def)                         
  by(simp add: Inv_Achieve  X_P_Achievements_def Y_P_Achievements_def rbt_search)
 
theorem Matchs:"c\<in>set C \<Longrightarrow> Match cs t c \<Longrightarrow> FRMA cs t C "
  apply(induct C arbitrary:cs t)
  by  auto

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
locale Region_Match = Tree +
fixes Search :: "'t \<Rightarrow> 'a::linorder ivl \<Rightarrow> bool"
fixes X_overlap::"'a::linorder Coordinate_System \<Rightarrow>'t \<Rightarrow>'a Region \<Rightarrow>bool"
fixes Y_overlap::"'a::linorder Coordinate_System \<Rightarrow>'t \<Rightarrow>'a Region \<Rightarrow>bool"
fixes Judge::"'a::linorder Coordinate_System \<Rightarrow>'t \<Rightarrow>'a Region \<Rightarrow>bool"
fixes match::"'a::linorder Coordinate_System \<Rightarrow>'t \<Rightarrow>'a Region \<Rightarrow>bool"
assumes set_overlap: "invar s \<Longrightarrow> Search s x = has_overlap (set s) x"
assumes match_correct:"invar s \<Longrightarrow>match cs s r = 
                         (X_overlap cs s r \<and>Y_overlap cs s r \<and>Judge cs s r)"


interpretation FRMA:Region_Match
  where empty = Leaf and insert = insert_IntervalT and delete = delete_IntervalT
  and Search = search and  isin = isin_IntervalT and set = set_tree 
  and invar = inv_rb_it and match = Match 
  and X_overlap = X_has_overlap and Y_overlap = Y_has_overlap and Judge = judge 
proof (standard, goal_cases)
  case 1
  then show ?case  by (simp add:inv_rb_it_def inv_bst_def)
next
  case 2
  then show ?case by (simp add: inv_rb_it_def RB_Interval.isin_set_inorder inv_bst_def) 
next
  case (3 s x)
  then show ?case by(simp add: inorder_insert set_ins_list inv_rb_it_def flip: set_inorder inv_bst_def)
next
  case (4 s x)
  then show ?case by(simp add: inorder_del set_del_list inv_rb_it_def flip: set_inorder inv_bst_def)
next
  case 5
  then show ?case by (simp add: inv_bst_def inv_rb_it_def) 
next
  case (6 s x)
  then show ?case using inv_rb_it_def rbt_insert by auto
next
  case (7 s x)
  then show ?case using inv_rb_it_def rbt_delete by auto 
next
  case (8 s x)
  then show ?case using rbt_search by auto
next
  case (9 s CS r)
  then show ?case by (simp add: match_correct)
qed

end