theory IntervalTreeplus
  imports   
  "Interval_Set"

begin   
fun baliL :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> ('a ivl * 'a) \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where
"baliL (R (R t1 a t2) b t3) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL (R t1 a (R t2 b t3)) c t4 = R (B t1 a t2) b (B t3 c t4)" |
"baliL t1 a t2 = B t1 a t2"

fun baliR :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> ('a ivl * 'a) \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where                                                     
"baliR t1 a (R t2 b (R t3 c t4)) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a (R (R t2 b t3) c t4) = R (B t1 a t2) b (B t3 c t4)" |
"baliR t1 a t2 = B t1 a t2"

fun baldL :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> ('a ivl * 'a) \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where
"baldL (R t1 a t2) b t3 = R (B t1 a t2) b t3" |
"baldL t1 a (B t2 b t3) = baliR t1 a (R t2 b t3)" |
"baldL t1 a (R (B t2 b t3) c t4) = R (B t1 a t2) b (baliR t3 c (paint Red t4))" |
"baldL t1 a t2 = R t1 a t2"

fun baldR :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> ('a ivl * 'a) \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where
"baldR t1 a (R t2 b t3) = R t1 a (B t2 b t3)" |
"baldR (B t1 a t2) b t3 = baliL(R t1 a t2) b t3" |
"baldR (R t1 a (B t2 b t3)) c t4 = R(baliL (paint Red t1) a t2) b (B t3 c t4)" |
"baldR t1 a t2 = R t1 a t2"

fun bheight :: "('a::{linorder,order_bot}) RBs_ivl_tree  \<Rightarrow> nat" where
"bheight Leaf = 0" |
"bheight (Node l (x, c) r) = (if c = Black then bheight l + 1 else bheight l)"

fun invc :: " ('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> bool" where
"invc Leaf = True" |
"invc (Node l (a,c) r) =
  ((c = Red \<longrightarrow> interval_color l = Black \<and> interval_color r = Black) \<and> invc l \<and> invc r)"

abbreviation invc2 :: "('a::{linorder,order_bot}) RBs_ivl_tree  \<Rightarrow> bool" where
"invc2 t \<equiv> invc(paint Black t)"

fun invh :: "('a::{linorder,order_bot}) RBs_ivl_tree  \<Rightarrow> bool" where
 "invh Leaf = True" |                                      
 "invh (Node l (x, c) r) = (bheight l = bheight r \<and> invh l \<and> invh r)"

definition empty :: "'a RBs_ivl_tree" where
"empty = Leaf"

fun ins :: "'a::{linorder,order_bot} ivl \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" 
  where
"ins x Leaf = R Leaf (x,high x) Leaf" |
"ins x (B l (a,m) r) =
  (case cmp x a of
     LT \<Rightarrow> (baliL (ins x l) (a,m) r) |
     GT \<Rightarrow> (baliR l (a,m) (ins x r)) |
     EQ \<Rightarrow> B l (a,m) r)" |
"ins x (R l (a,m) r) =
  (case cmp x a of
    LT \<Rightarrow> (R (ins x l) (a,m) r) |
    GT \<Rightarrow> (R l (a,m) (ins x r)) |
    EQ \<Rightarrow> R l (a,m) r)"

definition insert_IntervalT::"'a::{linorder,order_bot} ivl \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" 
  where"insert_IntervalT x t = node (paint Black (ins x t))"
 
fun split_min :: "'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> (('a ivl*'a) * 'a RBs_ivl_tree)" where
"split_min (Node l ((a, m),_)  r) =
  (if l = Leaf then ((a,m),r)
   else let (x,l') = split_min l 
         in (x, if interval_color l = Black then baldL l' (a,m) r else R l' (a,m) r))"
 
fun del :: "'a::{linorder,order_bot} ivl \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where
"del x Leaf = Leaf" |
"del x (Node l ((a, m),_) r) =
  (case cmp x a of
      LT \<Rightarrow> let l' = del x l in if l \<noteq> Leaf \<and> interval_color l = Black
            then baldL l' (a,m) r else R l' (a,m) r  |
      GT \<Rightarrow> let r' = del x r in if r\<noteq> Leaf \<and> interval_color r = Black
            then baldR l (a,m) r' else R l (a,m) r'  |
      EQ \<Rightarrow> if r = Leaf then l else let ((a',m'),r') = split_min r in
            if interval_color r = Black 
            then baldR l (a',m') r' else R l (a',m') r') "
 
definition delete_IntervalT::"'a::{linorder,order_bot} ivl \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree"  
where "delete_IntervalT x t = node (paint Black (del x t))"

fun search :: "'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"search Leaf x = False" |
"search (Node l ((a,_),_) r) x =
  (if overlap x a then True
   else if l \<noteq> Leaf \<and> max_hi l \<ge> low x then search l x
   else search r x)"

definition inv_bst::"('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> bool" 
  where "inv_bst t \<equiv> sorted(inorder t)"

fun inv_color::"'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> bool"
  where"inv_color t = (interval_color t = Black)"

definition inv_rb_it :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> bool" 
  where"inv_rb_it t = (inv_max_hi t \<and> inv_bst t \<and>invc t \<and> invh t \<and> inv_color t)"
                                                                     
fun isin_IntervalT :: "'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"isin_IntervalT Leaf x = False" |
"isin_IntervalT (Node l ((a,_),_) r) x =
  (case cmp x a of
     LT \<Rightarrow> isin_IntervalT l x |
     EQ \<Rightarrow> True |
     GT \<Rightarrow> isin_IntervalT r x)"

lemma max_hi_is_max:
  "inv_max_hi t \<Longrightarrow>  a \<in> set_tree t \<Longrightarrow> high a \<le> max_hi t"
  by(induct t, auto simp add: max3_def max_def)

lemma max_hi_exists:
  "inv_max_hi t \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> \<exists>a\<in>set_tree t. high a = max_hi t"
  apply(induct t )
  apply simp
  apply(auto simp add: max3_def max_def le_bot)
  apply (metis bot.extremum_uniqueI max_hi.simps(1))
  by fastforce

lemma node_correct:"inv_max_hi (node t)" 
  apply(induct t)
  apply simp
  by (metis inv_max_hi.simps(2) node.simps(2) prod.exhaust)

subsection "Delete Functional Correctness Proofs"

lemma inorder_paint: "inorder(paint c t) = inorder t"
  apply(cases t) 
  by auto

lemma inorder_baliL:
  "inorder(baliL l (a,m) r) = inorder l @ a # inorder r"
  apply(cases "(l,(a,m),r)" rule: baliL.cases)
  by auto

lemma inorder_baliR:
  "inorder(baliR l (a,m) r) = inorder l @ a # inorder r"
  apply(cases "(l,(a,m),r)" rule: baliR.cases) 
  by auto

lemma inorder_ins:
  "sorted(inorder t) \<Longrightarrow> inorder(ins x t) = ins_list x (inorder t)"
  apply(induction x t rule: ins.induct)
  by(auto simp: ins_list_simps inorder_baliL inorder_baliR)

lemma inorder_node:"inorder(node t) = inorder t" 
  apply(induct t)
  apply auto
  by (metis Interval_Set.inorder.simps(2))

lemma set_inorder[simp]: "set (inorder t) = set_tree t"
  apply (induction t)
  by auto

subsubsection \<open>Isin Functional Correctness Proofs\<close>
lemma isin_set_inorder: "sorted(inorder t) \<Longrightarrow> isin_IntervalT t x = (x \<in> set(inorder t))"
  apply(induct t)
  apply(auto simp: isin_simps)
  apply (meson cmp_def)
  by auto

theorem inorder_insert:
  "sorted(inorder t) \<Longrightarrow> inorder(insert_IntervalT x t) = ins_list x (inorder t)"
  by (auto simp add: insert_IntervalT_def inorder_ins inorder_paint inorder_node)

subsubsection \<open>Delete Functional Correctness Proofs\<close>

lemma inorder_baldL:"inorder (baldL l (a,m) r) = inorder l @ a # inorder r"
  apply(cases "(l,(a,m),r)" rule: baldL.cases)
  by (auto simp add: inorder_baliR inorder_paint)

lemma split_minD:
  "split_min t = ((a,m),t') \<Longrightarrow> t \<noteq> Leaf \<Longrightarrow> a # inorder t' = inorder t"
  apply(induction t arbitrary: t' rule: split_min.induct)
  by(auto simp: inorder_baldL sorted_lems split: prod.splits if_splits)
 
lemma inorder_baldR:"inorder (baldR l (a, m) r) = inorder l @ a # inorder r"
  apply(cases "(l,(a,m),r)" rule: baldR.cases)
  apply (auto simp add: inorder_baliL)
  apply (simp add: inorder_paint)
  using inorder_paint by auto

lemma inorder_del:
 "sorted(inorder t) \<Longrightarrow>  inorder(delete_IntervalT x t) = del_list x (inorder t)"
  apply(simp add:delete_IntervalT_def)
  apply(induction x t rule: del.induct)
  apply(auto simp: del_list_simps inorder_baldL inorder_baldR split_minD split: prod.splits)
  apply (metis inorder.simps(1) inorder.simps(2) inorder_node)
  apply (simp add: inorder_baldR inorder_node inorder_paint)
  apply (simp add: inorder_node inorder_paint) 
  apply (simp add:Let_def inorder_baldL inorder_node inorder_paint)
  apply (simp add: inorder_baldR inorder_node inorder_paint split_minD)
  apply (simp add:Let_def inorder_baldL inorder_node inorder_paint)
  apply (metis inorder.simps(2) inorder_node inorder_paint)
  apply (metis inorder.simps(2) inorder_node split_minD)
  by (simp add: Let_def inorder_baldL inorder_node inorder_paint)

subsection "Insert and Delete Inv_Max Proofs"
lemma inv_max_hi_insert:
  "inv_max_hi t \<Longrightarrow> inv_max_hi (insert_IntervalT x t)"
  apply(simp add:insert_IntervalT_def )
  by (simp add: node_correct)

lemma inv_max_hi_delete:
  "inv_max_hi t \<Longrightarrow> inv_max_hi (delete_IntervalT x t)"
  apply(simp add:delete_IntervalT_def)
  by (simp add: node_correct)

lemma search_correct:
  "inv_max_hi t \<and> sorted(inorder t) \<Longrightarrow> search t x = has_overlap (set_tree t) x"
  apply(induct t)
  apply(auto simp : has_overlap_def overlap_def)
  apply(metis UnCI sorted_cons sorted_wrt_append)
  apply(metis UnCI sorted_cons sorted_wrt_append)
  apply(meson sorted_mid_iff sorted_snoc)
  apply(meson sorted_mid_iff sorted_snoc)
  apply(metis dual_order.trans max_hi_is_max)
  apply(metis (no_types) dual_order.trans max_hi_is_max)
  apply(metis set_inorder ivl_less_eq linorder_not_less order_le_less_trans sorted_Cons_iff sorted_mid_iff)
  apply(metis set_inorder dual_order.strict_trans1 ivl_is_interval ivl_less_eq linorder_not_less max_hi_exists sorted_mid_iff sorted_snoc_iff)
  apply(metis sorted_cons sorted_mid_iff)
  by(metis sorted_cons sorted_mid_iff)

subsection \<open>RB Structural invariants\<close>
subsection \<open>Insert invariants\<close>

lemma neq_Black[simp]: "(c \<noteq> Black) = (c = Red)"
  by (cases c) auto

lemma invc2I: "invc t \<Longrightarrow> invc2 t"
  apply (cases t rule: tree2_cases)
  by auto

lemma color_paint_Black: "interval_color  (paint Black t) = Black"
 by (cases t) auto

lemma paininvh_node: "paint c2 (paint c1 t) = paint c2 t"
 by (cases t) auto

lemma invh_paint: "invh t \<Longrightarrow> invh (paint c t)"
 by (cases t) auto

lemma invc_baliL:
  "\<lbrakk>invc2 l; invc r\<rbrakk> \<Longrightarrow> invc (baliL l a r)" 
 by (induct l a r rule: baliL.induct) auto

lemma invc_baliR:
  "\<lbrakk>invc l; invc2 r\<rbrakk> \<Longrightarrow> invc (baliR l a r)" 
 by (induct l a r rule: baliR.induct) auto

lemma bheight_baliL:
  "bheight l = bheight r \<Longrightarrow> bheight (baliL l a r) = Suc (bheight l)"
 by (induct l a r rule: baliL.induct) auto

lemma bheight_baliR:
  "bheight l = bheight r \<Longrightarrow> bheight (baliR l a r) = Suc (bheight l)"
 by (induct l a r rule: baliR.induct) auto

lemma invh_baliL: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliL l a r)"
 by (induct l a r rule: baliL.induct) auto

lemma invh_baliR: 
  "\<lbrakk> invh l; invh r; bheight l = bheight r \<rbrakk> \<Longrightarrow> invh (baliR l a r)"
 by (induct l a r rule: baliR.induct) auto

lemma inv_baliR: "\<lbrakk> invh l; invh r; invc l; invc2 r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliR l a r) \<and> invh (baliR l a r) \<and> bheight (baliR l a r) = Suc (bheight l)"
 by (induct l a r rule: baliR.induct) auto

lemma inv_baliL: "\<lbrakk> invh l; invh r; invc2 l; invc r; bheight l = bheight r \<rbrakk>
 \<Longrightarrow> invc (baliL l a r) \<and> invh (baliL l a r) \<and> bheight (baliL l a r) = Suc (bheight l)"
 by (induct l a r rule: baliL.induct) auto

subsubsection \<open>Insertion\<close>

lemma invc_ins: "invc t \<longrightarrow> invc2 (ins x t) \<and> (interval_color t = Black \<longrightarrow> invc (ins x t))"
  apply (induct x t rule: ins.induct) 
  by(auto simp: invc_baliL invc_baliR invc2I)

lemma invh_ins: "invh t \<Longrightarrow> invh (ins x t) \<and> bheight (ins x t) = bheight t"
  apply(induct x t rule: ins.induct)
  by(auto simp: invh_baliL invh_baliR bheight_baliL bheight_baliR)

lemma inv_ins: "\<lbrakk> invc t; invh t \<rbrakk> \<Longrightarrow>
  invc2 (ins x t) \<and> (interval_color t = Black \<longrightarrow> invc (ins x t)) \<and>
  invh(ins x t) \<and> bheight (ins x t) = bheight t"
  apply(induct x t rule: ins.induct) 
  by(auto simp: inv_baliL inv_baliR invc2I)

lemma invc_node:"invc t \<Longrightarrow> invc(node t)"
  apply(induct t)
  apply (auto simp:Let_def)
  apply (metis (no_types, lifting) interval_color.elims interval_color.simps(2) node.simps(1) node.simps(2))
  by (metis (mono_tags, lifting) interval_color.elims interval_color.simps(2) node.simps(1) node.simps(2))

lemma bheight_node:"bheight t = bheight(node t)"
  apply(induct t)
  by(auto simp:Let_def) 

lemma invh_node:"invh t \<Longrightarrow> invh(node t)"
  apply(induct t)
  apply(auto simp:Let_def )
  by(metis bheight_node)
  
lemma inv_node:"inv_rb_it t \<Longrightarrow> inv_rb_it (node t)"
  apply(induct t)
  apply (auto simp :inv_rb_it_def)
  apply (metis node_correct inv_max_hi.simps(2))
  apply (metis Interval_Set.inorder.simps(2) inorder_node inv_bst_def )
  apply (metis (full_types) invc.simps(2) neq_Black invc_node)
  apply (metis invh.simps(2) bheight_node invh_node)
  by (meson interval_color.simps(2))

lemma ins_color_node:"interval_color (paint Black (ins x t)) = Black \<Longrightarrow> interval_color (node (paint Black (ins x t))) = Black"
  apply(induct t)
   apply (auto simp:Let_def)
  by (metis interval_color.elims interval_color.simps(2) node.simps(1) node.simps(2))

lemma del_color_node:"interval_color (paint Black (del x t)) = Black \<Longrightarrow> interval_color (node (paint Black (del x t))) = Black"
  apply(induct t)
  apply simp
  by (metis interval_color.elims interval_color.simps(2) node.simps(1) node.simps(2))
  
subsection \<open>Delete invariants\<close>

lemma bheight_paint_Red:
  "interval_color t = Black \<Longrightarrow> bheight (paint Red t) = bheight t - 1"
by (cases t) auto

lemma invh_baldL_invc:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  invc r \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
  apply(induct l a r rule: baldL.induct)
  by(auto simp: invh_baliR invh_paint bheight_baliR bheight_paint_Red)

lemma invh_baldL_Black: 
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r;  interval_color r = Black \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r"
  apply(induct l a r rule: baldL.induct) 
  by(auto simp add: invh_baliR bheight_baliR) 

lemma invc_baldL: "\<lbrakk>invc2 l; invc r; interval_color r = Black\<rbrakk> \<Longrightarrow> invc (baldL l a r)"
  apply(induct l a r rule: baldL.induct) 
  by(auto simp add: invc_baliR)

lemma invc2_baldL: "\<lbrakk> invc2 l; invc r \<rbrakk> \<Longrightarrow> invc2 (baldL l a r)"
  apply(induct l a r rule: baldL.induct) 
  by(auto simp: invc_baliR paininvh_node invc2I)

lemma invh_baldR_invc:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1;  invc l \<rbrakk>
  \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l"
  apply(induct l a r rule: baldR.induct)
  by(auto simp: invh_baliL bheight_baliL invh_paint bheight_paint_Red)
 
lemma invc_baldR: "\<lbrakk>invc l; invc2 r; interval_color l = Black\<rbrakk> \<Longrightarrow> invc (baldR l a r)"
  apply(induct l a r rule: baldR.induct) 
  by(auto simp add: invc_baliL)

lemma invc2_baldR: "\<lbrakk> invc l; invc2 r \<rbrakk> \<Longrightarrow>invc2 (baldR l a r)"
  apply(induct l a r rule: baldR.induct) 
  by(auto simp: invc_baliL paininvh_node invc2I)

lemma inv_baldL:
  "\<lbrakk> invh l;  invh r;  bheight l + 1 = bheight r; invc2 l; invc r \<rbrakk>
   \<Longrightarrow> invh (baldL l a r) \<and> bheight (baldL l a r) = bheight r
  \<and> invc2 (baldL l a r) \<and> (interval_color r = Black \<longrightarrow> invc (baldL l a r))"
  apply(induct l a r rule: baldL.induct)
  apply auto[1]
  using invc2_baldL invc_baldL invh_baldL_invc apply blast
  using invc2_baldL invc_baldL invh_baldL_invc apply blast
  using invc2_baldL invc_baldL invh_baldL_invc apply blast
  using invc2_baldL invc_baldL invh_baldL_invc apply blast
  by auto

lemma inv_baldR:
  "\<lbrakk> invh l;  invh r;  bheight l = bheight r + 1; invc l; invc2 r \<rbrakk>
   \<Longrightarrow> invh (baldR l a r) \<and> bheight (baldR l a r) = bheight l
  \<and> invc2 (baldR l a r) \<and> (interval_color l = Black \<longrightarrow> invc (baldR l a r))"
  apply(induct l a r rule: baldR.induct)
  apply force
  using invc2_baldR invc_baldR invh_baldR_invc apply blast
  using invc2_baldR invc_baldR invh_baldR_invc apply blast
  apply (meson invc2_baldR invc_baldR invh_baldR_invc)
  apply (meson invc2_baldR invc_baldR invh_baldR_invc)
  by auto

lemma neq_LeafD: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x c r. t = Node l (x,c) r"
  by(cases t rule: tree2_cases) auto

subsection \<open>Structural invariants\<close>
lemma neq_Red[simp]: "(c \<noteq> Red) = (c = Black)"
 by (cases c) auto

lemma inv_split_min: "\<lbrakk> split_min t = (x,t'); t \<noteq> Leaf; invh t; invc t \<rbrakk> \<Longrightarrow>
   invh t' \<and>
   (interval_color t = Red \<longrightarrow> bheight t' = bheight t \<and> invc t') \<and>
   (interval_color t = Black \<longrightarrow> bheight t' = bheight t - 1 \<and> invc2 t')"
  apply(induction t arbitrary: x t' rule: split_min.induct)
  apply(auto simp: inv_baldR inv_baldL invc2I  dest!: neq_LeafD)
  apply(auto split!: prod.splits if_splits)
  apply (smt (verit, del_insts) add_cancel_right_right add_diff_cancel_right' bheight.simps(2) interval_color.elims inv_baldL plus_1_eq_Suc)
  apply (smt (verit) add_cancel_right_right add_diff_cancel_right' bheight.simps(2) interval_color.elims inv_baldL plus_1_eq_Suc)
  apply (simp add: invc2I)
  apply (simp add: invc2_baldL)
  apply (metis (no_types, opaque_lifting) Suc_eq_plus1 Suc_pred bheight.elims interval_color.simps(2) invh_baldL_Black not_gr_zero old.prod.exhaust zero_eq_add_iff_both_eq_0 zero_neq_one)
  apply (metis Suc_eq_plus1 Suc_pred bheight.elims interval_color.simps(2) invh_baldL_Black not_gr_zero old.prod.exhaust zero_eq_add_iff_both_eq_0 zero_neq_one)
  apply (simp add: invc_baldL)
  apply (metis Suc_eq_plus1 Suc_pred bheight.elims interval_color.simps(2) invh_baldL_Black not_gr_zero old.prod.exhaust zero_eq_add_iff_both_eq_0 zero_neq_one)
  by (auto simp add: invc2_baldL invc2I)

lemma inv_del: "\<lbrakk> invh t; invc t \<rbrakk> \<Longrightarrow>
   invh (del x t) \<and>
   (interval_color t = Red \<longrightarrow> bheight (del x t) = bheight t \<and> invc (del x t)) \<and>
   (interval_color t = Black \<longrightarrow> bheight (del x t) = bheight t - 1 \<and> invc2 (del x t))"
  apply (induction x t rule: del.induct)
  by(auto simp: inv_baldR inv_baldL invc2I Let_def  
     dest!: inv_split_min 
      dest: neq_LeafD 
        split!: prod.splits if_splits)

theorem set_isin:"inv_rb_it t \<Longrightarrow> isin_IntervalT t x = (x \<in> set_tree t)"
  by (simp add: isin_set_inorder inv_bst_def inv_rb_it_def)

theorem set_insert:"inv_rb_it t \<Longrightarrow>set_tree (insert_IntervalT x t) = set_tree t \<union> {x}"
  by(simp add: inorder_insert set_ins_list inv_rb_it_def flip: set_inorder inv_bst_def)

theorem set_delete:"inv_rb_it t \<Longrightarrow>set_tree (delete_IntervalT x t) = set_tree t - {x}"
  by(simp add: inorder_del set_del_list inv_rb_it_def flip: set_inorder inv_bst_def)

theorem rbt_insert: "inv_rb_it t \<Longrightarrow> inv_rb_it (insert_IntervalT x t)"
  apply (auto simp add:invh_paint inv_rb_it_def insert_IntervalT_def)
  apply (simp add: node_correct )
  apply (simp add: inorder_ins inorder_node inorder_paint sorted_ins_list inv_bst_def)
  apply (simp add: invc_ins invc_node)
  apply (simp add: inv_ins invh_paint invh_node )
  by (simp add: color_paint_Black ins_color_node)

theorem rbt_delete: "inv_rb_it t \<Longrightarrow> inv_rb_it (delete_IntervalT x t)"
  apply(auto simp: delete_IntervalT_def  inv_rb_it_def node_correct )
  apply (metis delete_IntervalT_def inorder_del sorted_del_list inv_bst_def)
  apply (simp add: inv_del invc_node)
  apply (simp add: inv_del invh_paint invh_node)
  by (simp add: color_paint_Black del_color_node)

theorem rbt_search:
  "inv_rb_it t\<Longrightarrow> search t x = has_overlap (set_tree t) x"
  by (simp add: inv_rb_it_def search_correct inv_bst_def)
                                    
end
  



