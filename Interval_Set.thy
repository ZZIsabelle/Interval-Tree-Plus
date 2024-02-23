theory Interval_Set
  imports   
  "Cmp"
  "List_Ins_Del"
  "Isin2"
begin
typedef (overloaded) 'a::linorder ivl =
  "{p :: 'a \<times> 'a. fst p \<le> snd p}" by auto

definition low :: "'a::linorder ivl \<Rightarrow> 'a" where
"low p = fst (Rep_ivl p)"

definition high :: "'a::linorder ivl \<Rightarrow> 'a" where
"high p = snd (Rep_ivl p)"

lemma ivl_is_interval: "low p \<le> high p"
by (metis Rep_ivl high_def low_def mem_Collect_eq)

lemma ivl_inj: "low p = low q \<Longrightarrow> high p = high q \<Longrightarrow> p = q"
by (metis Rep_ivl_inverse high_def low_def prod_eqI)

instantiation ivl :: (linorder) linorder begin

definition ivl_less: "(x < y) = (low x < low y | (low x = low y \<and> high x < high y))"
definition ivl_less_eq: "(x \<le> y) = (low x < low y | (low x = low y \<and> high x \<le> high y))"

instance proof
  fix x y z :: "'a ivl"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    using ivl_less ivl_less_eq by force
  show b: "x \<le> x"
    by (simp add: ivl_less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    using ivl_less_eq by fastforce
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    using ivl_less_eq a ivl_inj ivl_less by fastforce
  show e: "x \<le> y \<or> y \<le> x"
    by (meson ivl_less_eq leI not_less_iff_gr_or_eq)
qed end

definition overlap :: "('a::linorder) ivl \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"overlap x y \<longleftrightarrow> (high x \<ge> low y \<and> high y \<ge> low x)"

definition has_overlap :: "('a::linorder) ivl set \<Rightarrow> 'a ivl \<Rightarrow> bool" where
"has_overlap S y \<longleftrightarrow> (\<exists>x\<in>S. overlap x y)"

datatype color = Red | Black

type_synonym 'a RBs_ivl_tree =  "(('a ivl * 'a)*color) tree"

abbreviation R where "R l a r \<equiv> Node l (a, Red) r"
abbreviation B where "B l a r \<equiv> Node l (a, Black) r"

fun max_hi :: "('a::order_bot) RBs_ivl_tree \<Rightarrow> 'a" where
"max_hi Leaf = bot" |
"max_hi (Node _ ((_,m),_) _) = m"

definition max3 :: "('a::linorder) ivl \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"max3 a m n = max (high a) (max m n)"

fun inv_max_hi :: "('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow> bool" where
"inv_max_hi Leaf \<longleftrightarrow> True" |
"inv_max_hi (Node l ((a, m),c) r) \<longleftrightarrow> 
                       (m = max3 a (max_hi l) (max_hi r) \<and> inv_max_hi l \<and> inv_max_hi r)"

fun set_tree :: "(('a*'b)*'c) tree \<Rightarrow> 'a set" where
"set_tree Leaf = {}" |
"set_tree (Node l ((a,_),_) r) = {a} \<union> set_tree l \<union> set_tree r"  

fun inorder :: "(('a*'b)*'c) tree \<Rightarrow> 'a list" where              
"inorder Leaf = []" |
"inorder (Node l ((a,_),_) r) = inorder l @ a # inorder r"

fun node ::"('a::{linorder,order_bot}) RBs_ivl_tree \<Rightarrow>'a RBs_ivl_tree"where
"node Leaf = Leaf"|
"node (Node l ((a,_),c) r) = (let l' = node l ;r' = node r in
                              (Node l' ((a,max3 a (max_hi l') (max_hi r')),c) r'))"

fun paint :: "color \<Rightarrow> 'a RBs_ivl_tree \<Rightarrow> 'a RBs_ivl_tree" where       
"paint c Leaf = Leaf" |
"paint c (Node l ((a,m),_) r) = Node l ((a,m),c) r"

fun interval_color :: "'a::{linorder,order_bot} RBs_ivl_tree \<Rightarrow> color" where  
"interval_color Leaf = Black" |
"interval_color (Node _ ((_,_), c) _) = c"

end