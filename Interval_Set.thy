theory Interval_Set
  imports   
  "Cmp"
  "List_Ins_Del"
  "Isin2"
begin
typedef (overloaded) 'a::linorder ivl =
  "{p :: 'a × 'a. fst p ≤ snd p}" by auto

definition low :: "'a::linorder ivl ⇒ 'a" where
"low p = fst (Rep_ivl p)"

definition high :: "'a::linorder ivl ⇒ 'a" where
"high p = snd (Rep_ivl p)"

lemma ivl_is_interval: "low p ≤ high p"
by (metis Rep_ivl high_def low_def mem_Collect_eq)

lemma ivl_inj: "low p = low q ⟹ high p = high q ⟹ p = q"
by (metis Rep_ivl_inverse high_def low_def prod_eqI)

instantiation ivl :: (linorder) linorder  begin

definition ivl_less: "(x < y) = (low x < low y | (low x = low y ∧ high x < high y))"
definition ivl_less_eq: "(x ≤ y) = (low x < low y | (low x = low y ∧ high x ≤ high y))"
definition equal_ivl :: "'a::linorder ivl ⇒ 'a ivl ⇒ bool"
  where "equal_ivl x y ≡ (low x = low y ∧ high x = high y)"

instance proof
  fix x y z :: "'a ivl"
  show a: "(x < y) = (x ≤ y ∧ ¬ y ≤ x)"
    using ivl_less ivl_less_eq by force
  show b: "x ≤ x"
    by (simp add: ivl_less_eq)
  show c: "x ≤ y ⟹ y ≤ z ⟹ x ≤ z"
    using ivl_less_eq by fastforce
  show d: "x ≤ y ⟹ y ≤ x ⟹ x = y"
    using ivl_less_eq a ivl_inj ivl_less by fastforce
  show e: "x ≤ y ∨ y ≤ x"
    by (meson ivl_less_eq leI not_less_iff_gr_or_eq)
qed end




definition overlap :: "('a::linorder) ivl ⇒ 'a ivl ⇒ bool" where
"overlap x y ⟷ (high x ≥ low y ∧ high y ≥ low x)"

definition has_overlap :: "('a::linorder) ivl set ⇒ 'a ivl ⇒ bool" where
"has_overlap S y ⟷ (∃x∈S. overlap x y)"

datatype color = Red | Black

type_synonym 'a RBs_ivl_tree =  "(('a ivl * 'a)*color) tree"

abbreviation R where "R l a r ≡ Node l (a, Red) r"
abbreviation B where "B l a r ≡ Node l (a, Black) r"

fun max_hi :: "('a::order_bot) RBs_ivl_tree ⇒ 'a" where
"max_hi Leaf = bot" |
"max_hi (Node _ ((_,m),_) _) = m"

definition max3 :: "('a::linorder) ivl ⇒ 'a ⇒ 'a ⇒ 'a" where
"max3 a m n = max (high a) (max m n)"

fun inv_max_hi :: "('a::{linorder,order_bot}) RBs_ivl_tree ⇒ bool" where
"inv_max_hi Leaf ⟷ True" |
"inv_max_hi (Node l ((a, m),c) r) ⟷ 
                       (m = max3 a (max_hi l) (max_hi r) ∧ inv_max_hi l ∧ inv_max_hi r)"

fun set_tree :: "(('a*'b)*'c) tree ⇒'a set" where
"set_tree Leaf = {}" |
"set_tree (Node l ((a,_),_) r) = {a} ∪ set_tree l ∪ set_tree r"  

fun inorder :: "(('a*'b)*'c) tree ⇒ 'a list" where              
"inorder Leaf = []" |
"inorder (Node l ((a,_),_) r) = inorder l @ a # inorder r"

fun node ::"('a::{linorder,order_bot}) RBs_ivl_tree ⇒'a RBs_ivl_tree"where
"node Leaf = Leaf"|
"node (Node l ((a,_),c) r) = (let l' = node l ;r' = node r in
                              (Node l' ((a,max3 a (max_hi l') (max_hi r')),c) r'))"

fun paint :: "color ⇒ 'a RBs_ivl_tree ⇒ 'a RBs_ivl_tree" where       
"paint c Leaf = Leaf" |
"paint c (Node l ((a,m),_) r) = Node l ((a,m),c) r"

fun interval_color :: "'a::{linorder,order_bot} RBs_ivl_tree ⇒ color" where  
"interval_color Leaf = Black" |
"interval_color (Node _ ((_,_), c) _) = c"

end
