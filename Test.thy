theory Test
  imports   
  "ITBM"
begin 
definition ivl_tree where
"ivl_tree \<equiv> Node Leaf ((Abs_ivl (0::nat, 5::nat),5::nat),Black) Leaf"
definition nat_ivl :: "nat ivl" where
 "nat_ivl = Abs_ivl (0, 5)"
definition nat_list::"(nat ivl) list"where
"nat_list  =  [Abs_ivl (0, 5),Abs_ivl (4, 5)]"
lemma"insert nat_ivl ivl_tree = ivl_tree"
  apply(simp add:insert_def nat_ivl_def ivl_tree_def max3_def high_def)
  by(simp add: Abs_ivl_inverse Rep_ivl_inverse)
lemma"insert (Abs_ivl (0::nat, 5::nat)) Leaf = ivl_tree"
  apply(simp add:insert_def max3_def high_def ivl_tree_def)
  by(simp add: Abs_ivl_inverse Rep_ivl_inverse)

definition CS::"nat Coordinate_System" where
"CS \<equiv> ([(Abs_ivl (5::nat,12::nat),Abs_ivl(10::nat,22::nat)),(Abs_ivl (16,28),Abs_ivl(14,20))] ,
         [(Abs_ivl (14::nat,21::nat),Abs_ivl(6::nat,16::nat)),(Abs_ivl (26,34),Abs_ivl(4,12))])"

lemma test1:"X_Dimension CS = [Abs_ivl (5::nat,12::nat),Abs_ivl (16,28)]"
  by(simp add:CS_def X_Dimension_def  map_Publication_def)

lemma test2:"Y_Dimension CS = [Abs_ivl (10::nat,22::nat),Abs_ivl (14,20)]"
  by(simp add:CS_def Y_Dimension_def  map_Publication_def)

lemma test3:"(X_P_Achievements CS \<langle>\<rangle>) = 
\<langle>\<langle>\<rangle>,((Abs_ivl (5::nat,12::nat),28::nat),Black),\<langle>\<langle>\<rangle>,((Abs_ivl (16::nat,28::nat),28::nat),Red),\<langle>\<rangle>\<rangle>\<rangle>"
  apply(simp add:CS_def X_P_Achievements_def X_Dimension_def map_Publication_def insert_def max3_def high_def)
  by(simp add: Abs_ivl_inverse ivl_less low_def high_def)

lemma test4:"(Y_P_Achievements CS \<langle>\<rangle>) = 
\<langle>\<langle>\<rangle>,((Abs_ivl (10::nat,22::nat),22::nat),Black),\<langle>\<langle>\<rangle>,((Abs_ivl (14::nat,20::nat),20::nat),Red),\<langle>\<rangle>\<rangle>\<rangle>"
  apply(simp add:CS_def Y_P_Achievements_def Y_Dimension_def map_Publication_def insert_def max3_def)
  by(simp add: Abs_ivl_inverse ivl_less low_def high_def)


lemma test5:"Match CS Leaf (Abs_ivl (14::nat,21::nat),Abs_ivl (6::nat,16::nat)) = True"
  apply(simp add:Match_def judge_def CS_def Y_P_Achievements_def Y_Dimension_def map_Publication_def insert_def X_P_Achievements_def X_Dimension_def)
  apply(simp add:overlap_def low_def high_def Abs_ivl_inverse ivl_less )
  by auto

lemma test6:"Match CS Leaf (Abs_ivl (26::nat,34::nat),Abs_ivl (4::nat,12::nat)) = False "
  apply(simp add:Match_def judge_def CS_def Y_P_Achievements_def Y_Dimension_def map_Publication_def insert_def X_P_Achievements_def X_Dimension_def)
  by(simp add:overlap_def low_def high_def Abs_ivl_inverse ivl_less max3_def)
 

end