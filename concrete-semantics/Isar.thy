theory Isar
    imports Main
begin 

lemma "\<not> surj (f :: 'a => 'a set)"
proof
    assume "surj f"
    then have "\<forall>A. \<exists>a. A = f a" by (simp add: surj_def)
    then have "\<exists>a. {x. x \<notin> f x} = f a" by blast
    thus "False" by blast
qed

lemma   
    fixes f :: "'a => 'a set"
    assumes s : "surj f"
    shows "False"
proof - 
    have "\<exists>a. {x. x \<notin> f x} = f a" using s
        by (auto simp: surj_def)
    thus "False" by blast
qed

end