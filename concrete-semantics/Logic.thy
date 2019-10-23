theory Logic
    imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree => 'a set" where
"set Tip = {}" |
"set (Node l n r) = (set l) Un {n} Un (set r)"

fun ord :: "int tree => bool" where
"ord Tip = True" |
"ord (Node l n r) = ((ALL lv : (set l). (lv < n)) & (ALL rv : (set r). (rv > n)))"

fun ins :: "int => int tree => int tree" where
"ins x Tip = Node Tip x Tip" |
"ins x (Node l v r) = (
    if x < v then Node (ins x l) v r
    else if x > v then Node l v (ins x r)
    else Node l v r
)"

lemma [simp] : "set (ins x t) = {x} Un set t"
    apply (induction t arbitrary: x)
    apply (auto)
done

lemma "ord t ==> ord (ins i t)"
    apply (induction t arbitrary: i)
    apply (auto)
done

lemma "\<forall>x. \<exists>y. xz = y" by auto
lemma "A \<subseteq> B \<inter> C ==> A \<subseteq> B \<union> C" by auto

fun evn :: "nat => bool" where
"evn 0 = True" | 
"evn (Suc 0) = False" | 
"evn (Suc (Suc n)) = evn n"

lemma evSS : "evn n ==> evn (Suc (Suc n))"
apply (induction n)
apply (auto)
done

(*
    This can also be proved using rule 'auto', with *or without* making the
    above lemma a simplification rule.
*)
lemma "evn (Suc (Suc (Suc (Suc 0))))"
    apply (rule evSS)
    apply (rule evSS)
    apply (auto)
done

inductive star :: "('a => 'a => bool) => 'a => 'a => bool" for r where
refl : "star r x x" |
step : "r x y ==> star r y z ==> star r x z"

lemma star_trans : "star r x y ==> star r y z ==> star r x z"
apply (induction rule: star.induct)
apply (assumption) (* solve first case by applying refl *)
apply (metis step)
done

inductive palindrome :: "'a list => bool" where
"palindrome []" |
"palindrome [x]" | 
"palindrome xs ==> palindrome (a#xs@[a])"

lemma rev_palindrome : "palindrome xs ==> xs = (rev xs)"
apply (induction rule: palindrome.induct)
apply (auto)
done

inductive star' :: "('a => 'a => bool) => 'a => 'a => bool" for r where
refl' : "star' r x y" |
step' : "star' r x y ==> r y z ==> star' r x z"

end