theory Export
imports Rustabelle
begin

definition fac :: "u32 => u32" where
"fac n = ((λcont s. (λcont s. cont s 1) (λs r. cont (let (s0, s1) = s in (s0, Some(r))) ()) s); (lift2 (op *) (lift2 (op *) (λcont s. cont s (let (_, x) = s in the x)) (λcont s. cont s 2)) (λcont s. cont s (let (x, _) = s in the x)))) (λ_ ret. ret) (Some(n), None::u32 option)"

end
