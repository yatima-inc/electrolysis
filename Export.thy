theory Export
imports Rustabelle
begin

definition fac :: "u32 => u32" where
"fac n = ((λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (Some n, s1, s2, s3, s4, s5, s6)));
(λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (s0, Some 1, s2, s3, s4, s5, s6)));
(λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (s0, s1, s2, s3, Some (let (_, x, _, _, _, _, _) = s in the x), s5, s6)));
(λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (s0, s1, s2, Some ((let (_, _, _, _, x, _, _) = s in the x) * 2), s4, s5, s6)));
(λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (s0, s1, s2, s3, s4, Some (let (x, _, _, _, _, _, _) = s in the x), s6)));
(λcont s. cont (let (s0, s1, s2, s3, s4, s5, s6) = s in (s0, s1, s2, s3, s4, s5, Some ((let (_, _, _, x, _, _, _) = s in the x) * (let (_, _, _, _, _, x, _) = s in the x)))));
id) (λs. (let (_, _, _, _, _, _, x) = s in the x)) (None::u32 option, None::u32 option, None::unit option, None::u32 option, None::u32 option, None::u32 option, None::u32 option)"

end
