theory lib
imports "../../Rustabelle"
begin

record ('Idx) examples_Range =
  "start" :: 'Idx
  "end" :: 'Idx

(* unimplemented item type: "examples_Range_A__Iterator_Item" *)



definition examples_Range_A__Iterator_next :: "'A examples_Range => 'A core_option_Option" where
"examples_Range_A__Iterator_next self = (let self = self in
let t_2 = Substs[types=[[A];[A];[]], regions=[[];[];[]]]_core_cmp_PartialOrd in
let t_3 = (&mut Range<A>.start self) in
let t_4 = (&mut Range<A>.end self) in
let (t_1) = (t_2 t_3 t_4) in
if t_1 then let t_5 = Substs[types=[[&A];[&A];[]], regions=[[];[];[]]]_core_ops_Add in
let t_6 = (&mut Range<A>.start self) in
let t_10 = Substs[types=[[];[A];[]], regions=[[];[];[]]]_core_num_One in
let (t_9) = (t_10 ) in
let t_8 = t_9 in
let t_7 = t_8 in
let (n) = (t_5 t_6 t_7) in
let t_12 = core_mem_swap in
let t_14 = n in
let t_13 = t_14 in
let t_16 = (&mut Range<A>.start self) in
let t_15 = t_16 in
let (t_11, t_13, t_15) = (t_12 t_13 t_15) in
let t_14 = t_13 in
let n = t_14 in
let t_16 = t_15 in
let (&mut Range<A>.start self) = t_16 in
let t_17 = core_option_Option_Some in
let (ret) = (t_17 n) in
ret else let ret = core_option_Option_None in
ret)"

(* examples_Range_A__Iterator_size_hint: unimplemented: rvalue Aggregate<Tuple>([Constant { span: examples/src/lib.rs:41:22: 41:23, ty: usize, literal: Value { value: Uint(0) } }, Constant { span: examples/src/lib.rs:41:25: 41:29, ty: core::option::Option<usize>, literal: Item { def_id: DefId { krate: 2, node: DefIndex(29035) => core::option::Option::None }, substs: Substs[types=[[usize];[];[]], regions=[[];[];[]]] } }]) *)

end
