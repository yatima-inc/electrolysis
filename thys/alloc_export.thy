theory alloc_export
imports core_export
begin

datatype 'T alloc_rc_Rc =
  alloc_rc_Rc 'T

datatype 'T alloc_raw_vec_RawVec =
  alloc_raw_vec_RawVec "'T list"

definition [simp]: "alloc_rc_Rc_T__new x = Some (alloc_rc_Rc x)"

definition [simp]: "alloc_rc_Rc_T__Deref_deref rc \<equiv> case rc of
  alloc_rc_Rc x \<Rightarrow> Some x"

end