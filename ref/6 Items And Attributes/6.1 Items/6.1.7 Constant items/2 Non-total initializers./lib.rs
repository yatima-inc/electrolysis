/* FIXME: Creates `sem u32` instead of `u32`, which we can't even detect easily.
   Should really be constant folded in rustc.
const BIT1: u32 = 1 << 0;
const BIT2: u32 = 1 << 1;
*/
