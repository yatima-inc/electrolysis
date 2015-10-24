use std::collections::HashMap;
use std::iter;

use itertools::Itertools;

use rustc_mir::repr::*;

use super::FnTranspiler;
use ::mir_graph::mir_sccs;

// A loop or the full function body
#[derive(Default)]
pub struct Component {
    pub prelude: String,
    pub header: Option<BasicBlock>,
    pub blocks: Vec<BasicBlock>,
    pub loops: Vec<Vec<BasicBlock>>,
    pub exits: Vec<BasicBlock>,
    pub nonlocal_defs: Vec<String>,
    pub nonlocal_uses: Vec<String>,
    pub refs: HashMap<usize, String>
}

impl Component {
    pub fn new(trans: &FnTranspiler, start: BasicBlock, blocks: Vec<BasicBlock>, is_loop: bool) -> Component {
        let loops = mir_sccs(trans.mir, start, &blocks);
        let loops = loops.into_iter().filter(|l| l.len() > 1).collect::<Vec<_>>();
        let mut comp = Component {
            header: if is_loop { Some(start) } else { None },
            blocks: blocks, loops: loops,
            .. Default::default()
        };
        comp.find_nonlocals(trans);
        comp
    }

    fn find_nonlocals(&mut self, trans: &FnTranspiler) {
        fn operand<'a, 'tcx>(op: &'a Operand<'tcx>, uses: &mut Vec<&'a Lvalue<'tcx>>) {
            match *op {
                Operand::Consume(ref lv) => uses.push(lv),
                Operand::Constant(_) => ()
            }
        }

        fn rvalue<'a, 'tcx>(rv: &'a Rvalue<'tcx>, uses: &mut Vec<&'a Lvalue<'tcx>>) {
            match *rv {
                Rvalue::Use(ref op) => operand(op, uses),
                Rvalue::BinaryOp(_, ref o1, ref o2) => {
                    operand(o1, uses);
                    operand(o2, uses);
                }
                Rvalue::Ref(_, _, ref lv) => uses.push(lv),
                Rvalue::Aggregate(_, ref ops) => {
                    for op in ops {
                        operand(op, uses);
                    }
                }
                _ => panic!("unimplemented: {:?}", rv),
            }
        }

        let mut defs = Vec::new();
        let mut uses = Vec::new();
        let mut drops = Vec::new();

        for &bb in &self.blocks {
            for stmt in &trans.mir.basic_block_data(bb).statements {
                match stmt.kind {
                    StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref ldest)) => {
                        defs.push(lv);
                        defs.push(ldest);
                    }
                    StatementKind::Assign(ref lv, ref rv) => {
                        defs.push(lv);
                        rvalue(rv, &mut uses);
                    }
                    StatementKind::Drop(DropKind::Deep, ref lv) => drops.push(lv),
                    _ => panic!("unimplemented: {:?}", stmt),
                }
            }
            match trans.mir.basic_block_data(bb).terminator {
                Terminator::Call { ref data, .. } => {
                    uses.push(&data.func);
                    for arg in &data.args {
                        uses.push(arg);
                    }
                    let muts = data.args.iter().filter(|lv| {
                        FnTranspiler::try_unwrap_mut_ref(trans.lvalue_ty(lv)).is_some()
                    });
                    defs.extend(iter::once(&data.destination).chain(muts));
                },
                _ => (),
            }
        }

        let ret = Lvalue::ReturnPointer;
        self.nonlocal_defs = trans.locals().iter().filter(|lv| defs.contains(lv) && !drops.contains(lv)).map(|lv| trans.lvalue_name(lv)).collect_vec();
        self.nonlocal_uses = trans.locals().iter().filter(|lv| **lv != ret && uses.contains(lv) && !drops.contains(lv)).map(|lv| trans.lvalue_name(lv)).collect_vec();
    }
}
