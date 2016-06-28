use std::collections::HashSet;

use rustc::mir::repr::*;

use trans::fun::FnTranspiler;
use mir_graph::mir_sccs;

/// A loop body or the full function body
#[derive(Default, Debug)]
pub struct Component<'a> {
    pub outer: Option<&'a Component<'a>>, // None for fn bodies
    pub header: Option<BasicBlock>, // loop header (dominates body)
    pub blocks: &'a [BasicBlock],
    pub loops: Vec<Vec<BasicBlock>>, // nested loops
    pub state_val: String, // tuple of loop vars
}

impl<'a> Component<'a> {
    pub fn new(trans: &FnTranspiler, start: BasicBlock, blocks: &'a [BasicBlock], outer: Option<&'a Component<'a>>)
        -> Component<'a> {
        let loops = mir_sccs(trans.mir(), start, blocks);
        let loops = loops.into_iter().filter(|l| l.len() > 1).collect();
        Component {
            outer: outer,
            header: outer.map(|_| start),
            blocks: blocks,
            loops: loops,
            .. Default::default()
        }
    }

    pub fn defs_uses<'b, It: Iterator<Item=&'b BasicBlock>>(blocks: It, trans: &FnTranspiler) -> (HashSet<String>, HashSet<String>) {
        fn operand<'a, 'tcx>(op: &'a Operand<'tcx>, uses: &mut Vec<&'a Lvalue<'tcx>>) {
            match *op {
                Operand::Consume(ref lv) => uses.push(lv),
                Operand::Constant(_) => {}
            }
        }

        fn rvalue<'a, 'tcx>(rv: &'a Rvalue<'tcx>, uses: &mut Vec<&'a Lvalue<'tcx>>) {
            match *rv {
                Rvalue::Use(ref op) => operand(op, uses),
                Rvalue::UnaryOp(_, ref op) => operand(op, uses),
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
                Rvalue::Cast(_, ref op, _) => operand(op, uses),
                Rvalue::Repeat(ref op, _) => operand(op, uses),
                Rvalue::Len(ref lv) => uses.push(lv),
                Rvalue::Slice { ref input, .. } => uses.push(input),
                Rvalue::Box(_) | Rvalue::InlineAsm(_) => {}
            }
        }

        let mut defs = Vec::new();
        let mut uses = Vec::new();

        for &bb in blocks {
            for stmt in &trans.mir().basic_block_data(bb).statements {
                match stmt.kind {
                    StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref ldest)) => {
                        defs.push(lv);
                        defs.push(ldest);
                    }
                    StatementKind::Assign(ref lv, ref rv) => {
                        defs.push(lv);
                        rvalue(rv, &mut uses);
                    }
                }
            }
            if let Some(ref term) = trans.mir().basic_block_data(bb).terminator {
                match *term {
                    Terminator::Call { ref func, ref args, .. } => {
                        operand(func, &mut uses);
                        for arg in args {
                            operand(arg, &mut uses);
                        }
                        defs.extend(trans.call_return_dests(term));
                    }
                    _ => {}
                }
            }
        }

        (defs.into_iter().filter_map(|lv| trans.lvalue_name(lv)).collect(),
         uses.into_iter().filter_map(|lv| trans.lvalue_name(lv)).collect())
    }
}
