use std::collections::HashSet;

use rustc::mir::*;

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
        let loops = mir_sccs(trans.mir, start, blocks);
        let loops = loops.into_iter().filter(|l| l.len() > 1).collect();
        Component {
            outer: outer,
            header: outer.map(|_| start),
            blocks: blocks,
            loops: loops,
            .. Default::default()
        }
    }

    pub fn defs_uses<'b, It: Iterator<Item=&'b BasicBlock>>(blocks: It, trans: &FnTranspiler) -> (HashSet<Local>, HashSet<Local>) {
        // fill `uses` and return root local
        fn lvalue(lv: &Lvalue, uses: &mut HashSet<Local>) -> Option<Local> {
            match *lv {
                Lvalue::Local(l) => Some(l),
                Lvalue::Static(_) => None,
                Lvalue::Projection(box Projection { ref base, ref elem }) => {
                    if let ProjectionElem::Index(ref idx) = *elem {
                        operand(idx, uses)
                    }
                    let lbase = lvalue(base, uses);
                    if let Some(lbase) = lbase {
                        uses.insert(lbase);
                    }
                    lbase
                }
            }
        }

        // fill `uses` and insert root local
        fn use_lvalue(lv: &Lvalue, uses: &mut HashSet<Local>) {
            if let Some(llv) = lvalue(lv, uses) {
                uses.insert(llv);
            }
        }

        fn operand(op: &Operand, uses: &mut HashSet<Local>) {
            match *op {
                Operand::Consume(ref lv) => use_lvalue(lv, uses),
                Operand::Constant(_) => {}
            }
        }

        fn rvalue<'a, 'tcx>(rv: &'a Rvalue<'tcx>, uses: &mut HashSet<Local>) {
            match *rv {
                Rvalue::Use(ref op) => operand(op, uses),
                Rvalue::UnaryOp(_, ref op) => operand(op, uses),
                Rvalue::BinaryOp(_, ref o1, ref o2) | Rvalue::CheckedBinaryOp(_, ref o1, ref o2) => {
                    operand(o1, uses);
                    operand(o2, uses);
                }
                Rvalue::Ref(_, _, ref lv) => use_lvalue(lv, uses),
                Rvalue::Aggregate(_, ref ops) => {
                    for op in ops {
                        operand(op, uses);
                    }
                }
                Rvalue::Cast(_, ref op, _) => operand(op, uses),
                Rvalue::Repeat(ref op, _) => operand(op, uses),
                Rvalue::Len(ref lv) => use_lvalue(lv, uses),
                Rvalue::Box(_) | Rvalue::InlineAsm { .. } => {}
            }
        }

        let mut defs = HashSet::new();
        let mut uses = HashSet::new();

        for &bb in blocks {
            for stmt in &trans.mir[bb].statements {
                match stmt.kind {
                    StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref dest)) => {
                        if let Some(llv) = lvalue(lv, &mut uses) {
                            defs.insert(llv);
                        }
                        if let Some(ldest) = lvalue(dest, &mut uses) {
                            defs.insert(ldest);
                        }
                    }
                    StatementKind::Assign(ref lv, ref rv) => {
                        if let Some(llv) = lvalue(lv, &mut uses) {
                            defs.insert(llv);
                        }
                        rvalue(rv, &mut uses);
                    }
                    _ => {}
                }
            }
            if let Some(ref term) = trans.mir[bb].terminator {
                match term.kind {
                    TerminatorKind::Call { ref func, ref args, destination: Some(_), .. } => {
                        operand(func, &mut uses);
                        for arg in args {
                            operand(arg, &mut uses);
                        }
                        for dest in trans.call_return_dests(&term.kind) {
                            if let Some(ldest) = lvalue(dest, &mut uses) {
                                defs.insert(ldest);
                            }
                        }
                    }
                    TerminatorKind::DropAndReplace { ref location, ref value, .. } => {
                        if let Some(llocation) = lvalue(location, &mut uses) {
                            defs.insert(llocation);
                        }
                        operand(value, &mut uses);
                    }
                    _ => {}
                }
            }
        }

        (defs, uses)
    }
}
