#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns)]

extern crate itertools;
extern crate petgraph;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_mir;
extern crate syntax;

mod mir_graph;

use std::collections::HashMap;
use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir;
use rustc_front::hir::{Crate, Path, FnDecl, Pat_, BindingMode, FunctionRetTy, Item, Item_, Ty_};
use rustc_front::print::pprust;
use rustc_mir::mir_map::build_mir_for_crate;
use rustc_mir::repr::*;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::ty::ctxt;
use rustc::middle::ty::FnOutput;
use rustc::middle::ty::Ty;
use rustc::middle::ty::TypeAndMut;
use rustc::middle::ty::TypeVariants;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use mir_graph::mir_sccs;

fn main() {
    let krate = env::args().nth(1).unwrap();
    let sess = session::build_session(
        session::config::Options {
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
            .. session::config::basic_options()
        },
        Some(path::PathBuf::from(&krate)),
        diagnostics::registry::Registry::new(&rustc::DIAGNOSTICS)
    );
    let cfg = session::config::build_configuration(&sess);
    driver::compile_input(sess, cfg,
        &session::config::Input::File(path::PathBuf::from(&krate)),
        &None, &None, None, driver::CompileController {
            after_analysis: driver::PhaseController {
                stop: rustc_driver::Compilation::Stop,
                callback: Box::new(|state| {
                    transpile_crate(state.hir_crate.unwrap(), state.tcx.unwrap()).unwrap();
                }),
            },
            .. driver::CompileController::basic()
        }
    );
}

fn transpile_path(path: &Path) -> String {
    // what could ever go wrong
    pprust::path_to_string(path).replace("::", "_")
}

fn transpile_hir_ty(ty: &hir::Ty) -> String {
    match ty.node {
        Ty_::TyPath(None, ref path) => transpile_path(path),
        _ => panic!("unimplemented: type {:?}", ty),
    }
}

fn binop_to_string(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
        BinOp::BitXor => "^",
        BinOp::BitAnd => "&",
        BinOp::BitOr => "|",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Eq => "==",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Ne => "!=",
        BinOp::Ge => ">=",
        BinOp::Gt => ">",
    }
}

struct FnTranspiler<'a, 'tcx: 'a> {
    fn_name: String,
    tcx: &'a ctxt<'tcx>,
    mir: &'a Mir<'tcx>,
    param_names: &'a Vec<String>,
    return_ty: String,
}

// A loop or the full function body
struct Component {
    prelude: String,
    header: Option<BasicBlock>,
    blocks: Vec<BasicBlock>,
    loops: Vec<Vec<BasicBlock>>,
    exits: Vec<BasicBlock>,
}

impl Component {
    fn new(mir: &Mir, start: BasicBlock, blocks: Vec<BasicBlock>, is_loop: bool) -> Component {
        let loops = mir_sccs(mir, start, &blocks);
        let loops = loops.into_iter().filter(|l| l.len() > 1).collect::<Vec<_>>();
        Component {
            prelude: "".to_string(),
            header: if is_loop { Some(start) } else { None },
            blocks: blocks, loops: loops, exits: Vec::new(),
        }
    }
}

fn selector(idx: usize, len: usize) -> Vec<&'static str> {
    iter::repeat("_").take(idx)
        .chain(iter::once("x"))
        .chain(iter::repeat("_").take(len - idx - 1))
        .collect()
}

impl<'a, 'tcx: 'a> FnTranspiler<'a, 'tcx> {
    // State = Maybe v0 * Maybe v1 * ... * Maybe t0 * ...

    fn get_locals_types(&self) -> Vec<String> {
        self.mir.var_decls.iter().map(|v| v.ty)
            .chain(self.mir.temp_decls.iter().map(|t| t.ty))
            .map(|ty| self.transpile_ty(ty))
            .chain(iter::once(self.return_ty.clone()))
            .collect()
    }

    fn num_locals(&self) -> usize { self.get_locals_types().len() }

    fn get_local(&self, idx: usize) -> String {
        format!("(let ({}) = s in the x)", selector(idx, self.num_locals()).join(", "))
    }

    fn get_lvalue(&self, lv: &Lvalue) -> String {
        match *lv {
            Lvalue::Var(idx) => self.get_local(idx as usize),
            Lvalue::Temp(idx) => self.get_local(self.mir.var_decls.len() + idx as usize),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                self.get_lvalue(base),
            Lvalue::Projection(box Projection {
                elem: ProjectionElem::Field(Field::Indexed(idx)),
                base: Lvalue::Projection(box Projection {
                    ref base,
                    elem: ProjectionElem::Downcast(ref adt_def, variant_idx),
                }),
            }) => {
                let variant = &adt_def.variants[variant_idx];
                format!("(case {lv} of {variant} {args} => x)",
                      lv=self.get_lvalue(base),
                      variant=self.transpile_def_id(variant.did),
                      args=selector(idx, variant.fields.len()).join(" "))
            }
            _ => panic!("unimplemented: loading {:?}", lv)
        }
    }

    fn get_lvalue_ty(&self, lv: &Lvalue) -> &Ty {
        match *lv {
            Lvalue::Var(idx) => &self.mir.var_decls[idx as usize].ty,
            Lvalue::Temp(idx) => &self.mir.temp_decls[idx as usize].ty,
            Lvalue::Arg(idx) => &self.mir.arg_decls[idx as usize].ty,
            _ => panic!("unimplemented: type of {:?}", lv)
        }
    }

    fn set_local(&self, idx: usize, val: Option<&str>) -> String {
        fn mk_name(idx: usize) -> String {
            format!("s{}", idx)
        }
        format!("(let ({}) = s in ({}))",
            (0..self.num_locals()).map(mk_name).join(", "),
            (0..self.num_locals()).map(|i| {
                if i == idx {
                    match val {
                        Some(val) => format!("Some {}", val),
                        None => format!("None")
                    }
                }
                else {
                    mk_name(i)
                }
            }).join(", "))
    }

    fn set_lvalue(&self, lv: &Lvalue, val: Option<&str>) -> String {
        match *lv {
            Lvalue::Var(idx) => self.set_local(idx as usize, val),
            Lvalue::Temp(idx) => self.set_local(self.mir.var_decls.len() + idx as usize, val),
            Lvalue::ReturnPointer => self.set_local(self.num_locals() - 1, val),
            _ => panic!("unimplemented: storing {:?}", lv)
        }
    }

    fn transpile_def_id(&self, did: DefId) -> String {
        // what could ever go wrong
        self.tcx.item_path_str(did).replace("::", "_")
    }

    fn transpile_ty(&self, ty: Ty) -> String {
        match ty.sty {
            TypeVariants::TyUint(ast::UintTy::TyU32) => "u32".to_string(),
            TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(", ")),
            },
            TypeVariants::TyBareFn(_, ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(|ty| match ty.sty {
                    TypeVariants::TyRef(_, TypeAndMut { mutbl: hir::Mutability::MutMutable, ref ty }) =>
                        Some(ty),
                    _ => None
                });
                match sig.output {
                    FnOutput::FnConverging(ref out_ty) => {
                        let output = format!("({})", iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join(", "));
                        sig.inputs.iter().map(|ty| self.transpile_ty(ty)).chain(iter::once(output)).join(" => ")
                    }
                    FnOutput::FnDiverging => panic!("diverging function"),
                }
            },
            TypeVariants::TyStruct(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            TypeVariants::TyEnum(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => panic!("unimplemented: {:?}", ty),
            }
        }
    }

    fn get_operand(&self, op: &Operand) -> String {
        match *op {
            Operand::Consume(ref lv) => self.get_lvalue(lv),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { value: ConstVal::Uint(i) } => i.to_string(),
                Literal::Value { .. } => panic!("unimplemented: {:?}", op),
                Literal::Item { def_id, .. }  => {
                    self.transpile_def_id(def_id)
                }
            }
        }
    }

    fn get_rvalue(&self, rv: &Rvalue) -> String {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::BinaryOp(op, ref o1, ref o2) =>
                format!("({} {} {})", self.get_operand(o1), binop_to_string(op),
                        self.get_operand(o2)),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) => self.get_lvalue(lv),
            Rvalue::Ref(_, BorrowKind::Mut, ref lv) => self.get_lvalue(lv),
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                let variant = &adt_def.variants[variant_idx];
                format!("({} {})", self.transpile_def_id(variant.did),
                        ops.iter().map(|op| self.get_operand(op)).join(" "))
            }
            _ => panic!("unimplemented: {:?}", rv),
        }
    }

    fn transpile_statement(&self, stmt: &Statement) -> String {
        match stmt.kind {
            StatementKind::Assign(ref lv, ref rv) => {
                let val = self.get_rvalue(rv);
                format!("(λcont s. cont {})", self.set_lvalue(lv, Some(&val)))
            }
            StatementKind::Drop(DropKind::Deep, ref lv) =>
                format!("(λcont s. cont {})", self.set_lvalue(lv, None)),
            _ => panic!("unimplemented: {:?}", stmt),
        }
    }

    fn get_loop_fun_name(&self, header: BasicBlock) -> String {
        format!("{}_{}", self.fn_name, header.index())
    }

    fn transpile_basic_block_rec(&self, bb: BasicBlock, comp: &mut Component) -> String {
        if comp.header == Some(bb) {
            format!("({} cont s)", self.get_loop_fun_name(bb))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn transpile_basic_block(&self, bb: BasicBlock, comp: &mut Component) -> String {
        println!("{:?}, header {:?}", bb, comp.header);
        macro_rules! rec { ($bb:expr) => { self.transpile_basic_block_rec($bb, comp) } }

        if !comp.blocks.contains(&bb) {
            comp.exits.push(bb);
            return format!("(cont s)");
        }
        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = Component::new(self.mir, bb, l, true);
            println!("LOOP: {:?}", l_comp.blocks);
            comp.prelude = format!("{}\n\nfunction {name} where \"{name} cont s = {body}\"",
                                   comp.prelude,
                                   name=self.get_loop_fun_name(bb),
                                   body=self.transpile_basic_block(bb, &mut l_comp));
            return format!("(λcont. {} {})",
                           self.get_loop_fun_name(bb),
                           l_comp.exits.iter().map(|&e| {
                               format!("({} cont)", rec!(e))
                           }).join(" "));
        }

        let data = self.mir.basic_block_data(bb);
        let stmts = data.statements.iter().map(|s| self.transpile_statement(s)).collect_vec();
        let terminator = match data.terminator {
            Terminator::Goto { target } =>
                rec!(target),
            Terminator::Panic { .. } => format!("panic"),
            Terminator::If { ref cond, ref targets } =>
                format!("(ite {} {} {})", self.get_operand(cond),
                rec!(targets[0]),
                rec!(targets[1])),
            Terminator::Return => format!("id"),
            Terminator::Call { ref data, ref targets } => {
                let call = format!("({} {})", self.get_lvalue(&data.func),
                                   data.args.iter().map(|lv| self.get_lvalue(lv)).join(" "));
                format!("(λcont s. cont {});\n{}",
                        self.set_lvalue(&data.destination, Some(&call)),
                        rec!(targets[0]))
            },
            Terminator::Switch { ref discr, ref targets } =>
                if let TypeVariants::TyEnum(ref adt_def, _) = self.get_lvalue_ty(discr).sty {
                    format!("(λcont s. cont (case {} of {}))", self.get_lvalue(discr),
                        adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                            format!("{} _ => {}", self.transpile_def_id(var.did),
                                    rec!(target))
                        }).join(" | "))
                } else {
                    unreachable!()
                },
            _ => panic!("unimplemented: {:?}", data),
        };
        stmts.into_iter().chain(iter::once(terminator)).join(";\n")
    }
}

fn transpile_fn<'tcx>(f: &mut Write, name: &ast::Name, decl: &FnDecl, tcx: &ctxt<'tcx>, mir: &Mir<'tcx>)
        -> io::Result<()> {
    let (param_names, param_types): (Vec<_>, Vec<_>) = decl.inputs.iter().map(|param| {
        match param.pat.node {
            Pat_::PatIdent(BindingMode::BindByRef(hir::Mutability::MutMutable), _, _) =>
               panic!("unimplemented: &mut param ({:?})", param),
            Pat_::PatIdent(_, ref ident, _) =>
                (ident.node.name.as_str().to_string(), &param.ty),
            _ => panic!("unimplemented: param pattern ({:?})", param),
        }
    }).unzip();
    let return_ty = match decl.output {
        FunctionRetTy::DefaultReturn(_) => "()".to_string(),
        FunctionRetTy::Return(ref ty) => transpile_hir_ty(ty),
        FunctionRetTy::NoReturn(_) => panic!("should skip: no-return fn"),
    };

    let transpiler = FnTranspiler { fn_name: format!("{}", name), tcx: tcx, mir: mir, param_names: &param_names,
        return_ty: return_ty.clone() };
    let mut comp = Component::new(mir, START_BLOCK, mir.all_basic_blocks(), false);
    let block = transpiler.transpile_basic_block(START_BLOCK, &mut comp);

    try!(write!(f, "{prelude}

definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = ({block}) (λs. {get_retval}) ({init_state})\"

",
                prelude=comp.prelude,
                name=name,
                param_types=param_types.iter().map(|ty| transpile_hir_ty(*ty)).join(" => "),
                return_ty=return_ty,
                param_names=param_names.iter().join(" "),
                block=block,
                get_retval=transpiler.get_local(transpiler.num_locals() - 1),
                init_state=transpiler.get_locals_types()
                    .iter().map(|ty| format!("None::{} option", ty))
                    .join(", ")
    ));
    return Ok(());
}

fn transpile_crate(krate: &Crate, tcx: &ctxt) -> io::Result<()> {
    let mut f = try!(File::create("Export.thy"));
    try!(write!(f, "theory Export
imports Rustabelle
begin"));
    let mir_map = build_mir_for_crate(tcx);
    for item in krate.module.items.iter() {
        if let Item {
            id, ref name,
            node: Item_::ItemFn(ref decl, _, _, _, ref generics, _), ..
        } = **item {
            try!(transpile_fn(&mut f, name, decl, tcx, mir_map.get(&id).unwrap()));
        };
    }
    try!(write!(f, "end\n"));
    return Ok(());
}
