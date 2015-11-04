#![feature(rustc_private)]
#![feature(box_patterns)]
#![feature(slice_patterns)]
#![feature(path_relative_from)]

macro_rules! throw { ($($arg: tt)*) => { return Err(format!($($arg)*)) } }

extern crate itertools;
extern crate petgraph;

#[macro_use]
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_front;
extern crate rustc_mir;
extern crate syntax;
extern crate rustc_trans;

mod component;
mod mir_graph;
mod traits;

use std::env;
use std::io;
use std::io::prelude::*;
use std::iter;
use std::fs::File;
use std::path;

use itertools::Itertools;

use syntax::ast;
use rustc_front::hir;
use rustc_front::hir::{Path, FnDecl, Pat_, BindingMode, FunctionRetTy, Item, Item_, Ty_};
use rustc_front::print::pprust;
use rustc_mir::mir_map::build_mir_for_crate;
use rustc_mir::repr::*;
use rustc::middle::const_eval::ConstVal;
use rustc::middle::def_id::DefId;
use rustc::middle::ty;

use rustc_driver::driver;
use syntax::diagnostics;
use rustc::session;

use component::Component;

type TransResult = Result<String, String>;

trait StringResultIterator<E> : Iterator<Item=Result<String, E>> {
    fn join_results(&mut self, sep: &str) -> Result<String, E> {
        let items = try!(self.collect::<Result<Vec<_>, _>>());
        Ok(items.iter().join(sep))
    }
}

impl<T, E> StringResultIterator<E> for T where T: Iterator<Item=Result<String, E>> { }

fn main() {
    let krate = env::args().nth(1).unwrap();
    let crate_name = env::args().nth(2).unwrap();
    let sess = session::build_session(
        session::config::Options {
            crate_name: Some(crate_name),
            crate_types: vec![session::config::CrateType::CrateTypeRlib],
            maybe_sysroot: Some(path::PathBuf::from("/usr/local")),
            unstable_features: syntax::feature_gate::UnstableFeatures::Allow,
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
                callback: Box::new(|state| transpile_crate(&state).unwrap()),
            },
            .. driver::CompileController::basic()
        }
    );
}

fn transpile_path(path: &Path) -> String {
    // what could ever go wrong
    pprust::path_to_string(path).replace("::", "_")
}

fn transpile_hir_ty(ty: &hir::Ty) -> TransResult {
    match ty.node {
        Ty_::TyPath(None, ref path) => Ok(transpile_path(path)),
        _ => Err(format!("unimplemented: type {:?}", ty)),
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

pub struct FnTranspiler<'a, 'tcx: 'a> {
    crate_name: &'a str,
    fn_name: String,
    tcx: &'a ty::ctxt<'tcx>,
    mir: &'a Mir<'tcx>,
    param_names: &'a Vec<String>,
}

fn selector(idx: usize, len: usize) -> Vec<&'static str> {
    iter::repeat("_").take(idx)
        .chain(iter::once("x"))
        .chain(iter::repeat("_").take(len - idx - 1))
        .collect()
}

fn transpile_def_id(did: DefId, tcx: &ty::ctxt, crate_name: &str) -> String {
    // what could ever go wrong
    let mut path = tcx.item_path_str(did);
    if did.is_local() {
        path = format!("{}::{}", crate_name, path);
    }
    path.replace("::", "_").replace("<", "_").replace(">", "_").replace(".", "_")
}

impl<'a, 'tcx: 'a> FnTranspiler<'a, 'tcx> {
    fn lvalue_name(&self, lv: &Lvalue) -> TransResult {
        Ok(match *lv {
            Lvalue::Var(idx) => format!("{}", self.mir.var_decls[idx as usize].name),
            Lvalue::Temp(idx) => format!("t_{}", idx),
            Lvalue::Arg(idx) => self.param_names[idx as usize].clone(),
            Lvalue::ReturnPointer => "ret".to_string(),
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                try!(self.lvalue_name(base)),
            _ => throw!("unimplemented: naming {:?}", lv),
        })
    }

    fn locals(&self) -> Vec<Lvalue> {
        self.mir.var_decls.iter().enumerate().map(|(idx, _)| Lvalue::Var(idx as u32))
            .chain(self.mir.temp_decls.iter().enumerate().map(|(idx, _)| Lvalue::Temp(idx as u32)))
            .chain(iter::once(Lvalue::ReturnPointer))
            .collect()
    }

    fn num_locals(&self) -> usize { self.locals().len() }

    fn get_lvalue(&self, lv: &Lvalue) -> TransResult {
        match *lv {
            Lvalue::Var(_) | Lvalue::Temp(_) | Lvalue::Arg(_) => self.lvalue_name(lv),
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
                Ok(format!("(case {lv} of {variant} {args} => x)",
                           lv=try!(self.get_lvalue(base)),
                           variant=self.transpile_def_id(variant.did),
                           args=selector(idx, variant.fields.len()).join(" ")))
            }
            _ => Err(format!("unimplemented: loading {:?}", lv)),
        }
    }

    fn lvalue_ty(&self, lv: &Lvalue) -> Result<&ty::Ty, String> {
        Ok(match *lv {
            Lvalue::Var(idx) => &self.mir.var_decls[idx as usize].ty,
            Lvalue::Temp(idx) => &self.mir.temp_decls[idx as usize].ty,
            Lvalue::Arg(idx) => &self.mir.arg_decls[idx as usize].ty,
            _ => throw!("unimplemented: type of {:?}", lv),
        })
    }

    fn lvalue_idx(&self, lv: &Lvalue) -> Result<usize, String> {
        Ok(match *lv {
            Lvalue::Var(idx) => idx as usize,
            Lvalue::Temp(idx) => self.mir.var_decls.len() + idx as usize,
            Lvalue::ReturnPointer => self.num_locals() - 1,
            Lvalue::Projection(box Projection { ref base, elem: ProjectionElem::Deref }) =>
                try!(self.lvalue_idx(base)),
            _ => throw!("unimplemented: storing {:?}", lv),
        })
    }

    fn set_lvalue(&self, lv: &Lvalue, val: &str) -> TransResult {
        Ok(format!("let {} = {} in\n", try!(self.lvalue_name(lv)), val))
    }

    fn set_lvalues<'b, It: Iterator<Item=&'b Lvalue<'tcx>>>(&self, lvs: It, val: &str) -> TransResult
        where 'tcx: 'b {
        Ok(format!("let ({}) = {} in\n",
                   try!(lvs.map(|lv| self.lvalue_name(lv)).join_results(", ")),
                   val))
    }

    fn transpile_def_id(&self, did: DefId) -> String {
        transpile_def_id(did, self.tcx, self.crate_name)
    }

    fn try_unwrap_mut_ref(ty: &ty::Ty<'tcx>) -> Option<ty::Ty<'tcx>> {
        match ty.sty {
            ty::TypeVariants::TyRef(_, ty::TypeAndMut { mutbl: hir::Mutability::MutMutable, ty }) =>
                Some(ty),
            _ => None
        }
    }

    fn transpile_ty(&self, ty: ty::Ty) -> String {
        match ty.sty {
            ty::TypeVariants::TyUint(ast::UintTy::TyU32) => "u32".to_string(),
            ty::TypeVariants::TyTuple(ref tys) => match &tys[..] {
                [] => "unit".to_string(),
                _ => format!("({})", tys.iter().map(|ty| self.transpile_ty(ty)).join(" × ")),
            },
            ty::TypeVariants::TyBareFn(_, ref data) => {
                let sig = data.sig.skip_binder();
                let muts = sig.inputs.iter().filter_map(FnTranspiler::try_unwrap_mut_ref);
                match sig.output {
                    ty::FnOutput::FnConverging(out_ty) => {
                        format!("({} => {})", sig.inputs.iter().map(|ty| self.transpile_ty(ty)).join(" => "),
                                iter::once(out_ty).chain(muts).map(|ty| self.transpile_ty(ty)).join(" × "))
                    }
                    ty::FnOutput::FnDiverging => panic!("diverging function"),
                }
            },
            ty::TypeVariants::TyStruct(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            ty::TypeVariants::TyEnum(ref adt_def, _) =>
                self.transpile_def_id(adt_def.did),
            ty::TypeVariants::TyRef(_, ref data) => self.transpile_ty(data.ty),
            _ => match ty.ty_to_def_id() {
                Some(did) => self.transpile_def_id(did),
                None => panic!("unimplemented: {:?}", ty),
            }
        }
    }

    fn get_operand(&self, op: &Operand<'tcx>) -> TransResult {
        Ok(match *op {
            Operand::Consume(ref lv) => try!(self.get_lvalue(lv)),
            Operand::Constant(ref c) => match c.literal {
                Literal::Value { value: ConstVal::Uint(i) } => i.to_string(),
                Literal::Value { .. } => throw!("unimplemented: {:?}", op),
                Literal::Item { def_id, substs }  => {
                    if let Some(method_did) = traits::lookup_trait_item_impl(self.tcx, def_id, substs) {
                        self.transpile_def_id(method_did)
                    } else {
                        self.transpile_def_id(def_id)
                    }
                }
            }
        })
    }

    fn get_rvalue(&self, rv: &Rvalue<'tcx>) -> TransResult {
        match *rv {
            Rvalue::Use(ref op) => self.get_operand(op),
            Rvalue::BinaryOp(op, ref o1, ref o2) =>
                Ok(format!("({} {} {})", try!(self.get_operand(o1)), binop_to_string(op),
                           try!(self.get_operand(o2)))),
            Rvalue::Ref(_, BorrowKind::Shared, ref lv) => self.get_lvalue(lv),
            Rvalue::Ref(_, BorrowKind::Mut, ref lv) => self.get_lvalue(lv),
            Rvalue::Aggregate(AggregateKind::Adt(ref adt_def, variant_idx, _), ref ops) => {
                let variant = &adt_def.variants[variant_idx];
                let ops = try!(ops.iter().map(|op| self.get_operand(op)).collect::<Result<Vec<_>, _>>());
                Ok(format!("({} {})", self.transpile_def_id(variant.did), ops.iter().join(" ")))
            }
            _ => Err(format!("unimplemented: {:?}", rv)),
        }
    }

    fn transpile_statement(&self, stmt: &Statement<'tcx>, comp: &mut Component) -> TransResult {
        match stmt.kind {
            StatementKind::Assign(ref lv, Rvalue::Ref(_, BorrowKind::Mut, ref lsource)) => {
                comp.refs.insert(try!(self.lvalue_idx(lv)), try!(self.get_lvalue(lsource)));
                self.set_lvalue(lv, &&try!(self.get_lvalue(lsource)))
                //format!("let ({lv}, {lsource}) = ({lsource}, undefined) in\n", lv=self.get_lvalue(lv), lsource=self.get_lvalue(lsource))
            }
            StatementKind::Assign(ref lv, ref rv) => {
                if *lv != Lvalue::ReturnPointer && try!(self.lvalue_ty(lv)).is_nil() {
                    // optimization/rustc_mir workaround: don't save '()'
                    Ok("".to_string())
                } else {
                    self.set_lvalue(lv, &&try!(self.get_rvalue(rv)))
                }
            }
            StatementKind::Drop(DropKind::Deep, ref lv) => {
                //match comp.refs.get(&self.lvalue_idx(lv)) {
                //    Some(lsource) => format!("let ({lsource}, {lv}) = ({lv}, undefined) in\n", lsource=lsource, lv=self.get_lvalue(lv)),
                //    None => self.set_lvalue(lv, "undefined")
                //}
                Ok(match comp.refs.get(&&try!(self.lvalue_idx(lv))) {
                    Some(lsource) => format!("let {} = {} in\n", lsource, try!(self.get_lvalue(lv))),
                    None => "".to_string()
                })
            }
            _ => Err(format!("unimplemented: {:?}", stmt)),
        }
    }

    fn transpile_basic_block_rec(&self, bb: BasicBlock, comp: &mut Component) -> TransResult {
        if comp.header == Some(bb) {
            Ok(format!("(({}), True)", comp.nonlocal_defs.iter().join(", ")))
        } else {
            self.transpile_basic_block(bb, comp)
        }
    }

    fn call_return_dests<'b>(&self, call: &'b CallData<'tcx>) -> Result<Vec<&'b Lvalue<'tcx>>, String> {
        let args_with_tys = try!(call.args.iter().map(|lv| {
            self.lvalue_ty(lv).map(|ty| (lv, ty))
        }).collect::<Result<Vec<_>, _>>());
        let muts = args_with_tys.into_iter().filter(|&(_, ty)| {
            FnTranspiler::try_unwrap_mut_ref(ty).is_some()
        }).map(|(lv, _)| lv);
        Ok(iter::once(&call.destination).chain(muts).collect())
    }

    fn transpile_basic_block(&self, bb: BasicBlock, comp: &mut Component) -> TransResult {
        macro_rules! rec { ($bb:expr) => { try!(self.transpile_basic_block_rec($bb, comp)) } }

        if !comp.blocks.contains(&bb) {
            comp.exits.push(bb);
            return Ok(format!("(({}), False)", comp.nonlocal_defs.iter().join(", ")));
        }
        if let Some(l) = comp.loops.clone().into_iter().find(|l| l.contains(&bb)) {
            let mut l_comp = try!(Component::new(self, bb, l, true));
            let body = try!(self.transpile_basic_block(bb, &mut l_comp));
            let name = format!("{}_{}", self.fn_name, bb.index());
            assert!(l_comp.exits.len() == 1);
            comp.prelude = format!("{}

definition {name} where \"{name} {uses} = (\\<lambda>({defs}). {body})\"",
                                   comp.prelude,
                                   name=name,
                                   uses=l_comp.nonlocal_uses.iter().join(" "),
                                   defs=l_comp.nonlocal_defs.iter().join(", "),
                                   body=body);
            return Ok(format!("let ({muts}) = loop ({name} {immuts}) ({muts}) in\n{cont}", muts=l_comp.nonlocal_defs.iter().join(", "),
                              name=name, immuts=l_comp.nonlocal_uses.iter().join(" "), cont=rec!(l_comp.exits[0])));
        }

        let data = self.mir.basic_block_data(bb);
        let stmts = try!(data.statements.iter().map(|s| self.transpile_statement(s, comp)).collect::<Result<Vec<_>, _>>());
        let terminator = match data.terminator {
            Terminator::Goto { target } =>
                rec!(target),
            Terminator::Panic { .. } => format!("panic"),
            Terminator::If { ref cond, ref targets } =>
                format!("if {} then {} else {}", try!(self.get_operand(cond)),
                rec!(targets[0]),
                rec!(targets[1])),
            Terminator::Return => format!("ret"),
            Terminator::Call { ref data, ref targets } => {
                let call = format!("({} {})", try!(self.get_lvalue(&data.func)),
                                   try!(data.args.iter().map(|lv| self.get_lvalue(lv)).join_results(" ")));
                try!(self.set_lvalues(try!(self.call_return_dests(data)).into_iter(), &call)) + &&rec!(targets[0])
            },
            Terminator::Switch { ref discr, ref targets } =>
                if let ty::TypeVariants::TyEnum(ref adt_def, _) = try!(self.lvalue_ty(discr)).sty {
                    let arms: TransResult = adt_def.variants.iter().zip(targets).map(|(var, &target)| {
                        Ok(format!("{} {} => {}", self.transpile_def_id(var.did),
                                   iter::repeat("_").take(var.fields.len()).join(" "),
                                   rec!(target)))
                    }).join_results(" | ");
                    format!("case {} of {}", try!(self.get_lvalue(discr)), try!(arms))
                } else {
                    unreachable!()
                },
            Terminator::Diverge => unreachable!(),
        };
        Ok(stmts.into_iter().chain(iter::once(terminator)).join(""))
    }
}

struct ModuleTranspiler<'a, 'tcx: 'a> {
    input: &'a path::Path,
    crate_name: &'a str,
    tcx: &'a ty::ctxt<'tcx>,
    mir_map: &'a rustc_mir::mir_map::MirMap<'tcx>,
}

impl<'a, 'tcx> ModuleTranspiler<'a, 'tcx> {
    fn try_transpile_fn(&self, id: ast::NodeId, decl: &FnDecl, name: &String) -> TransResult {
        let params = try!(decl.inputs.iter().map(|param| {
            match param.pat.node {
                Pat_::PatIdent(BindingMode::BindByRef(hir::Mutability::MutMutable), _, _) =>
                   throw!("unimplemented: &mut param ({:?})", param),
                Pat_::PatIdent(_, ref ident, _) =>
                    Ok((ident.node.name.as_str().to_string(), &param.ty)),
                _ => throw!("unimplemented: param pattern ({:?})", param),
            }
        }).collect::<Result<Vec<_>, _>>());
        let (param_names, param_types): (Vec<_>, Vec<_>) = params.into_iter().unzip();

        let return_ty = match decl.output {
            FunctionRetTy::DefaultReturn(_) => "()".to_string(),
            FunctionRetTy::Return(ref ty) => try!(transpile_hir_ty(ty)),
            FunctionRetTy::NoReturn(_) => throw!("no-return fn"),
        };

        let mir = &self.mir_map[&id];
        let trans = FnTranspiler {
            crate_name: self.crate_name, fn_name: name.clone(),
            tcx: self.tcx, mir: mir, param_names: &param_names
        };
        let mut comp = try!(Component::new(&trans, START_BLOCK, mir.all_basic_blocks(), false));
        let body = try!(trans.transpile_basic_block(START_BLOCK, &mut comp));

        Ok(format!("{prelude}

definition {name} :: \"{param_types} => {return_ty}\" where
\"{name} {param_names} = ({body})\"

",
                    prelude=comp.prelude,
                    name=name,
                    param_types=try!(param_types.iter().map(|ty| transpile_hir_ty(*ty)).join_results(" => ")),
                    return_ty=return_ty,
                    param_names=param_names.iter().join(" "),
                    body=body,
        ))
    }

    fn transpile_fn(&self, f: &mut Write, id: ast::NodeId, decl: &FnDecl) -> io::Result<()> {
        let name = format!("{}", transpile_def_id(self.tcx.map.local_def_id(id), self.tcx, self.crate_name));
        match self.try_transpile_fn(id, decl, &name) {
            Ok(trans) => try!(write!(f, "{}", trans)),
            Err(err) => try!(write!(f, "(* {}: {} *)", name, err)),
        };
        Ok(())
    }

    fn transpile_module(&self, module: &hir::Mod) -> io::Result<()> {
        let p = &self.tcx.sess.codemap().span_to_filename(module.inner);
        let p = path::Path::new(p);
        let base = self.input.parent().unwrap();
        let p = path::Path::new("export").join(self.crate_name).join(p.relative_from(base).unwrap()).with_extension("thy");
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        let mut f = try!(File::create(&p));
        try!(write!(f, "theory {}
imports \"../../Rustabelle\"
begin

", p.file_stem().unwrap().to_str().unwrap()));

        for item in module.items.iter() {
            match item.node {
                Item_::ItemFn(ref decl, _, _, _, ref generics, _) =>
                    try!(self.transpile_fn(&mut f, item.id, decl)),
                Item_::ItemImpl(_, _, ref generics, _, _, ref items) =>
                    for item in items {
                        match item.node {
                            hir::ImplItem_::MethodImplItem(ref sig, _) =>
                                try!(self.transpile_fn(&mut f, item.id, &sig.decl)),
                            _ => println!("unimplemented: {:?}", item),
                        }
                    },
                Item_::ItemExternCrate(..) | Item_::ItemUse(..) => (),
                Item_::ItemMod(ref module) => try!(self.transpile_module(module)),
                Item_::ItemTy(ref ty, ref generics) =>
                    try!(write!(f, "typedef {} = {}\n\n", 1, 2)),
                _ => println!("unimplemented: {:?}", item),
            };
        }
        try!(write!(f, "end\n"));
        Ok(())
    }
}

fn transpile_crate(state: &driver::CompileState) -> io::Result<()> {
    let tcx = state.tcx.unwrap();
    let trans = ModuleTranspiler {
        input: match *state.input {
            session::config::Input::File(ref p) => p,
            _ => panic!("A file would be nice."),
        },
        crate_name: state.crate_name.unwrap(),
        tcx: tcx,
        mir_map: &build_mir_for_crate(tcx),
    };
    trans.transpile_module(&state.hir_crate.unwrap().module)
}
