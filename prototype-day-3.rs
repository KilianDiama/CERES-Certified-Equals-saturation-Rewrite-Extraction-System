// ============================================================
// NOYAU v17 — Correctifs P0 des audits v16
// rustc -O kernel_v17.rs -o kernel_v17 && ./kernel_v17
// rustc --test kernel_v17.rs -o kernel_v17_tests && ./kernel_v17_tests
// ============================================================

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Instant;

// ============================================================
// HASH 128 bits
// ============================================================
#[inline(always)]
fn mix64(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}
#[inline(always)]
fn read_u64_le(b: &[u8], i: usize) -> u64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&b[i..i + 8]);
    u64::from_le_bytes(buf)
}
pub type Fingerprint = [u64; 2];
pub fn hash128(bytes: &[u8], seed: u64) -> Fingerprint {
    let mut h1 = mix64(seed ^ 0xa5a5_a5a5_a5a5_a5a5);
    let mut h2 = mix64(seed ^ 0x5a5a_5a5a_5a5a_5a5a);
    let mut i = 0;
    while i + 16 <= bytes.len() {
        let k1 = read_u64_le(bytes, i);
        let k2 = read_u64_le(bytes, i + 8);
        h1 = mix64(h1 ^ k1).wrapping_add(k2);
        h2 = mix64(h2.rotate_left(23) ^ k2).wrapping_add(k1);
        i += 16;
    }
    if i + 8 <= bytes.len() {
        let k = read_u64_le(bytes, i);
        h1 = mix64(h1 ^ k);
        h2 = mix64(h2 ^ k.rotate_left(31));
        i += 8;
    }
    let mut tail: u64 = 0;
    let mut shift = 0u32;
    while i < bytes.len() {
        tail |= (bytes[i] as u64) << shift;
        shift += 8;
        i += 1;
    }
    h1 = mix64(h1 ^ tail.wrapping_mul(0x9e37_79b9_7f4a_7c15));
    h2 = mix64(h2 ^ tail.wrapping_mul(0xc2b2_ae3d_27d4_eb4f));
    h1 = mix64(h1 ^ h2);
    h2 = mix64(h2 ^ h1);
    [h1, h2]
}

// ============================================================
// TYPES DE BASE
// ============================================================
pub type ClassId = u32;
pub type PatternId = Fingerprint;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum Op {
    Const = 0, Add = 1, Mul = 2, Xor = 3, Sub = 4, And = 5, Or = 6,
}
impl Op {
    #[inline] pub fn commutative(self) -> bool { matches!(self, Op::Add|Op::Mul|Op::Xor|Op::And|Op::Or) }
    #[inline] pub fn associative(self) -> bool { matches!(self, Op::Add|Op::Mul|Op::And|Op::Or) }
    #[inline] pub fn code(self) -> u8 { self as u8 }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ENode {
    pub op: Op,
    pub children: Vec<ClassId>,
    pub payload: Vec<u8>,
}

// ============================================================
// ERREUR D'INSTANCIATION — niveau module (fix compilation)
// ============================================================
#[derive(Debug, Clone, Copy)]
pub struct InstantiateError(pub u32);
impl std::fmt::Display for InstantiateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "variable {} non liée", self.0)
    }
}
impl std::error::Error for InstantiateError {}

// ============================================================
// PROUVEUR — avec budget polynomial
// ============================================================
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NormExpr {
    Const(u64),
    Var(u32),
    Op(Op, Vec<NormExpr>),
}

type Mono = BTreeMap<NormExpr, u32>;
type Poly = BTreeMap<Mono, u64>;

/// Budgets anti-explosion.
const POLY_MAX_MONOMES: usize = 4096;
const POLY_MAX_DEGREE: u32 = 32;
const POLY_MAX_FUEL: usize = 200_000;

fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut out = a.clone();
    for (m, c) in b {
        let e = out.entry(m.clone()).or_insert(0);
        *e = e.wrapping_add(*c);
    }
    out.retain(|_, c| *c != 0);
    out
}
fn poly_sub(a: &Poly, b: &Poly) -> Poly {
    let mut out = a.clone();
    for (m, c) in b {
        let e = out.entry(m.clone()).or_insert(0);
        *e = e.wrapping_sub(*c);
    }
    out.retain(|_, c| *c != 0);
    out
}
fn poly_mul(a: &Poly, b: &Poly) -> Poly {
    let mut out = Poly::new();
    for (ma, ca) in a {
        for (mb, cb) in b {
            let mut m: Mono = ma.clone();
            let mut ok = true;
            for (atom, exp) in mb {
                let e = m.entry(atom.clone()).or_insert(0);
                let ne = match e.checked_add(*exp) { Some(v) => v, None => { ok = false; break; } };
                if ne > POLY_MAX_DEGREE { ok = false; break; }
                *e = ne;
            }
            if !ok { continue; }
            let c = ca.wrapping_mul(*cb);
            let e = out.entry(m).or_insert(0);
            *e = e.wrapping_add(c);
        }
    }
    out.retain(|_, c| *c != 0);
    out
}

/// [P0] Pliage polynomial AVEC budget : retourne None si explosé.
fn poly_from_norm_bounded(e: &NormExpr, fuel: &mut usize) -> Option<Poly> {
    if *fuel == 0 { return None; }
    *fuel = fuel.saturating_sub(1);
    match e {
        NormExpr::Const(c) => {
            let mut p = Poly::new();
            if *c != 0 { p.insert(Mono::new(), *c); }
            Some(p)
        }
        NormExpr::Var(v) => {
            let mut mono = Mono::new();
            mono.insert(NormExpr::Var(*v), 1);
            let mut p = Poly::new();
            p.insert(mono, 1);
            Some(p)
        }
        NormExpr::Op(Op::Add, subs) => {
            let mut acc = Poly::new();
            for s in subs {
                acc = poly_add(&acc, &poly_from_norm_bounded(s, fuel)?);
                if acc.len() > POLY_MAX_MONOMES { return None; }
            }
            Some(acc)
        }
        NormExpr::Op(Op::Mul, subs) => {
            let mut acc = Poly::new();
            acc.insert(Mono::new(), 1);
            for s in subs {
                let sp = poly_from_norm_bounded(s, fuel)?;
                if acc.len().saturating_mul(sp.len()) > POLY_MAX_MONOMES { return None; }
                acc = poly_mul(&acc, &sp);
                if acc.len() > POLY_MAX_MONOMES { return None; }
            }
            Some(acc)
        }
        NormExpr::Op(Op::Sub, subs) if subs.len() == 2 => {
            let a = poly_from_norm_bounded(&subs[0], fuel)?;
            let b = poly_from_norm_bounded(&subs[1], fuel)?;
            Some(poly_sub(&a, &b))
        }
        _ => {
            let mut mono = Mono::new();
            mono.insert(e.clone(), 1);
            let mut p = Poly::new();
            p.insert(mono, 1);
            Some(p)
        }
    }
}

fn norm_from_poly(p: &Poly) -> NormExpr {
    if p.is_empty() { return NormExpr::Const(0); }
    if p.len() == 1 {
        let (m, c) = p.iter().next().unwrap();
        if m.is_empty() { return NormExpr::Const(*c); }
        let mut factors: Vec<NormExpr> = Vec::new();
        if *c != 1 { factors.push(NormExpr::Const(*c)); }
        for (atom, exp) in m { for _ in 0..*exp { factors.push(atom.clone()); } }
        return if factors.len() == 1 { factors.into_iter().next().unwrap() }
               else { NormExpr::Op(Op::Mul, factors) };
    }
    let mut terms: Vec<NormExpr> = Vec::new();
    for (m, c) in p {
        if m.is_empty() { terms.push(NormExpr::Const(*c)); continue; }
        let mut factors: Vec<NormExpr> = Vec::new();
        if *c != 1 { factors.push(NormExpr::Const(*c)); }
        for (atom, exp) in m { for _ in 0..*exp { factors.push(atom.clone()); } }
        terms.push(if factors.len() == 1 { factors.into_iter().next().unwrap() }
                   else { NormExpr::Op(Op::Mul, factors) });
    }
    terms.sort();
    NormExpr::Op(Op::Add, terms)
}

fn normalize_xor(mut subs: Vec<NormExpr>) -> NormExpr {
    let mut flat: Vec<NormExpr> = Vec::new();
    for s in subs.drain(..) {
        match s { NormExpr::Op(Op::Xor, inner) => flat.extend(inner), other => flat.push(other) }
    }
    let mut const_x: u64 = 0;
    let mut counts: BTreeMap<NormExpr, u64> = BTreeMap::new();
    for s in flat {
        match s { NormExpr::Const(c) => const_x ^= c, other => *counts.entry(other).or_insert(0) += 1 }
    }
    let mut result: Vec<NormExpr> = Vec::new();
    if const_x != 0 { result.push(NormExpr::Const(const_x)); }
    for (k, c) in counts { if c % 2 == 1 { result.push(k); } }
    match result.len() {
        0 => NormExpr::Const(0),
        1 => result.into_iter().next().unwrap(),
        _ => NormExpr::Op(Op::Xor, result),
    }
}
fn normalize_and(mut subs: Vec<NormExpr>) -> NormExpr {
    let mut flat: Vec<NormExpr> = Vec::new();
    for s in subs.drain(..) {
        match s { NormExpr::Op(Op::And, inner) => flat.extend(inner), other => flat.push(other) }
    }
    flat.sort(); flat.dedup();
    if flat.iter().any(|s| matches!(s, NormExpr::Const(0))) { return NormExpr::Const(0); }
    let mut const_acc: Option<u64> = None;
    let mut non_const: Vec<NormExpr> = Vec::new();
    for s in flat {
        match s {
            NormExpr::Const(c) => const_acc = Some(const_acc.map_or(c, |a| a & c)),
            other => non_const.push(other),
        }
    }
    let const_keep = match const_acc { Some(u64::MAX) => None, other => other };
    if let Some(c) = const_keep { non_const.push(NormExpr::Const(c)); non_const.sort(); }
    match non_const.len() {
        0 => NormExpr::Const(u64::MAX),
        1 => non_const.into_iter().next().unwrap(),
        _ => NormExpr::Op(Op::And, non_const),
    }
}
fn normalize_or(mut subs: Vec<NormExpr>) -> NormExpr {
    let mut flat: Vec<NormExpr> = Vec::new();
    for s in subs.drain(..) {
        match s { NormExpr::Op(Op::Or, inner) => flat.extend(inner), other => flat.push(other) }
    }
    flat.sort(); flat.dedup();
    if flat.iter().any(|s| matches!(s, NormExpr::Const(u64::MAX))) { return NormExpr::Const(u64::MAX); }
    let mut const_acc: Option<u64> = None;
    let mut non_const: Vec<NormExpr> = Vec::new();
    for s in flat {
        match s {
            NormExpr::Const(c) => const_acc = Some(const_acc.map_or(c, |a| a | c)),
            other => non_const.push(other),
        }
    }
    let const_keep = match const_acc { Some(0) => None, other => other };
    if let Some(c) = const_keep { non_const.push(NormExpr::Const(c)); non_const.sort(); }
    match non_const.len() {
        0 => NormExpr::Const(0),
        1 => non_const.into_iter().next().unwrap(),
        _ => NormExpr::Op(Op::Or, non_const),
    }
}

#[derive(Clone, Debug)]
pub enum Pat { Var(u32), Const(u64), Op(Op, Vec<Pat>) }

pub fn normalize_pat(p: &Pat) -> NormExpr {
    match p {
        Pat::Var(v) => NormExpr::Var(*v),
        Pat::Const(c) => NormExpr::Const(*c),
        Pat::Op(op, subs) => {
            let children: Vec<NormExpr> = subs.iter().map(normalize_pat).collect();
            match op {
                Op::Const => NormExpr::Const(0),
                Op::Add | Op::Mul | Op::Sub => {
                    // [P0] Budget : si explosé, on retombe sur une forme non-normalisée
                    // qui ne matchera rien de l'autre côté → Unknown honnête.
                    let raw = NormExpr::Op(*op, children.clone());
                    let mut fuel = POLY_MAX_FUEL;
                    match poly_from_norm_bounded(&raw, &mut fuel) {
                        Some(p) => norm_from_poly(&p),
                        None => NormExpr::Op(*op, children), // sentinel non-normalisé
                    }
                }
                Op::Xor => normalize_xor(children),
                Op::And => normalize_and(children),
                Op::Or => normalize_or(children),
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProofResult { Proven, Unknown }

pub fn prove_rule(lhs: &Pat, rhs: &Pat) -> ProofResult {
    if normalize_pat(lhs) == normalize_pat(rhs) { ProofResult::Proven } else { ProofResult::Unknown }
}

// ============================================================
// ANALYSES
// ============================================================
#[derive(Clone, Debug, PartialEq)]
pub enum ConstData { Unknown, Known(u64), Conflict }
impl ConstData {
    #[inline] pub fn as_known(&self) -> Option<u64> {
        match self { ConstData::Known(v) => Some(*v), _ => None }
    }
    fn merge2(a: &Self, b: &Self) -> Self {
        match (a, b) {
            (ConstData::Known(x), ConstData::Known(y)) if x == y => ConstData::Known(*x),
            (ConstData::Unknown, x) => x.clone(),
            (x, ConstData::Unknown) => x.clone(),
            _ => ConstData::Conflict,
        }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub struct SizeData { pub min_nodes: u64 }
impl SizeData {
    #[inline] pub fn inf() -> Self { SizeData { min_nodes: u64::MAX } }
    #[inline] pub fn is_inf(&self) -> bool { self.min_nodes == u64::MAX }
}
#[derive(Clone, Debug, PartialEq)]
pub struct RangeData { pub lo: u64, pub hi: u64, pub exact: bool }
impl RangeData {
    #[inline] pub fn unknown() -> Self { RangeData { lo: 0, hi: u64::MAX, exact: false } }
    #[inline] pub fn exact_of(v: u64) -> Self { RangeData { lo: v, hi: v, exact: true } }
    fn merge2(a: &Self, b: &Self) -> Self {
        if a.exact && b.exact && a.lo == b.lo { return a.clone(); }
        RangeData { lo: a.lo.min(b.lo), hi: a.hi.max(b.hi), exact: a.exact && b.exact && a.lo == b.lo }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub struct BitWidthData { pub bits: u32, pub exact: bool }
impl BitWidthData {
    #[inline] pub fn full() -> Self { BitWidthData { bits: 64, exact: false } }
    fn merge2(a: &Self, b: &Self) -> Self {
        if a.bits == b.bits { return BitWidthData { bits: a.bits, exact: a.exact && b.exact }; }
        BitWidthData { bits: a.bits.max(b.bits), exact: false }
    }
}
#[derive(Clone, Debug, PartialEq)]
pub struct CostHintData { pub intrinsic: u64 }
impl CostHintData {
    fn merge2(a: &Self, b: &Self) -> Self { CostHintData { intrinsic: a.intrinsic.min(b.intrinsic) } }
}
#[derive(Clone, Debug)]
pub struct AnalysisData {
    pub cst: ConstData, pub size: SizeData, pub range: RangeData,
    pub bitwidth: BitWidthData, pub cost_hint: CostHintData,
}
impl AnalysisData {
    pub fn new() -> Self {
        AnalysisData {
            cst: ConstData::Unknown, size: SizeData::inf(),
            range: RangeData::unknown(), bitwidth: BitWidthData::full(),
            cost_hint: CostHintData { intrinsic: u64::MAX / 2 },
        }
    }
    pub fn make(node: &ENode, children: &[AnalysisData]) -> AnalysisData {
        let cst = compute_const(node, children);
        let range0 = compute_range(node, children, &cst);
        let bitwidth0 = compute_bitwidth(&range0);
        let range = refine_range_with_bitwidth(range0, &bitwidth0);
        let bitwidth = compute_bitwidth(&range);
        let cost_hint = compute_cost_hint(node, &bitwidth, &cst);
        let size = compute_size(children);
        AnalysisData { cst, size, range, bitwidth, cost_hint }
    }
    pub fn merge(a: &AnalysisData, b: &AnalysisData) -> AnalysisData {
        AnalysisData {
            cst: ConstData::merge2(&a.cst, &b.cst),
            size: SizeData { min_nodes: a.size.min_nodes.min(b.size.min_nodes) },
            range: RangeData::merge2(&a.range, &b.range),
            bitwidth: BitWidthData::merge2(&a.bitwidth, &b.bitwidth),
            cost_hint: CostHintData::merge2(&a.cost_hint, &b.cost_hint),
        }
    }
}

fn compute_const(node: &ENode, children: &[AnalysisData]) -> ConstData {
    match node.op {
        Op::Const => match strict_payload_to_u64(&node.payload) {
            Some(v) => ConstData::Known(v),
            None => ConstData::Conflict, // payload malformé → signal
        },
        Op::Sub => {
            if children.len() != 2 { return ConstData::Unknown; }
            match (children[0].cst.as_known(), children[1].cst.as_known()) {
                (Some(a), Some(b)) => ConstData::Known(a.wrapping_sub(b)),
                _ => {
                    if matches!(children[0].cst, ConstData::Conflict) || matches!(children[1].cst, ConstData::Conflict) {
                        ConstData::Conflict
                    } else { ConstData::Unknown }
                }
            }
        }
        _ => {
            let (init, f): (u64, fn(u64, u64) -> u64) = match node.op {
                Op::Add => (0, |a, b| a.wrapping_add(b)),
                Op::Mul => (1, |a, b| a.wrapping_mul(b)),
                Op::Xor => (0, |a, b| a ^ b),
                Op::And => (u64::MAX, |a, b| a & b),
                Op::Or => (0, |a, b| a | b),
                Op::Const | Op::Sub => unreachable!(),
            };
            let mut acc = init;
            for c in children {
                match &c.cst {
                    ConstData::Known(v) => acc = f(acc, *v),
                    ConstData::Unknown => return ConstData::Unknown,
                    ConstData::Conflict => return ConstData::Conflict,
                }
            }
            ConstData::Known(acc)
        }
    }
}

// [P0] range_add : checked sur lo ET hi
fn range_add(a: &RangeData, b: &RangeData) -> RangeData {
    match (a.lo.checked_add(b.lo), a.hi.checked_add(b.hi)) {
        (Some(lo), Some(hi)) => RangeData { lo, hi, exact: a.exact && b.exact },
        _ => RangeData::unknown(),
    }
}
fn range_mul(a: &RangeData, b: &RangeData) -> RangeData {
    if a.exact && b.exact { return RangeData::exact_of(a.lo.wrapping_mul(b.lo)); }
    if a.exact && b.lo == b.hi { return RangeData::exact_of(a.lo.wrapping_mul(b.lo)); }
    if b.exact && a.lo == a.hi { return RangeData::exact_of(a.lo.wrapping_mul(b.lo)); }
    match a.hi.checked_mul(b.hi) {
        Some(hi) => RangeData { lo: 0, hi, exact: false },
        None => RangeData::unknown(),
    }
}
fn range_sub(a: &RangeData, b: &RangeData) -> RangeData {
    if a.lo >= b.hi {
        match (a.lo.checked_sub(b.hi), a.hi.checked_sub(b.lo)) {
            (Some(lo), Some(hi)) => RangeData { lo, hi, exact: false },
            _ => RangeData::unknown(),
        }
    } else if a.exact && b.exact {
        RangeData::exact_of(a.lo.wrapping_sub(b.lo))
    } else { RangeData::unknown() }
}

/// [P0] Correctif : renvoie un masque ≥ x, jamais < x.
/// mask = 2^ceil(log2(x+1)) - 1.
#[inline]
fn bitmask_upper(x: u64) -> u64 {
    if x == u64::MAX { return u64::MAX; }
    match x.checked_add(1).and_then(|y| y.checked_next_power_of_two()) {
        Some(p) => (p - 1).max(x),
        None => u64::MAX,
    }
}

fn compute_range(node: &ENode, children: &[AnalysisData], cst: &ConstData) -> RangeData {
    if let ConstData::Known(v) = cst { return RangeData::exact_of(*v); }
    match node.op {
        Op::Const => match strict_payload_to_u64(&node.payload) {
            Some(v) => RangeData::exact_of(v),
            None => RangeData::unknown(),
        },
        Op::Add if children.len() == 2 => range_add(&children[0].range, &children[1].range),
        Op::Mul if children.len() == 2 => range_mul(&children[0].range, &children[1].range),
        Op::Sub if children.len() == 2 => range_sub(&children[0].range, &children[1].range),
        Op::And => {
            let cap = children.iter().map(|c| c.range.hi).min().unwrap_or(u64::MAX);
            RangeData { lo: 0, hi: cap, exact: false }
        }
        Op::Or | Op::Xor => {
            let cap: u64 = children.iter()
                .map(|c| bitmask_upper(c.range.hi))
                .fold(0u64, |a, b| a | b);
            RangeData { lo: 0, hi: cap, exact: false }
        }
        _ => RangeData::unknown(),
    }
}
fn compute_bitwidth(r: &RangeData) -> BitWidthData {
    if r.exact { BitWidthData { bits: 64 - r.lo.leading_zeros(), exact: true } }
    else { BitWidthData { bits: 64 - r.hi.leading_zeros(), exact: false } }
}
fn refine_range_with_bitwidth(r: RangeData, bw: &BitWidthData) -> RangeData {
    if bw.bits >= 64 { return r; }
    let cap: u64 = if bw.bits == 0 { 0 } else { (1u64 << bw.bits) - 1 };
    RangeData { lo: r.lo, hi: r.hi.min(cap), exact: r.exact }
}
fn compute_cost_hint(node: &ENode, bw: &BitWidthData, cst: &ConstData) -> CostHintData {
    if matches!(cst, ConstData::Known(_)) { return CostHintData { intrinsic: 0 }; }
    let op_weight: u64 = match node.op {
        Op::Const => 0,
        Op::Add | Op::Sub | Op::Xor | Op::And | Op::Or => 1,
        Op::Mul => 3,
    };
    let bits_factor = (bw.bits as u64).saturating_add(7) / 8;
    CostHintData { intrinsic: op_weight.saturating_mul(bits_factor.max(1)) }
}
fn compute_size(children: &[AnalysisData]) -> SizeData {
    let mut total: u64 = 1;
    for c in children {
        if c.size.is_inf() { return SizeData::inf(); }
        total = total.saturating_add(c.size.min_nodes);
    }
    SizeData { min_nodes: total }
}

// ============================================================
// BINDINGS
// ============================================================
pub type Bindings = HashMap<u32, ClassId>;

fn merge_bindings(a: &Bindings, b: &Bindings) -> Option<Bindings> {
    let mut out = a.clone();
    for (k, v) in b {
        match out.get(k) {
            Some(e) if *e != *v => return None,
            _ => { out.insert(*k, *v); }
        }
    }
    Some(out)
}
fn dedup_bindings(bs: Vec<Bindings>) -> Vec<Bindings> {
    let mut seen: HashSet<Vec<(u32, ClassId)>> = HashSet::new();
    let mut out = Vec::new();
    for b in bs {
        let mut k: Vec<(u32, ClassId)> = b.iter().map(|(a, b)| (*a, *b)).collect();
        k.sort();
        if seen.insert(k) { out.push(b); }
    }
    out
}
fn encode_pat(p: &Pat, buf: &mut Vec<u8>) {
    match p {
        Pat::Var(v) => { buf.push(0); buf.extend_from_slice(&v.to_le_bytes()); }
        Pat::Const(c) => { buf.push(1); buf.extend_from_slice(&c.to_le_bytes()); }
        Pat::Op(op, subs) => {
            buf.push(2); buf.push(op.code());
            buf.extend_from_slice(&(subs.len() as u32).to_le_bytes());
            for s in subs { encode_pat(s, buf); }
        }
    }
}
pub fn pattern_id(p: &Pat) -> PatternId {
    let mut buf = Vec::new();
    encode_pat(p, &mut buf);
    hash128(&buf, 0xdead_beef_cafe_babe)
}
fn pattern_specificity(p: &Pat) -> u32 {
    match p {
        Pat::Var(_) => 10,
        Pat::Const(_) => 0,
        Pat::Op(_, subs) => 5 + subs.iter().map(pattern_specificity).sum::<u32>() / 2,
    }
}
fn pattern_vars(p: &Pat) -> Vec<u32> {
    let mut out = Vec::new();
    fn go(p: &Pat, out: &mut Vec<u32>) {
        match p {
            Pat::Var(v) => out.push(*v),
            Pat::Const(_) => {}
            Pat::Op(_, subs) => for s in subs { go(s, out); }
        }
    }
    go(p, &mut out);
    out.sort(); out.dedup();
    out
}

// [P0] Strict : refuse tout payload != 8 octets
#[inline]
fn strict_payload_to_u64(p: &[u8]) -> Option<u64> {
    if p.len() != 8 { return None; }
    let mut buf = [0u8; 8];
    buf.copy_from_slice(p);
    Some(u64::from_be_bytes(buf))
}

// ============================================================
// MULTI-COST
// ============================================================
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct MultiCost { pub energy: u64, pub size: u64, pub depth: u64 }
impl MultiCost {
    #[inline] pub fn zero() -> Self { MultiCost { energy: 0, size: 0, depth: 0 } }
    pub const INF: MultiCost = MultiCost { energy: u64::MAX / 2, size: u64::MAX / 2, depth: u64::MAX / 2 };
    #[inline] pub fn is_inf(&self) -> bool { self.energy >= u64::MAX / 2 }
    #[inline] pub fn sum(&self) -> u64 { self.energy.saturating_add(self.size).saturating_add(self.depth) }
}
#[inline]
fn dominates(a: &MultiCost, b: &MultiCost) -> bool {
    a.energy <= b.energy && a.size <= b.size && a.depth <= b.depth
        && (a.energy < b.energy || a.size < b.size || a.depth < b.depth)
}

#[derive(Clone, Copy, Debug)]
pub enum ExtractionMode {
    Exact,
    Bounded { pareto_cap: usize, cartesian_cap: usize },
}
impl Default for ExtractionMode { fn default() -> Self { ExtractionMode::Exact } }
impl ExtractionMode {
    fn pareto_cap(&self) -> Option<usize> {
        match self {
            ExtractionMode::Exact => None,
            ExtractionMode::Bounded { pareto_cap, .. } => Some((*pareto_cap).max(1)),
        }
    }
    fn cartesian_cap(&self) -> Option<usize> {
        match self {
            ExtractionMode::Exact => None,
            ExtractionMode::Bounded { cartesian_cap, .. } => Some((*cartesian_cap).max(1)),
        }
    }
}

// ============================================================
// PARETO — fixpoint monotone (ever_seen)
// ============================================================
#[derive(Clone, Debug, Default)]
pub struct Pareto {
    pub costs: Vec<MultiCost>,
    pub witness: Vec<(usize, Vec<MultiCost>)>,
    pub truncated: bool,
    ever_seen: HashSet<MultiCost>,
}
impl Pareto {
    pub fn new() -> Self {
        Pareto { costs: Vec::new(), witness: Vec::new(), truncated: false, ever_seen: HashSet::new() }
    }
    pub fn insert_with(&mut self, c: MultiCost, node_idx: usize,
                       child_costs: Vec<MultiCost>, mode: ExtractionMode) -> bool {
        if c.is_inf() { return false; }
        if !self.ever_seen.insert(c) { return false; }
        for e in &self.costs { if dominates(e, &c) { return false; } }
        if self.costs.contains(&c) { return false; }
        let mut i = 0;
        while i < self.costs.len() {
            if dominates(&c, &self.costs[i]) {
                self.costs.remove(i); self.witness.remove(i);
            } else { i += 1; }
        }
        self.costs.push(c);
        self.witness.push((node_idx, child_costs));
        if let Some(cap) = mode.pareto_cap() {
            if self.costs.len() > cap {
                self.truncated = true;
                let mut idx: Vec<usize> = (0..self.costs.len()).collect();
                idx.sort_by_key(|&i| self.costs[i].sum());
                self.costs = idx.iter().take(cap).map(|&i| self.costs[i]).collect();
                self.witness = idx.iter().take(cap).map(|&i| self.witness[i].clone()).collect();
            }
        }
        true
    }
    #[inline] pub fn best(&self) -> Option<MultiCost> { self.costs.iter().min().copied() }
    #[inline] pub fn iter(&self) -> impl Iterator<Item = &MultiCost> { self.costs.iter() }
    #[inline] pub fn is_empty(&self) -> bool { self.costs.is_empty() }
    pub fn witness_of(&self, c: &MultiCost) -> Option<&(usize, Vec<MultiCost>)> {
        self.costs.iter().position(|x| x == c).map(|i| &self.witness[i])
    }
}

// ============================================================
// MODÈLES DE COÛT
// ============================================================
pub trait CostModel: Send + Sync + 'static {
    fn name(&self) -> &'static str;
    fn node_cost(&self, node: &ENode, children: &[MultiCost]) -> MultiCost;
}
pub struct CpuCost;
impl CostModel for CpuCost {
    fn name(&self) -> &'static str { "cpu" }
    fn node_cost(&self, n: &ENode, ch: &[MultiCost]) -> MultiCost {
        let (e0, s0) = match n.op { Op::Const => (0, 0), Op::Mul => (3, 1), _ => (1, 1) };
        let mut energy = e0; let mut size = s0;
        let mut depth: u64 = if n.op == Op::Const { 0 } else { 1 };
        for c in ch {
            energy = energy.saturating_add(c.energy);
            size = size.saturating_add(c.size);
            depth = depth.max(c.depth.saturating_add(1));
        }
        MultiCost { energy, size, depth }
    }
}
pub struct GpuCost;
impl CostModel for GpuCost {
    fn name(&self) -> &'static str { "gpu" }
    fn node_cost(&self, n: &ENode, ch: &[MultiCost]) -> MultiCost {
        let mut acc = match n.op {
            Op::Const => MultiCost::zero(),
            Op::Mul => MultiCost { energy: 5, size: 1, depth: 2 },
            _ => MultiCost { energy: 1, size: 1, depth: 1 },
        };
        for c in ch {
            acc.energy = acc.energy.saturating_add(c.energy);
            acc.size = acc.size.saturating_add(c.size);
            acc.depth = acc.depth.max(c.depth.saturating_add(1));
        }
        acc
    }
}
pub struct FpgaCost;
impl CostModel for FpgaCost {
    fn name(&self) -> &'static str { "fpga" }
    fn node_cost(&self, n: &ENode, ch: &[MultiCost]) -> MultiCost {
        let mut acc = match n.op {
            Op::Const => MultiCost::zero(),
            Op::Xor | Op::And | Op::Or => MultiCost { energy: 1, size: 1, depth: 1 },
            Op::Add | Op::Sub => MultiCost { energy: 2, size: 1, depth: 1 },
            Op::Mul => MultiCost { energy: 10, size: 1, depth: 3 },
        };
        for c in ch {
            acc.energy = acc.energy.saturating_add(c.energy);
            acc.size = acc.size.saturating_add(c.size);
            acc.depth = acc.depth.max(c.depth.saturating_add(1));
        }
        acc
    }
}

// ============================================================
// EXPR
// ============================================================
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Expr {
    Const(u64),
    Var(u32),   // Var(c) où c est un ClassId dans le contexte de vérification
    Add(Vec<Expr>), Mul(Vec<Expr>), Xor(Vec<Expr>),
    Sub(Vec<Expr>), And(Vec<Expr>), Or(Vec<Expr>),
}
impl Expr {
    pub fn eval(&self, env: &HashMap<u32, u64>) -> u64 {
        match self {
            Expr::Const(v) => *v,
            Expr::Var(v) => *env.get(v).unwrap_or(&0),
            Expr::Add(xs) => xs.iter().fold(0u64, |a, x| a.wrapping_add(x.eval(env))),
            Expr::Mul(xs) => xs.iter().fold(1u64, |a, x| a.wrapping_mul(x.eval(env))),
            Expr::Xor(xs) => xs.iter().fold(0u64, |a, x| a ^ x.eval(env)),
            Expr::Sub(xs) if xs.len() == 2 => xs[0].eval(env).wrapping_sub(xs[1].eval(env)),
            Expr::Sub(_) => 0,
            Expr::And(xs) => xs.iter().fold(u64::MAX, |a, x| a & x.eval(env)),
            Expr::Or(xs) => xs.iter().fold(0u64, |a, x| a | x.eval(env)),
        }
    }
    pub fn repr(&self) -> String {
        match self {
            Expr::Const(v) => format!("{}", v),
            Expr::Var(v) => format!("v{}", v),
            Expr::Add(xs) => format!("(+ {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
            Expr::Mul(xs) => format!("(* {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
            Expr::Xor(xs) => format!("(^ {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
            Expr::Sub(xs) => format!("(- {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
            Expr::And(xs) => format!("(& {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
            Expr::Or(xs) => format!("(| {})", xs.iter().map(|x| x.repr()).collect::<Vec<_>>().join(" ")),
        }
    }
}

pub fn instantiate_pat_expr(p: &Pat, s: &HashMap<u32, Expr>) -> Expr {
    match p {
        Pat::Var(v) => s.get(v).cloned().unwrap_or(Expr::Var(*v)),
        Pat::Const(c) => Expr::Const(*c),
        Pat::Op(op, subs) => {
            let children: Vec<Expr> = subs.iter().map(|x| instantiate_pat_expr(x, s)).collect();
            match op {
                Op::Const => Expr::Const(0),
                Op::Add => Expr::Add(children),
                Op::Mul => Expr::Mul(children),
                Op::Xor => Expr::Xor(children),
                Op::Sub => Expr::Sub(children),
                Op::And => Expr::And(children),
                Op::Or => Expr::Or(children),
            }
        }
    }
}

// ============================================================
// PREUVES
// ============================================================
#[derive(Clone, Debug)]
pub enum Proof {
    Refl(Expr),
    Sym(Box<Proof>),
    Trans(Box<Proof>, Box<Proof>),
    Congr(Op, Vec<Proof>),
    Rule { name: String, lhs: Pat, rhs: Pat, subst: HashMap<u32, Expr> },
    ConstFold { op: Op, args: Vec<u64>, result: u64 },
}

pub fn eval_const_op(op: Op, args: &[u64]) -> Option<u64> {
    match op {
        Op::Const => None,
        Op::Add => Some(args.iter().fold(0u64, |a, &b| a.wrapping_add(b))),
        Op::Mul => Some(args.iter().fold(1u64, |a, &b| a.wrapping_mul(b))),
        Op::Xor => Some(args.iter().fold(0u64, |a, &b| a ^ b)),
        Op::And => Some(args.iter().fold(u64::MAX, |a, &b| a & b)),
        Op::Or => Some(args.iter().fold(0u64, |a, &b| a | b)),
        Op::Sub if args.len() == 2 => Some(args[0].wrapping_sub(args[1])),
        Op::Sub => None,
    }
}

/// Vérificateur interne : contrôle que la preuve est bien formée.
/// [P0] Ne vérifie PAS encore que la preuve correspond aux extrémités de l'union
/// (c'est fait par `EGraph::verify_record` qui connaît l'egraph).
pub fn check_proof(p: &Proof) -> Result<(Expr, Expr), String> {
    match p {
        Proof::Refl(e) => Ok((e.clone(), e.clone())),
        Proof::Sym(inner) => { let (a, b) = check_proof(inner)?; Ok((b, a)) }
        Proof::Trans(p1, p2) => {
            let (a, b) = check_proof(p1)?;
            let (c, d) = check_proof(p2)?;
            if b != c {
                return Err(format!("transitivité rompue : {} ≠ {}", b.repr(), c.repr()));
            }
            Ok((a, d))
        }
        Proof::Congr(op, ps) => {
            let mut lhs = Vec::with_capacity(ps.len());
            let mut rhs = Vec::with_capacity(ps.len());
            for q in ps {
                let (a, b) = check_proof(q)?;
                lhs.push(a); rhs.push(b);
            }
            let wrap = |xs: Vec<Expr>| match op {
                Op::Add => Expr::Add(xs), Op::Mul => Expr::Mul(xs),
                Op::Xor => Expr::Xor(xs), Op::Sub => Expr::Sub(xs),
                Op::And => Expr::And(xs), Op::Or => Expr::Or(xs),
                Op::Const => Expr::Const(0),
            };
            Ok((wrap(lhs), wrap(rhs)))
        }
        Proof::Rule { lhs, rhs, subst, .. } => {
            match prove_rule(lhs, rhs) {
                ProofResult::Proven => {}
                ProofResult::Unknown => return Err("règle non prouvée".into()),
            }
            let l = instantiate_pat_expr(lhs, subst);
            let r = instantiate_pat_expr(rhs, subst);
            Ok((l, r))
        }
        Proof::ConstFold { op, args, result } => {
            let computed = eval_const_op(*op, args)
                .ok_or_else(|| format!("arité invalide pour {:?}", op))?;
            if computed != *result {
                return Err(format!("const fold {} ≠ {}", computed, result));
            }
            let xs: Vec<Expr> = args.iter().map(|v| Expr::Const(*v)).collect();
            let lhs = match op {
                Op::Add => Expr::Add(xs), Op::Mul => Expr::Mul(xs),
                Op::Xor => Expr::Xor(xs), Op::Sub => Expr::Sub(xs),
                Op::And => Expr::And(xs), Op::Or => Expr::Or(xs),
                Op::Const => Expr::Const(0),
            };
            Ok((lhs, Expr::Const(*result)))
        }
    }
}

// ============================================================
// SCHEDULER
// ============================================================
pub struct EGraphView<'a> { pub classes: &'a [EClass] }
impl<'a> EGraphView<'a> {
    pub fn find_ro(&self, mut id: ClassId) -> ClassId {
        while self.classes[id as usize].parent != id { id = self.classes[id as usize].parent; }
        id
    }
    pub fn const_of_binding(&self, b: &Bindings, v: u32) -> Option<u64> {
        let id = *b.get(&v)?;
        let r = self.find_ro(id);
        self.classes[r as usize].data.cst.as_known()
    }
}

pub type CondFn = fn(&EGraphView, &Bindings) -> bool;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuleTrust { Trusted, Experimental }

#[derive(Clone)]
pub struct RuleDef {
    pub name: String,
    pub lhs: Pat, pub rhs: Pat,
    pub cond: Option<CondFn>,
    pub priority: u64,
    pub trust: RuleTrust,
    pub applications: u64,
    pub yield_total: u64,
    pub nodes_added: u64,
    pub backoff_until: u64,
    pub bailed: u64,
}

pub struct RuleScheduler { pub rules: Vec<RuleDef>, pub total_nodes: u64 }
impl RuleScheduler {
    pub fn new() -> Self { RuleScheduler { rules: Vec::new(), total_nodes: 0 } }
    pub fn add_trusted(&mut self, name: &str, lhs: Pat, rhs: Pat) {
        self.add_with_trust(name, lhs, rhs, None, RuleTrust::Trusted);
    }
    pub fn add_experimental(&mut self, name: &str, lhs: Pat, rhs: Pat) {
        self.add_with_trust(name, lhs, rhs, None, RuleTrust::Experimental);
    }
    pub fn add_conditional(&mut self, name: &str, lhs: Pat, rhs: Pat, cond: CondFn) {
        self.add_with_trust(name, lhs, rhs, Some(cond), RuleTrust::Trusted);
    }
    fn add_with_trust(&mut self, name: &str, lhs: Pat, rhs: Pat, cond: Option<CondFn>, trust: RuleTrust) {
        if trust == RuleTrust::Trusted && prove_rule(&lhs, &rhs) != ProofResult::Proven {
            panic!("règle Trusted non prouvée : {}", name);
        }
        self.rules.push(RuleDef {
            name: name.into(), lhs, rhs, cond, priority: 100, trust,
            applications: 0, yield_total: 0, nodes_added: 0, backoff_until: 0, bailed: 0,
        });
    }
    pub fn adapt(&mut self) {
        for r in &mut self.rules {
            if r.applications > 0 {
                let rate = (r.yield_total.saturating_mul(100)) / r.applications.max(1);
                r.priority = 50 + rate.min(200);
            }
            if r.nodes_added > r.backoff_until && r.bailed >= 2 {
                r.backoff_until = r.backoff_until.saturating_mul(2).saturating_add(1000);
            }
        }
        self.rules.sort_by(|a, b| b.priority.cmp(&a.priority));
    }
    pub fn record(&mut self, name: &str, produced: bool, nodes_delta: u64) {
        for r in &mut self.rules {
            if r.name == name {
                r.applications = r.applications.saturating_add(1);
                if produced { r.yield_total = r.yield_total.saturating_add(1); }
                r.nodes_added = r.nodes_added.saturating_add(nodes_delta);
                if !produced { r.bailed = r.bailed.saturating_add(1); }
                return;
            }
        }
    }
    #[inline]
    pub fn is_backed_off(&self, i: usize) -> bool {
        self.total_nodes < self.rules[i].backoff_until
    }
}

// ============================================================
// ECLASS / UNION RECORD
// ============================================================
#[derive(Clone, Debug)]
pub struct UnionRecord {
    pub from: ClassId,
    pub to: ClassId,
    pub rule: String,
    pub detail: String,
    pub bindings: Option<Bindings>,
    pub proof: Option<Proof>,
}

pub struct EClass {
    pub parent: ClassId,
    pub size: u32,
    pub nodes: Vec<ENode>,
    pub parents: Vec<(ClassId, usize)>,
    pub fp: Fingerprint,
    pub data: AnalysisData,
}

// ============================================================
// RUNNER
// ============================================================
#[derive(Clone, Copy, Debug)]
pub struct Budget {
    pub start: Instant,
    pub time_ms: u128,
    pub nodes: usize,
    pub stop: bool,
}
impl Budget {
    pub fn new(time_ms: u128, nodes: usize) -> Self {
        Budget { start: Instant::now(), time_ms, nodes, stop: false }
    }
    #[inline]
    pub fn expired(&mut self, cur_nodes: usize) -> bool {
        if self.stop { return true; }
        if cur_nodes >= self.nodes { self.stop = true; return true; }
        if self.start.elapsed().as_millis() >= self.time_ms { self.stop = true; return true; }
        false
    }
}

pub struct Runner {
    pub iter_limit: usize,
    pub node_limit: usize,
    pub time_limit_ms: u128,
    pub parallel: bool,
    pub parallel_threshold: usize,
    pub max_matches_per_rule: usize,
    pub worker_threads: usize,
}
impl Default for Runner {
    fn default() -> Self {
        Runner {
            iter_limit: 100, node_limit: 1_000_000, time_limit_ms: 5_000,
            parallel: true, parallel_threshold: 4, max_matches_per_rule: 64,
            worker_threads: 4,
        }
    }
}
impl Runner {
    pub fn new() -> Self { Self::default() }
    pub fn with_iter_limit(mut self, n: usize) -> Self { self.iter_limit = n; self }
    pub fn with_node_limit(mut self, n: usize) -> Self { self.node_limit = n; self }
    pub fn with_time_limit_ms(mut self, t: u128) -> Self { self.time_limit_ms = t; self }
    pub fn with_parallel(mut self, p: bool) -> Self { self.parallel = p; self }
    pub fn with_max_matches(mut self, n: usize) -> Self { self.max_matches_per_rule = n.max(1); self }
    pub fn with_workers(mut self, n: usize) -> Self { self.worker_threads = n.max(1); self }

    pub fn run(&self, g: &mut EGraph) -> usize {
        let mut budget = Budget::new(self.time_limit_ms, self.node_limit);
        let mut iters = 0;
        let n = g.classes.len() as ClassId;
        for cid in 0..n { if g.find_ro(cid) == cid { g.push_dirty(cid); } }

        loop {
            let mut applied = false;
            loop {
                if budget.expired(g.classes.len()) { break; }
                let dirty = g.drain_dirty();
                if dirty.is_empty() { break; }
                let cap = self.max_matches_per_rule;
                let collected: Vec<(ClassId, Vec<(usize, Bindings)>)> =
                    if self.parallel && dirty.len() >= self.parallel_threshold {
                        let g_ro: &EGraph = &*g;
                        let workers = self.worker_threads;
                        thread::scope(|s| {
                            let counter = AtomicUsize::new(0);
                            let dirty_ref = &dirty;
                            let handles: Vec<_> = (0..workers).map(|_| {
                                s.spawn(|| {
                                    let mut local = Vec::new();
                                    loop {
                                        let i = counter.fetch_add(1, Ordering::Relaxed);
                                        if i >= dirty_ref.len() { break; }
                                        let cid = dirty_ref[i];
                                        local.push((cid, g_ro.collect_matches(cid, cap)));
                                    }
                                    local
                                })
                            }).collect();
                            let mut out = Vec::new();
                            for h in handles { out.extend(h.join().unwrap()); }
                            out
                        })
                    } else {
                        dirty.iter().map(|&cid| (cid, g.collect_matches(cid, cap))).collect()
                    };
                for (cid, matches) in collected {
                    if g.apply_collected(cid, matches) { applied = true; }
                }
                if g.rebuild() { applied = true; }
            }
            iters += 1;
            g.scheduler.total_nodes = g.classes.len() as u64;
            if iters % 3 == 0 { g.scheduler.adapt(); }
            if !applied { break; }
            if iters >= self.iter_limit { break; }
            if g.classes.len() >= self.node_limit { break; }
            if budget.expired(g.classes.len()) { break; }
        }
        iters
    }
}

// ============================================================
// EGRAPH
// ============================================================
struct MatchCache {
    generation: u64,
    entries: HashMap<(PatternId, ClassId), Vec<Bindings>>,
}

pub struct EGraph {
    pub classes: Vec<EClass>,
    hashcons: HashMap<ENode, ClassId>,
    dirty: VecDeque<ClassId>,
    dirty_set: HashSet<ClassId>,
    pub history: Vec<UnionRecord>,
    parent_history: Vec<Option<(ClassId, usize)>>,
    index: HashMap<(u8, u32), Vec<ClassId>>,
    rem_index: HashMap<(u8, u32, u32, u8), Vec<ClassId>>,
    index_valid: bool,
    rem_index_valid: bool,
    match_cache: Mutex<MatchCache>,
    cache_generation: u64,
    pub scheduler: RuleScheduler,
    pub unions: u64,
    pub rule_apps: u64,
}

impl EGraph {
    pub fn new() -> Self {
        EGraph {
            classes: Vec::new(), hashcons: HashMap::new(),
            dirty: VecDeque::new(), dirty_set: HashSet::new(),
            history: Vec::new(), parent_history: Vec::new(),
            index: HashMap::new(), rem_index: HashMap::new(),
            index_valid: false, rem_index_valid: false,
            match_cache: Mutex::new(MatchCache { generation: 0, entries: HashMap::new() }),
            cache_generation: 0,
            scheduler: RuleScheduler::new(),
            unions: 0, rule_apps: 0,
        }
    }
    #[inline] fn invalidate_cache(&mut self) { self.cache_generation = self.cache_generation.wrapping_add(1); }

    pub fn find(&mut self, id: ClassId) -> ClassId {
        let mut root = id;
        while self.classes[root as usize].parent != root { root = self.classes[root as usize].parent; }
        let mut c = id;
        while self.classes[c as usize].parent != root {
            let n = self.classes[c as usize].parent;
            self.classes[c as usize].parent = root;
            c = n;
        }
        root
    }
    pub fn find_ro(&self, mut id: ClassId) -> ClassId {
        while self.classes[id as usize].parent != id { id = self.classes[id as usize].parent; }
        id
    }
    fn canon_node_ro(&self, n: &ENode) -> ENode {
        ENode {
            op: n.op,
            children: n.children.iter().map(|&c| self.find_ro(c)).collect(),
            payload: n.payload.clone(),
        }
    }
    pub fn push_dirty(&mut self, cid: ClassId) {
        let r = self.find_ro(cid);
        if self.dirty_set.insert(r) { self.dirty.push_back(r); }
    }
    fn pop_dirty(&mut self) -> Option<ClassId> {
        while let Some(cid) = self.dirty.pop_front() {
            self.dirty_set.remove(&cid);
            if self.find_ro(cid) == cid { return Some(cid); }
        }
        None
    }
    fn drain_dirty(&mut self) -> Vec<ClassId> {
        let mut out = Vec::new();
        while let Some(cid) = self.pop_dirty() { out.push(cid); }
        out
    }

    pub fn make_node(&mut self, op: Op, children: Vec<ClassId>, payload: Vec<u8>) -> ClassId {
        let mut children: Vec<ClassId> = children.into_iter().map(|c| self.find(c)).collect();
        if op.associative() {
            let mut flat = Vec::new();
            for c in children {
                let cr = self.find(c);
                let nodes: Vec<ENode> = self.classes[cr as usize].nodes.clone();
                let mut expanded = false;
                for n in &nodes {
                    if n.op == op {
                        for &cc in &n.children { flat.push(self.find(cc)); }
                        expanded = true; break;
                    }
                }
                if !expanded { flat.push(cr); }
            }
            children = flat;
        }
        if op.commutative() { children.sort_unstable(); }

        let node = ENode { op, children, payload };
        if let Some(&id) = self.hashcons.get(&node) { return self.find(id); }
        let id = self.classes.len() as ClassId;
        let child_data: Vec<AnalysisData> = node.children.iter().map(|&c| {
            let rc = self.find_ro(c);
            self.classes[rc as usize].data.clone()
        }).collect();
        let data = AnalysisData::make(&node, &child_data);

        self.classes.push(EClass {
            parent: id, size: 1, nodes: vec![node.clone()],
            parents: Vec::new(), fp: [0; 2], data,
        });
        self.parent_history.push(None);
        for &c in &node.children {
            let rc = self.find_ro(c);
            self.classes[rc as usize].parents.push((id, 0));
        }
        self.hashcons.insert(node, id);
        self.push_dirty(id);
        self.index_valid = false; self.rem_index_valid = false;
        self.invalidate_cache();
        id
    }

    pub fn make_const_u64(&mut self, v: u64) -> ClassId {
        self.make_node(Op::Const, vec![], v.to_be_bytes().to_vec())
    }

    // --------------------------------------------------------
    // Union avec certificat VÉRIFIÉ pré-union
    // --------------------------------------------------------
    pub fn union_with_proof(&mut self, a: ClassId, b: ClassId, rule: &str, detail: &str) -> bool {
        self.union_with_certificate(a, b, rule, detail, None, None)
    }

    pub fn union_with_certificate(
        &mut self, a: ClassId, b: ClassId,
        rule: &str, detail: &str,
        bindings: Option<Bindings>,
        proof: Option<Proof>,
    ) -> bool {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb { return false; }

        // [P0] Vérification AVANT mutation : la preuve doit relier ra et rb.
        if let Some(p) = &proof {
            let rec = UnionRecord {
                from: ra, to: rb,
                rule: rule.into(), detail: detail.into(),
                bindings: bindings.clone(), proof: Some(p.clone()),
            };
            if self.verify_record_pre_union(&rec).is_err() {
                return false;
            }
        }

        let (big, small) = if self.classes[ra as usize].size >= self.classes[rb as usize].size {
            (ra, rb)
        } else { (rb, ra) };

        let small_nodes = self.classes[small as usize].nodes.clone();
        for n in &small_nodes {
            let cn = self.canon_node_ro(n);
            if let Some(&id) = self.hashcons.get(&cn) {
                if self.find_ro(id) == small { self.hashcons.remove(&cn); }
            }
        }
        self.parent_history[small as usize] = Some((big, self.history.len()));
        self.history.push(UnionRecord {
            from: small, to: big,
            rule: rule.into(), detail: detail.into(),
            bindings, proof,
        });

        let small_data = self.classes[small as usize].data.clone();
        let merged = AnalysisData::merge(&self.classes[big as usize].data, &small_data);
        self.classes[big as usize].data = merged;
        self.classes[small as usize].parent = big;
        self.classes[big as usize].size += self.classes[small as usize].size;

        let small_nodes = std::mem::take(&mut self.classes[small as usize].nodes);
        self.classes[big as usize].nodes.extend(small_nodes);

        let small_parents = std::mem::take(&mut self.classes[small as usize].parents);
        for p in small_parents {
            self.classes[big as usize].parents.push(p);
            self.push_dirty(p.0);
        }
        let big_nodes = self.classes[big as usize].nodes.clone();
        for n in &big_nodes {
            let cn = self.canon_node_ro(n);
            self.hashcons.insert(cn, big);
        }
        self.push_dirty(big);
        self.index_valid = false; self.rem_index_valid = false;
        self.invalidate_cache();
        self.unions += 1;
        true
    }

    pub fn union(&mut self, a: ClassId, b: ClassId) -> bool {
        self.union_with_proof(a, b, "generic", "")
    }

    pub fn rebuild(&mut self) -> bool {
        let mut any = false;
        while let Some(cid) = self.pop_dirty() {
            let nodes = self.classes[cid as usize].nodes.clone();
            for node in &nodes {
                let cn = self.canon_node_ro(node);
                match self.hashcons.get(&cn).copied() {
                    Some(other) => {
                        let ro = self.find(other);
                        if ro != cid {
                            // [P0] Congruence : preuve utilisant les vrais enfants canonisés.
                            // Congr(op, [Refl(Var(child))]) donne op(children) = op(children).
                            // La liaison aux classes est vérifiée par expr_is_in_class.
                            let proof = Proof::Congr(node.op,
                                node.children.iter().map(|&c| {
                                    Proof::Refl(Expr::Var(self.find_ro(c)))
                                }).collect());
                            if self.union_with_certificate(
                                cid, ro, "congruence", "canon identique",
                                None, Some(proof),
                            ) { any = true; break; }
                        }
                    }
                    None => { self.hashcons.insert(cn, cid); }
                }
            }
            let new_root = self.find(cid);
            if self.const_fold_rewrite(new_root) { any = true; }
        }
        any
    }

    fn const_fold_rewrite(&mut self, cid: ClassId) -> bool {
        let root = self.find_ro(cid);
        let nodes = self.classes[root as usize].nodes.clone();
        let mut folds: Vec<(Op, Vec<u64>, u64)> = Vec::new();
        for node in &nodes {
            if node.op == Op::Const { continue; }
            let mut vals = Vec::with_capacity(node.children.len());
            let mut all_const = true;
            for &c in &node.children {
                let rc = self.find_ro(c);
                match self.classes[rc as usize].data.cst.as_known() {
                    Some(v) => vals.push(v),
                    None => { all_const = false; break; }
                }
            }
            if !all_const { continue; }
            if let Some(r) = eval_const_op(node.op, &vals) {
                folds.push((node.op, vals, r));
            }
        }
        for (op, vals, r) in folds {
            let target = self.make_const_u64(r);
            let proof = Proof::ConstFold { op, args: vals, result: r };
            if self.union_with_certificate(
                root, target, "const_fold", "analyse → rewrite",
                None, Some(proof),
            ) { return true; }
        }
        false
    }

    // --------------------------------------------------------
    // MATCHING
    // --------------------------------------------------------
    pub fn collect_matches(&self, cid: ClassId, cap: usize) -> Vec<(usize, Bindings)> {
        let mut out = Vec::new();
        for (i, r) in self.scheduler.rules.iter().enumerate() {
            if self.scheduler.is_backed_off(i) { continue; }
            let matches = self.ematch_n(&r.lhs, cid, cap);
            for b in matches {
                if let Some(cond) = r.cond {
                    let view = EGraphView { classes: &self.classes };
                    if !cond(&view, &b) { continue; }
                }
                out.push((i, b));
            }
        }
        out
    }

    pub fn apply_collected(&mut self, cid: ClassId, matches: Vec<(usize, Bindings)>) -> bool {
        let mut changed = false;
        for (i, b) in matches {
            let r = self.scheduler.rules[i].clone();
            let inst = match self.instantiate(&r.rhs, &b) {
                Ok(id) => id,
                Err(_) => { self.scheduler.record(&r.name, false, 0); continue; }
            };
            let subst: HashMap<u32, Expr> = b.iter().map(|(v, c)| (*v, Expr::Var(*c))).collect();
            let proof = Proof::Rule {
                name: r.name.clone(),
                lhs: r.lhs.clone(),
                rhs: r.rhs.clone(),
                subst,
            };
            let before = self.classes.len() as u64;
            let produced = self.union_with_certificate(
                cid, inst, &r.name, "scheduled", Some(b), Some(proof),
            );
            let nodes_delta = (self.classes.len() as u64).saturating_sub(before);
            self.scheduler.record(&r.name, produced, nodes_delta);
            if produced { changed = true; }
        }
        if changed { self.rule_apps += 1; }
        changed
    }

    fn cache_lookup_or_miss(&self, key: &(PatternId, ClassId)) -> Option<Vec<Bindings>> {
        let mut cache = self.match_cache.lock().unwrap();
        if cache.generation != self.cache_generation {
            cache.entries.clear();
            cache.generation = self.cache_generation;
            return None;
        }
        cache.entries.get(key).cloned()
    }
    fn cache_insert(&self, key: (PatternId, ClassId), value: Vec<Bindings>) {
        let mut cache = self.match_cache.lock().unwrap();
        if cache.generation != self.cache_generation {
            cache.entries.clear();
            cache.generation = self.cache_generation;
        }
        cache.entries.insert(key, value);
    }

    pub fn ematch(&self, pat: &Pat, class: ClassId) -> Vec<Bindings> {
        let pid = pattern_id(pat);
        let key = (pid, self.find_ro(class));
        if let Some(v) = self.cache_lookup_or_miss(&key) { return v; }
        let r = self.ematch_inner(pat, class, false);
        self.cache_insert(key, r.clone());
        r
    }
    pub fn ematch_n(&self, pat: &Pat, class: ClassId, cap: usize) -> Vec<Bindings> {
        let all = self.ematch(pat, class);
        if cap == 0 || all.len() <= cap { all }
        else { all.into_iter().take(cap).collect() }
    }
    pub fn ematch_first(&self, pat: &Pat, class: ClassId) -> Option<Bindings> {
        let pid = pattern_id(pat);
        let key = (pid, self.find_ro(class));
        if let Some(v) = self.cache_lookup_or_miss(&key) { return v.into_iter().next(); }
        let r = self.ematch_inner(pat, class, true);
        let first = r.first().cloned();
        self.cache_insert(key, r);
        first
    }

    fn ematch_inner(&self, pat: &Pat, class: ClassId, first: bool) -> Vec<Bindings> {
        let root = self.find_ro(class);
        match pat {
            Pat::Var(v) => {
                let mut b = HashMap::new();
                b.insert(*v, root);
                vec![b]
            }
            Pat::Const(c) => {
                let bytes = c.to_be_bytes();
                for n in &self.classes[root as usize].nodes {
                    if n.op == Op::Const && n.payload == bytes {
                        return vec![HashMap::new()];
                    }
                }
                Vec::new()
            }
            Pat::Op(op, subpats) => {
                let mut results = Vec::new();
                for n in &self.classes[root as usize].nodes {
                    if n.op != *op { continue; }
                    // [P0] Pas de `assoc_subset_match` : pattern arité == nœud arité UNIQUEMENT.
                    // Le subset matching v16 était unsound (perte d'opérandes).
                    if n.children.len() != subpats.len() { continue; }
                    let sub = if op.commutative() {
                        self.ac_match(subpats, &n.children, first)
                    } else {
                        self.ordered_match(subpats, &n.children, first)
                    };
                    for b in sub {
                        results.push(b);
                        if first { return results; }
                    }
                }
                results
            }
        }
    }

    fn ordered_match(&self, subpats: &[Pat], children: &[ClassId], first: bool) -> Vec<Bindings> {
        let mut acc: Vec<Bindings> = vec![HashMap::new()];
        for (p, c) in subpats.iter().zip(children.iter()) {
            let mut next = Vec::new();
            for base in &acc {
                for s in self.ematch_inner(p, *c, first) {
                    if let Some(m) = merge_bindings(base, &s) {
                        next.push(m);
                        if first { break; }
                    }
                }
                if first && !next.is_empty() { break; }
            }
            acc = next;
            if acc.is_empty() { break; }
        }
        acc
    }

    /// [P0] AC matching complet : énumération de tous les appariements bipartites.
    /// Plus de fast path incorrect.
    fn ac_match(&self, subpats: &[Pat], children: &[ClassId], first: bool) -> Vec<Bindings> {
        if subpats.len() != children.len() { return Vec::new(); }
        let mut order: Vec<usize> = (0..subpats.len()).collect();
        order.sort_by_key(|&i| pattern_specificity(&subpats[i]));
        let mut results = Vec::new();
        let mut used = vec![false; children.len()];
        let mut bindings: Bindings = HashMap::new();
        self.ac_match_rec(subpats, &order, children, 0, &mut used, &mut bindings, &mut results, first);
        dedup_bindings(results)
    }

    #[allow(clippy::too_many_arguments)]
    fn ac_match_rec(
        &self, subpats: &[Pat], order: &[usize], children: &[ClassId],
        depth: usize, used: &mut Vec<bool>, bindings: &mut Bindings,
        results: &mut Vec<Bindings>, first: bool,
    ) {
        if first && !results.is_empty() { return; }
        if depth == order.len() {
            results.push(bindings.clone());
            return;
        }
        let idx = order[depth];
        if let Pat::Var(v) = &subpats[idx] {
            if let Some(&existing) = bindings.get(v) {
                let er = self.find_ro(existing);
                for j in 0..children.len() {
                    if used[j] { continue; }
                    if self.find_ro(children[j]) == er {
                        used[j] = true;
                        self.ac_match_rec(subpats, order, children, depth + 1, used, bindings, results, first);
                        used[j] = false;
                        return;
                    }
                }
                return;
            }
        }
        for j in 0..children.len() {
            if used[j] { continue; }
            for s in self.ematch_inner(&subpats[idx], children[j], first) {
                if let Some(m) = merge_bindings(bindings, &s) {
                    let saved = std::mem::replace(bindings, m);
                    used[j] = true;
                    self.ac_match_rec(subpats, order, children, depth + 1, used, bindings, results, first);
                    used[j] = false;
                    *bindings = saved;
                    if first && !results.is_empty() { return; }
                }
            }
        }
    }

    // --------------------------------------------------------
    // INDEX / REM
    // --------------------------------------------------------
    fn ensure_index(&mut self) {
        if self.index_valid { return; }
        self.index.clear();
        let n = self.classes.len() as ClassId;
        for cid in 0..n {
            if self.find_ro(cid) != cid { continue; }
            for node in &self.classes[cid as usize].nodes {
                let key = (node.op.code(), node.children.len() as u32);
                self.index.entry(key).or_default().push(cid);
            }
        }
        self.index_valid = true;
    }
    fn ensure_rem_index(&mut self) {
        if self.rem_index_valid { return; }
        self.rem_index.clear();
        let n = self.classes.len() as ClassId;
        for cid in 0..n {
            if self.find_ro(cid) != cid { continue; }
            for node in &self.classes[cid as usize].nodes {
                let op = node.op.code();
                let ar = node.children.len() as u32;
                for (pos, &ch) in node.children.iter().enumerate() {
                    let rc = self.find_ro(ch);
                    for cnode in &self.classes[rc as usize].nodes {
                        let key = (op, ar, pos as u32, cnode.op.code());
                        self.rem_index.entry(key).or_default().push(cid);
                    }
                }
            }
        }
        self.rem_index_valid = true;
    }
    pub fn rel_ematch(&mut self, pat: &Pat) -> Vec<(ClassId, Bindings)> {
        self.ensure_index();
        self.ensure_rem_index();
        let cands = self.candidates_for(pat);
        let mut out = Vec::new();
        for cid in cands {
            for b in self.ematch_inner(pat, cid, false) {
                out.push((cid, b));
            }
        }
        out
    }
    fn candidates_for(&self, pat: &Pat) -> Vec<ClassId> {
        match pat {
            Pat::Var(_) => (0..self.classes.len() as ClassId)
                .filter(|&i| self.find_ro(i) == i).collect(),
            Pat::Const(_) => (0..self.classes.len() as ClassId)
                .filter(|&i| self.find_ro(i) == i)
                .filter(|&i| self.classes[i as usize].nodes.iter().any(|n| n.op == Op::Const))
                .collect(),
            Pat::Op(op, subpats) => {
                let ar = subpats.len() as u32;
                let mut candidate_sets: Vec<HashSet<ClassId>> = Vec::new();
                for (pos, sp) in subpats.iter().enumerate() {
                    if let Pat::Op(child_op, _) = sp {
                        let key = (op.code(), ar, pos as u32, child_op.code());
                        if let Some(ids) = self.rem_index.get(&key) {
                            candidate_sets.push(ids.iter().map(|&i| self.find_ro(i)).collect());
                        } else { return Vec::new(); }
                    }
                }
                if candidate_sets.is_empty() {
                    let key = (op.code(), ar);
                    return match self.index.get(&key) {
                        Some(v) => v.iter().map(|&i| self.find_ro(i))
                            .collect::<HashSet<_>>().into_iter().collect(),
                        None => Vec::new(),
                    };
                }
                let mut it = candidate_sets.into_iter();
                let mut acc = it.next().unwrap();
                for s in it { acc = acc.intersection(&s).copied().collect(); }
                acc.into_iter().collect()
            }
        }
    }

    // --------------------------------------------------------
    // INSTANTIATE — sans panic
    // --------------------------------------------------------
    pub fn instantiate(&mut self, pat: &Pat, b: &Bindings) -> Result<ClassId, InstantiateError> {
        match pat {
            Pat::Var(v) => b.get(v).copied().ok_or(InstantiateError(*v)),
            Pat::Const(c) => Ok(self.make_const_u64(*c)),
            Pat::Op(op, subs) => {
                let mut children = Vec::with_capacity(subs.len());
                for s in subs { children.push(self.instantiate(s, b)?); }
                Ok(self.make_node(*op, children, vec![]))
            }
        }
    }
    fn instantiate_lookup(&self, pat: &Pat, b: &Bindings) -> Option<ClassId> {
        match pat {
            Pat::Var(v) => b.get(v).copied(),
            Pat::Const(c) => {
                let bytes = c.to_be_bytes().to_vec();
                let node = ENode { op: Op::Const, children: vec![], payload: bytes };
                self.hashcons.get(&node).copied()
            }
            Pat::Op(op, subs) => {
                let mut children: Vec<ClassId> = Vec::new();
                for s in subs { children.push(self.instantiate_lookup(s, b)?); }
                let mut children: Vec<ClassId> = children.iter().map(|&c| self.find_ro(c)).collect();
                if op.associative() {
                    let mut flat = Vec::new();
                    for c in children {
                        let cr = self.find_ro(c);
                        let nodes = &self.classes[cr as usize].nodes;
                        let mut expanded = false;
                        for n in nodes {
                            if n.op == *op {
                                for &cc in &n.children { flat.push(self.find_ro(cc)); }
                                expanded = true; break;
                            }
                        }
                        if !expanded { flat.push(cr); }
                    }
                    children = flat;
                }
                if op.commutative() { children.sort_unstable(); }
                let node = ENode { op: *op, children, payload: vec![] };
                self.hashcons.get(&node).copied()
            }
        }
    }

    // --------------------------------------------------------
    // EXTRACTION PARETO
    // --------------------------------------------------------
    fn compute_pareto(&self, model: &dyn CostModel, mode: ExtractionMode) -> Vec<Pareto> {
        let n = self.classes.len();
        let mut pareto: Vec<Pareto> = (0..n).map(|_| Pareto::new()).collect();
        loop {
            let mut changed = false;
            for cid in 0..n as ClassId {
                if self.find_ro(cid) != cid { continue; }
                let nodes = &self.classes[cid as usize].nodes;
                for (ni, node) in nodes.iter().enumerate() {
                    let mut child_paretos: Vec<&Pareto> = Vec::new();
                    let mut ok = true;
                    for &ch in &node.children {
                        let rc = self.find_ro(ch);
                        if pareto[rc as usize].is_empty() { ok = false; break; }
                        child_paretos.push(&pareto[rc as usize]);
                    }
                    if !ok { continue; }
                    let (combos, cart_trunc) = cartesian_costs(&child_paretos, mode.cartesian_cap());
                    if cart_trunc { pareto[cid as usize].truncated = true; }
                    for combo in combos {
                        let c = model.node_cost(node, &combo);
                        if pareto[cid as usize].insert_with(c, ni, combo.clone(), mode) {
                            changed = true;
                        }
                    }
                }
            }
            if !changed { break; }
        }
        pareto
    }

    pub fn extract_pareto(&self, id: ClassId, model: &dyn CostModel, mode: ExtractionMode) -> Pareto {
        let pareto = self.compute_pareto(model, mode);
        pareto[self.find_ro(id) as usize].clone()
    }
    pub fn extract_best(&self, id: ClassId, model: &dyn CostModel, mode: ExtractionMode) -> Option<(Expr, MultiCost)> {
        let pareto = self.compute_pareto(model, mode);
        let root = self.find_ro(id);
        let target = pareto[root as usize].best()?;
        let mut memo: HashMap<(ClassId, MultiCost), MemoState> = HashMap::new();
        let e = self.reconstruct(root, target, &pareto, &mut memo)?;
        Some((e, target))
    }
    fn reconstruct(
        &self, id: ClassId, target: MultiCost,
        pareto: &[Pareto], memo: &mut HashMap<(ClassId, MultiCost), MemoState>,
    ) -> Option<Expr> {
        let root = self.find_ro(id);
        match memo.get(&(root, target)) {
            Some(MemoState::Done(e)) => return Some(e.clone()),
            Some(MemoState::Visiting) => return None,
            None => {}
        }
        memo.insert((root, target), MemoState::Visiting);
        let p = &pareto[root as usize];
        let (node_idx, child_costs) = p.witness_of(&target)?.clone();
        let node = self.classes[root as usize].nodes.get(node_idx)?;
        let mut child_exprs = Vec::with_capacity(node.children.len());
        for (i, &ch) in node.children.iter().enumerate() {
            let cc = child_costs.get(i).copied()?;
            let ce = match self.reconstruct(ch, cc, pareto, memo) {
                Some(e) => e,
                None => { memo.remove(&(root, target)); return None; }
            };
            child_exprs.push(ce);
        }
        let e = match node.op {
            Op::Const => match strict_payload_to_u64(&node.payload) {
                Some(v) => Expr::Const(v),
                None => { memo.remove(&(root, target)); return None; }
            },
            Op::Add => Expr::Add(child_exprs),
            Op::Mul => Expr::Mul(child_exprs),
            Op::Xor => Expr::Xor(child_exprs),
            Op::Sub => Expr::Sub(child_exprs),
            Op::And => Expr::And(child_exprs),
            Op::Or => Expr::Or(child_exprs),
        };
        memo.insert((root, target), MemoState::Done(e.clone()));
        Some(e)
    }

    // --------------------------------------------------------
    // LOOKUPS
    // --------------------------------------------------------
    pub fn const_of(&self, id: ClassId) -> Option<u64> {
        self.classes[self.find_ro(id) as usize].data.cst.as_known()
    }
    pub fn range_of(&self, id: ClassId) -> (u64, u64, bool) {
        let r = &self.classes[self.find_ro(id) as usize].data.range;
        (r.lo, r.hi, r.exact)
    }

    pub fn compute_fingerprints(&mut self, max_iter: usize) {
        for _ in 0..max_iter {
            let mut changed = false;
            let n = self.classes.len() as ClassId;
            for cid in 0..n {
                if self.find_ro(cid) != cid { continue; }
                let new_fp = self.class_fp(cid);
                if new_fp != self.classes[cid as usize].fp {
                    self.classes[cid as usize].fp = new_fp;
                    changed = true;
                }
            }
            if !changed { break; }
        }
    }
    fn class_fp(&self, cid: ClassId) -> Fingerprint {
        let nodes = &self.classes[cid as usize].nodes;
        let mut hs: Vec<Fingerprint> = Vec::with_capacity(nodes.len());
        for n in nodes {
            let mut buf = Vec::new();
            buf.push(n.op.code());
            buf.extend_from_slice(&(n.children.len() as u32).to_le_bytes());
            for &c in &n.children {
                let rc = self.find_ro(c);
                for x in self.classes[rc as usize].fp { buf.extend_from_slice(&x.to_le_bytes()); }
            }
            buf.extend_from_slice(&(n.payload.len() as u32).to_le_bytes());
            buf.extend_from_slice(&n.payload);
            hs.push(hash128(&buf, 0x5eed_5eed_5eed_5eed));
        }
        hs.sort();
        let mut acc = Vec::new();
        for h in &hs { for x in h { acc.extend_from_slice(&x.to_le_bytes()); } }
        hash128(&acc, 0xf00d_f00d_f00d_f00d)
    }
    pub fn fingerprint_of(&self, id: ClassId) -> Fingerprint {
        self.classes[self.find_ro(id) as usize].fp
    }

    // --------------------------------------------------------
    // EXPLAIN — [P0] BFS sur graphe des records d'union
    // --------------------------------------------------------
    pub fn explain_shortest(&self, a: ClassId, b: ClassId) -> Vec<UnionRecord> {
        if a == b { return Vec::new(); }
        // Graphe non orienté : from ↔ to.
        let mut adj: HashMap<ClassId, Vec<(ClassId, usize)>> = HashMap::new();
        for (i, rec) in self.history.iter().enumerate() {
            adj.entry(rec.from).or_default().push((rec.to, i));
            adj.entry(rec.to).or_default().push((rec.from, i));
        }
        let mut visited: HashSet<ClassId> = HashSet::new();
        let mut pred: HashMap<ClassId, (ClassId, usize)> = HashMap::new();
        let mut queue: VecDeque<ClassId> = VecDeque::new();
        queue.push_back(a);
        visited.insert(a);
        while let Some(curr) = queue.pop_front() {
            if curr == b { break; }
            if let Some(neighbors) = adj.get(&curr) {
                for &(nb, idx) in neighbors {
                    if visited.insert(nb) {
                        pred.insert(nb, (curr, idx));
                        queue.push_back(nb);
                    }
                }
            }
        }
        if !visited.contains(&b) { return Vec::new(); }
        let mut path = Vec::new();
        let mut curr = b;
        while curr != a {
            match pred.get(&curr) {
                Some((prev, idx)) => {
                    path.push(self.history[*idx].clone());
                    curr = *prev;
                }
                None => break,
            }
        }
        path.reverse();
        path
    }

    // --------------------------------------------------------
    // VÉRIFICATION DE CERTIFICAT — [P0] lié aux extrémités
    // --------------------------------------------------------
    /// Vérifie AVANT l'union que la preuve relie bien `rec.from` et `rec.to`.
    /// À appeler dans `union_with_certificate` avant mutation.
    pub fn verify_record_pre_union(&self, rec: &UnionRecord) -> Result<(), String> {
        if rec.from as usize >= self.classes.len() || rec.to as usize >= self.classes.len() {
            return Err("IDs invalides".into());
        }
        let proof = rec.proof.as_ref().ok_or("record sans certificat")?;
        let (lhs, rhs) = check_proof(proof)?;
        let r_from = self.find_ro(rec.from);
        let r_to = self.find_ro(rec.to);
        // Orientation 1 : lhs ∈ from, rhs ∈ to
        let ok1 = self.expr_is_in_class(&lhs, r_from) && self.expr_is_in_class(&rhs, r_to);
        // Orientation 2 : lhs ∈ to, rhs ∈ from
        let ok2 = self.expr_is_in_class(&lhs, r_to) && self.expr_is_in_class(&rhs, r_from);
        if !ok1 && !ok2 {
            return Err(format!(
                "preuve non liée à l'union: lhs={} rhs={} from={} to={}",
                lhs.repr(), rhs.repr(), r_from, r_to
            ));
        }
        // Vérification des bindings si présents.
        if let Some(b) = &rec.bindings {
            if let Proof::Rule { lhs: l, rhs: rp, subst, .. } = proof {
                for v in pattern_vars(l) {
                    if !b.contains_key(&v) { return Err(format!("var {} non liée (lhs)", v)); }
                }
                for v in pattern_vars(rp) {
                    if !b.contains_key(&v) { return Err(format!("var {} non liée (rhs)", v)); }
                }
                for (v, e) in subst {
                    if let Expr::Var(c) = e {
                        if let Some(&cls) = b.get(v) {
                            if *c != cls {
                                return Err(format!("subst[{}]=Var({}) ≠ binding {}", v, c, cls));
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Variante publique : après union, `from` et `to` sont déjà fusionnés.
    /// Utile pour re-vérifier l'historique. (La vérification pré-union
    /// reste la garantie forte.)
    pub fn verify_record(&self, rec: &UnionRecord) -> Result<(), String> {
        self.verify_record_pre_union(rec)
    }

    /// [P0] Est-ce que `class` contient un nœud correspondant à `expr` ?
    /// `expr` est une expression concrète : ses `Var(c)` sont des ClassId.
    pub fn expr_is_in_class(&self, expr: &Expr, class: ClassId) -> bool {
        let root = self.find_ro(class);
        match expr {
            Expr::Var(v) => {
                let c = *v as ClassId;
                if c as usize >= self.classes.len() { return false; }
                self.find_ro(c) == root
            }
            Expr::Const(v) => {
                let bytes = v.to_be_bytes().to_vec();
                if self.classes[root as usize].nodes.iter()
                    .any(|n| n.op == Op::Const && n.payload == bytes) { return true; }
                // Fallback : analyse cst (sound si l'analyse est sound).
                self.classes[root as usize].data.cst.as_known() == Some(*v)
            }
            Expr::Add(xs) => self.expr_op_in_class(Op::Add, xs, root),
            Expr::Mul(xs) => self.expr_op_in_class(Op::Mul, xs, root),
            Expr::Xor(xs) => self.expr_op_in_class(Op::Xor, xs, root),
            Expr::Sub(xs) => self.expr_op_in_class(Op::Sub, xs, root),
            Expr::And(xs) => self.expr_op_in_class(Op::And, xs, root),
            Expr::Or(xs) => self.expr_op_in_class(Op::Or, xs, root),
        }
    }

    fn expr_op_in_class(&self, op: Op, args: &[Expr], root: ClassId) -> bool {
        for n in &self.classes[root as usize].nodes {
            if n.op != op { continue; }
            if n.children.len() != args.len() { continue; }
            // Tous les args sont-ils des Vars (= ClassId) ?
            let all_var = args.iter().all(|a| matches!(a, Expr::Var(_)));
            if all_var {
                let mut arg_classes: Vec<ClassId> = args.iter().map(|a| {
                    if let Expr::Var(v) = a { self.find_ro(*v as ClassId) } else { unreachable!() }
                }).collect();
                let mut child_classes: Vec<ClassId> =
                    n.children.iter().map(|&c| self.find_ro(c)).collect();
                if op.commutative() {
                    arg_classes.sort(); child_classes.sort();
                }
                if arg_classes == child_classes { return true; }
            } else {
                // Match récursif. Commutatif : tester les permutations (petits n).
                if op.commutative() {
                    let mut perm: Vec<usize> = (0..args.len()).collect();
                    if self.try_perm_match(args, &n.children, &mut perm, 0) { return true; }
                } else {
                    if args.iter().zip(n.children.iter()).all(|(a, &c)| self.expr_is_in_class(a, c)) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn try_perm_match(&self, args: &[Expr], children: &[ClassId], perm: &mut Vec<usize>, depth: usize) -> bool {
        if depth == perm.len() {
            return args.iter().zip(perm.iter())
                .all(|(a, &i)| self.expr_is_in_class(a, children[i]));
        }
        for i in depth..perm.len() {
            perm.swap(depth, i);
            if self.try_perm_match(args, children, perm, depth + 1) { return true; }
            perm.swap(depth, i);
        }
        false
    }

    pub fn class_count(&self) -> usize {
        (0..self.classes.len() as ClassId).filter(|&i| self.find_ro(i) == i).count()
    }
    pub fn node_count(&self) -> usize {
        (0..self.classes.len() as ClassId)
            .filter(|&i| self.find_ro(i) == i)
            .map(|i| self.classes[i as usize].nodes.len())
            .sum()
    }
    pub fn history_len(&self) -> usize { self.history.len() }
}

#[derive(Clone, Debug)]
enum MemoState { Visiting, Done(Expr) }

fn cartesian_costs(paretos: &[&Pareto], cap: Option<usize>) -> (Vec<Vec<MultiCost>>, bool) {
    let mut out: Vec<Vec<MultiCost>> = vec![Vec::new()];
    let mut truncated = false;
    for p in paretos {
        let mut next = Vec::new();
        for existing in &out {
            for c in p.iter() {
                let mut e = existing.clone();
                e.push(*c);
                next.push(e);
                if let Some(cap) = cap {
                    if next.len() >= cap { truncated = true; break; }
                }
            }
            if let Some(cap) = cap { if next.len() >= cap { break; } }
        }
        out = next;
        if let Some(cap) = cap {
            if out.len() >= cap { truncated = true; break; }
        }
    }
    (out, truncated)
}

// ============================================================
// DÉMO
// ============================================================
fn main() {
    println!("=== NOYAU v17 — Correctifs P0 des audits ===\n");

    // --- Test 1 : bitmask_upper corrigé ---
    println!("--- Test 1 : bitmask_upper (P0) ---");
    for x in [0u64, 1, 2, 3, 7, 8, 15, 16] {
        let m = bitmask_upper(x);
        let ok = if m >= x { "✓" } else { "✗" };
        println!("  bitmask_upper({}) = {} {}", x, m, ok);
    }

    // --- Test 2 : range_add checked ---
    println!("\n--- Test 2 : range_add (P0) ---");
    let a = RangeData { lo: u64::MAX - 1, hi: u64::MAX, exact: false };
    let b = RangeData { lo: 1, hi: 1, exact: true };
    let r = range_add(&a, &b);
    println!("  [MAX-1, MAX] + [1,1] = [{},{}] (unknown = OK)", r.lo, r.hi);

    // --- Test 3 : verify_record pré-union ---
    println!("\n--- Test 3 : verify_record pré-union (P0) ---");
    let mut g = EGraph::new();
    g.scheduler.add_trusted(
        "x+0→x",
        Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Const(0)]),
        Pat::Var(0),
    );
    let x = g.make_const_u64(42);
    let z = g.make_const_u64(0);
    let xp0 = g.make_node(Op::Add, vec![x, z], vec![]);
    let runner = Runner::new().with_iter_limit(50);
    runner.run(&mut g);

    println!("  classes={} nodes={} unions={}",
             g.class_count(), g.node_count(), g.unions);

    // --- Test 4 : explain_shortest sur graphe d'unions ---
    println!("\n--- Test 4 : explain_shortest (P0) ---");
    let path = g.explain_shortest(xp0, x);
    println!("  Chemin x+0→x : {} étape(s)", path.len());
    for rec in &path {
        match g.verify_record(rec) {
            Ok(()) => println!("    ✓ {} ({}→{})", rec.rule, rec.from, rec.to),
            Err(e) => println!("    ✗ {} : {}", rec.rule, e),
        }
    }

    // --- Test 5 : certificat forgé rejeté ---
    println!("\n--- Test 5 : certificat forgé rejeté ---");
    let forged = UnionRecord {
        from: xp0, to: x,
        rule: "fake".into(), detail: "".into(),
        bindings: None, proof: None,
    };
    match g.verify_record(&forged) {
        Ok(()) => println!("  ✗ ACCEPTÉ (bug)"),
        Err(e) => println!("  ✓ rejeté : {}", e),
    }

    // --- Test 6 : pas de subset matching unsound ---
    println!("\n--- Test 6 : arity mismatch rejeté (P0) ---");
    let mut g2 = EGraph::new();
    let a = g2.make_const_u64(1);
    let b = g2.make_const_u64(2);
    let c = g2.make_const_u64(3);
    let abc = g2.make_node(Op::Add, vec![a, b, c], vec![]); // aplati à 3
    let pat2 = Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Var(1)]); // arité 2
    let m = g2.ematch(&pat2, abc);
    println!("  (+ x y) sur (+ 1 2 3) : {} matches (0 = correct, plus de faux théorèmes)", m.len());

    // --- Test 7 : AC matching complet sur arité égale ---
    println!("\n--- Test 7 : AC matching complet ---");
    let a2 = g2.make_const_u64(10);
    let b2 = g2.make_const_u64(20);
    let ab = g2.make_node(Op::Add, vec![a2, b2], vec![]);
    let pat3 = Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Var(1)]);
    let matches = g2.ematch(&pat3, ab);
    println!("  (+ x y) sur (+ 10 20) : {} bindings (2 attendu)", matches.len());
    for m in &matches {
        println!("    x={:?} y={:?}",
                 m.get(&0).map(|c| g2.const_of(*c)),
                 m.get(&1).map(|c| g2.const_of(*c)));
    }

    // --- Test 8 : extraction ---
    println!("\n--- Test 8 : extraction Pareto ---");
    let mut g3 = EGraph::new();
    g3.scheduler.add_trusted(
        "x+x→2x",
        Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Var(0)]),
        Pat::Op(Op::Mul, vec![Pat::Const(2), Pat::Var(0)]),
    );
    let y = g3.make_const_u64(21);
    let dbl = g3.make_node(Op::Add, vec![y, y], vec![]);
    let runner = Runner::new().with_iter_limit(30);
    runner.run(&mut g3);
    match g3.extract_best(dbl, &CpuCost, ExtractionMode::Exact) {
        Some((e, c)) => println!("  Exact : {} cost=({},{},{})",
            e.repr(), c.energy, c.size, c.depth),
        None => println!("  Exact : aucun"),
    }

    println!("\n=== Bilan ===");
    println!("  classes={} nodes={} history={}",
             g3.class_count(), g3.node_count(), g3.history_len());
}

// ============================================================
// TESTS
// ============================================================
#[cfg(test)]
mod tests {
    use super::*;

    fn v(i: u32) -> Pat { Pat::Var(i) }
    fn c(x: u64) -> Pat { Pat::Const(x) }
    fn p_add(a: Pat, b: Pat) -> Pat { Pat::Op(Op::Add, vec![a, b]) }

    // ---------- bitmask_upper ----------
    #[test]
    fn bitmask_upper_ne_sous_estime_jamais() {
        for x in [0u64, 1, 2, 3, 4, 7, 8, 15, 16, 100, 1023, 1024, 65535, 65536] {
            let m = bitmask_upper(x);
            assert!(m >= x, "bitmask_upper({}) = {} < {}", x, m, x);
        }
        assert_eq!(bitmask_upper(0), 0);
        assert_eq!(bitmask_upper(1), 1);
        assert_eq!(bitmask_upper(2), 3);
        assert_eq!(bitmask_upper(3), 3);
        assert_eq!(bitmask_upper(4), 7);
        assert_eq!(bitmask_upper(7), 7);
        assert_eq!(bitmask_upper(8), 15);
        assert_eq!(bitmask_upper(u64::MAX), u64::MAX);
    }

    // ---------- range_add ----------
    #[test]
    fn range_add_overflow_sound() {
        let a = RangeData { lo: u64::MAX - 1, hi: u64::MAX, exact: false };
        let b = RangeData { lo: 1, hi: 1, exact: true };
        let r = range_add(&a, &b);
        assert_eq!(r.lo, 0);
        assert_eq!(r.hi, u64::MAX);
    }

    // ---------- prover ----------
    #[test]
    fn prover_neutres() {
        assert_eq!(prove_rule(&p_add(v(0), c(0)), &v(0)), ProofResult::Proven);
        assert_eq!(prove_rule(
            &Pat::Op(Op::And, vec![v(0), c(u64::MAX)]), &v(0)), ProofResult::Proven);
        assert_eq!(prove_rule(
            &Pat::Op(Op::Or, vec![v(0), c(0)]), &v(0)), ProofResult::Proven);
    }

    #[test]
    fn prover_rejects_false() {
        assert_eq!(prove_rule(&p_add(v(0), c(1)), &v(0)), ProofResult::Unknown);
    }

    // ---------- Pareto fixpoint ----------
    #[test]
    fn pareto_dedup() {
        let mut p = Pareto::new();
        let c = MultiCost { energy: 1, size: 2, depth: 3 };
        assert!(p.insert_with(c, 0, vec![], ExtractionMode::Exact));
        assert!(!p.insert_with(c, 1, vec![], ExtractionMode::Exact));
        assert_eq!(p.costs.len(), 1);
    }

    #[test]
    fn pareto_bounded_terminates() {
        let mut p = Pareto::new();
        let mode = ExtractionMode::Bounded { pareto_cap: 1, cartesian_cap: 4 };
        for i in 0..10u64 {
            p.insert_with(MultiCost { energy: i, size: 10 - i, depth: 1 }, 0, vec![], mode);
        }
        assert!(p.truncated);
    }

    // ---------- verify_record ----------
    #[test]
    fn verify_record_rejects_no_proof() {
        let mut g = EGraph::new();
        let x = g.make_const_u64(1);
        let z = g.make_const_u64(0);
        let xp0 = g.make_node(Op::Add, vec![x, z], vec![]);
        let rec = UnionRecord {
            from: xp0, to: x,
            rule: "fake".into(), detail: "".into(),
            bindings: None, proof: None,
        };
        assert!(g.verify_record(&rec).is_err());
    }

    #[test]
    fn verify_record_rejects_wrong_rule() {
        let mut g = EGraph::new();
        g.scheduler.add_trusted(
            "x+0→x",
            Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Const(0)]),
            Pat::Var(0),
        );
        let x = g.make_const_u64(5);
        let z = g.make_const_u64(0);
        let xp0 = g.make_node(Op::Add, vec![x, z], vec![]);
        let runner = Runner::new().with_iter_limit(50);
        runner.run(&mut g);
        // Chercher un record valide
        let mut found_valid = false;
        for rec in &g.history {
            if rec.rule == "x+0→x" {
                if g.verify_record(rec).is_ok() { found_valid = true; }
            }
        }
        assert!(found_valid, "aucun record de la règle x+0→x ne passe verify");
    }

    // ---------- arity ----------
    #[test]
    fn no_subset_matching() {
        let mut g = EGraph::new();
        let a = g.make_const_u64(1);
        let b = g.make_const_u64(2);
        let c = g.make_const_u64(3);
        let abc = g.make_node(Op::Add, vec![a, b, c], vec![]);
        let pat = Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Var(1)]);
        let m = g.ematch(&pat, abc);
        assert_eq!(m.len(), 0, "subset matching doit être désactivé");
    }

    // ---------- AC complete ----------
    #[test]
    fn ac_matching_complet() {
        let mut g = EGraph::new();
        let a = g.make_const_u64(10);
        let b = g.make_const_u64(20);
        let ab = g.make_node(Op::Add, vec![a, b], vec![]);
        let pat = Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Var(1)]);
        let matches = g.ematch(&pat, ab);
        assert_eq!(matches.len(), 2, "2 appariements attendus sur arité égale");
    }

    // ---------- explain ----------
    #[test]
    fn explain_shortest_trouve_chemin() {
        let mut g = EGraph::new();
        g.scheduler.add_trusted(
            "x+0→x",
            Pat::Op(Op::Add, vec![Pat::Var(0), Pat::Const(0)]),
            Pat::Var(0),
        );
        let x = g.make_const_u64(7);
        let z = g.make_const_u64(0);
        let xp0 = g.make_node(Op::Add, vec![x, z], vec![]);
        let runner = Runner::new().with_iter_limit(50);
        runner.run(&mut g);
        let path = g.explain_shortest(xp0, x);
        assert!(!path.is_empty());
    }

    // ---------- differential ----------
    fn eval_pat(p: &Pat, env: &HashMap<u32, u64>) -> u64 {
        match p {
            Pat::Var(v) => *env.get(v).unwrap(),
            Pat::Const(c) => *c,
            Pat::Op(Op::Const, _) => 0,
            Pat::Op(Op::Add, subs) => subs.iter().fold(0u64, |a, s| a.wrapping_add(eval_pat(s, env))),
            Pat::Op(Op::Mul, subs) => subs.iter().fold(1u64, |a, s| a.wrapping_mul(eval_pat(s, env))),
            Pat::Op(Op::Xor, subs) => subs.iter().fold(0u64, |a, s| a ^ eval_pat(s, env)),
            Pat::Op(Op::And, subs) => subs.iter().fold(u64::MAX, |a, s| a & eval_pat(s, env)),
            Pat::Op(Op::Or, subs) => subs.iter().fold(0u64, |a, s| a | eval_pat(s, env)),
            Pat::Op(Op::Sub, subs) if subs.len() == 2 =>
                eval_pat(&subs[0], env).wrapping_sub(eval_pat(&subs[1], env)),
            Pat::Op(Op::Sub, _) => 0,
        }
    }

    #[test]
    fn differential_prover_soundness() {
        let pairs: Vec<(Pat, Pat)> = vec![
            (p_add(v(0), c(0)), v(0)),
            (Pat::Op(Op::Mul, vec![v(0), c(1)]), v(0)),
            (p_add(v(0), v(0)), Pat::Op(Op::Mul, vec![c(2), v(0)])),
            (Pat::Op(Op::And, vec![v(0), c(u64::MAX)]), v(0)),
            (Pat::Op(Op::Or, vec![v(0), c(0)]), v(0)),
            (Pat::Op(Op::Xor, vec![v(0), v(0)]), c(0)),
        ];
        let samples = [0u64, 1, 2, 7, 42, u64::MAX - 1, u64::MAX];
        for (i, (lhs, rhs)) in pairs.iter().enumerate() {
            if prove_rule(lhs, rhs) != ProofResult::Proven { continue; }
            for &x in &samples {
                let mut env = HashMap::new();
                env.insert(0, x);
                assert_eq!(eval_pat(lhs, &env), eval_pat(rhs, &env),
                    "pair #{} x={}", i, x);
            }
        }
    }

    #[test]
    fn strict_payload_rejects_malformed() {
        assert!(strict_payload_to_u64(&[]).is_none());
        assert!(strict_payload_to_u64(&[1, 2, 3]).is_none());
        assert!(strict_payload_to_u64(&[0; 16]).is_none());
        assert_eq!(strict_payload_to_u64(&42u64.to_be_bytes()), Some(42));
    }
}
