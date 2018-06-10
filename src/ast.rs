use std::fmt;
#[cfg(feature="bigint")]
use num_bigint::BigUint;

#[cfg(feature="bigint")]
pub type IntegerType = BigUint;
#[cfg(not(feature="bigint"))]
pub type IntegerType = u64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgumentError {
    KeywordExpression,
    PositionalAfterKeyword,
    StarargsAfterKeyword,
}

impl ArgumentError {
    pub fn to_string(self) -> &'static str {
        match self {
            ArgumentError::KeywordExpression => "Keyword cannot be an expression.",
            ArgumentError::PositionalAfterKeyword => "Positional argument after keyword argument or **kwargs.",
            ArgumentError::StarargsAfterKeyword => "*args after keyword argument or **kwargs.",
        }
    }
}

impl From<u32> for ArgumentError {
    fn from(i: u32) -> ArgumentError {
        match i {
            1 => ArgumentError::KeywordExpression,
            2 => ArgumentError::PositionalAfterKeyword,
            3 => ArgumentError::StarargsAfterKeyword,
            _ => panic!("Invalid error code.")
        }
    }
}

impl From<ArgumentError> for u32 {
    fn from(e: ArgumentError) -> u32 {
        match e {
            ArgumentError::KeywordExpression => 1,
            ArgumentError::PositionalAfterKeyword => 2,
            ArgumentError::StarargsAfterKeyword => 3,
        }
    }
}

pub type Name = String;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StarParams<T> {
    /// No single star
    No,
    /// `*` alone, with no name
    Anonymous,
    /// *args` or `*args:type`
    Named(T),
}

impl<T> Default for StarParams<T> {
    fn default() -> StarParams<T> {
        StarParams::No
    }
}

#[derive(Clone, Debug, PartialEq, Default,)]
pub struct TypedArgsList {
    pub positional_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    pub star_args: StarParams<(Name, Option<Expression>)>,
    pub keyword_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    pub star_kwargs: Option<(Name, Option<Expression>)>,
}

#[derive(Clone, Debug, PartialEq, Default)]
pub struct UntypedArgsList {
    pub positional_args: Vec<(Name, Option<Expression>)>,
    pub star_args: StarParams<Name>,
    pub keyword_args: Vec<(Name, Option<Expression>)>,
    pub star_kwargs: Option<Name>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Decorator {
    pub name: Vec<Name>,
    pub args: Option<Arglist>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Argument<T> {
    Normal(T),
    Star(Expression),
}
#[derive(Clone, Debug, PartialEq, Default)]
pub struct Arglist {
    pub positional_args: Vec<Argument<Expression>>,
    pub keyword_args: Vec<Argument<(Name, Expression)>>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Subscript {
    Simple(Expression),
    Double(Option<Expression>, Option<Expression>),
    Triple(Option<Expression>, Option<Expression>, Option<Expression>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Uop {
    Plus,
    Minus,
    /// `~`
    Invert,
    Not,
}

impl fmt::Display for Uop {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", match self {
            Uop::Plus => "+",
            Uop::Minus => "-",
            Uop::Invert => "~",
            Uop::Not => "not ",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Bop {
    Add,
    Sub,
    Mult,
    Matmult,
    Mod,
    Floordiv,
    Div,
    Power,
    Lshift,
    Rshift,
    BitAnd,
    BitXor,
    BitOr,
    /// lower than
    Lt,
    /// greater than
    Gt,
    Eq,
    /// lower or equal
    Leq,
    /// greater or equal
    Geq,
    Neq,
    In,
    NotIn,
    Is,
    IsNot,
    And,
    Or,
}

impl fmt::Display for Bop {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", match self {
            Bop::Add => "+",
            Bop::Sub => "-",
            Bop::Mult => "*",
            Bop::Matmult => "]",
            Bop::Mod => "%",
            Bop::Floordiv => "//",
            Bop::Div => "/",
            Bop::Power => "**",
            Bop::Lshift => "<<",
            Bop::Rshift => ">>",
            Bop::BitAnd => "&",
            Bop::BitXor => "^",
            Bop::BitOr => "|",
            Bop::Lt => "<",
            Bop::Gt => ">",
            Bop::Eq => "==",
            Bop::Leq => "<=",
            Bop::Geq => ">=",
            Bop::Neq => "!=",
            Bop::In => " in ",
            Bop::NotIn => " not in ",
            Bop::Is => " is ",
            Bop::IsNot => " is not ",
            Bop::And => " and ",
            Bop::Or => " or ",
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum ComprehensionChunk {
    If { cond: Expression },
    For { async: bool, item: Vec<Expression>, iterator: Expression },
}

#[derive(Clone, Debug, PartialEq)]
pub enum DictItem {
    Star(Expression),
    Unique(Expression, Expression),
}

#[derive(Clone, Debug, PartialEq)]
pub enum SetItem {
    Star(Expression),
    Unique(Expression),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PyString {
    pub prefix: String,
    pub content: String,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Expression {
    Ellipsis,
    None,
    True,
    False,
    Name(Name),
    Int(IntegerType),
    ImaginaryInt(IntegerType),
    Float(f64),
    ImaginaryFloat(f64),
    String(Vec<PyString>),
    Bytes(Vec<u8>),
    DictLiteral(Vec<DictItem>),
    SetLiteral(Vec<SetItem>),
    ListLiteral(Vec<SetItem>),
    TupleLiteral(Vec<SetItem>),
    DictComp(Box<DictItem>, Vec<ComprehensionChunk>),
    SetComp(Box<SetItem>, Vec<ComprehensionChunk>),
    ListComp(Box<SetItem>, Vec<ComprehensionChunk>),
    Generator(Box<SetItem>, Vec<ComprehensionChunk>),

    Call(Box<Expression>, Arglist),
    Subscript(Box<Expression>, Vec<Subscript>),
    /// `foo.bar`
    Attribute(Box<Expression>, Name),
    /// Unary operator
    Uop(Uop, Box<Expression>),
    /// Binary operator. A simplified version of `MultiBop`, when the
    /// expressivity of MultiBop is not needed.
    Bop(Bop, Box<Expression>, Box<Expression>),
    /// Binary operator... but may be applied on more than one expr
    /// (eg. `a <= b < c`)
    MultiBop(Box<Expression>, Vec<(Bop, Expression)>),
    /// 1 if 2 else 3
    Ternary(Box<Expression>, Box<Expression>, Box<Expression>),
    Yield(Vec<Expression>),
    YieldFrom(Box<Expression>),
    Star(Box<Expression>),
    Lambdef(UntypedArgsList, Box<Expression>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Import {
    /// `from x import y`
    ImportFrom {
        /// For `from .....x import y`, this is 5
        leading_dots: usize,
        /// For `from .....x import y`, this `x`
        path: Vec<Name>,
        /// For `from x import y, z`, this `vec![(y, None), (vec![z], None)]`.
        /// For `from x import y as z`, this `vec![(y, Some(z))]`.
        /// For `from x import *`, this is `vec![]`.
        names: Vec<(Name, Option<Name>)>
    },
    /// `import x.y as z, foo.bar` is
    /// `Import::Import(vec![(vec![x, y], Some(z)), (vec![foo, bar], None)])`.
    Import { names: Vec<(Vec<Name>, Option<Name>)> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AugAssignOp {
    Add,
    Sub,
    Mult,
    MatMult,
    Div,
    Mod,
    BitAnd,
    BitOr,
    BitXor,
    Lshift,
    Rshift,
    Power,
    Floordiv,
}

impl fmt::Display for AugAssignOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", match self {
            AugAssignOp::Add => "+=",
            AugAssignOp::Sub => "-=",
            AugAssignOp::Mult => "*=",
            AugAssignOp::MatMult => "@=",
            AugAssignOp::Div => "/=",
            AugAssignOp::Mod => "%=",
            AugAssignOp::BitAnd => "&=",
            AugAssignOp::BitOr => "|=",
            AugAssignOp::BitXor => "^=",
            AugAssignOp::Lshift => "<<=",
            AugAssignOp::Rshift => ">>=",
            AugAssignOp::Power => "**=",
            AugAssignOp::Floordiv => "//=",
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Statement {
    Pass,
    Del(Vec<Expression>),
    Break,
    Continue,
    Return(Vec<Expression>),
    RaiseExcFrom(Expression, Expression),
    RaiseExc(Expression),
    Raise,
    Global(Vec<Name>),
    Nonlocal(Vec<Name>),
    Assert(Expression, Option<Expression>),
    Import(Import),
    Expressions(Vec<Expression>),
    // `lhs = rhs1 = rhs2` -> `lhs, vec![rhs1, rhs2]`
    Assignment(Vec<Expression>, Vec<Vec<Expression>>),
    // `lhs: type = rhs` -> `lhs, type, rhs`
    TypedAssignment(Vec<Expression>, Expression, Vec<Expression>),
    // `lhs += rhs` -> `lhs, AugAssignOp::Add, rhs`
    AugmentedAssignment(Vec<Expression>, AugAssignOp, Vec<Expression>),

    Compound(Box<CompoundStatement>),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Funcdef {
    pub async: bool,
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub parameters: TypedArgsList,
    pub return_type: Option<Expression>,
    pub code: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Classdef {
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub arguments: Arglist,
    pub code: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Try {
    pub try_block: Vec<Statement>,
    /// except `1 [as 2]: 3`
    pub except_clauses: Vec<(Expression, Option<Name>, Vec<Statement>)>,
    /// Empty iff no `except:` clause.
    pub last_except: Vec<Statement>,
    /// Empty iff no `else:` clause.
    pub else_block: Vec<Statement>,
    /// Empty iff no `finally:` clause.
    pub finally_block: Vec<Statement>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CompoundStatement {
    If(Vec<(Expression, Vec<Statement>)>, Option<Vec<Statement>>),
    For { async: bool, item: Vec<Expression>, iterator: Vec<Expression>, for_block: Vec<Statement>, else_block: Option<Vec<Statement>> },
    While(Expression, Vec<Statement>, Option<Vec<Statement>>),
    With(Vec<(Expression, Option<Expression>)>, Vec<Statement>),
    Funcdef(Funcdef),
    Classdef(Classdef),
    Try(Try),
}
