//! enums and structures that store the syntax tree outputed by the parser.

use std::fmt;

#[cfg(feature="bigint")]
use num_bigint::BigUint;

#[cfg(feature="wtf8")]
use wtf8;

#[cfg(feature="bigint")]
pub type IntegerType = BigUint;
#[cfg(not(feature="bigint"))]
pub type IntegerType = u64;

#[cfg(feature="wtf8")]
pub type PyStringContent = wtf8::Wtf8Buf;
#[cfg(feature="wtf8")]
pub type PyStringCodePoint = wtf8::CodePoint;

#[cfg(not(feature="wtf8"))]
pub type PyStringContent = String;
#[cfg(not(feature="wtf8"))]
pub type PyStringCodePoint = char;

pub type Name = String;

/// Represents whether a function signature has `*`, `*args`, or none of these.
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

/// The list of parameters of a function definition.
#[derive(Clone, Debug, PartialEq, Default,)]
pub struct TypedArgsList {
    pub positional_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    pub star_args: StarParams<(Name, Option<Expression>)>,
    pub keyword_args: Vec<(Name, Option<Expression>, Option<Expression>)>,
    pub star_kwargs: Option<(Name, Option<Expression>)>,
}

/// The list of parameters of a lambda definition.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct UntypedArgsList {
    pub positional_args: Vec<(Name, Option<Expression>)>,
    pub star_args: StarParams<Name>,
    pub keyword_args: Vec<(Name, Option<Expression>)>,
    pub star_kwargs: Option<Name>,
}

/// A function or class decorator.
#[derive(Clone, Debug, PartialEq)]
pub struct Decorator {
    pub name: Vec<Name>,
    pub args: Option<Vec<Argument>>,
}

/// An argument to a function call
#[derive(Clone, Debug, PartialEq)]
pub enum Argument {
    Positional(Expression),
    Starargs(Expression),
    Keyword(Name, Expression),
    Kwargs(Expression),
}

/// The `foo[bar]` syntax.
#[derive(Clone, Debug, PartialEq)]
pub enum Subscript {
    /// `foo[i]`
    Simple(Expression),
    /// `foo[start:end]`, `foo[start:]`, etc.
    Double(Option<Expression>, Option<Expression>),
    /// `foo[start:end:step]`, `foo[start::]`, etc.
    Triple(Option<Expression>, Option<Expression>, Option<Expression>),
}

/// Unary operators.
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
        write!(f, "{}", match *self {
            Uop::Plus => "+",
            Uop::Minus => "-",
            Uop::Invert => "~",
            Uop::Not => "not ",
        })
    }
}

/// Binary operators.
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
        write!(f, "{}", match *self {
            Bop::Add => "+",
            Bop::Sub => "-",
            Bop::Mult => "*",
            Bop::Matmult => "@",
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

/// One of the `if` or `for` clause(s) of a comprehension list/dict/set or
/// generator expression.
#[derive(Clone, Debug, PartialEq)]
pub enum ComprehensionChunk {
    If { cond: Expression },
    For { async: bool, item: Vec<Expression>, iterator: Expression },
}

/// `**foo` or `foo:bar`, as in a dict comprehension.
#[derive(Clone, Debug, PartialEq)]
pub enum DictItem {
    Star(Expression),
    Unique(Expression, Expression),
}

/// `*foo` or `foo`, as in a list/set comprehension or a generator expression.
#[derive(Clone, Debug, PartialEq)]
pub enum SetItem {
    Star(Expression),
    Unique(Expression),
}

/// A Python string. See the doc of the crate for the boring speech about
/// encoding stuff.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PyString {
    pub prefix: String,
    pub content: PyStringContent,
}

/// The big thing: a Python expression.
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
    Await(Box<Expression>),

    Call(Box<Expression>, Vec<Argument>),
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

/// An import statement.
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
        names: Vec<(Name, Option<Name>)>
    },
    /// For `from x import *`, this is `vec![]`.
    ImportStarFrom {
        leading_dots: usize,
        path: Vec<Name>,
    },
    /// `import x.y as z, foo.bar` is
    /// `Import::Import(vec![(vec![x, y], Some(z)), (vec![foo, bar], None)])`.
    Import { names: Vec<(Vec<Name>, Option<Name>)> },
}

/// `+=` and its friends.
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
        write!(f, "{}", match *self {
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

/// A Python statement.
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
    // `lhs: type` -> `lhs, type`
    TypeAnnotation(Vec<Expression>, Expression),
    // `lhs: type = rhs` -> `lhs, type, rhs`
    TypedAssignment(Vec<Expression>, Expression, Vec<Expression>),
    // `lhs += rhs` -> `lhs, AugAssignOp::Add, rhs`
    AugmentedAssignment(Vec<Expression>, AugAssignOp, Vec<Expression>),

    Compound(Box<CompoundStatement>),
}

/// A function definition, including its decorators.
#[derive(Clone, Debug, PartialEq)]
pub struct Funcdef {
    pub async: bool,
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub parameters: TypedArgsList,
    pub return_type: Option<Expression>,
    pub code: Vec<Statement>,
}

/// A class definition, including its decorators.
#[derive(Clone, Debug, PartialEq)]
pub struct Classdef {
    pub decorators: Vec<Decorator>,
    pub name: String,
    pub arguments: Vec<Argument>,
    pub code: Vec<Statement>,
}

/// A try block.
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

/// Statements with blocks.
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
