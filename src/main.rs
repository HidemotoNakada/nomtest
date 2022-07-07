use nom::{
  IResult,
  branch::alt,
  combinator::map,
  bytes::complete::{tag},
  sequence::tuple,
  character::complete::{digit1, space0}
};
use std::str::FromStr;

pub trait AST {
  fn eval(&self) -> f64;
}

impl AST for f64 {
  fn eval(&self) -> f64{ *self }
}

pub enum Operator {
  Add, Sub, Mul,Div
}

pub struct BinOp {
  pub op: Operator, 
  pub lhs: Box<dyn AST>,
  pub rhs: Box<dyn AST>
}

impl AST for BinOp {
  fn eval(&self) -> f64 {
    let (lhs, rhs) = (self.lhs.eval(),  self.rhs.eval());
    match self.op {
      Operator::Add => lhs + rhs,
      Operator::Sub => lhs - rhs,
      Operator::Mul => lhs * rhs,
      Operator::Div => lhs / rhs,
    }
  }
}

fn factor(input: &str) -> IResult<&str, Box<dyn AST>> {
  fn literal(input: & str) -> IResult<&str, Box<dyn AST>> {
    let float_literal = map(tuple((digit1, tag("."), digit1)), 
      |(n, _, m)| format!("{}.{}", n, m));
    let int_literal = map(digit1, |v: &str| v.to_owned());

    let (input, v) = alt((float_literal, int_literal))(input)?;
    Ok((input, Box::new(f64::from_str(&v).unwrap())))
  }

  fn exp_factor(input: &str) -> IResult<&str, Box<dyn AST>> {
    let (input, (_, _, e, _, _)) = tuple((tag("("), space0, expr,  space0, tag(")")))(input)?;
    return Ok((input, e))
  }
  Ok(alt((exp_factor, literal))(input)?)
}

fn term(input: &str) -> IResult<&str, Box<dyn AST>> {
  fn binary_term(input: &str) -> IResult<&str, Box<dyn AST>> {
    let (input, (lhs, _, v, _, rhs)) = tuple((factor, space0, alt((tag("*"),tag("/"))),  space0, factor))(input)?;
    if v == "*" {
      Ok((input, Box::new(BinOp{op: Operator::Mul, lhs, rhs})))
    } else {
      Ok((input, Box::new(BinOp{op: Operator::Div, lhs, rhs})))
    }
  }
  Ok(alt((binary_term, factor,))(input)?)
}

fn expr(input: &str) -> IResult<&str, Box<dyn AST>> {
  fn binary_expr(input: &str) -> IResult<&str, Box<dyn AST>> {
    let (input, (lhs, _, v, _, rhs)) = tuple((term, space0, alt((tag("+"),tag("-"))), space0, expr))(input)?;
    if v == "+" {
      Ok((input, Box::new(BinOp{op: Operator::Add, lhs, rhs})))
    } else {
      Ok((input, Box::new(BinOp{op: Operator::Sub, lhs, rhs})))
    }
  }
  Ok(alt((binary_expr, term))(input)?)
}

fn main() {
  let args: Vec<String> = std::env::args().collect();
  if args.len() != 2 {
    eprintln!("USAGE: {} 'EXPRESSION' ", args[0]);
    std::process::exit(0);
  }
  match expr(& args[1].trim()) {
    Ok((rest, ast)) => {
      if rest.len() == 0 {
        println!("{}", ast.eval());
      } else {
        eprintln!("Error: cannot parse all the input");
      }
    },
    Err(e) => eprintln!("{:?}", e)
  }
}

#[test]
fn parse_add() {
  assert_eq!(expr("1 + 2").unwrap().1.eval(), 3.0);
  assert_eq!(expr("1+2").unwrap().1.eval(), 3.0);
  assert_eq!(expr("1+2 + 3").unwrap().1.eval(), 6.0);
  assert_eq!(expr("1-2").unwrap().1.eval(), -1.0);
  assert_eq!(expr("1*2 + 2").unwrap().1.eval(), 4.0);
  assert_eq!(expr("2*(2 + 5)").unwrap().1.eval(), 14.0);
  assert_eq!(expr("2 * 2 + 5").unwrap().1.eval(), 9.0);

  assert_eq!(expr("2.0").unwrap().1.eval(), 2.0);
  assert_eq!(expr("0.2").unwrap().1.eval(), 0.2);
  assert_eq!(expr("0.2 - 0.1").unwrap().1.eval(), 0.1);
  
}

