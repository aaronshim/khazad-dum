import scala.util.parsing.combinator._
import java.io.FileReader


object VCGen {

  /* Arithmetic expressions. */
  trait ArithExp

  case class Num(value: Int) extends ArithExp
  case class Var(name: String) extends ArithExp
  case class Add(left: ArithExp, right: ArithExp) extends ArithExp
  case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
  case class Div(left: ArithExp, right: ArithExp) extends ArithExp
  case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
  case class Parens(a: ArithExp) extends ArithExp
  case class AVar(name: String, index: ArithExp) extends ArithExp


  /* Comparisons of arithmetic expressions. */
  type Comparison = Product3[ArithExp, String, ArithExp]


  /* Boolean expressions. */
  trait BoolExp

  case class BCmp(cmp: Comparison) extends BoolExp
  case class BImplies(left: BoolExp, right: BoolExp) extends BoolExp
  case class BNot(b: BoolExp) extends BoolExp
  case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
  case class BForAll(x: String, b: BoolExp) extends BoolExp
  case class BParens(b: BoolExp) extends BoolExp


  /* Statements and blocks. */
  trait Statement
  type Block = List[Statement]

  case class Assign(x: String, value: ArithExp) extends Statement
  case class If(cond: BoolExp, th: Block, el: Block) extends Statement
  case class While(cond: BoolExp, inv: Block, body: Block) extends Statement
  case class Inv(cond: BoolExp) extends Statement
  case class Precondition(cond: BoolExp) extends Statement
  case class Postcondition(cond: BoolExp) extends Statement


  /* Complete programs. */
  type Program = Product3[String, Block, Block]


  object ImpParser extends RegexParsers {
    /* General helpers. */
    val pvar  : Parser[String] = "\\p{Alpha}(\\p{Alnum}|_)*".r

    /* Parsing for ArithExp. */
    def num   : Parser[ArithExp] = "-?\\d+".r ^^ (s => Num(s.toInt))
    def avar  : Parser[ArithExp] =
      pvar ~ ("[" ~> aexp <~ "]") ^^ {
        case pvar ~ aexp => AVar(pvar, aexp)
      }
    def atom  : Parser[ArithExp] =
      "(" ~> aexp <~ ")" | avar |
      num | pvar ^^ { Var(_) } |
      "-" ~> atom ^^ { Sub(Num(0), _) }
    def factor: Parser[ArithExp] =
      atom ~ rep("*" ~ atom | "/" ~ atom | "%" ~ atom) ^^ {
        case left ~ list => (left /: list) {
          case (left, "*" ~ right) => Mul(left, right)
          case (left, "/" ~ right) => Div(left, right)
          case (left, "%" ~ right) => Mod(left, right)
        }
      }
    def term  : Parser[ArithExp] =
      factor ~ rep("+" ~ factor | "-" ~ factor) ^^ {
        case left ~ list => (left /: list) {
          case (left, "+" ~ right) => Add(left, right)
          case (left, "-" ~ right) => Sub(left, right)
        }
      }

    def aexp  : Parser[ArithExp] = term

    /* Parsing for Comparison. */
    def comp  : Parser[Comparison] =
      aexp ~ ("=" | "<=" | ">=" | "<" | ">" | "!=") ~ aexp ^^ {
        case left ~ op ~ right => (left, op, right)
      }

    /* Parsing for Implies. */
    def implies : Parser[BImplies] =
      (bexp <~ "==>") ~ bexp ^^ {
        case left ~ right => BImplies(left, right)
      }

    /* Parsing for BoolExp. */
    def bforall : Parser[BoolExp] =
      ("forall" ~> pvar <~ ",") ~ implies ^^ {
        case v ~ b => BForAll(v, b)
      } |
      ("forall" ~> pvar <~ ",") ~ bexp ^^ {
        case v ~ b => BForAll(v, b)
      }
    def batom : Parser[BoolExp] =
      "(" ~> bexp <~ ")" |
      comp ^^ { BCmp(_) } |
      "!" ~> batom ^^ { BNot(_) } | bforall | implies
    def bconj : Parser[BoolExp] =
      batom ~ rep("&&" ~> batom) ^^ {
        case left ~ list => (left /: list) { BConj(_, _) }
      }
    def bdisj : Parser[BoolExp] =
      bconj ~ rep("||" ~> bconj) ^^ {
        case left ~ list => (left /: list) { BDisj(_, _) }
      }
    def bexp  : Parser[BoolExp] = bdisj

    /* Parsing for Statement and Block. */
    def block : Parser[Block] = rep(stmt)
    def stmt  : Parser[Statement] =
      (pvar <~ ":=") ~ (aexp <~ ";") ^^ {
        case v ~ e => Assign(v, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "else") ~ (block <~ "end") ^^ {
        case c ~ t ~ e => If(c, t, e)
      } |
      ("if" ~> bexp <~ "then") ~ (block <~ "end") ^^ {
        case c ~ t => If(c, t, Nil)
      } |
      ("while" ~> bexp) ~ (invariant <~ "do") ~ (block <~ "end") ^^ {
        case c ~ i ~ b => While(c, i, b)
      }

    def invariant : Parser[Block] = rep(invstmt)
    def invstmt   : Parser[Statement] =
      ("inv" ~> bexp) ^^ { Inv(_) }
    def prepost   : Parser[Block] = rep(prestmt | poststmt)
    def prestmt   : Parser[Statement] =
      ("pre" ~> bexp) ^^ { Precondition(_) }
    def poststmt   : Parser[Statement] =
      ("post" ~> bexp) ^^ { Postcondition(_) }

    /* Parsing for Program. */
    def prog   : Parser[Program] =
      ("program" ~> pvar) ~ (prepost <~ "is") ~ (block <~ "end") ^^ {
        case n ~ p ~ b => (n, p, b)
      }
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._;

    val parsedProgram:ParseResult[Program] = parseAll(prog, reader)

    parsedProgram match {
      case Success(r, n) => handleResult(r)
      case Failure(msg, n) => println(msg)
      case Error(msg, n) => println(msg)
    }
  }

  def handleResult(r: Program) = {
    val name = r._1
    val prepost : Block = r._2
    val code : Block = r._3

    println("Name: " + name)
    println("Pre/post-conditions: ")
    handleBlock(prepost)
    println("Code: ")
    handleBlock(code)
  }

  def handleBlock(block: Block, level: Int = 0): Unit = {
    printlnTab("(", level)
    for (line <- block) {
      line match {
        case ass: Assign => handleAssign(ass, level+1)
        case w: While => handleWhile(w, level+1)
        case i: Inv => handleInv(i, level+1)
        case pre: Precondition => handlePrecondition(pre, level+1)
        case post: Postcondition => handlePostcondition(post, level+1)
        case _ => printlnTab(line, level+1)
      }
    }
    printlnTab(")", level)
  }

  def handleWhile(w: While, level: Int = 0) = {
    printlnTab("While(", level)
      handleBoolExp(w.cond, level+1)
      handleBlock(w.inv, level+1)
      handleBlock(w.body, level+1)
    printlnTab(")", level)
  }

  def handleInv(i: Inv, level: Int = 0) = {
    printlnTab("Inv(", level)
      handleBoolExp(i.cond, level+1)
    printlnTab(")", level)
  }
  def handlePrecondition(p: Precondition, level: Int = 0) = {
    printlnTab("Precondition(", level)
      handleBoolExp(p.cond, level+1)
    printlnTab(")", level)
  }
  def handlePostcondition(p: Postcondition, level: Int = 0) = {
    printlnTab("Postcondition(", level)
      handleBoolExp(p.cond, level+1)
    printlnTab(")", level)
  }

  def handleAssign(ass: Assign, level: Int) = {
    printlnTab("Assign(", level)
      printlnTab(ass.x, level+1)
      handleArithExp(ass.value, level+1)
    printlnTab(")", level)
  }

  def handleBoolExp(b: BoolExp, level: Int): Unit = {
    b match {
      case cmp: BCmp => handleBCmp(cmp, level)
      case conj: BConj => handleBConj(conj, level)
      case disj: BDisj => handleBDisj(disj, level)
      case imp: BImplies => handleBImplies(imp, level)
      case fa: BForAll => handleBForAll(fa, level)
      case _ => printlnTab(b, level)
// BNot
// BParens
    }
  }

  def handleArithExp(a: ArithExp, level: Int): Unit = {
    a match {
      case n: Num => printlnTab(n, level)
      case v: Var => printlnTab(v, level)
      case add: Add => handleAdd(add, level)
      case sub: Sub => handleSub(sub, level)
      case mul: Mul => handleMul(mul, level)
      case av: AVar => handleAVar(av, level)
      case _ => printlnTab(a, level)
// Div
// Mod
// Parens
    }
  }

  def handleBCmp(b: BCmp, level: Int) = {
    printlnTab("BCmp(", level)
      handleArithExp(b.cmp._1, level+1)
      printlnTab(b.cmp._2, level+1)
      handleArithExp(b.cmp._3, level+1)
    printlnTab(")", level)
  }
  def handleBConj(b: BConj, level: Int) = {
    printlnTab("BConj(", level)
      handleBoolExp(b.left, level+1)
      handleBoolExp(b.right, level+1)
    printlnTab(")", level)
  }
  def handleBDisj(b: BDisj, level: Int) = {
    printlnTab("BDisj(", level)
      handleBoolExp(b.left, level+1)
      handleBoolExp(b.right, level+1)
    printlnTab(")", level)
  }

  def handleBImplies(imp: BImplies, level: Int) = {
    printlnTab("BImplies(", level)
      handleBoolExp(imp.left, level+1)
      printlnTab("==>", level+1)
      handleBoolExp(imp.right, level+1)
    printlnTab(")", level)
  }

  def handleBForAll(fa: BForAll, level: Int) = {
    printlnTab("BForAll(", level)
      printlnTab(fa.x, level+1)
      handleBoolExp(fa.b, level+1)
    printlnTab(")", level)
  }

  def handleAdd(a: Add, level: Int) = {
    printlnTab("Add(", level)
      handleArithExp(a.left, level+1)
      handleArithExp(a.right, level+1)
    printlnTab(")", level)
  }
  def handleSub(a: Sub, level: Int) = {
    printlnTab("Sub(", level)
      handleArithExp(a.left, level+1)
      handleArithExp(a.right, level+1)
    printlnTab(")", level)
  }
  def handleMul(a: Mul, level: Int) = {
    printlnTab("Mul(", level)
      handleArithExp(a.left, level+1)
      handleArithExp(a.right, level+1)
    printlnTab(")", level)
  }

  def handleAVar(av: AVar, level: Int) = {
    printlnTab("AVar(", level)
      printlnTab(av.name, level+1)
      handleArithExp(av.index, level+1)
    printlnTab(")", level)
  }

  def printlnTab(str: Any, level: Int) = {
    println("  " * level + str)
  }
}
