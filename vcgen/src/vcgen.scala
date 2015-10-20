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
  case class BTrue() extends BoolExp
  case class BFalse() extends BoolExp


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

  object GCGen {
    type GCBlock = List[GCStatement]

    trait GCStatement

    case class Assume(b: BoolExp) extends GCStatement
    case class Havoc(x: String) extends GCStatement
    case class Assert(b: BoolExp) extends GCStatement
    case class GCParens(gc: GCBlock) extends GCStatement
    case class BoxOp(left: GCStatement, right: GCStatement) extends GCStatement

    var varCounter = 1

    def generateGC(prog: Program): GCBlock = {
      val name = prog._1
      val prepost : Block = prog._2
      val code : Block = prog._3

      println("Generating GC for program '" + name + "'...")

      // Get the pre and post conditions.
      val(preconditions, postconditions) = extractPrePost(prepost)

      var gc: GCBlock = List()

      // Put in preconditions.
      if (preconditions != None) {
        gc :+= Assume(preconditions.get)
      }

      // Put in program gcs.
      gc = gc ::: traverseCode(code)

      // Put in postconditions.
      if (postconditions != None) {
        gc :+= Assume(postconditions.get)
      }

      return gc
    }

    def traverseCode(code: Block): GCBlock = {
      var gctmp: GCBlock = List()

      for (line <- code) {
        line match {
          case sAssign: Assign => gctmp = gctmp ::: appendAssign(sAssign)
          case sIf: If => gctmp = gctmp ::: appendIf(sIf)
          case sWhile: While => gctmp = gctmp ::: appendWhile(sWhile)
          case _ => 0
        }
      }

      return gctmp
    }

    def appendWhile(s: While): GCBlock = {
      val inv: Block = s.inv
      val cond: BoolExp = s.cond
      val body: Block = s.body

      var gctmp : GCBlock = List()

      var invariant: Option[BoolExp] = None
      for (i <- inv) {
        i match {
          case invar: Inv => {
            if (invariant == None) {
              invariant = Option(invar.cond)
            } else {
              invariant = Option(BDisj(invar.cond, invariant.get))
            }
          }
        }
      }

      var invariantOrTrue: BoolExp = BTrue()
      if (invariant != None) {
        invariantOrTrue = invariant.get
      }

      gctmp :+= Assert(invariantOrTrue)

      //havocs
      val vars: List[String] = extractVars(body)
      gctmp = gctmp ::: vars.map { x => Havoc(x) }

      gctmp :+= Assume(invariantOrTrue)

      gctmp :+= BoxOp(
        GCParens(
          Assume(cond) +:
          traverseCode(body) :::
          List(Assert(invariantOrTrue), Assume(BFalse()))
        ),
        Assume(BNot(cond))
      )

      return gctmp
    }

    def appendAssign(s: Assign): GCBlock = {
      val x: String = s.x
      var value: ArithExp = s.value

      var gctmp: GCBlock = List()

      gctmp :+=
        Assume(
          BCmp(
            (Var(x), "=", Var(x)) // First x needs to be tmp
          )
        )
      gctmp :+= Havoc(x)

      value = replaceVarInArithExp(value, x, x + "f" + varCounter)
      varCounter += 1

      gctmp :+=
        Assume(
          BCmp(
            (Var(x), "=", value)
          )
        )

      return gctmp
    }

    def appendIf(s: If): GCBlock = {
      val cond: BoolExp = s.cond
      val body: Block = s.th
      val el: Block = s.el

      var gctmp: GCBlock = List()

      gctmp :+=
        BoxOp(
          GCParens(
            Assume(cond) +: traverseCode(body)
          ),
          GCParens(
            Assume(BNot(cond)) +: traverseCode(el)
          )
        )

      return gctmp
    }

    def replaceVarInArithExp(ae: ArithExp, x: String, tmp: String): ArithExp = {
      ae match {
        case v: Var => return Var(tmp)
        case v: AVar => {
          return AVar(tmp, replaceVarInArithExp(v.index, x, tmp))
        }
        case a: Add => {
          return Add(
            replaceVarInArithExp(a.left, x, tmp),
            replaceVarInArithExp(a.right, x, tmp)
          )
        }
        case a: Sub => {
          return Sub(
            replaceVarInArithExp(a.left, x, tmp),
            replaceVarInArithExp(a.right, x, tmp)
          )
        }
        case a: Mul => {
          return Mul(
            replaceVarInArithExp(a.left, x, tmp),
            replaceVarInArithExp(a.right, x, tmp)
          )
        }
        case a: Div => {
          return Div(
            replaceVarInArithExp(a.left, x, tmp),
            replaceVarInArithExp(a.right, x, tmp)
          )
        }
        case a: Mod => {
          return Mod(
            replaceVarInArithExp(a.left, x, tmp),
            replaceVarInArithExp(a.right, x, tmp)
          )
        }
        case p: Parens => {
          return Parens(replaceVarInArithExp(p.a, x, tmp))
        }
        case n: Num => return n
      }
    }

    def extractVars(code: Block): List[String] = {
      var varList: List[String] = List()
      for (line <- code) {
        varList = varList ::: extractVarsFromStatement(line)
      }
      return varList
    }

    def extractVarsFromStatement(s: Statement): List[String] = {
      var varList: List[String] = List()
      s match {
        case assignment: Assign => varList :+= assignment.x
        case ifs: If => varList = varList ::: (extractVars(ifs.th) ::: extractVars(ifs.el))
        case whiles: While => varList = varList ::: extractVars(whiles.body)
        case _ => 0
      }
      return varList
    }

    def extractPrePost(prepost: Block): (Option[BoolExp], Option[BoolExp]) = {
      var preconditions: Option[BoolExp] = None
      var postconditions: Option[BoolExp] = None
      for (line <- prepost) {
        line match {
          case pre: Precondition => {
            if (preconditions == None) {
              preconditions = Option(pre.cond)
            } else {
              preconditions = Option(BDisj(pre.cond, preconditions.get))
            }
          }
          case post: Postcondition => {
            if (postconditions == None) {
              postconditions = Option(post.cond)
            } else {
              postconditions = Option(BDisj(post.cond, postconditions.get))
            }
          }
        }
      }
      return (preconditions, postconditions)
    }
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._
    import GCGen._

    val parsedProgram:ParseResult[Program] = parseAll(prog, reader)

    parsedProgram match {
      case Success(r, n) => println(generateGC(r))
      // case Success(r, n) => handleResult(r)
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

  def handleBoolExp(b: BoolExp, level: Int = 0): Unit = {
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
