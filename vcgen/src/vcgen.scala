import scala.util.parsing.combinator._
import sys.process._
//import scala.language.postfixOps
import java.io._

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
        gc :+= Assert(postconditions.get)
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
              invariant = Option(BConj(invar.cond, invariant.get))
            }
          }
        }
      }

      // invariant just before entering the loop
      if (invariant != None) {
        gctmp :+= Assert(invariant.get)
      }

      //havocs
      val vars: List[String] = extractVars(body)
      gctmp = gctmp ::: vars.map { x => Havoc(x) }

      // invariant just after entering the loop
      if (invariant != None) {
        gctmp :+= Assume(invariant.get)
      }

      // try to construct the stuff to go in the body of the GC
      //  (albeit a bit messily constructed)
      var endPiece : GCBlock = List()
      if (invariant != None) {
        endPiece :+= Assert(invariant.get)
      }
      endPiece :+= Assume(BFalse())

      gctmp :+= BoxOp(
        GCParens(
          Assume(cond) +:
          traverseCode(body) :::
          endPiece
        ),
        Assume(BNot(cond))
      )

      return gctmp
    }

    def appendAssign(s: Assign): GCBlock = {
      val x: String = s.x
      var value: ArithExp = s.value

      var gctmp: GCBlock = List()

      // WE NEED TO GENERATE A TMP
      var freshVariable = newFreshVariable(x)

      gctmp :+=
        Assume(
          BCmp(
            (Var(freshVariable), "=", Var(x)) // First x needs to be tmp
          )
        )
      gctmp :+= Havoc(x)

      value = replaceVarInArithExp(value, x, freshVariable)

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
        case v: Var => if (x.equals(v.name)) Var(tmp) else v
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
              preconditions = Option(BConj(pre.cond, preconditions.get))
            }
          }
          case post: Postcondition => {
            if (postconditions == None) {
              postconditions = Option(post.cond)
            } else {
              postconditions = Option(BConj(post.cond, postconditions.get))
            }
          }
        }
      }
      return (preconditions, postconditions)
    }

    def handleGCStatement(gcs: GCStatement, level: Int) {
      gcs match {
        case a: Assume => handleAssume(a, level)
        case h: Havoc => handleHavoc(h, level)
        case a: Assert => handleAssert(a, level)
        case p: GCParens => handleGCParens(p, level)
        case b: BoxOp => handleBoxOp(b, level)
      }
    }
    def handleGC(gc: GCBlock, level: Int = 0) = {
      for (s <- gc) {
        handleGCStatement(s, level)
      }
    }

    // case class Assume(b: BoolExp) extends GCStatement
    // case class Havoc(x: String) extends GCStatement
    // case class Assert(b: BoolExp) extends GCStatement
    // case class GCParens(gc: GCBlock) extends GCStatement
    // case class BoxOp(left: GCStatement, right: GCStatement) extends GCStatement

    // def processHavocs(gcs: GCBlock): GCBlock = {
    //   val head: GCStatement = gcs.head()

    //   head match {
    //     case x: Havoc => Havoc(newFreshVariable(x.x)) :::
    //     case _ => gc
    //   }

    //   var newGC: GCBlock = List()

    //   gcs.foldLeft(seed)((head) => newGC :+= processHavocsStep(head))

    //   return newGC
    // }

    // from GC to VC (Weakest precondition) in boolean format
    def generateVC(gcs: GCBlock): BoolExp = {

      // seed value
      var formula = BTrue()

      // unwrap the GC block
      def computeWP(gcs: GCBlock, seed: BoolExp): BoolExp = {
        gcs.foldRight(seed)((head, b) => computeWPStep(head, b))
      }

      // rules for each of the GC commands minus the c1 ; c2 case
      def computeWPStep(gc: GCStatement, b: BoolExp): BoolExp = {
        gc match {
          case assume: Assume => BImplies(assume.b, b)
          case havoc: Havoc => {
            val newVarName: String = newFreshVariable(havoc.x)
            // println("Havocing " + havoc.x + " with " + newVarName)
            replaceVarInBoolExp(b, havoc.x, newVarName)
          }
          case assert: Assert => BConj(assert.b, b)
          case parens: GCParens => computeWP(parens.gc, b)
          case box: BoxOp => BConj(computeWPStep(box.left, b), computeWPStep(box.right, b))
        }
      }

      // returning-- essentially, the whole function is a wrapper for this
      computeWP(gcs, formula)
    }

    // for assume-havoc-assert cycles in translating Assign statments
    //  as well as translating out Havoc statments during WP
    def newFreshVariable(x : String) : String = {
      varCounter += 1
      x + "f" + varCounter
    }

    // just like our replace arithmetic method
    def replaceVarInBoolExp(exp: BoolExp, find: String, replace: String) : BoolExp = {
      exp match {
        case cmp: BCmp => {
          var left: ArithExp = cmp.cmp._1
          var comparator: String = cmp.cmp._2
          var right: ArithExp = cmp.cmp._3
          BCmp((replaceVarInArithExp(left, find, replace), comparator, replaceVarInArithExp(right, find, replace)))
        }
        case implies: BImplies => BImplies(replaceVarInBoolExp(implies.left, find, replace),
          replaceVarInBoolExp(implies.right, find, replace))
        case bnot: BNot => BNot(replaceVarInBoolExp(bnot.b, find, replace))
        case bdisj: BDisj => BDisj(replaceVarInBoolExp(bdisj.left, find, replace),
          replaceVarInBoolExp(bdisj.right, find, replace))
        case bconj: BConj => BConj(replaceVarInBoolExp(bconj.left, find, replace),
          replaceVarInBoolExp(bconj.right, find, replace))
        case fa: BForAll => {
          var str : String = if (fa.x.equals(find)) replace else fa.x
          BForAll(str, replaceVarInBoolExp(fa.b, find, replace))
        }
        case parens: BParens => BParens(replaceVarInBoolExp(parens.b, find, replace))
        case t: BTrue => t
        case f: BFalse => f
      }
    }

    def handleAssume(a: Assume, level: Int) = {
      printlnTab("Assume(", level)
        handleBoolExp(a.b, level+1)
      printlnTab(")", level)
    }
    def handleHavoc(h: Havoc, level: Int) = {
      printlnTab("Havoc(" + h.x + ")", level)
    }
    def handleAssert(a: Assert, level: Int) = {
      printlnTab("Assert(", level)
        handleBoolExp(a.b, level+1)
      printlnTab(")", level)
    }
    def handleGCParens(p: GCParens, level: Int) = {
      printlnTab("(", level)
        handleGC(p.gc, level+1)
      printlnTab(")", level)
    }
    def handleBoxOp(b: BoxOp, level: Int) = {
      printlnTab("BoxOp(", level)
        handleGCStatement(b.left, level+1)
        handleGCStatement(b.right, level+1)
      printlnTab(")", level)
    }
  }

  // take the VC from the computed weakest precondition of the last step and write it in Z3 syntax
  def generateZ3(wp : BoolExp): Unit = {
    // todo
    var input = ""

    // write these in the form "(declare-fun * () Int)
    def extractVarsFromBExp(b: BoolExp): List[String] = {
      b match {
        case cmp: BCmp => extractVarsFromAExp(cmp.cmp._1) ::: extractVarsFromAExp(cmp.cmp._3)
        case implies: BImplies => extractVarsFromBExp(implies.left) ::: extractVarsFromBExp(implies.right)
        case bnot: BNot => extractVarsFromBExp(bnot.b)
        case bdisj: BDisj => extractVarsFromBExp(bdisj.left) ::: extractVarsFromBExp(bdisj.right)
        case bconj: BConj => extractVarsFromBExp(bconj.left) ::: extractVarsFromBExp(bconj.right)
        case fa: BForAll => fa.x :: extractVarsFromBExp(fa.b)
        case parens: BParens => extractVarsFromBExp(parens.b)
        case _ => List()
      }
    }
    def extractVarsFromAExp(a: ArithExp): List[String] = {
      a match {
        /*
        case class Num(value: Int) extends ArithExp
        case class Var(name: String) extends ArithExp
        case class Add(left: ArithExp, right: ArithExp) extends ArithExp
        case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
        case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
        case class Div(left: ArithExp, right: ArithExp) extends ArithExp
        case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
        case class Parens(a: ArithExp) extends ArithExp
        case class AVar(name: String, index: ArithExp) extends ArithExp
         */
        case v: Var => List(v.name)
        case a: Add => extractVarsFromAExp(a.left) ::: extractVarsFromAExp(a.right)
        case s: Sub => extractVarsFromAExp(s.left) ::: extractVarsFromAExp(s.right)
        case m: Mul => extractVarsFromAExp(m.left) ::: extractVarsFromAExp(m.right)
        case d: Div => extractVarsFromAExp(d.left) ::: extractVarsFromAExp(d.right)
        case m: Mod => extractVarsFromAExp(m.left) ::: extractVarsFromAExp(m.right)
        case p: Parens => extractVarsFromAExp(p.a)
        case _ => List()
      }
    }
    var vars = extractVarsFromBExp(wp)
    vars = vars.distinct // clean repeat variables
    for (v <- vars) {
      input += ("(declare-fun " + v + " () Int)\n")
    }

    def boolExpToSMT(b: BoolExp): String = {
      // helper for this calculation
      def aExpToSMT(a: ArithExp): String = {
        a match {
          /*
          case class Num(value: Int) extends ArithExp
          case class Var(name: String) extends ArithExp
          case class Add(left: ArithExp, right: ArithExp) extends ArithExp
          case class Sub(left: ArithExp, right: ArithExp) extends ArithExp
          case class Mul(left: ArithExp, right: ArithExp) extends ArithExp
          case class Div(left: ArithExp, right: ArithExp) extends ArithExp
          case class Mod(left: ArithExp, right: ArithExp) extends ArithExp
          case class Parens(a: ArithExp) extends ArithExp
          case class AVar(name: String, index: ArithExp) extends ArithExp
           */
          case x: Num => x.value.toString
          case x: Var => x.name
          case x: Add => "(+ " + aExpToSMT(x.left) + " " + aExpToSMT(x.right) + ")"
          case x: Sub => "(- " + aExpToSMT(x.left) + " " + aExpToSMT(x.right) + ")"
          case x: Mul => "(* " + aExpToSMT(x.left) + " " + aExpToSMT(x.right) + ")"
          case x: Div => "(/ " + aExpToSMT(x.left) + " " + aExpToSMT(x.right) + ")"
          case x: Mod => "(mod " + aExpToSMT(x.left) + " " + aExpToSMT(x.right) + ")"
          case x: Parens => aExpToSMT(x.a) // I think this is the right way, since all levels come wrapped in parenthesis anyway?
          case _ => "" // eek
        }
      }

      b match {
        /*
        case class BCmp(cmp: Comparison) extends BoolExp
        case class BImplies(left: BoolExp, right: BoolExp) extends BoolExp
        case class BNot(b: BoolExp) extends BoolExp
        case class BDisj(left: BoolExp, right: BoolExp) extends BoolExp
        case class BConj(left: BoolExp, right: BoolExp) extends BoolExp
        case class BForAll(x: String, b: BoolExp) extends BoolExp
        case class BParens(b: BoolExp) extends BoolExp
        case class BTrue() extends BoolExp
        case class BFalse() extends BoolExp
        */
        case x: BCmp => {
          x.cmp._2 match {
            case "!=" => "(not (=" + aExpToSMT(x.cmp._1) + " " + aExpToSMT(x.cmp._3) + "))"
            case comparator => "(" + comparator + " " +  aExpToSMT(x.cmp._1) + " " + aExpToSMT(x.cmp._3) + ")"
          }
        }
        case x: BImplies => "(implies " + boolExpToSMT(x.left) + " " + boolExpToSMT(x.right) + ")"
        case x: BNot => "(not " + boolExpToSMT(x.b) + ")"
        case x: BDisj => "(or " + boolExpToSMT(x.left) + " " + boolExpToSMT(x.right) + ")"
        case x: BConj => "(and " + boolExpToSMT(x.left) + " " + boolExpToSMT(x.right) + ")"
        case x: BForAll => "(forall ((" + x.x + " Int)) " + boolExpToSMT(x.b) + ")"
        case x: BParens => boolExpToSMT(x.b) // everything comes attached to parenthesis anyway
        case x: BTrue => "true" // these primitives will not be called outside parenthetical structures?
        case x: BFalse => "false"
      }
    }

    // final touches
    input += ("(assert (not " + boolExpToSMT(wp) + "))\n")
    input += "(check-sat)\n"

    // now what?
    println("\nOUR Z3 INPUT:")
    println(input)

    // processor builder!
    try {
      var output: String = ("z3 -in" #< new ByteArrayInputStream(input.getBytes)).!!
      println("\nOUR Z3 OUTPUT:\n" + output)
      output match {
        case x if x.startsWith("unsat") => println("Program valid.")
        case x if x.startsWith("sat") => {
          println("Program is not valid.")
          input += "(get-model)\n"
          output = ("z3 -in" #< new ByteArrayInputStream(input.getBytes)).!!
          println("\nProgram is not valid under the conditions:\n" + output)
        }
        case _ => println("Z3 WTF?!?!?!")
      }
    }
    catch {
      case e: Exception => println("Z3 crashed on this input...")
    }
  }

  def main(args: Array[String]): Unit = {
    val reader = new FileReader(args(0))
    import ImpParser._
    import GCGen._

    val parsedProgram:ParseResult[Program] = parseAll(prog, reader)

    parsedProgram match {
      case Success(r, n) => {
        // GUARDED COMMANDS
        var gc = generateGC(r)
        handleGC(gc)

        // WEAKEST PRECONDITIONS FORMULA
        // gc = processHavocs(gc)
        var wp = generateVC(gc)
        println("\nOur Weakest Precondition calculation:")
        // wp = cBE(wp)
        // wp = cBE(wp)
        // wp = cBE(wp)
        // wp = cBE(wp)
        // wp = cBE(wp)
        handleBoolExp(wp)

        // Z3 LANGUAGE TRANSLATION
        generateZ3(wp)
      }
      // case Success(r, n) => handleResult(r)
      case Failure(msg, n) => println(msg)
      case Error(msg, n) => println(msg)
    }
  }

  def cBE(b: BoolExp): BoolExp = {
    b match {
      case x: BImplies => {
        x.left match {
          case y: BFalse => BTrue()
          case _ => {
            x.right match {
              case y: BImplies => {
                cBE(BImplies(BConj(cBE(x.left), cBE(y.left)), cBE(y.right)))
              }
              case _ => BImplies(cBE(x.left), cBE(x.right))
            }
          }
        }
      }
      case x: BNot => BNot(cBE(x.b))
      case x: BDisj => {
        x.left match {
          case y: BFalse => cBE(x.right)
          case y: BTrue => BTrue()
          case _ => {
            x.right match {
              case y: BFalse => cBE(x.left)
              case y: BTrue => BTrue()
              case _ => BDisj(cBE(x.left), cBE(x.right))
            }
          }
        }
      }
      case x: BConj => {
        x.left match {
          case y: BTrue => cBE(x.right)
          case y: BFalse => BFalse()
          case _ => {
            x.right match {
              case y: BTrue => cBE(x.left)
              case y: BFalse => BFalse()
              case _ => BConj(cBE(x.left), cBE(x.right))
            }
          }
        }
      }
      case x: BForAll => BForAll(x.x, cBE(x.b))
      case x: BParens => BParens(cBE(x))
      case x: BCmp => {
        x.cmp._2 match {
          case "=" => {
            x.cmp._1 match {
              case y: Var => {
                x.cmp._3 match {
                  case z: Var => BTrue()
                  case _ => x
                }
              }
              case _ => x
            }
          }
          case _ => x
        }
      }
      case _ => b
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
