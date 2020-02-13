// See LICENSE for license details.

package firrtlTests

import firrtl._
import firrtl.ir._
import firrtl.annotations.CircuitTarget
import firrtl.passes.{CheckHighForm, CheckTypes, CheckInitialization}
import firrtl.transforms.{DontTouchAnnotation, InferResets}
import FirrtlCheckers._

// TODO
// - Test nodes in the connection
// - Test with whens (is this allowed?)
class InferResetsSpec extends FirrtlFlatSpec {
  import _root_.logger.{ClassLogLevelAnnotation, Logger, LogLevel, LogLevelAnnotation}

  def compile(input: String, compiler: Compiler = new MiddleFirrtlCompiler, annotations: AnnotationSeq = Seq.empty): CircuitState = {
    val gll = LogLevelAnnotation(LogLevel.None)
    val cll = Seq(
      ClassLogLevelAnnotation("firrtl.passes.ReplaceAccesses$", gll.globalLogLevel),
      ClassLogLevelAnnotation("firrtl.passes.ExpandConnects$",  gll.globalLogLevel),
      ClassLogLevelAnnotation("firrtl.transforms.InferResets",  LogLevel.Trace),
      ClassLogLevelAnnotation("firrtl.annotations.transforms.EliminateTargetPaths",  LogLevel.Trace),
      ClassLogLevelAnnotation("firrtl.passes.ExpandWhens$",     gll.globalLogLevel),
      ClassLogLevelAnnotation("firrtl.passes.InferTypes$",      gll.globalLogLevel),
      ClassLogLevelAnnotation("firrtl.ResolveAndCheck",         gll.globalLogLevel)
    )
    Logger.makeScope(gll +: cll) {
      compiler.compileAndEmit(CircuitState(parse(input), ChirrtlForm, annotations), List.empty)
    }
  }

  behavior of "ResetType"

  val BoolType = UIntType(IntWidth(1))

  it should "support casting to other types" in {
    val result = compile(s"""
      |circuit top:
      |  module top:
      |    input a : UInt<1>
      |    output v : UInt<1>
      |    output w : SInt<1>
      |    output x : Clock
      |    output y : Fixed<1><<0>>
      |    output z : AsyncReset
      |    wire r : Reset
      |    r <= a
      |    v <= asUInt(r)
      |    w <= asSInt(r)
      |    x <= asClock(r)
      |    y <= asFixedPoint(r, 0)
      |    z <= asAsyncReset(r)""".stripMargin
    )
    result should containLine ("wire r : UInt<1>")
    result should containLine ("r <= a")
    result should containLine ("v <= asUInt(r)")
    result should containLine ("w <= asSInt(r)")
    result should containLine ("x <= asClock(r)")
    result should containLine ("y <= asSInt(r)")
    result should containLine ("z <= asAsyncReset(r)")
  }

  it should "work across Module boundaries" in {
    val result = compile(s"""
      |circuit top :
      |  module child :
      |    input clock : Clock
      |    input childReset : Reset
      |    input x : UInt<8>
      |    output z : UInt<8>
      |    reg r : UInt<8>, clock with : (reset => (childReset, UInt(123)))
      |    r <= x
      |    z <= r
      |  module top :
      |    input clock : Clock
      |    input reset : UInt<1>
      |    input x : UInt<8>
      |    output z : UInt<8>
      |    inst c of child
      |    c.clock <= clock
      |    c.childReset <= reset
      |    c.x <= x
      |    z <= c.z
      |""".stripMargin
    )
    result should containTree { case Port(_, "childReset", Input, BoolType) => true }
  }

  it should "work across multiple Module boundaries" in {
    val result = compile(s"""
      |circuit top :
      |  module child :
      |    input resetIn : Reset
      |    output resetOut : Reset
      |    resetOut <= resetIn
      |  module top :
      |    input clock : Clock
      |    input reset : UInt<1>
      |    input x : UInt<8>
      |    output z : UInt<8>
      |    inst c of child
      |    c.resetIn <= reset
      |    reg r : UInt<8>, clock with : (reset => (c.resetOut, UInt(123)))
      |    r <= x
      |    z <= r
      |""".stripMargin
    )
    result should containTree { case Port(_, "resetIn", Input, BoolType) => true }
    result should containTree { case Port(_, "resetOut", Output, BoolType) => true }
  }

  it should "work in nested and flipped aggregates with regular and partial connect" in {
    val result = compile(s"""
      |circuit top :
      |  module top :
      |    output fizz : { flip foo : { a : AsyncReset, flip b: Reset }[2], bar : { a : Reset, flip b: AsyncReset }[2] }
      |    output buzz : { flip foo : { a : AsyncReset, c: UInt<1>, flip b: Reset }[2], bar : { a : Reset, flip b: AsyncReset, c: UInt<8> }[2] }
      |    fizz.bar <= fizz.foo
      |    buzz.bar <- buzz.foo
      |""".stripMargin,
      new LowFirrtlCompiler
    )
    result should containTree { case Port(_, "fizz_foo_0_a", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_foo_0_b", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_foo_1_a", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_foo_1_b", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_bar_0_a", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_bar_0_b", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_bar_1_a", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "fizz_bar_1_b", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_foo_0_a", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_foo_0_b", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_foo_1_a", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_foo_1_b", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_bar_0_a", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_bar_0_b", Input, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_bar_1_a", Output, AsyncResetType) => true }
    result should containTree { case Port(_, "buzz_bar_1_b", Input, AsyncResetType) => true }
  }

  it should "not crash if a ResetType has no drivers" in {
    a [CheckInitialization.RefNotInitializedException] shouldBe thrownBy {
      compile(s"""
        |circuit test :
        |  module test :
        |    output out : Reset
        |    wire w : Reset
        |    out <= w
        |    out <= UInt(1)
        |""".stripMargin
      )
    }
  }

  it should "allow last connect semantics to pick the right type for Reset" in {
    val result =
      compile(s"""
        |circuit top :
        |  module top :
        |    input reset0 : AsyncReset
        |    input reset1 : UInt<1>
        |    output out : Reset
        |    wire w0 : Reset
        |    wire w1 : Reset
        |    w0 <= reset0
        |    w1 <= reset1
        |    out <= w0
        |    out <= w1
        |""".stripMargin
      )
    result should containTree { case DefWire(_, "w0", AsyncResetType) => true }
    result should containTree { case DefWire(_, "w1", BoolType)       => true }
    result should containTree { case Port(_, "out", Output, BoolType) => true }
  }

  it should "support last connect semantics across whens" in {
    val result =
      compile(s"""
        |circuit top :
        |  module top :
        |    input reset0 : AsyncReset
        |    input reset1 : AsyncReset
        |    input reset2 : UInt<1>
        |    input en : UInt<1>
        |    output out : Reset
        |    wire w0 : Reset
        |    wire w1 : Reset
        |    wire w2 : Reset
        |    w0 <= reset0
        |    w1 <= reset1
        |    w2 <= reset2
        |    out <= w2
        |    when en :
        |      out <= w0
        |    else :
        |      out <= w1
        |""".stripMargin
      )
    result should containTree { case DefWire(_, "w0", AsyncResetType) => true }
    result should containTree { case DefWire(_, "w1", AsyncResetType) => true }
    result should containTree { case DefWire(_, "w2", BoolType)       => true }
    result should containTree { case Port(_, "out", Output, AsyncResetType) => true }
  }

  it should "not allow different Reset Types to drive a single Reset" in {
    val passExceptions = the [passes.PassExceptions] thrownBy {
      compile(s"""
        |circuit top :
        |  module top :
        |    input reset0 : AsyncReset
        |    input reset1 : UInt<1>
        |    input en : UInt<1>
        |    output out : Reset
        |    wire w1 : Reset
        |    wire w2 : Reset
        |    w1 <= reset0
        |    w2 <= reset1
        |    out <= w1
        |    when en :
        |      out <= w2
        |""".stripMargin
      )
    }
    passExceptions.exceptions should contain (_: CheckTypes.MuxSameType)
    passExceptions.exceptions should contain (_: CheckTypes.InvalidRegInit)
  }

  it should "allow concrete reset types to overrule invalidation" in {
    val result = compile(s"""
      |circuit test :
      |  module test :
      |    input in : AsyncReset
      |    output out : Reset
      |    out is invalid
      |    out <= in
      |""".stripMargin)
    result should containTree { case Port(_, "out", Output, AsyncResetType) => true }
  }

  it should "default to BoolType for Resets that are only invalidated" in {
    val result = compile(s"""
      |circuit test :
      |  module test :
      |    output out : Reset
      |    out is invalid
      |""".stripMargin)
    result should containTree { case Port(_, "out", Output, BoolType) => true }
  }

  it should "not error if component of ResetType is invalidated and connected to an AsyncResetType" in {
    val result = compile(s"""
      |circuit test :
      |  module test :
      |    input cond : UInt<1>
      |    input in : AsyncReset
      |    output out : Reset
      |    out is invalid
      |    when cond :
      |      out <= in
      |""".stripMargin)
    result should containTree { case Port(_, "out", Output, AsyncResetType) => true }
  }

  it should "allow ResetType to drive AsyncResets or UInt<1>" in {
    val result1 = compile(s"""
      |circuit top :
      |  module top :
      |    input in : UInt<1>
      |    output out : UInt<1>
      |    wire w : Reset
      |    w <= in
      |    out <= w
      |""".stripMargin
    )
    result1 should containTree { case DefWire(_, "w", BoolType) => true }
    val result2 = compile(s"""
      |circuit top :
      |  module top :
      |    output foo : { flip a : UInt<1> }
      |    input bar : { flip a : UInt<1> }
      |    wire w : { flip a : Reset }
      |    foo <= w
      |    w <= bar
      |""".stripMargin
    )
    val AggType = BundleType(Seq(Field("a", Flip, BoolType)))
    result2 should containTree { case DefWire(_, "w", AggType) => true }
    val result3 = compile(s"""
      |circuit top :
      |  module top :
      |    input in : UInt<1>
      |    output out : UInt<1>
      |    wire w : Reset
      |    w <- in
      |    out <- w
      |""".stripMargin
    )
    result3 should containTree { case DefWire(_, "w", BoolType) => true }
  }

  it should "error if a ResetType driving UInt<1> infers to AsyncReset" in {
    an [Exception] shouldBe thrownBy {
      compile(s"""
        |circuit top :
        |  module top :
        |    input in : AsyncReset
        |    output out : UInt<1>
        |    wire w : Reset
        |    w <= in
        |    out <= w
        |""".stripMargin
      )
    }
  }

  it should "error if a ResetType driving AsyncReset infers to UInt<1>" in {
    an [Exception] shouldBe thrownBy {
      compile(s"""
        |circuit top :
        |  module top :
        |    input in : UInt<1>
        |    output out : AsyncReset
        |    wire w : Reset
        |    w <= in
        |    out <= w
        |""".stripMargin
      )
    }
  }

  it should "not allow ResetType as an Input or ExtModule output" in {
    // TODO what exception should be thrown here?
    an [CheckHighForm.ResetInputException] shouldBe thrownBy {
      val result = compile(s"""
        |circuit top :
        |  module top :
        |    input in : { foo : Reset }
        |    output out : Reset
        |    out <= in.foo
        |""".stripMargin
      )
    }
    an [CheckHighForm.ResetExtModuleOutputException] shouldBe thrownBy {
      val result = compile(s"""
        |circuit top :
        |  extmodule ext :
        |    output out : { foo : Reset }
        |  module top :
        |    output out : Reset
        |    inst e of ext
        |    out <= e.out.foo
        |""".stripMargin
      )
    }
  }

  it should "not allow Vecs to infer different Reset Types" in {
    an [CheckTypes.InvalidConnect] shouldBe thrownBy {
      val result = compile(s"""
        |circuit top :
        |  module top :
        |    input reset0 : AsyncReset
        |    input reset1 : UInt<1>
        |    output out : Reset[2]
        |    out[0] <= reset0
        |    out[1] <= reset1
        |""".stripMargin
      )
    }
  }

  // Or is this actually an error? The behavior is that out is inferred as AsyncReset[2]
  ignore should "not allow Vecs only be partially inferred" in {
    // Some exception should be thrown, TODO figure out which one
    an [Exception] shouldBe thrownBy {
      val result = compile(s"""
        |circuit top :
        |  module top :
        |    input reset : AsyncReset
        |    output out : Reset[2]
        |    out is invalid
        |    out[0] <= reset
        |""".stripMargin
      )
    }
  }

  it should "support inferring modules that would dedup differently" in {
    // val input =
    //   """|circuit top:
    //      |  module child:
    //      |    input childReset: Reset
    //      |    node r = UInt<1>(0)
    //      |  module top:
    //      |    input reset1: UInt<1>
    //      |    input reset2: AsyncReset
    //      |    inst c1 of child
    //      |    c1.childReset <= reset1
    //      |    inst c2 of child
    //      |    c2.childReset <= reset2
    //      |""".stripMargin

    val input = """|circuit Foo:
                   |  module Bar:
                   |    input reset: Reset
                   |    node x = UInt<1>(0)
                   |    skip
                   |  module Foo:
                   |    inst bar of Bar
                   |""".stripMargin

    val inputState = CircuitState(
      Parser.parse(input),
      ChirrtlForm,
      Seq(
        DontTouchAnnotation(CircuitTarget("Foo").module("Bar").ref("x"))
      )
    )

    val outputState = Logger.makeScope(
      Seq(
        ClassLogLevelAnnotation("firrtl.transforms.DedupModules", LogLevel.Info),
        ClassLogLevelAnnotation("firrtl.annotations.transforms.EliminateTargetPaths",  LogLevel.Info),
        ClassLogLevelAnnotation("firrtl.transforms.InferResets", LogLevel.Info))){
      Seq(
        new IRToWorkingIR,
        new ResolveAndCheck,
        new InferResets,
        new firrtl.transforms.DedupModules).foldLeft(inputState){ case (a, b) => b.runTransform(a) }
    }

    outputState.annotations.foreach(a => info(a.serialize))
    info(outputState.circuit.serialize)

    val dontTouches = outputState.annotations.collect{ case a: DontTouchAnnotation => a }

    dontTouches.zip(Seq(DontTouchAnnotation(CircuitTarget("Foo").module("Bar___Foo_bar").ref("x")))).foreach{
      case (a, b) =>
        val Seq(aa, bb) = Seq(a, b)
        info(s"${aa.target.serialize} == ${bb.target.serialize}")
        aa should be (bb)
    }

    // val result = compile(inputState,
    //                      compiler = new VerilogCompiler,
    //                      annotations = Seq(DontTouchAnnotation(CircuitTarget("top").module("child").ref("r")))
    // )
    // result should containTree { case Port(_, "childReset", Input, BoolType) => true }
    // result should containTree { case Port(_, "childReset", Input, AsyncResetType) => true }
  }

  it should "deal with modules that are fully removed" in {
    import firrtl.EmittedCircuitAnnotation
    import firrtl.stage.{FirrtlStage, FirrtlSourceAnnotation}
    val input =
      """|circuit Foo:
         |  module Baz:
         |    input clk: Clock
         |    input rst: Reset
         |    input a: UInt<1>
         |    output b: UInt<1>
         |    reg a_d: UInt<1>, clk with: (reset => (rst, UInt<1>(0)))
         |    a_d <= a
         |    b <= a_d
         |
         |  module Bar:
         |    input clk: Clock
         |    input rst: Reset
         |    input a: UInt<1>
         |    output b: UInt<1>
         |    reg a_d: UInt<1>, clk with: (reset => (rst, UInt<1>(0)))
         |    inst baz of Baz
         |    baz.clk <= clk
         |    baz.rst <= rst
         |    baz.a <= a
         |    a_d <= baz.b
         |    b <= a_d
         |
         |  module Foo:
         |    input clk: Clock
         |    input rst: UInt<1>
         |    input a: UInt<1>
         |    output b: UInt<1>
         |    inst bar of Bar
         |
         |    bar.clk <= clk
         |    bar.rst <= rst
         |    bar.a <= a
         |    b <= bar.b""".stripMargin

    (new FirrtlStage)
      .execute(Array("-X", "mverilog"), Seq(FirrtlSourceAnnotation(input)))
      .foreach{
        case a: EmittedCircuitAnnotation[_] => println(a.value)
        case _ =>
      }

  }
}
