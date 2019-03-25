package noocleus

import cats.data.Validated.{Invalid, Valid}
import noocleus.semantic.{Environment, TypeAnalysis}
import noocleus.syntax.Parser

import scala.io.Source

object Application {
  
  def main(args: Array[String]): Unit = {
    val prelude =
      s"""
         |data Bool = True | False in
         |data Nat = S Nat | Z in
         |data Option a = Some a | None in
         |data List a = Cons a (List a) | Nil in
         |data Either l r = Left l | Right r in
         |
         |let id = x => x in
         |
         |let andThen = f => g => x => g (f x) in
         |let swap    = f => x => y => f y x in
         |let compose = swap andThen in
         |
         |let even = n => n match {
         |  case Z       => True
         |  case S Z     => False
         |  case S (S n) => even n
         |} in
         |
         |let if = test => then => else => test match {
         |  case True  => then
         |  case False => else
         |} in
         |
         |let &&  = x => y => if x y False in
         |let ||  = x => y => if x True y in
         |let !   = x => if x False True in
         |let ^   = x => y => || (&& x (! y)) (&& (! x) y) in
         |let biNegate = f => x => y => ! (f x y) in
         |let nand     = biNegate && in
         |let nor      = biNegate || in
         |let xnor     = biNegate ^ in
         |
         |let reverse = list =>
         |  let helper = list => acc => list match {
         |    case Cons head tail => helper tail (Cons head acc)
         |    case Nil            => acc
         |  } in helper list Nil
         |in
         |
         |let exists = list => predicate => list match {
         |  case Nil            => False
         |  case Cons head tail =>
         |    if (predicate head)
         |      True
         |      (exists tail predicate)
         |} in
         |
         |let + = a => b => a match {
         |  case S n => S (+ n b)
         |  case Z   => b
         |} in
         |
         |let * = a => b => a match {
         |  case S Z => b
         |  case Z   => Z
         |  case S n => + (* n b) b
         |} in
         |
         |let - = a => b => (a, b) match {
         |  case (a, Z)     => a
         |	case (Z, b)     => Z
         |	case (S a, S b) => - a b
         |} in
         |
         |let < = a => b => (a, b) match {
         |	case (Z, Z)     => False
         |	case (Z, b)     => True
         |	case (S a, S b) => < a b
         |} in
         |
         |let > = a => b => (a, b) match {
         |	case (Z, Z)     => False
         |	case (a, Z)     => True
         |	case (S a, S b) => > a b
         |} in
         |
         |let factorial = n =>
         |  if (> n Z)
         |    (* (factorial (- n (S Z))) n)
         |    (S Z)
         |in
         |
         |let closedRangeWithStep = start => end => step =>
         |	let loop = start => end => acc =>
         |		let subtract = < step Z in
         |		let compare  = if subtract < > in
         |		let finished = compare start end in
         |		let next	 = + start step in
         |		let recurse  = loop next end (Cons start acc) in
         |			if finished (reverse acc) recurse
         |	in loop start end Nil
         |in
         |
         |let openRangeWithStep = start => step =>
         |	let loop = start =>
         |		let next = + start step in
         |		let recurse = Cons start (loop next) in
         |			recurse
         |	in loop start
         |in
         |
         |let range = start => next => end => end match {
         |	case Some end =>
         |		next match {
         |			case Some next => closedRangeWithStep start end (- next start)
         |			case None		   => closedRangeWithStep start end (if (< start end) (S Z) (- Z (S Z)))
         |		}
         |	case None =>
         |		next match {
         |			case Some next => openRangeWithStep start (- next start)
         |			case None	     => openRangeWithStep start (S Z)
         |		}
         |} in
         |
         |let mapList = f => xs =>
         |  let loop = xs => acc => xs match {
         |    case Nil            => reverse acc
         |    case Cons head tail => loop tail (Cons (f head) acc)
         |  } in loop xs Nil
         |in
         |
         |let length = list => list match {
         |  case Nil            => Z
         |  case Cons head tail => S (length tail)
         |} in
         |
         |let concatLists = xs => ys =>
         |  let helper = xs => ys => xs match {
         |    case Nil            => ys
         |    case Cons head tail => helper tail (Cons head ys)
         |  } in helper (reverse xs) ys
         |in
         |
         |let flatten = xs =>
         |  let helper = xs => acc => xs match {
         |    case Nil                        => reverse acc
         |    case Cons Nil rest              => helper rest acc
         |    case Cons (Cons head tail) rest => helper (Cons tail rest) (Cons head acc)
         |  } in helper xs Nil
         |in
         |
         |let flatMapList = f => xs => flatten (mapList f xs) in
         |
         |let either = f => g => either => either match {
         |  case Left l  => f l
         |  case Right r => g r
         |} in
         |
         |let foldList = z => f => xs => xs match {
         |  case Nil            => z
         |  case Cons head tail => foldList (f z head) f tail
         |} in
         |
       """.stripMargin
  
    print("> ")
    System.out.flush()
    
    for (line <- Source.stdin.getLines()) {
      val result = Parser.parse(prelude + line)
        .andThen(TypeAnalysis.inferSigma(_)(Environment()).unsafeRunSync())
      
      result match {
        case Valid(sigma) =>
          println(": " + sigma)
        case Invalid(error) =>
          println(error)
      }
      
      print("> ")
      System.out.flush()
    }
  }
  
}
